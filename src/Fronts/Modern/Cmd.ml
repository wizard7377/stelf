(* FIXME: Make_Cmd should be sealed with `: CMD.CMD` here, but the seal was
   removed for the same reason as Make_Modern — see Modern.ml.  Restore when
   Make_Modern carries proper `with module` constraints. *)
module Make_Cmd (Modern : MODERN.MODERN) = struct
  module Modern = Modern
  module Parser = Modern.Parser
  module Cst = Modern.Cst
  module Paths = Modern.Paths
  module Names = Modern.Names

  type 'a t = 'a Modern.t

  open Parser

  let ghost' = Cst.View.Loc.(review Ghost)
  let mk_loc = Cst.View.mk_loc

  (* Skip outer text (non-% characters) between commands.  The "outer" context
     is document/command level: the only things that live here are [%keyword]
     commands, line comments, and [%[ ... %]] prose strings.  Sequences handled:
       %% ...   — any run of two-or-more [%] starts a prose line (wiki
                  [%%! title:] metadata, [%%%%%%] banners, [%%]-commented code);
                  skipped to end of line
       % ...    — line comment (skips to end of line)
       %[ ... %] — string (multiple [[] close with the same number of []]);
                  ignorable prose in the outer context, a value in a term
     NB: the [%%X]-escapes-X-to-a-literal-token rule is an *inner* (term-lexing)
     concept and lives in [ident]/[ident1]; out here [%%] runs are just prose.
     [%%] is tried before single [%] so a bare [%%\n] is a prose line, not a
     [%]-plus-empty-comment; keeping the whole run on one skip-to-newline also
     avoids the old [%%%]-eats-triples bug on odd-length banners. *)
  let skip_outer : unit t =
    fix (fun self ->
        skip_while (fun c -> c <> '%')
        *> option ()
             (* [%[]-block comment must be tried first, else its [[] would be
                mistaken for the second [%] of a [%%] line comment. *)
             (string_lit () *> self
             (* A run of two-or-more [%] is a line comment to end of line.
                Handling the whole run here (rather than a [%%%]-escape that
                consumes exactly three) avoids leaving a stray [%] behind when
                the run length is 1 mod 3 (e.g. a bare [%%%%]), which [parse1]
                would then reject as an unrecognized command. *)
             <|> string "%%" *> commit
                 *> skip_while (fun c -> c <> '\n')
                 *> self
             (* A single [%] followed by a horizontal blank is a line comment.
                Consume ONLY the space/tab, not newline-crossing [blank]: an
                empty comment (e.g. the banner [%%%% ], whose residual [% ] has
                nothing after the space) must not swallow the newline and let
                [skip_while (<> '\n')] devour the *following* declaration.
                Leaving the newline for [self]'s leading [skip_while (<> '%')]
                keeps the skip line-scoped. *)
             <|> string "%"
                 *> skip (function ' ' | '\t' -> true | _ -> false)
                 *> commit
                 *> skip_while (fun c -> c <> '\n')
                 *> self))

  (* Defer a thunk-parser to prevent infinite recursion at construction time.
     Used for %module and %eval which recursively embed cmd lists. *)
  let defer p = return () >>= fun () -> p ()

  let parse_order () : Cst.View.Thm.Order.t t =
    fix (fun self ->
        begin
          choice ~failure_msg:"order"
            [
              (let@ ids, s, e = Modern.parse_id_list () in
               let loc = mk_loc s e in
               return Cst.View.(Thm.Order.(review @@ Varg (loc, ids))));
              (* [many], not [many1]: Twelf permits empty orders, e.g.
                 `%total {} (f _ _)` for non-recursive totality proofs. *)
              inside "[" "]"
                (commit
                *> let@ orders, s, e = many (self <* commit) in
                   let loc = mk_loc s e in
                   return Cst.View.(Thm.Order.(review @@ Simul (loc, orders))));
              inside "{" "}"
                (commit
                *> let@ orders, s, e = many (self <* commit) in
                   let loc = mk_loc s e in
                   return Cst.View.(Thm.Order.(review @@ Lex (loc, orders))));
            ]
        end)

  let order_list () : Cst.View.Thm.Order.t list t =
    (* Try [parse_order] first: it reads a parenthesised list of bare variables
       [(D1 D2 ... Dn)] as a single mutual [Varg [D1; ...; Dn]] (predicate i
       decreases on Di), which is what a mutual [%total] needs.  Only fall back
       to [( order order ... )] grouping (a list of per-predicate complex
       orders) when [parse_order] can't take the whole parenthesised group,
       e.g. [([D1] {D2})]. *)
    (let+ x = parse_order () in
     [ x ])
    <|> inside "(" ")" (many (parse_order ()))

  (* The argument of [%require], shared with the [%open %require] shorthand so
     that path-style and identifier-style arguments behave identically in both. *)
  let parse_require_arg () : string list t =
    (let+ s = Modern.parse_text () in
     String.trim s |> String.split_on_char '/')
    <|> Modern.parse_id_list ()

  (* ------------------------------------------------------------------ *)
  (* Derivation helpers for the %prop / %proof shorthands.                *)
  (*                                                                      *)
  (* All are pure functions of a FULL_MODE -- the (mode, decl) list that   *)
  (* [parse_full_mode] produces -- plus the judgement's name:              *)
  (*   DECLS       the {NAME TYPE} bindings with the modes erased          *)
  (*   INPUTS      the names of the %in-moded entries, in order            *)
  (*   HOLE_DECLS  one _ per entry                                         *)
  (*   CALL_PAT    the entries' names, non-%in positions blanked to _      *)
  (* ------------------------------------------------------------------ *)

  type full_mode = (Cst.mode * Cst.decl) list

  (* The braced, moded, named, typed prefix of a mode declaration --
     [{%in X nat} {%out Y nat}] -- keeping the (mode, decl) PAIRS.

     This deliberately mirrors the [many @@ inside "{" "}" ...] in
     [Modern.parse_mode_dec], rather than calling it: that function projects the
     names out of the decls and discards their TYPES, which is exactly what the
     derived %sort needs.  Keep the two in step if %mode's braced syntax changes.

     [many], not [many1]: a nullary judgement (%prop true) is legal and
     degenerates to a %sort plus an empty mode spine. *)
  let parse_full_mode () : full_mode t =
    many
      (inside "{" "}"
         (let* m = Modern.parse_mode () and* d = Modern.parse_decl () in
          return (m, d)))
    <?> "mode arguments"

  (* DECLS -- exactly what %sort wants. *)
  let decls_of : full_mode -> Cst.decl list = List.map snd

  (* The first name a declaration binds, or [None] when it is `_`. *)
  let decl_name (d : Cst.decl) : string option =
    match Cst.View.Decl.view d with
    | Cst.View.Decl.Decl1 (_, ns, _, _) | Cst.View.Decl.Decl0 (_, ns, _) -> (
        match ns with n :: _ -> n | [] -> None)

  let is_input (m : Cst.mode) : bool =
    match Cst.View.Mode.view m with Cst.View.Mode.Plus _ -> true | _ -> false

  (* A metavariable occurrence.  [Uppercase] vs [Lowercase] is inert here --
     [term_to_name] and [term_to_head] (Impl.ml:231-242) accept [Ucid_] and
     [Lcid_] identically, as does [lookup_head] (Impl.ml:396) -- so this picks
     the uppercase class to match the corpus idiom for mode arguments. *)
  let var_term loc n = Cst.View.Term.(review @@ Uppercase (loc, ([], n)))
  let hole loc = Cst.View.Term.(review @@ Omitted loc)

  (* NAME applied to a spine.  A flat [App] is fine: [ReconTerm.fold_app]
     left-folds it into the same nested [App_] the parser's own left-nested
     juxtaposition produces. *)
  let app_term loc name args =
    Cst.View.Term.(
      review @@ App (loc, review @@ Lowercase (loc, ([], name)), args))

  (* The %mode declaration, built directly rather than by synthesizing a head
     term and re-deriving its symbol: [Mode.Term.review] discards the spine of
     its argument and [Mode.Dec.review] discards the decls' types, so the head
     SYMBOL plus the (mode, name) spine is all the CST can carry.  This is also
     why [parse_mode_dec] gets away with an always-empty [ModeNil]. *)
  let mode_dec_of loc name (fm : full_mode) : Cst.modeDec =
    let spine = List.map (fun (m, d) -> (m, decl_name d)) fm in
    let root =
      Cst.View.Mode.Term.(
        review
        @@ ModeTerm
             (loc, ([], name), Cst.View.Mode.Spine.(review @@ ModeNil loc)))
    in
    Cst.View.Mode.Dec.(review @@ ModeDec (loc, spine, root))

  (* HOLE_DECLS -- one _ per entry, for the %worlds call pattern. *)
  let hole_args loc (fm : full_mode) = List.map (fun _ -> hole loc) fm

  (* CALL_PAT -- a named %in keeps its name; %out, %out1, %star and unnamed
     entries become holes. *)
  let call_pat loc (fm : full_mode) =
    List.map
      (fun (m, d) ->
        match (is_input m, decl_name d) with
        | true, Some n -> var_term loc n
        | _ -> hole loc)
      fm

  (* The lexicographic termination order over INPUTS.

     An unnamed input ({%in _ nat}) simply drops out rather than being an error.
     Degrading is both simpler and better-behaved than raising: [Modern.ParseError]
     escapes angstrom entirely and its handler (Modern.ml:833) renders a caret at
     character 0 of the whole file.  And the degraded form is meaningful on its
     own -- [%total {}] with `_` call-pattern arguments is the established corpus
     idiom for a non-recursive proof, and [parse_order] permits the empty order. *)
  let lex_order loc (fm : full_mode) : Cst.View.Thm.Order.t list =
    Cst.View.Thm.Order.
      [
        review
        @@ Lex
             ( loc,
               List.filter_map
                 (fun (m, d) ->
                   if is_input m then
                     Option.map
                       (fun n -> review @@ Varg (loc, [ n ]))
                       (decl_name d)
                   else None)
                 fm );
      ]

  let rec parse_cmd_list () : Cst.cmd list t =
    keyword "{" *> commit *> skip_outer *> many (defer parse1 <* skip_outer)
    <* keyword "}" *> commit

  and parse1 () : Cst.cmd t =
    choice ~failure_msg:"command"
      [
        begin
          whitespace
          *> let@ _, s, e = keyword "." *> commit *> skip_outer *> return () in
             let loc = mk_loc s e in
             return Cst.View.Cmd.(review @@ Stop (loc, ()))
          (* querytabled BEFORE query — "query" is a prefix of "querytabled" *)
        end;
        begin
          (let@ (n, b, d, q), s, e =
             keyword "querytabled" *> commit *> Modern.parse_query ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ QueryTabled (loc, n, b, d, q)))
          <?> "querytabled"
        end;
        begin
          (let@ (n, b, d, q), s, e =
             keyword "query" *> commit *> Modern.parse_query ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Query (loc, n, b, d, q)))
          <?> "query"
        end;
        begin
          (let@ tm, s, e = keyword "?" *> commit *> Modern.parse_expr () in
           let loc = mk_loc s e in
           return
             Cst.View.Cmd.(
               review
               @@ AdhocQuery
                    (loc, Cst.View.Query.(review @@ Query (ghost', None, tm)))))
          <?> "adhoc query"
        end;
        begin
          (let@ tm, s, e = keyword "unique" *> commit *> Modern.parse_expr () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Unique (loc, tm)))
          (* module BEFORE mode — "mode" is a prefix of "module" *)
          <?> "unique"
        end;
        begin
          let@ (id, cmds), s, e =
            keyword "scope" *> commit
            *> let* id = Modern.parse_var () in
               let+ cmds =
                 parse_cmd_list ()
                 <|> let+ cmd = parse1 () in
                     [ cmd ]
               in
               (id, cmds)
          in
          let loc = mk_loc s e in
          return
            Cst.View.Cmd.(
              review @@ Scope (loc, id, review @@ Eval (ghost', cmds)))
        end;
        begin
          (let@ md, s, e =
             keyword "mode" *> commit *> Modern.parse_mode_dec ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Mode (loc, md)))
          (* TODO Check this *)
          <?> "mode"
        end;
        begin
          (let@ d, s, e =
             keywords [ "define"; "def" ] *> commit *> Modern.parse_define ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Define (loc, d)))
          <?> "define"
        end;
        begin
          (let@ tm, s, e = keyword "decl" *> commit *> Modern.parse_expr () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ DeclCmd (loc, tm)))
          <?> "declaration"
        end;
        begin
          (let@ (id, tm), s, e =
             keyword "inline" *> commit
             *> let* id = Modern.parse_var () in
                let+ tm = Modern.parse_expr () in
                (id, tm)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Inline (loc, id, tm)))
          <?> "inline"
        end;
        begin
          (let@ (id1, id2), s, e =
             keyword "symbol" *> commit
             *> let* id1 = Modern.parse_var () in
                let+ id2 = Modern.parse_var () in
                (id1, id2)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Symbol (loc, id1, id2)))
          <?> "symbol"
        end;
        begin
          (let@ ids, s, e =
             keyword "freeze" *> commit *> Modern.parse_id_list ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Freeze (loc, ids)))
          <?> "freeze"
        end;
        begin
          (let@ ids, s, e =
             keyword "thaw" *> commit *> Modern.parse_id_list ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Thaw (loc, ids)))
          <?> "thaw"
        end;
        begin
          (let@ (ids, ds), s, e =
             keyword "sort" *> commit
             *> let* ids = Modern.parse_id_list () in
                let+ ds =
                  many
                    (inside "{" "}" (commit *> Modern.parse_decl ())
                    <|> Modern.parse_decl_simple ())
                in
                (ids, ds)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Sort (loc, ids, ds)))
          <?> "sort"
        end;
        begin
          (* [%data NAME DECLS CMD]  ==>  %sort NAME DECLS %. %scope NAME CMD
             A sort and the constructors inhabiting it are one unit; this writes
             the name once instead of twice.

             NAME is a single identifier rather than an id-list: [%sort] accepts
             a list for mutual sorts but [%scope] takes exactly one name, so
             mutual definitions still need the long form.

             The [loc]s below are all the same outer span on purpose --
             [Cst.View.Cmd.review] (Cst.ml:1128) discards the location of every
             command constructor, so nothing downstream can observe a finer one. *)
          (let@ (id, ds, cmds), s, e =
             keyword "data" *> commit
             *> let* id = Modern.parse_var () in
                let* ds =
                  many
                    (inside "{" "}" (commit *> Modern.parse_decl ())
                    <|> Modern.parse_decl_simple ())
                in
                let+ cmds =
                  parse_cmd_list ()
                  <|> let+ cmd = parse1 () in
                      [ cmd ]
                in
                (id, ds, cmds)
           in
           let loc = mk_loc s e in
           return
             Cst.View.Cmd.(
               review
               @@ Eval
                    ( loc,
                      [
                        review @@ Sort (loc, [ id ], ds);
                        review @@ Scope (loc, id, review @@ Eval (ghost', cmds));
                      ] )))
          <?> "data"
        end;
        begin
          (* [%prop NAME FULL_MODE]
               ==>  %{ %sort NAME DECLS %. %mode FULL_MODE (NAME ARGS) %}
             A judgement's sort and its mode are two views of the same
             information; this writes the argument list once instead of three
             times (in the %sort, in the %mode's braces, and in the %mode's
             head term). *)
          (let@ (id, fm), s, e =
             keyword "prop" *> commit
             *> let* id = Modern.parse_var () in
                let+ fm = parse_full_mode () in
                (id, fm)
           in
           let loc = mk_loc s e in
           return
             Cst.View.Cmd.(
               review
               @@ Eval
                    ( loc,
                      [
                        review @@ Sort (loc, [ id ], decls_of fm);
                        review @@ Mode (loc, mode_dec_of loc id fm);
                      ] )))
          <?> "prop"
        end;
        begin
          (* [%proof (WORLD)? NAME FULL_MODE CMD]
               ==>  %{ %sort   NAME DECLS                %.
                       %scope  NAME CMD                  %.
                       %mode   FULL_MODE (NAME ARGS)     %.
                       %worlds (WORLD) (NAME HOLE_DECLS) %.
                       %total  {INPUTS} (NAME CALL_PAT)  %}

             WORLD is optional and must be parenthesised; that is what keeps it
             unambiguous against NAME, which is a bare identifier.

             %scope (the clauses) comes BEFORE %mode on purpose.  STELF mode
             checks a whole family retroactively when the %mode is installed --
             [ModeCheck.checkMode] runs [checkAll (Index.lookup a)]
             (Modecheck.ml:867) and is reached from exactly one place,
             Impl.ml:684 -- and there is no per-clause check at install time.  So
             it is clauses declared AFTER a %mode that would escape checking, not
             before.  %worlds must likewise precede %total, whose [checkFam]
             needs both the mode and the world installed. *)
          (let@ (world, id, fm, cmds), s, e =
             keyword "proof" *> commit
             *> let* world =
                  option [] (inside "(" ")" (many (Modern.parse_var ())))
                in
                let* id = Modern.parse_var () in
                let* fm = parse_full_mode () in
                let+ cmds =
                  parse_cmd_list ()
                  <|> let+ cmd = parse1 () in
                      [ cmd ]
                in
                (world, id, fm, cmds)
           in
           let loc = mk_loc s e in
           return
             Cst.View.Cmd.(
               review
               @@ Eval
                    ( loc,
                      [
                        review @@ Sort (loc, [ id ], decls_of fm);
                        review @@ Scope (loc, id, review @@ Eval (ghost', cmds));
                        review @@ Mode (loc, mode_dec_of loc id fm);
                        review
                        @@ Worlds
                             (loc, world, [ app_term loc id (hole_args loc fm) ]);
                        review
                        @@ Total
                             ( loc,
                               lex_order loc fm,
                               [ app_term loc id (call_pat loc fm) ] );
                      ] )))
          <?> "proof"
        end;
        begin
          (let@ d, s, e = keyword "term" *> commit *> Modern.parse_decl () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Term (loc, d)))
          <?> "term"
        end;
        begin
          (let@ (id, items), s, e =
             keyword "block" *> commit
             *> let* id = Modern.parse_var () in
                let+ items = many (Modern.parse_block_item ()) in
                (id, items)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Block (loc, id, items)))
          <?> "block"
        end;
        begin
          (let@ (id, ids), s, e =
             keyword "union" *> commit
             *> let* id = Modern.parse_var () in
                let+ ids = inside "(" ")" (many (Modern.parse_var ())) in
                (id, ids)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Union (loc, id, ids)))
          <?> "union"
        end;
        begin
          (let@ (ids, tms), s, e =
             keyword "worlds" *> commit
             *> let* ids = inside "(" ")" (many (Modern.parse_var ())) in
                let+ tms = many1 (Modern.parse_expr1 ()) in
                (ids, tms)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Worlds (loc, ids, tms)))
          <?> "worlds"
        end;
        begin
          (let@ ids, s, e =
             keyword "deterministic" *> commit *> Modern.parse_id_list ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Deterministic (loc, ids)))
          <?> "deterministic"
        end;
        begin
          (let@ (id1, iparams), s, e =
             keyword "use" *> commit
             *> let* id1 = Modern.parse_id_list () in
                let+ iparams = inside "(" ")" (many (Modern.parse_expr ())) in
                (id1, iparams)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Use (loc, id1, iparams)))
          <?> "use"
        end;
        begin
          (* [%open %require NAME] is a derived form for [%require NAME] followed
             by [%open NAME].  The [%] sigil on [require] is what keeps this
             unambiguous: a scope literally named [require] is still opened by
             the bare [%open require].

             Caveat: the two commands read their id-list differently.  [%require]
             joins it with '/' into a FILE path (Loader.ml:32); [%open] splits it
             into [Qid (prefix, last)], a STRUCTURE path (Impl.ml:793).  They
             coincide only for a single-segment name, which is the intended use.
             The full [%require] grammar is accepted anyway so that the two
             commands cannot drift apart. *)
          (let@ r, s, e =
             keyword "open" *> commit
             *> ((let+ ids =
                    keyword "require" *> commit *> parse_require_arg ()
                  in
                  `Require ids)
                <|> let+ ids = Modern.parse_id_list () in
                    `Open ids)
           in
           let loc = mk_loc s e in
           return
             Cst.View.Cmd.(
               match r with
               | `Open ids -> review @@ Open (loc, ids)
               | `Require ids ->
                   review
                   @@ Eval
                        ( loc,
                          [
                            review @@ Require (loc, ids);
                            review @@ Open (loc, ids);
                          ] )))
          <?> "open"
        end;
        begin
          (let@ ids, s, e =
             keyword "require" *> commit *> parse_require_arg ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Require (loc, ids)))
          <?> "require"
        end;
        begin
          (let@ cmds, s, e = keyword "eval" *> commit *> parse_cmd_list () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Eval (loc, cmds)))
          <?> "eval"
        end;
        begin
          (let@ (fix, n, ids), s, e =
             keyword "prec" *> commit
             *> let* fix = Modern.parse_fixity_kw () in
                let* n = Modern.parse_fixity () in
                let+ ids = Modern.parse_id_list () in
                (fix, n, ids)
           in
           let loc = mk_loc s e in
           let () = Modern.register_local_fixity fix n ids in
           return Cst.View.Cmd.(review @@ Prec (loc, fix, n, ids)))
          <?> "prec"
        end;
        begin
          (let@ s_, s, e = keyword "solve" *> commit *> Modern.parse_solve () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Solve (loc, s_)))
          <?> "solve"
        end;
        begin
          (let@ _, s, e = keyword "quit" *> commit *> return () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ ReplQuit (loc, ())))
          <?> "quit"
        end;
        begin
          (let@ t, s, e =
             keyword "help" *> commit
             *> option None
                  (let+ id = Modern.parse_var () in
                   Some id)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ ReplHelp (loc, t)))
          <?> "help"
        end;
        begin
          (let@ id, s, e = keyword "get" *> commit *> Modern.parse_var () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ ReplGet (loc, id)))
          <?> "get"
        end;
        begin
          (let@ (id, v), s, e =
             keyword "set" *> commit
             *> let* id = Modern.parse_var () in
                let+ v = Modern.parse_var () in
                (id, v)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ ReplSet (loc, id, v)))
          <?> "set"
        end;
        begin
          (let@ _, s, e = keyword "version" *> commit *> return () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ ReplVersion (loc, ())))
          <?> "version"
        end;
        begin
          (let@ (order, body), s, e =
             keyword "total" *> commit
             *> let* order = order_list () in
                let+ body = many1 (Modern.parse_expr1 ()) in
                (order, body)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review (Total (loc, order, body))))
          <?> "total"
        end;
        begin
          (let@ (order, body), s, e =
             keyword "terminates" *> commit
             *> let* order = order_list () in
                let+ body = many1 (Modern.parse_expr1 ()) in
                (order, body)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review (Terminates (loc, order, body))))
          <?> "terminates"
        end;
        begin
          (let@ md, s, e =
             keyword "covers" *> commit *> Modern.parse_mode_dec ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Covers (loc, md)))
          <?> "covers"
        end;
        begin
          (let@ id, s, e = keyword "name" *> commit *> Modern.parse_var () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Name (loc, id)))
          <?> "name"
        end;
        begin
          (let@ id, s, e = keyword "prose" *> commit *> Modern.parse_var () in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Prose (loc, id)))
          <?> "prose"
        end;
        begin
          (let@ (rel, body), s, e =
             keyword "reduces" *> commit
             *> let* rel = Modern.parse_reduces_rel () in
                let+ body = many1 (Modern.parse_expr1 ()) in
                (rel, body)
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review (Reduces (loc, rel, body))))
          <?> "reduces"
        end;
      ]

  let parse () : Cst.cmd list t = skip_outer *> many (parse1 () <* skip_outer)
end
