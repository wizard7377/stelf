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

  (* Skip outer text (non-% characters) between commands.
     Handles the sequences that begin with % but are NOT commands:
       %[ ... %] — block comment (skips to matching %]; nests by bracket count)
       %% ...    — line comment: a run of two-or-more % (Twelf banners such as
                   %%, %%%, %%%%, or "%%%% Header") comments to end of line
       % ...     — line comment: a single % followed by a horizontal blank
     A leading single % followed by a letter/[.] (e.g. [%sort], [%.]) is left
     untouched for [parse1] to consume as a command. *)
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
               let+ cmds = parse_cmd_list () in
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
          (let@ id, s, e =
             keyword "open" *> commit *> Modern.parse_id_list ()
           in
           let loc = mk_loc s e in
           return Cst.View.Cmd.(review @@ Open (loc, id)))
          <?> "open"
        end;
        begin
          (let@ ids, s, e =
             keyword "require" *> commit
             *> ((let+ s = Modern.parse_text () in
                  String.trim s |> String.split_on_char '/')
                <|> Modern.parse_id_list ())
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
