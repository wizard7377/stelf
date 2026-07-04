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

  (* Skip outer text (non-% characters) between commands.
     Handles three special sequences starting with %:
       %%%       — escape for a literal %
       %% ...    — line comment (skips to end of line)
       %{! ... !}% — block comment (skips to matching !}%) *)
  let skip_outer : unit t =
    fix (fun self ->
      skip_while (fun c -> c <> '%')
      *> option ()
           (   (string "%%%" *> commit *> self)
           <|> (string "%%" *> commit
                *> skip_while (fun c -> c <> '\n')
                *> self)
           <|> (string "%{!" *> commit
                *> fix (fun inner ->
                     skip_while (fun c -> c <> '!')
                     *> ((string "!}%" *> commit)
                        <|> (char '!' *> inner)))
                *> self)))

  (* Defer a thunk-parser to prevent infinite recursion at construction time.
     Used for %module and %eval which recursively embed cmd lists. *)
  let defer p = return () >>= fun () -> p ()

  let parse_order () : Cst.View.Thm.Order.t t =
    fix (fun self ->
        begin
          choice ~failure_msg:"order"
            [
              (let+ ids = Modern.parse_id_list () in
               Cst.View.(
                 Thm.Order.(review @@ Varg (Cst.View.Loc.(review Ghost), ids))));
              inside "[" "]"
                (commit
                *> let+ orders = many1 (self <* commit) in
                   Cst.View.(
                     Thm.Order.(
                       review @@ Simul (Cst.View.Loc.(review Ghost), orders))));
              inside "{" "}"
                (commit
                *> let+ orders = many1 (self <* commit) in
                   Cst.View.(
                     Thm.Order.(
                       review @@ Lex (Cst.View.Loc.(review Ghost), orders))));
            ]
        end)

  let order_list () : Cst.View.Thm.Order.t list t =
    inside "(" ")" (many1 (parse_order ()))
    <|> let+ x = parse_order () in
        [ x ]

  let rec parse_cmd_list () : Cst.cmd list t =
    keyword "{" *> commit *> skip_outer *> many (defer parse1 <* skip_outer)
    <* keyword "}" *> commit

  and parse1 () : Cst.cmd t =
    choice ~failure_msg:"command"
      [
        begin
          whitespace *> (keyword "." *> commit *> skip_outer *> return (Cst.View.Cmd.(review @@ Stop (ghost', ()))))
          (* querytabled BEFORE query — "query" is a prefix of "querytabled" *)
        end;
        begin
          (keyword "querytabled" *> commit
          *>
          let+ n, b, d, q = Modern.parse_query () in
          Cst.View.Cmd.(review @@ QueryTabled (ghost', n, b, d, q)))
          <?> "querytabled"
        end;
        begin
          (keyword "query" *> commit
          *>
          let+ n, b, d, q = Modern.parse_query () in
          Cst.View.Cmd.(review @@ Query (ghost', n, b, d, q)))
          <?> "query"
        end;
        begin
          (keyword "?" *> commit
          *>
          let+ tm = Modern.parse_expr () in
          Cst.View.Cmd.(review @@ AdhocQuery (ghost', Cst.View.Query.(review @@ Query (ghost', None, tm)))))
          <?> "adhoc query"
        end;
        begin
          (keyword "unique" *> commit
          *>
          let+ tm = Modern.parse_expr () in
          Cst.View.Cmd.(review @@ Unique (ghost', tm))
          (* module BEFORE mode — "mode" is a prefix of "module" *))
          <?> "unique"
        end;
        begin
          keyword "scope" *> commit
          *>
          let* id = Modern.parse_var () in
          let+ cmds = parse_cmd_list () in
          Cst.View.Cmd.(
            review @@ Scope (Cst.View.Loc.(review Ghost), id, review @@ Eval (ghost', cmds)))
        end;
        begin
          (keyword "mode" *> commit
          *>
          let+ md = Modern.parse_mode_dec () in
          Cst.View.Cmd.(review @@ Mode (ghost', md)) (* TODO Check this *))
          <?> "mode"
        end;
        begin
          (keywords [ "define"; "def" ]
          *> commit
          *>
          let+ d = Modern.parse_define () in
          Cst.View.Cmd.(review @@ Define (Cst.View.Loc.(review Ghost), d)))
          <?> "define"
        end;
        begin
          (keyword "decl" *> commit
          *>
          let+ tm = Modern.parse_expr () in
          Cst.View.Cmd.(review @@ DeclCmd (ghost', tm)))
          <?> "declaration"
        end;
        begin
          (keyword "inline" *> commit
          *>
          let* id = Modern.parse_var () in
          let+ tm = Modern.parse_expr () in
          Cst.View.Cmd.(review @@ Inline (ghost', id, tm)))
          <?> "inline"
        end;
        begin
          (keyword "symbol" *> commit
          *>
          let* id1 = Modern.parse_var () in
          let+ id2 = Modern.parse_var () in
          Cst.View.Cmd.(review @@ Symbol (ghost', id1, id2)))
          <?> "symbol"
        end;
        begin
          (keyword "freeze" *> commit
          *>
          let+ ids = Modern.parse_id_list () in
          Cst.View.Cmd.(review @@ Freeze (ghost', ids)))
          <?> "freeze"
        end;
        begin
          (keyword "thaw" *> commit
          *>
          let+ ids = Modern.parse_id_list () in
          Cst.View.Cmd.(review @@ Thaw (ghost', ids)))
          <?> "thaw"
        end;
        begin
          (keyword "sort" *> commit
          *>
          let* ids = Modern.parse_id_list () in
          let+ ds = many ((inside "{" "}" (commit *> Modern.parse_decl ())) <|> Modern.parse_decl_simple ()) in
          Cst.View.Cmd.(review @@ Sort (Cst.View.Loc.(review Ghost), ids, ds)))
          <?> "sort"
        end;
        begin
          (keyword "term" *> commit
          *>
          let+ d = Modern.parse_decl () in
          Cst.View.Cmd.(review @@ Term (ghost', d)))
          <?> "term"
        end;
        begin
          (keyword "block" *> commit
          *>
          let* id = Modern.parse_var () in
          let+ items = many (Modern.parse_block_item ()) in
          Cst.View.Cmd.(review @@ Block (ghost', id, items)))
          <?> "block"
        end;
        begin
          (keyword "union" *> commit
          *>
          let* id = Modern.parse_var () in
          let+ ids = inside "(" ")" (many (Modern.parse_var ())) in
          Cst.View.Cmd.(review @@ Union (ghost', id, ids)))
          <?> "union"
        end;
        begin
          (keyword "worlds" *> commit
          *>
          let* ids = inside "(" ")" (many (Modern.parse_var ())) in
          let+ tms = many1 (Modern.parse_expr1 ()) in
          Cst.View.Cmd.(review @@ Worlds (ghost', ids, tms)))
          <?> "worlds"
        end;
        begin
          (keyword "deterministic" *> commit
          *>
          let+ ids = Modern.parse_id_list () in
          Cst.View.Cmd.(review @@ Deterministic (ghost', ids)))
          <?> "deterministic"
        end;
        begin
          (keyword "use" *> commit
          *>
          let* id1 = Modern.parse_id_list () in
          let+ iparams = inside "(" ")" (many (Modern.parse_expr ())) in
          Cst.View.Cmd.(
            review @@ Use (Cst.View.Loc.(review Ghost), id1, iparams)))
          <?> "use"
        end;
        begin
          (keyword "open" *> commit
          *>
          let+ id = Modern.parse_id_list () in
          Cst.View.Cmd.(review @@ Open (Cst.View.Loc.(review Ghost), id)))
          <?> "open"
        end;
        begin
          (keyword "require" *> commit
          *>
          let+ ids =
            (let+ s = Modern.parse_text () in
             String.trim s |> String.split_on_char '/')
            <|> Modern.parse_id_list ()
          in
          Cst.View.Cmd.(review @@ Require (ghost', ids)))
          <?> "require"
        end;
        begin
          (keyword "eval" *> commit
          *>
          let+ cmds = parse_cmd_list () in
          Cst.View.Cmd.(review @@ Eval (ghost', cmds)))
          <?> "eval"
        end;
        begin
          (keyword "prec" *> commit
          *>
          let* fix = Modern.parse_fixity_kw () in
          let* n = Modern.parse_fixity () in
          let* ids = Modern.parse_id_list () in
          let () = Modern.register_local_fixity fix n ids in
          return (Cst.View.Cmd.(review @@ Prec (ghost', fix, n, ids))))
          <?> "prec"
        end;
        begin
          (keyword "solve" *> commit
          *>
          let+ s = Modern.parse_solve () in
          Cst.View.Cmd.(review @@ Solve (ghost', s)))
          <?> "solve"
        end;
        begin
          keyword "quit" *> commit *> return (Cst.View.Cmd.(review @@ ReplQuit (ghost', ()))) <?> "quit"
        end;
        begin
          (keyword "help" *> commit
          *>
          let+ t =
            option None
              (let+ id = Modern.parse_var () in
               Some id)
          in
          Cst.View.Cmd.(review @@ ReplHelp (ghost', t)))
          <?> "help"
        end;
        begin
          (keyword "get" *> commit
          *>
          let+ id = Modern.parse_var () in
          Cst.View.Cmd.(review @@ ReplGet (ghost', id)))
          <?> "get"
        end;
        begin
          (keyword "set" *> commit
          *>
          let* id = Modern.parse_var () in
          let+ v = Modern.parse_var () in
          Cst.View.Cmd.(review @@ ReplSet (ghost', id, v)))
          <?> "set"
        end;
        begin
          keyword "version" *> commit *> return (Cst.View.Cmd.(review @@ ReplVersion (ghost', ())))
          <?> "version"
        end;
        begin
          (keyword "total" *> commit
          *>
          let* order = order_list () in
          let+ body = many1 (Modern.parse_expr1 ()) in
          Cst.View.Cmd.(
            review (Total (Cst.View.Loc.(review Ghost), order, body))))
          <?> "total"
        end;
        begin
          (keyword "terminates" *> commit
          *>
          let* order = order_list () in
          let+ body = many1 (Modern.parse_expr1 ()) in
          Cst.View.Cmd.(
            review (Terminates (Cst.View.Loc.(review Ghost), order, body))))
          <?> "terminates"
        end;
        begin
          (keyword "covers" *> commit
          *>
          let+ md = Modern.parse_mode_dec () in
          Cst.View.Cmd.(review @@ Covers (ghost', md)))
          <?> "covers"
        end;
        begin
          (keyword "name" *> commit
          *>
          let+ id = Modern.parse_var () in
          Cst.View.Cmd.(review @@ Name (ghost', id)))
          <?> "name"
        end;
        begin
          (keyword "reduces" *> commit
          *>
          let* rel = Modern.parse_reduces_rel () in
          let+ body = many1 (Modern.parse_expr1 ()) in
          Cst.View.Cmd.(
            review (Reduces (Cst.View.Loc.(review Ghost), rel, body))))
          <?> "reduces"
        end;
      ]

  let parse () : Cst.cmd list t = skip_outer *> many (parse1 () <* skip_outer)
end
