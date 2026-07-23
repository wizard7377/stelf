module Macro (C : CST.CST) : MACRO.MACRO with module C = C = struct
  module C = C

  type t = int * C.cmd

  let args (n, _) = n
  let create n cmd = (n, cmd)

  let rec apply (_n, cmd) args = go_cmd 0 args cmd

  and go_cmd i args (cmd : C.cmd) : C.cmd =
    let open C.View.Cmd in
    match !>cmd with
    | Symbol _ | Freeze _ | Thaw _ | Union _ | Deterministic _ | Prec _ | Stop _
    | ReplQuit _ | ReplHelp _ | ReplGet _ | ReplSet _ | ReplVersion _ | Name _
    | Prose _ | Require _ | Open _ ->
        cmd
    | Unique (loc, tm) -> review (Unique (loc, go_term i args tm))
    | DeclCmd (loc, tm) -> review (DeclCmd (loc, go_term i args tm))
    | Inline (loc, id, tm) -> review (Inline (loc, id, go_term i args tm))
    | Worlds (loc, ids, tms) ->
        review (Worlds (loc, ids, List.map (go_term i args) tms))
    | Total (loc, orders, tms) ->
        review (Total (loc, orders, List.map (go_term i args) tms))
    | Terminates (loc, orders, tms) ->
        review (Terminates (loc, orders, List.map (go_term i args) tms))
    | Reduces (loc, pred, tms) ->
        review (Reduces (loc, pred, List.map (go_term i args) tms))
    | Use (loc, ids, tms) ->
        review (Use (loc, ids, List.map (go_term i args) tms))
    | Sort (loc, ids, decls) ->
        review (Sort (loc, ids, List.map (go_decl i args) decls))
    | Term (loc, d) -> review (Term (loc, go_decl i args d))
    | Block (loc, id, items) ->
        review (Block (loc, id, List.map (go_block_item i args) items))
    | Query (loc, n, b, d, q) ->
        review (Query (loc, n, b, d, go_query i args q))
    | QueryTabled (loc, n, b, d, q) ->
        review (QueryTabled (loc, n, b, d, go_query i args q))
    | AdhocQuery (loc, q) -> review (AdhocQuery (loc, go_query i args q))
    | Define (loc, d) -> review (Define (loc, go_define i args d))
    | Solve (loc, s) -> review (Solve (loc, go_solve i args s))
    | Mode (loc, md) -> review (Mode (loc, go_mode_dec i args md))
    | Covers (loc, md) -> review (Covers (loc, go_mode_dec i args md))
    | Eval (loc, cmds) -> review (Eval (loc, List.map (go_cmd i args) cmds))
    | Scope (loc, id, cmd') -> review (Scope (loc, id, go_cmd i args cmd'))
    | Macro (loc, n', name, cmd') ->
        assert (n' > 0);
        review (Macro (loc, n', name, go_cmd (i + 1) args cmd'))
    | Seq _ -> cmd (* view Seq_ raises failwith; this branch is unreachable *)

  and go_term i args (term : C.term) : C.term =
    let open C.View.Term in
    match !>term with
    | MacroParam (_, None, n) ->
        assert (n > 0 && n <= List.length args);
        List.nth args (n - 1)
    | MacroParam (_, Some j, n) when i > j ->
        assert (n > 0 && n <= List.length args);
        List.nth args (n - 1)
    | MacroParam (_, Some _, _) -> term
    | Lowercase _ | Uppercase _ | Qualified _ | Text _ | ExistVar _ | FreeVar _
    | Omitted _ | Typ _ | Internal _ ->
        term
    | Pi (loc, decls, body) ->
        review (Pi (loc, List.map (go_decl i args) decls, go_term i args body))
    | Lam (loc, decls, body) ->
        review (Lam (loc, List.map (go_decl i args) decls, go_term i args body))
    | App (loc, head, arg_list) ->
        review
          (App (loc, go_term i args head, List.map (go_term i args) arg_list))
    | HasType (loc, tm, ty) ->
        review (HasType (loc, go_term i args tm, go_term i args ty))
    | Arrow (loc, a, b) ->
        review (Arrow (loc, go_term i args a, go_term i args b))
    | BackArrow (loc, a, b) ->
        review (BackArrow (loc, go_term i args a, go_term i args b))
    | Foreign (loc, tm) -> review (Foreign (loc, go_term i args tm))

  and go_decl i args (decl : C.decl) : C.decl =
    let open C.View.Decl in
    match !>decl with
    | Decl1 (loc, names, ty, extra) ->
        review (Decl1 (loc, names, go_term i args ty, extra))
    | Decl0 (loc, names, ty) -> review (Decl0 (loc, names, go_term i args ty))

  and go_query i args (q : C.query) : C.query =
    let open C.View.Query in
    match !>q with
    | Query (loc, n, tm) -> review (Query (loc, n, go_term i args tm))

  and go_define i args (d : C.define) : C.define =
    let open C.View.Define in
    match !>d with
    | Define (loc, n, tm1, tm2_opt) ->
        review
          (Define
             (loc, n, go_term i args tm1, Option.map (go_term i args) tm2_opt))

  and go_solve i args (s : C.solve) : C.solve =
    let open C.View.Solve in
    match !>s with
    | Solve (loc, n, tm) -> review (Solve (loc, n, go_term i args tm))

  and go_block_item i args (bi : C.block_item) : C.block_item =
    let open C.View.BlockItem in
    match !>bi with
    | Any (loc, d) -> review (Any (loc, go_decl i args d))
    | All (loc, d) -> review (All (loc, go_decl i args d))

  and go_mode_dec i args (md : C.modeDec) : C.modeDec =
    let open C.View.Mode.Dec in
    match !>md with
    | ModeDec (loc, spine, mt) ->
        review (ModeDec (loc, spine, go_mode_term i args mt))

  and go_mode_term i args (mt : C.modeTerm) : C.modeTerm =
    let open C.View.Mode.Term in
    match !>mt with
    | ModeTerm _ -> mt
    | ModePi (loc, d, body, _) ->
        review
          (ModePi
             ( loc,
               go_decl i args d,
               go_mode_term i args body,
               go_mode_term i args body ))

  let ghost = C.View.Loc.(review Ghost)
  let reify (_, cmd) = cmd
end
