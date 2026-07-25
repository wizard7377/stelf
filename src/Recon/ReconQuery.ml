module type RECON_QUERY = RECON_QUERY.RECON_QUERY

exception Error of string

module Make_ReconQuery
    (M : S.S)
    (RT : RECON_TERM.RECON_TERM with module M = M) :
  RECON_QUERY with module M = M = struct
  module M = M
  module Cst = M.Cst
  module Ast = M.Ast
  module Paths = M.Paths
  module Syntax = M.Syntax

  exception Error = Error

  let error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  let freeVar (opt_name, xs_) =
    match opt_name with
    | None -> false
    | Some name -> List.exists (fun (_, n) -> name = n) xs_

  let queryToQuery (q, loc) =
    let (Paths.Loc (filename, r)) = loc in
    let opt_name, tm =
      match Cst.View.Query.view q with
      | Cst.View.Query.Query (_, opt_name, tm) -> (opt_name, tm)
      | _ -> assert false
    in
    ignore (Names.varReset IntSyn.Null);
    ignore (RT.resetErrors filename);
    let (RT.JClass ((v_, _oc), l_)) = RT.reconQuery (RT.jclass tm) in
    ignore (RT.checkErrors r);
    let _ =
      match l_ with IntSyn.Type -> () | _ -> error (r, "Query was not a type")
    in
    let xs_ = Names.namedEVars () in
    let _ =
      if freeVar (opt_name, xs_) then
        error (r, "Proof term variable " ^ valOf opt_name ^ " occurs in type")
    in
    (v_, opt_name, xs_)

  (* Finish a definition within a solve/query context *)
  let finishDefine (opt_name, ((u_, oc1), (v_, oc2_opt), l_)) =
    let i, (u'_, v'_) =
      try Abstract.abstractDef (u_, v_)
      with Abstract.Error msg ->
        raise (Abstract.Error (Paths.wrap (Paths.toRegion oc1, msg)))
    in
    let name = match opt_name with None -> "_" | Some n -> n in
    let ocd = Paths.def (i, oc1, oc2_opt) in
    let cd =
      try
        Typecheck.Typecheck_.Strict.check ((u'_, v'_), None);
        IntSyn.ConDef (name, None, i, u'_, v'_, l_, IntSyn.ancestor u'_)
      with Typecheck.Typecheck_.Strict.Error _ ->
        IntSyn.AbbrevDef (name, None, i, u'_, v'_, l_)
    in
    let cd = Names.nameConDec cd in
    let _ =
      Display.chatter_s 3 ~kind:Display.Response (Print.conDecToString cd ^ "\n")
    in
    let _ =
      if !Global.doubleCheck then begin
        Typecheck.Typecheck_.TypeCheck.check (v'_, IntSyn.Uni l_);
        Typecheck.Typecheck_.TypeCheck.check (u'_, v'_)
      end
    in
    let con_dec_opt = match opt_name with None -> None | Some _ -> Some cd in
    (con_dec_opt, Some ocd)

  (* Finish a solve goal (the final result of a solveToSolve) *)
  let finishSolve (nameOpt, r, m_, v_) =
    let i, (u'_, v'_) =
      try Abstract.abstractDef (m_, v_)
      with Abstract.Error msg -> raise (Abstract.Error (Paths.wrap (r, msg)))
    in
    let name = match nameOpt with None -> "_" | Some n -> n in
    let cd =
      try
        Typecheck.Typecheck_.Strict.check ((u'_, v'_), None);
        IntSyn.ConDef (name, None, i, u'_, v'_, IntSyn.Type, IntSyn.ancestor u'_)
      with Typecheck.Typecheck_.Strict.Error _ ->
        IntSyn.AbbrevDef (name, None, i, u'_, v'_, IntSyn.Type)
    in
    let cd = Names.nameConDec cd in
    let _ =
      Display.chatter_s 3 ~kind:Display.Response (Print.conDecToString cd ^ "\n")
    in
    let _ =
      if !Global.doubleCheck then begin
        Typecheck.Typecheck_.TypeCheck.check (v'_, IntSyn.Uni IntSyn.Type);
        Typecheck.Typecheck_.TypeCheck.check (u'_, v'_)
      end
    in
    match nameOpt with None -> None | Some _ -> Some cd

  let solveToSolve (defines, sol, loc) =
    let (Paths.Loc (filename, r)) = loc in
    let nameOpt, solve_tm =
      match Cst.View.Solve.view sol with
      | Cst.View.Solve.Solve (_, nameOpt, solve_tm) -> (nameOpt, solve_tm)
      | _ -> assert false
    in
    ignore (Names.varReset IntSyn.Null);
    ignore (RT.resetErrors filename);
    (* Build job: AND of all define jobs, then the solve type *)
    let mkd d =
      let _, tm1, tm2_opt =
        match Cst.View.Define.view d with
        | Cst.View.Define.Define (_, opt, tm1, tm2_opt) -> (opt, tm1, tm2_opt)
        | _ -> assert false
      in
      match tm2_opt with None -> RT.jterm tm1 | Some tm2 -> RT.jof (tm1, tm2)
    in
    let rec mkj = function
      | [] -> RT.jnothing
      | def :: defs -> RT.jand (mkd def, mkj defs)
    in
    let combined_job = RT.jand (mkj defines, RT.jclass solve_tm) in
    let (RT.JAnd (defines', RT.JClass ((v_, _), l_))) =
      RT.reconQuery combined_job
    in
    ignore (RT.checkErrors r);
    let _ =
      match l_ with IntSyn.Type -> () | _ -> error (r, "Query was not a type")
    in
    (* Continuation: given proof term m_, iterate through defines and finish solve *)
    let rec sc (m_, defs, jobs) =
      match (defs, jobs) with
      | [], _ -> (
          match finishSolve (nameOpt, r, m_, v_) with
          | None -> []
          | Some con_dec -> [ (con_dec, None) ])
      | def :: rest_defs, RT.JAnd (RT.JTerm ((u_, oc1), v_d, l_d), rest_jobs)
        -> (
          let opt_name, _, _ =
            match Cst.View.Define.view def with
            | Cst.View.Define.Define (_, opt, tm1, tm2_opt) ->
                (opt, tm1, tm2_opt)
            | _ -> assert false
          in
          match finishDefine (opt_name, ((u_, oc1), (v_d, None), l_d)) with
          | None, _ -> sc (m_, rest_defs, rest_jobs)
          | Some con_dec, ocd_opt ->
              (con_dec, ocd_opt) :: sc (m_, rest_defs, rest_jobs))
      | ( def :: rest_defs,
          RT.JAnd (RT.JOf ((u_, oc1), (v_d, oc2), l_d), rest_jobs) ) -> (
          let opt_name, _, _ =
            match Cst.View.Define.view def with
            | Cst.View.Define.Define (_, opt, tm1, tm2_opt) ->
                (opt, tm1, tm2_opt)
            | _ -> assert false
          in
          match finishDefine (opt_name, ((u_, oc1), (v_d, Some oc2), l_d)) with
          | None, _ -> sc (m_, rest_defs, rest_jobs)
          | Some con_dec, ocd_opt ->
              (con_dec, ocd_opt) :: sc (m_, rest_defs, rest_jobs))
      | _ -> assert false
    in
    (v_, fun m_ -> sc (m_, defines, defines'))
end
