(* # 1 "src/frontend/recon_query.sig.ml" *)
open! Basis

(* External Syntax for queries *)
(* Author: Frank Pfenning *)
module type EXTQUERY = sig
  module ExtSyn : Recon_term.EXTSYN

  (*! structure Paths : PATHS !*)
  type nonrec query

  (* query *)
  val query : string option * ExtSyn.term -> query

  (* ucid : tm | tm *)
  type nonrec define

  val define : string option * ExtSyn.term * ExtSyn.term option -> define

  type nonrec solve

  val solve : string option * ExtSyn.term * Paths.region -> solve
end

(* id : tm | _ : tm *)
(* signature EXTQUERY *)
module type RECON_QUERY = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTQUERY

  exception Error of string

  val queryToQuery :
    query * Paths.location ->
    IntSyn.exp * string option * (IntSyn.exp * string) list

  (* (A, SOME(""X""), [(Y1, ""Y1""),...] *)
  (* where A is query type, X the optional proof term variable name *)
  (* Yi the EVars in the query and ""Yi"" their names *)
  val solveToSolve :
    define list * solve * Paths.location ->
    IntSyn.exp * (IntSyn.exp -> (IntSyn.conDec * Paths.occConDec option) list)
end
(* signature RECON_QUERY *)

(* # 1 "src/frontend/recon_query.fun.ml" *)
open! Basis

module ReconQuery (ReconQuery__0 : sig
  (* Reconstruct queries *)
  (* Author: Frank Pfenning *)
  (* Modified: Roberto Virga, Jeff Polakow *)
  module Global : GLOBAL

  (*! structure IntSyn' : INTSYN !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  (*! structure Paths' : PATHS !*)
  module ReconTerm' : Recon_term.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
  (*! sharing ReconTerm'.Paths = Paths' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Strict : STRICT

  (*! sharing Strict.IntSyn = IntSyn' !*)
  (*! sharing Strict.Paths = Paths' !*)
  module Timers : Timers.TIMERS
  module Print : PRINT
end) : RECON_QUERY = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  module Timers = ReconQuery__0.Timers
  module ExtSyn = ReconQuery__0.ReconTerm'
  module T = ReconQuery__0.ReconTerm'

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type nonrec name = string

  (* Queries, with optional proof term variable *)
  type query = Query_ of name option * T.term

  let rec query (nameOpt, tm) = Query_ (nameOpt, tm)

  (* define := <constant name> option * <def body> * <type> option *)
  type define = Define_ of string option * T.term * T.term option
  type solve = Solve_ of string option * T.term * Paths.region

  let rec define (nameOpt, tm1, tm2Opt) = Define_ (nameOpt, tm1, tm2Opt)
  let rec solve (nameOpt, tm, r) = Solve_ (nameOpt, tm, r)

  (* freeVar (XOpt, [(X1,""X1""),...,(Xn,""Xn"")]) = true
     iff XOpt = SOME(""Xi""), false otherwise
  *)
  let rec freeVar = function
    | Some name, xs_ -> List.exists (function _, name' -> name = name') xs_
    | _ -> false

  (* queryToQuery (q) = (V, XOpt, [(X1,""X1""),...,(Xn,""Xn"")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
  (* call TypeCheck... if !doubleCheck = true? *)
  (* Wed May 20 08:00:28 1998 -fp *)
  let rec queryToQuery (Query_ (optName, tm), Paths.Loc (fileName, r)) =
    let _ = Names.varReset IntSyn.Null in
    let _ = T.resetErrors fileName in
    let (T.JClass ((v_, oc), l_)) =
      Timers.time Timers.recon T.reconQuery (T.jclass tm)
    in
    let _ = T.checkErrors r in
    let _ =
      begin match l_ with
      | IntSyn.Type -> ()
      | _ -> error (r, "Query was not a type")
      end
    in
    let xs_ = Names.namedEVars () in
    let _ =
      begin if freeVar (optName, xs_) then
        error (r, ("Proof term variable " ^ valOf optName) ^ " occurs in type")
      else ()
      end
    in
    (v_, optName, xs_)
  (* construct an external term for the result of the query
        val res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *)
  (* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName ""occur"" in a constraint involving the type
           without being detected by this test?  -kw *)

  let rec finishDefine
      (Define_ (optName, tm, clsOpt), ((u_, oc1), (v_, oc2Opt), l_)) =
    let i, (u'_, v'_) =
      try Timers.time Timers.abstract Abstract.abstractDef (u_, v_)
      with Abstract.Error msg ->
        raise (Abstract.Error (Paths.wrap (Paths.toRegion oc1, msg)))
    in
    let name =
      begin match optName with None -> "_" | Some name -> name
      end
    in
    let ocd = Paths.def (i, oc1, oc2Opt) in
    let cd =
      try
        begin
          Strict.check ((u'_, v'_), Some ocd);
          IntSyn.ConDef (name, None, i, u'_, v'_, l_, IntSyn.ancestor u'_)
        end
      with Strict.Error _ -> IntSyn.AbbrevDef (name, None, i, u'_, v'_, l_)
    in
    let cd = Names.nameConDec cd in
    let _ =
      begin if !Global.chatter >= 3 then
        print (Timers.time Timers.printing Print.conDecToString cd ^ "\n")
      else ()
      end
    in
    let _ =
      begin if !Global.doubleCheck then begin
        Timers.time Timers.checking TypeCheck.check (v'_, IntSyn.Uni l_);
        Timers.time Timers.checking TypeCheck.check (u'_, v'_)
      end
      else ()
      end
    in
    let conDecOpt =
      begin match optName with None -> None | Some _ -> Some cd
      end
    in
    (conDecOpt, Some ocd)
  (* is this necessary? -kw *)

  let rec finishSolve (Solve_ (nameOpt, tm, r), u_, v_) =
    let i, (u'_, v'_) =
      try Timers.time Timers.abstract Abstract.abstractDef (u_, v_)
      with Abstract.Error msg -> raise (Abstract.Error (Paths.wrap (r, msg)))
    in
    let name =
      begin match nameOpt with None -> "_" | Some name -> name
      end
    in
    let cd =
      try
        begin
          Strict.check ((u'_, v'_), None);
          IntSyn.ConDef
            (name, None, i, u'_, v'_, IntSyn.Type, IntSyn.ancestor u'_)
        end
      with Strict.Error _ ->
        IntSyn.AbbrevDef (name, None, i, u'_, v'_, IntSyn.Type)
    in
    let cd = Names.nameConDec cd in
    let _ =
      begin if !Global.chatter >= 3 then
        print (Timers.time Timers.printing Print.conDecToString cd ^ "\n")
      else ()
      end
    in
    let _ =
      begin if !Global.doubleCheck then begin
        Timers.time Timers.checking TypeCheck.check (v'_, IntSyn.Uni IntSyn.Type);
        Timers.time Timers.checking TypeCheck.check (u'_, v'_)
      end
      else ()
      end
    in
    let conDecOpt =
      begin match nameOpt with None -> None | Some _ -> Some cd
      end
    in
    conDecOpt
  (* is this necessary? -kw *)

  (* queryToQuery (q) = (V, XOpt, [(X1,""X1""),...,(Xn,""Xn"")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names
 
     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
  (* call TypeCheck... if !doubleCheck = true? *)
  (* Wed May 20 08:00:28 1998 -fp *)
  let rec solveToSolve
      (defines, (Solve_ (optName, tm, r0) as sol), Paths.Loc (fileName, r)) =
    let _ = Names.varReset IntSyn.Null in
    let _ = T.resetErrors fileName in
    let rec mkd = function
      | Define_ (_, tm1, None) -> T.jterm tm1
      | Define_ (_, tm1, Some tm2) -> T.jof (tm1, tm2)
    in
    let rec mkj = function
      | [] -> T.jnothing
      | def :: defs -> T.jand (mkd def, mkj defs)
    in
    let (T.JAnd (defines', T.JClass ((v_, _), l_))) =
      Timers.time Timers.recon T.reconQuery (T.jand (mkj defines, T.jclass tm))
    in
    let _ = T.checkErrors r in
    let _ =
      begin match l_ with
      | IntSyn.Type -> ()
      | _ -> error (r0, "Query was not a type")
      end
    in
    let rec sc = function
      | m_, [], _ -> begin
          match finishSolve (sol, m_, v_) with
          | None -> []
          | Some conDec_ -> [ (conDec_, None) ]
        end
      | m_, def :: defs, T.JAnd (T.JTerm ((u_, oc1), v_, l_), f) -> begin
          match finishDefine (def, ((u_, oc1), (v_, None), l_)) with
          | None, _ -> sc (m_, defs, f)
          | Some conDec_, ocdOpt -> (conDec_, ocdOpt) :: sc (m_, defs, f)
        end
      | m_, def :: defs, T.JAnd (T.JOf ((u_, oc1), (v_, oc2), l_), f) -> begin
          match finishDefine (def, ((u_, oc1), (v_, Some oc2), l_)) with
          | None, _ -> sc (m_, defs, f)
          | Some conDec_, ocdOpt -> (conDec_, ocdOpt) :: sc (m_, defs, f)
        end
    in
    (v_, function m_ -> sc (m_, defines, defines'))
  (* val Xs = Names.namedEVars () *)
end
(*! sharing Print.IntSyn = IntSyn' !*)
(* functor ReconQuery *)

(* # 1 "src/frontend/recon_query.sml.ml" *)
