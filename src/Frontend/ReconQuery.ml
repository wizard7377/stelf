open! Timing
open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths.Paths_
open! Print.Print_
open! Typecheck.Typecheck_

(* # 1 "src/frontend/ReconQuery.sig.ml" *)

(* External Syntax for queries *)
(* Author: Frank Pfenning *)
include RECONQUERY

(* id : tm | _ : tm *)
(* signature EXTQUERY *)
(* signature RECON_QUERY *)

(* # 1 "src/frontend/ReconQuery.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  module ReconTerm' : RECONTERM.RECON_TERM

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

  exception Error = Error

  (* error (r, msg) raises a syntax error within region r with text msg *)
  let error r msg = raise (Error (Paths.wrap r msg))

  type nonrec name = string

  (* Queries, with optional proof term variable *)
  type query = Query_ of name option * T.term

  let query nameOpt tm = Query_ (nameOpt, tm)

  (* define := <constant name> option * <def body> * <type> option *)
  type define = Define_ of string option * T.term * T.term option
  type solve = Solve_ of string option * T.term * Paths.region

  let define nameOpt tm1 tm2Opt = Define_ (nameOpt, tm1, tm2Opt)
  let solve nameOpt tm r = Solve_ (nameOpt, tm, r)

  (* freeVar (XOpt, [(X1,""X1""),...,(Xn,""Xn"")]) = true
     iff XOpt = SOME(""Xi""), false otherwise
  *)
  let freeVar = function
    | Some name, xs -> List.exists (function _, name' -> name = name') xs
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
  let queryToQuery (Query_ (optName, tm)) (Paths.Loc (fileName, r)) =
    ignore (Names.varReset IntSyn.Null);
    ignore (T.resetErrors fileName);
    let (T.JClass ((v, oc), l)) =
      Timers.time Timers.recon T.reconQuery (T.jclass tm)
    in
    ignore (T.checkErrors r);
    ignore begin match l with
      | IntSyn.Type -> ()
      | _ -> error r ("Query was not a type")
      end;
    let xs = Names.namedEVars () in
    ignore begin if freeVar (optName, xs) then
        error r (("Proof term variable " ^ valOf optName) ^ " occurs in type")
      else ()
      end;
    (v, optName, xs)
  (* construct an external term for the result of the query
        val res = (case optName
                     of NONE => T.omitted (r)
                      | SOME name => T.evar (name, r)) *)
  (* ??? Since the reconstruction of a query is subject to constraints,
           couldn't optName ""occur"" in a constraint involving the type
           without being detected by this test?  -kw *)

  let finishDefine (Define_ (optName, tm, clsOpt), ((u, oc1), (v, oc2Opt), l))
      =
    let i, (u', v') =
      try Timers.time Timers.abstract (fun () -> Abstract.abstractDef u v) ()
      with Abstract.Error msg ->
        raise (Abstract.Error (Paths.wrap (Paths.toRegion oc1) msg))
    in
    let name =
      begin match optName with None -> "_" | Some name -> name
      end
    in
    let ocd = Paths.def i oc1 oc2Opt in
    let cd =
      try
        begin
          Strict.check ((u', v'), Some ocd);
          IntSyn.ConDef (name, None, i, u', v', l, IntSyn.ancestor u')
        end
      with Strict.Error _ -> IntSyn.AbbrevDef (name, None, i, u', v', l)
    in
    let cd = Names.nameConDec cd in
    ignore (Display.chatter_s 3
        (Timers.time Timers.printing Print.conDecToString cd ^ "\n"));
    ignore begin if !Global.doubleCheck then begin
        Timers.time Timers.checking TypeCheck.check (v', IntSyn.Uni l);
        Timers.time Timers.checking TypeCheck.check (u', v')
      end
      else ()
      end;
    let conDecOpt =
      begin match optName with None -> None | Some _ -> Some cd
      end
    in
    (conDecOpt, Some ocd)
  (* is this necessary? -kw *)

  let finishSolve (Solve_ (nameOpt, tm, r), u, v) =
    let i, (u', v') =
      try Timers.time Timers.abstract (fun () -> Abstract.abstractDef u v) ()
      with Abstract.Error msg -> raise (Abstract.Error (Paths.wrap r msg))
    in
    let name =
      begin match nameOpt with None -> "_" | Some name -> name
      end
    in
    let cd =
      try
        begin
          Strict.check ((u', v'), None);
          IntSyn.ConDef
            (name, None, i, u', v', IntSyn.Type, IntSyn.ancestor u')
        end
      with Strict.Error _ ->
        IntSyn.AbbrevDef (name, None, i, u', v', IntSyn.Type)
    in
    let cd = Names.nameConDec cd in
    ignore (Display.chatter_s 3
        (Timers.time Timers.printing Print.conDecToString cd ^ "\n"));
    ignore begin if !Global.doubleCheck then begin
        Timers.time Timers.checking TypeCheck.check (v', IntSyn.Uni IntSyn.Type);
        Timers.time Timers.checking TypeCheck.check (u', v')
      end
      else ()
      end;
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
  let solveToSolve
      defines (Solve_ (optName, tm, r0) as sol) (Paths.Loc (fileName, r)) =
    ignore (Names.varReset IntSyn.Null);
    ignore (T.resetErrors fileName);
    let mkd = function
      | Define_ (_, tm1, None) -> T.jterm tm1
      | Define_ (_, tm1, Some tm2) -> T.jof tm1 tm2
    in
    let rec mkj = function
      | [] -> T.jnothing
      | def :: defs -> T.jand (mkd def) (mkj defs)
    in
    let (T.JAnd (defines', T.JClass ((v, _), l))) =
      Timers.time Timers.recon T.reconQuery (T.jand (mkj defines) (T.jclass tm))
    in
    ignore (T.checkErrors r);
    ignore begin match l with
      | IntSyn.Type -> ()
      | _ -> error r0 ("Query was not a type")
      end;
    let rec sc (m, a, b) = match a, b with
      | [], _ ->
          begin match finishSolve (sol, m, v) with
          | None -> []
          | Some conDec -> [ (conDec, None) ]
          end
      | def :: defs, T.JAnd (T.JTerm ((u, oc1), v, l), f) ->
          begin match finishDefine (def, ((u, oc1), (v, None), l)) with
          | None, _ -> sc (m, defs, f)
          | Some conDec, ocdOpt -> (conDec, ocdOpt) :: sc (m, defs, f)
          end
      | def :: defs, T.JAnd (T.JOf ((u, oc1), (v, oc2), l), f) ->
          begin match finishDefine (def, ((u, oc1), (v, Some oc2), l)) with
          | None, _ -> sc (m, defs, f)
          | Some conDec, ocdOpt -> (conDec, ocdOpt) :: sc (m, defs, f)
          end
    in
    (v, function m -> sc (m, defines, defines'))
  (* val Xs = Names.namedEVars () *)
end
(*! sharing Print.IntSyn = IntSyn' !*)
(* functor ReconQuery *)

(* # 1 "src/frontend/ReconQuery.sml.ml" *)
