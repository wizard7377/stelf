(* # 1 "src/compile/Cprint.sig.ml" *)
open! Basis

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
include Cprint_intf
(* signature CPRINT *)

(* # 1 "src/compile/Cprint.fun.ml" *)
open! Basis

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
module Make_CPrint
    (Print_ : PRINT)
    (Formatter_ : FORMATTER)
    (Names_ : NAMES) :
  CPRINT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  module Print = Print_
  module Formatter = Formatter_
  module Names = Names_
  open! CompSyn.CompSyn

  let rec compose = function
    | IntSyn.Null, g_ -> g_
    | IntSyn.Decl (g_, d_), g'_ -> IntSyn.Decl (compose (g_, g'_), d_)

  (* goalToString (G, g) where G |- g  goal *)
  let rec goalToString arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | t, (g_, Atom p) -> ((t ^ "SOLVE   ") ^ Print.expToString (g_, p)) ^ "\n"
    | t, (g_, Impl (p, a_, _, g)) ->
        (((((t ^ "ASSUME  ") ^ Print.expToString (g_, a_)) ^ "\n")
         ^ clauseToString (t ^ "\t") (g_, p))
        ^ goalToString t (IntSyn.Decl (g_, IntSyn.Dec (None, a_)), g))
        ^ "\n"
    | t, (g_, All (d_, g)) ->
        let d'_ = Names.decLUName (g_, d_) in
        ((((t ^ "ALL     ")
          ^ Print.Formatter.makestring_fmt (Print.formatDec (g_, d'_)))
         ^ "\n")
        ^ goalToString t (IntSyn.Decl (g_, d'_), g))
        ^ "\n"
    end

  and auxToString arg__3 arg__4 =
    begin match (arg__3, arg__4) with
    | t, (g_, Trivial) -> ""
    | t, (g_, UnifyEq (g'_, p1, n_, ga)) ->
        (((((t ^ "UNIFYEqn  ") ^ Print.expToString (compose (g'_, g_), p1))
          ^ " = ")
         ^ Print.expToString (compose (g'_, g_), n_))
        ^ "\n")
        ^ auxToString t (g_, ga)
    end

  and clauseToString arg__5 arg__6 =
    begin match (arg__5, arg__6) with
    | t, (g_, Eq p) -> ((t ^ "UNIFY   ") ^ Print.expToString (g_, p)) ^ "\n"
    | t, (g_, Assign (p, ga)) ->
        (((t ^ "ASSIGN  ") ^ try Print.expToString (g_, p) with _ -> "<exc>")
        ^ "\n")
        ^ auxToString t (g_, ga)
    | t, (g_, And (r, a_, g)) ->
        clauseToString t (IntSyn.Decl (g_, IntSyn.Dec (None, a_)), r)
        ^ goalToString t (g_, g)
    | t, (g_, In (r, a_, g)) ->
        let d_ = Names.decEName (g_, IntSyn.Dec (None, a_)) in
        ((((clauseToString t (IntSyn.Decl (g_, d_), r) ^ t) ^ "META    ")
         ^ Print.decToString (g_, d_))
        ^ "\n")
        ^ goalToString t (g_, g)
    | t, (g_, Exists (d_, r)) ->
        let d'_ = Names.decEName (g_, d_) in
        (((t ^ "EXISTS  ") ^ try Print.decToString (g_, d'_) with _ -> "<exc>")
        ^ "\n")
        ^ clauseToString t (IntSyn.Decl (g_, d'_), r)
    | t, (g_, Axists ((IntSyn.ADec (Some n, d) as d_), r)) ->
        let d'_ = Names.decEName (g_, d_) in
        (((t ^ "EXISTS'  ")
         ^ try Print.decToString (g_, d'_) with _ -> "<exc>")
        ^ "\n")
        ^ clauseToString t (IntSyn.Decl (g_, d'_), r)
    end

  (* auxToString (G, r) where G |- r auxgoal *)
  (* clauseToString (G, r) where G |- r  resgoal *)
  let rec subgoalsToString arg__7 arg__8 =
    begin match (arg__7, arg__8) with
    | t, (g_, True) -> t ^ "True "
    | t, (g_, Conjunct (goal_, a_, sg_)) ->
        ((t ^ goalToString t (IntSyn.Decl (g_, IntSyn.Dec (None, a_)), goal_))
        ^ " and ")
        ^ subgoalsToString t (g_, sg_)
    end

  (* conDecToString (c, clause) printed representation of static clause *)
  let rec conDecToString = function
    | c, SClause r ->
        let _ = Names.varReset IntSyn.Null in
        let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
        let l = String.size name in
        (name
        ^ begin if l > 6 then ":\n" else ":"
        end)
        ^ clauseToString "\t" (IntSyn.Null, r)
        ^ "\n"
    | c, Void -> Print.conDecToString (IntSyn.sgnLookup c) ^ "\n\n"

  (* sProgToString () = printed representation of static program *)
  let rec sProgToString () =
    let size, _ = IntSyn.sgnSize () in
    let rec ts cid =
      begin if cid < size then
        conDecToString (cid, sProgLookup cid) ^ ts (cid + 1)
      else ""
      end
    in
    ts 0

  (* dProgToString (G, dProg) = printed representation of dynamic program *)
  let rec dProgToString = function
    | DProg (Null, Null) -> ""
    | DProg
        ( IntSyn.Decl (g_, IntSyn.Dec (Some x, _)),
          IntSyn.Decl (dPool, CompSyn.CompSyn.Dec (r, _, _)) ) ->
        (((dProgToString (DProg (g_, dPool)) ^ "\nClause    ") ^ x) ^ ":\n")
        ^ clauseToString "\t" (g_, r)
    | DProg
        ( IntSyn.Decl (g_, IntSyn.Dec (Some x, a_)),
          IntSyn.Decl (dPool, parameter_) ) ->
        (((dProgToString (DProg (g_, dPool)) ^ "\nParameter ") ^ x) ^ ":\t")
        ^ Print.expToString (g_, a_)
  (* case for CompSyn.BDec is still missing *)
end
(*! sharing Names.IntSyn = IntSyn' !*)
(* local open ... *)
(* functor CPrint *)

module CPrint = Make_CPrint (Print) (Formatter) (Names)

(* # 1 "src/compile/Cprint.sml.ml" *)
