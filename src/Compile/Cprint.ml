open! Intsyn.Lambda_
open! Names.Names_
open! Print.Print_
open! Formatter__Formatter_

(* # 1 "src/compile/Cprint.sig.ml" *)

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
include CPRINT
(* signature CPRINT *)

(* # 1 "src/compile/Cprint.fun.ml" *)
open! Basis

(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)
module Make_CPrint (Print_ : PRINT) (Formatter_ : FORMATTER) (Names_ : NAMES) :
  CPRINT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  module Print = Print_
  module Formatter = Formatter_
  module Names = Names_
  open! CompSyn.CompSyn

  let rec compose = function
    | IntSyn.Null, g -> g
    | IntSyn.Decl (g, d), g' -> IntSyn.Decl (compose (g, g'), d)

  (* goalToString (G, g) where G |- g  goal *)
  let rec goalToString arg__1 arg__2 =
    begin match (arg__1, arg__2) with
    | t, (g, Atom p) -> ((t ^ "SOLVE   ") ^ Print.expToString g p) ^ "\n"
    | t, (g_, Impl (p, a, _, g)) ->
        (((((t ^ "ASSUME  ") ^ Print.expToString g_ a) ^ "\n")
         ^ clauseToString (t ^ "\t") (g_, p))
        ^ goalToString t (IntSyn.Decl (g_, IntSyn.Dec (None, a)), g))
        ^ "\n"
    | t, (g_, All (d, g)) ->
        let d' = Names.decLUName g_ d in
        ((((t ^ "ALL     ")
          ^ Print.Formatter.makestring_fmt (Print.formatDec g_ d'))
         ^ "\n")
        ^ goalToString t (IntSyn.Decl (g_, d'), g))
        ^ "\n"
    end

  and auxToString arg__3 arg__4 =
    begin match (arg__3, arg__4) with
    | t, (g, Trivial) -> ""
    | t, (g, UnifyEq (g', p1, n, ga)) ->
        (((((t ^ "UNIFYEqn  ") ^ Print.expToString (compose (g', g)) p1)
          ^ " = ")
         ^ Print.expToString (compose (g', g)) n)
        ^ "\n")
        ^ auxToString t (g, ga)
    end

  and clauseToString arg__5 arg__6 =
    begin match (arg__5, arg__6) with
    | t, (g, Eq p) -> ((t ^ "UNIFY   ") ^ Print.expToString g p) ^ "\n"
    | t, (g, Assign (p, ga)) ->
        (((t ^ "ASSIGN  ") ^ try Print.expToString g p with _ -> "<exc>")
        ^ "\n")
        ^ auxToString t (g, ga)
    | t, (g_, And (r, a, g)) ->
        clauseToString t (IntSyn.Decl (g_, IntSyn.Dec (None, a)), r)
        ^ goalToString t (g_, g)
    | t, (g_, In (r, a, g)) ->
        let d = Names.decEName g_ (IntSyn.Dec (None, a)) in
        ((((clauseToString t (IntSyn.Decl (g_, d), r) ^ t) ^ "META    ")
         ^ Print.decToString g_ d)
        ^ "\n")
        ^ goalToString t (g_, g)
    | t, (g, Exists (d, r)) ->
        let d' = Names.decEName g d in
        (((t ^ "EXISTS  ") ^ try Print.decToString g d' with _ -> "<exc>")
        ^ "\n")
        ^ clauseToString t (IntSyn.Decl (g, d'), r)
    | t, (g, Axists ((IntSyn.ADec (Some n, d) as d_), r)) ->
        let d' = Names.decEName g d_ in
        (((t ^ "EXISTS'  ")
         ^ try Print.decToString g d' with _ -> "<exc>")
        ^ "\n")
        ^ clauseToString t (IntSyn.Decl (g, d'), r)
    end

  (* auxToString (G, r) where G |- r auxgoal *)
  (* clauseToString (G, r) where G |- r  resgoal *)
  let rec subgoalsToString arg__7 arg__8 =
    begin match (arg__7, arg__8) with
    | t, (g, True) -> t ^ "True "
    | t, (g, Conjunct (goal, a, sg)) ->
        ((t ^ goalToString t (IntSyn.Decl (g, IntSyn.Dec (None, a)), goal))
        ^ " and ")
        ^ subgoalsToString t (g, sg)
    end

  (* conDecToString (c, clause) printed representation of static clause *)
  let conDecToString (c, a) = match a with
    | SClause r ->
        ignore (Names.varReset IntSyn.Null);
        let name = IntSyn.conDecName (IntSyn.sgnLookup c) in
        let l = String.size name in
        (name
        ^ begin if l > 6 then ":\n" else ":"
        end)
        ^ clauseToString "\t" (IntSyn.Null, r)
        ^ "\n"
    | Void -> Print.conDecToString (IntSyn.sgnLookup c) ^ "\n\n"

  (* sProgToString () = printed representation of static program *)
  let sProgToString () =
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
        ( IntSyn.Decl (g, IntSyn.Dec (Some x, _)),
          IntSyn.Decl (dPool, CompSyn.CompSyn.Dec (r, _, _)) ) ->
        (((dProgToString (DProg (g, dPool)) ^ "\nClause    ") ^ x) ^ ":\n")
        ^ clauseToString "\t" (g, r)
    | DProg
        ( IntSyn.Decl (g, IntSyn.Dec (Some x, a)),
          IntSyn.Decl (dPool, parameter) ) ->
        (((dProgToString (DProg (g, dPool)) ^ "\nParameter ") ^ x) ^ ":\t")
        ^ Print.expToString g a
  (* case for CompSyn.BDec is still missing *)
end
(*! sharing Names.IntSyn = IntSyn' !*)
(* local open ... *)
(* functor CPrint *)

module CPrint = Make_CPrint (Print) (Formatter) (Names)

(* # 1 "src/compile/Cprint.sml.ml" *)
