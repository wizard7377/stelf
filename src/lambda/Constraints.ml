(* # 1 "src/lambda/Constraints.sig.ml" *)

open! Basis
(** Constraint simplification and reporting helpers for LF terms. *)

open Intsyn

(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)
include Constraints_intf
(* signature CONSTRAINTS *)

(* # 1 "src/lambda/Constraints.fun.ml" *)
open! Conv
open! Basis
open Intsyn

(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)
(* Modified: Roberto Virga *)
module MakeConstraints (Conv : CONV) : CONSTRAINTS = struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of IntSyn.cnstr list

  (*
     Constraints cnstr are of the form (X<I>[s] = U).
     Invariants:
       G |- s : G'  G' |- X<I> : V
       G |- U : W
       G |- V[s] == W : L
       (X<>,s) is whnf, but X<>[s] is not a pattern
     If X<I> is uninstantiated, the constraint is inactive.
     If X<I> is instantiated, the constraint is active.

     Constraints are attached directly to the EVar X
     or to a descendent  -fp?
  *)
  module I = IntSyn

  let rec simplify = function
    | [] -> []
    | { contents = I.Solved } :: cnstrs -> simplify cnstrs
    | ({ contents = I.Eqn (g_, u1_, u2_) } as eqn_) :: cnstrs -> begin
        if Conv.conv ((u1_, I.id), (u2_, I.id)) then simplify cnstrs
        else eqn_ :: simplify cnstrs
      end
    | ({ contents = I.FgnCnstr (csfc_csid, csfc_ops) } as fgnCnstr_) :: cnstrs
      -> begin
        if I.FgnCnstrStd.Simplify.apply (csfc_csid, csfc_ops) () then
          simplify cnstrs
        else fgnCnstr_ :: simplify cnstrs
      end

  let rec names_to_string = function
    | name :: [] -> name ^ "."
    | name :: names -> (name ^ ", ") ^ names_to_string names

  let rec warn_constraints = function
    | [] -> ()
    | names -> print (("Constraints remain on " ^ names_to_string names) ^ "\n")

  (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where G |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *)
  let simplify = simplify
  let namesToString = names_to_string
  let warnConstraints = warn_constraints
end
(*! structure IntSyn' : INTSYN !*)
(*! sharing Conv.IntSyn = IntSyn' !*)
(* functor Constraints *)

(* # 1 "src/lambda/Constraints.sml.ml" *)
