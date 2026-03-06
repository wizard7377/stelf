# 1 "src/lambda/constraints.sig.ml"
open! Basis;;
(* Manipulating Constraints *);;
(* Author: Jeff Polakow, Frank Pfenning *);;
(* Modified: Roberto Virga *);;
module type CONSTRAINTS = sig
                          (*! structure IntSyn : INTSYN !*)
                          exception Error of IntSyn.cnstr list 
                          val
                            simplify : IntSyn.cnstr list -> IntSyn.cnstr list
                          val warnConstraints : string list -> unit
                          end;;
(* signature CONSTRAINTS *);;
# 1 "src/lambda/constraints.fun.ml"
open! Conv;;
open! Basis;;
(* Manipulating Constraints *);;
(* Author: Jeff Polakow, Frank Pfenning *);;
(* Modified: Roberto Virga *);;
module Constraints(Constraints__0: sig module Conv : CONV end) : CONSTRAINTS
  =
  struct
    (*! structure IntSyn = IntSyn' !*);;
    exception Error of IntSyn.cnstr list ;;
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
  *);;
    open!
      struct
        module I = IntSyn;;
        let rec simplify =
          function 
                   | [] -> []
                   | ({ contents = solved_} :: cnstrs) -> simplify cnstrs
                   | (({ contents = I.Eqn (g_, u1_, u2_)} as eqn_) :: cnstrs)
                       -> begin
                       if Conv.conv ((u1_, I.id), (u2_, I.id)) then
                       simplify cnstrs else (Eqn :: simplify cnstrs) end
                   | (({ contents = I.FgnCnstr csfc} as fgnCnstr_) :: cnstrs)
                       -> begin
                       if I.FgnCnstrStd.Simplify.apply csfc () then
                       simplify cnstrs else (fgnCnstr_ :: simplify cnstrs)
                       end;;
        let rec namesToString =
          function 
                   | (name :: []) -> name ^ "."
                   | (name :: names) -> (name ^ ", ") ^ (namesToString names);;
        let rec warnConstraints =
          function 
                   | [] -> ()
                   | names
                       -> print
                          (("Constraints remain on " ^ (namesToString names))
                             ^ "\n");;
        end;;
    (* simplify cnstrs = cnstrs'
       Effects: simplifies the constraints in cnstrs by removing constraints
         of the form U = U' where G |- U == U' : V (mod beta/eta)
         Neither U nor U' needs to be a pattern
         *);;
    let simplify = simplify;;
    let namesToString = namesToString;;
    let warnConstraints = warnConstraints;;
    end;;
(*! structure IntSyn' : INTSYN !*);;
(*! sharing Conv.IntSyn = IntSyn' !*);;
(* functor Constraints *);;
# 1 "src/lambda/constraints.sml.ml"
