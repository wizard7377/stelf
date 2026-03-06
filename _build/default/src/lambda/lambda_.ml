# 1 "src/lambda/lambda_.sig.ml"

# 1 "src/lambda/lambda_.fun.ml"

# 1 "src/lambda/lambda_.sml.ml"
open! Basis;;
(* Now in intsyn.fun *);;
(*
structure IntSyn =
  IntSyn (structure Global = Global);
*);;
(* Now in tomega.sml *);;
(*
structure Whnf =
  Whnf (! structure IntSyn' = IntSyn !);

structure Conv =
  Conv (! structure IntSyn' = IntSyn !
	structure Whnf = Whnf);

structure Tomega : TOMEGA =
   Tomega (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure Conv = Conv)
*);;
module Constraints = (Constraints)(struct
                                     (*! structure IntSyn' = IntSyn !*);;
                                     module Conv = Conv;;
                                     end);;
module UnifyNoTrail = (Unify)(struct
                                (*! structure IntSyn' = IntSyn !*);;
                                module Whnf = Whnf;;
                                module Trail = NoTrail;;
                                end);;
module UnifyTrail = (Unify)(struct
                              (*! structure IntSyn' = IntSyn !*);;
                              module Whnf = Whnf;;
                              module Trail = Trail;;
                              end);;
(* structure Normalize : NORMALIZE =  
  Normalize (! structure IntSyn' = IntSyn !
             ! structure Tomega' = Tomega !
             structure Whnf = Whnf)
 *);;
module Match = (Match)(struct
                         module Whnf = Whnf;;
                         module Unify = UnifyTrail;;
                         module Trail = Trail;;
                         end);;
module Abstract = (Abstract)(struct
                               module Whnf = Whnf;;
                               module Constraints = Constraints;;
                               module Unify = UnifyNoTrail;;
                               end);;
module Approx = (Approx)(struct
                           (*! structure IntSyn' = IntSyn !*);;
                           module Whnf = Whnf;;
                           end);;