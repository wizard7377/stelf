(* # 1 "src/tomega/tomega_unify.sig.ml" *)
open! Basis
module Tomega = Lambda_.Tomega

(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
module type TOMEGAUNIFY = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  exception Unify of string

  val unifyFor : Tomega.dec IntSyn.ctx * Tomega.for_ * Tomega.for_ -> unit
end
(* Signature TOMEGATYPECHECK *)

(* # 1 "src/tomega/tomega_unify.fun.ml" *)
open! Basis

module TomegaUnify (TomegaUnify__0 : sig
  (* Unification on Formulas *)
  (* Author: Carsten Schuermann *)
  (*! structure IntSyn' : INTSYN !*)
  (*! structure Tomega' : TOMEGA !*)
  (*! sharing Tomega'.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module TypeCheck : TYPECHECK

  (*! sharing TypeCheck.IntSyn = IntSyn' !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Normalize : Normalize.NORMALIZE

  (*! sharing Normalize.IntSyn = IntSyn' !*)
  (*! sharing Normalize.Tomega = Tomega' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega' !*)
  module Subordinate : SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Weaken : WEAKEN
end) : TOMEGAUNIFY = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Unify of string

  open! struct
    module I = IntSyn
    module T = Tomega

    let rec unifyFor (psi_, f1_, f2_) =
      unifyForN (psi_, T.forSub (f1_, T.id), T.forSub (f2_, T.id))

    and unifyForN = function
      | psi_, T.True, T.True -> ()
      | psi_, T.Ex ((d1_, _), f1_), T.Ex ((d2_, _), f2_) -> begin
          unifyDec (psi_, T.UDec d1_, T.UDec d2_);
          unifyFor (I.Decl (psi_, T.UDec d1_), f1_, f2_)
        end
      | psi_, T.All ((d1_, _), f1_), T.All ((d2_, _), f2_) -> begin
          unifyDec (psi_, d1_, d2_);
          unifyFor (I.Decl (psi_, d1_), f1_, f2_)
        end
      | psi_, T.FVar (_, r), f_ -> r := Some f_
      | psi_, f_, T.FVar (_, r) -> r := Some f_
      | psi_, _, _ -> raise (Unify "Formula mismatch")

    and unifyDec = function
      | psi_, T.UDec d1_, T.UDec d2_ -> begin
          if Conv.convDec ((d1_, I.id), (d2_, I.id)) then ()
          else raise (Unify "Declaration mismatch")
        end
      | psi_, T.PDec (_, f1_, _, _), T.PDec (_, f2_, _, _) ->
          unifyFor (psi_, f1_, f2_)
  end

  (* unifyFor (Psi, F1, F2) = R

       Invariant:
       If   F1, F2 contain free variables X1 ... Xn
       and  Psi |- F1 for
       and  Psi |- F2 for
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- F1[I] = F2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
  (* unifyDec (Psi, D1, D2) = R

       Invariant:
       If   D1, D2 contain free variables X1 ... Xn
       and  Psi |- D1 dec
       and  Psi |- D2 dec
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- D1[I] = D2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
  let unifyFor = unifyFor
end
(*! sharing Weaken.IntSyn = IntSyn' !*)

(* # 1 "src/tomega/tomega_unify.sml.ml" *)
