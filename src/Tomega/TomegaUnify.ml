open! Intsyn
open! Intsyn.Lambda_
open! Print.Print_
open! Typecheck.Typecheck_
open! Meta

(* # 1 "src/tomega/TomegaUnify.sig.ml" *)
module Tomega = Lambda_.Tomega

(* Unification on Formulas *)
(* Author: Carsten Schuermann *)
include TOMEGAUNIFY
(* Signature TOMEGATYPECHECK *)

(* # 1 "src/tomega/TomegaUnify.fun.ml" *)
open! Basis

exception Unify of string

let () =
  Printexc.register_printer (function Unify msg -> Some msg | _ -> None)

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
  module Subordinate : Subordinate.Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  module Weaken : WEAKEN.WEAKEN
end) : TOMEGAUNIFY = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  exception Unify = Unify

  open! struct
    module I = IntSyn
    module T = Tomega

    let rec unifyFor psi f1 f2 =
      unifyForN (psi, T.forSub f1 T.id, T.forSub f2 T.id)

    and unifyForN (psi, a, b) = match a, b with
      | T.True, T.True -> ()
      | T.Ex ((d1, _), f1), T.Ex ((d2, _), f2) -> begin
          unifyDec (psi, T.UDec d1, T.UDec d2);
          unifyFor (I.Decl (psi, T.UDec d1)) f1 f2
        end
      | T.All ((d1, _), f1), T.All ((d2, _), f2) -> begin
          unifyDec (psi, d1, d2);
          unifyFor (I.Decl (psi, d1)) f1 f2
        end
      | T.FVar (_, r), f -> r := Some f
      | f, T.FVar (_, r) -> r := Some f
      | _, _ -> raise (Unify "Formula mismatch")

    and unifyDec (psi, a, b) = match a, b with
      | T.UDec d1, T.UDec d2 ->
          begin if Conv.convDec d1 I.id (d2, I.id) then ()
          else raise (Unify "Declaration mismatch")
          end
      | T.PDec (_, f1, _, _), T.PDec (_, f2, _, _) ->
          unifyFor psi f1 f2
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

(* # 1 "src/tomega/TomegaUnify.sml.ml" *)
