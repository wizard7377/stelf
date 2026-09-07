open! Intsyn.Lambda_

(* # 1 "src/meta/Funweaken.sig.ml" *)
open Funsyn

(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)
include FUNWEAKEN
(* signature FUNWEAKEN *)

(* # 1 "src/meta/Funweaken.fun.ml" *)

(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)
module FunWeaken (FunWeaken__0 : sig
  module Weaken : WEAKEN.WEAKEN
end) : FUNWEAKEN.FUNWEAKEN = struct
  (*! structure FunSyn = FunSyn' !*)
  open FunWeaken__0

  open! struct
    module F = FunSyn
    module I = IntSyn

    let rec strengthenPsi a b = match a, b with
      | I.Null, s -> (I.Null, s)
      | I.Decl (psi, F.Prim d), s ->
          let psi', s' = strengthenPsi psi s in
          (I.Decl (psi', F.Prim (Weaken.strengthenDec d s')), I.dot1 s')
      | I.Decl (psi, F.Block (F.CtxBlock (l, g))), s ->
          let psi', s' = strengthenPsi psi s in
          let g'', s'' = Weaken.strengthenCtx g s' in
          (I.Decl (psi', F.Block (F.CtxBlock (l, g''))), s'')

    let rec strengthenPsi' a b = match a, b with
      | [], s -> ([], s)
      | F.Prim d :: psi, s ->
          let d' = Weaken.strengthenDec d s in
          let s' = I.dot1 s in
          let psi'', s'' = strengthenPsi' psi s' in
          (F.Prim d' :: psi'', s'')
      | F.Block (F.CtxBlock (l, g)) :: psi, s ->
          let g', s' = Weaken.strengthenCtx g s in
          let psi'', s'' = strengthenPsi' psi s' in
          (F.Block (F.CtxBlock (l, g')) :: psi'', s'')
  end

  (* strengthenPsi (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'
    *)
  (* strengthenPsi' (Psi, s) = (Psi', s')

       If   Psi0 |- Psi ctx
       and  Psi0 |- s : Psi1
       then Psi1 |- Psi' = Psi[s^-1] ctx
       and  Psi0 |- s' : Psi1, Psi'  weakening substitution
    *)
  let strengthenPsi = strengthenPsi
  let strengthenPsi' = strengthenPsi'
end
(*! structure FunSyn' : FUNSYN !*)
(*! sharing Weaken.IntSyn = FunSyn'.IntSyn !*)
(* functor FunWeaken *)

(* # 1 "src/meta/Funweaken.sml.ml" *)
