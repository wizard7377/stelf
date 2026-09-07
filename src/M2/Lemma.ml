open! Intsyn.Lambda_

(* # 1 "src/m2/Lemma.sig.ml" *)
open Metasyn

(* Lemma *)
(* Author: Carsten Schuermann *)
include LEMMA
(* signature LEMMA *)

(* # 1 "src/m2/Lemma.fun.ml" *)
open! Basis
open Metasyn
open MetaAbstract

(* Lemma *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Lemma (Lemma__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : METAABSTRACT.METAABSTRACT with module MetaSyn = MetaSyn'
end) : LEMMA with module MetaSyn = Lemma__0.MetaSyn' = struct
  open Lemma__0
  module MetaSyn = MetaAbstract.MetaSyn

  exception Error = Error

  open! struct
    module A = MetaAbstract
    module M = MetaSyn
    module I = IntSyn

    let rec createEVars = function
      | M.Prefix (I.Null, I.Null, I.Null) ->
          (M.Prefix (I.Null, I.Null, I.Null), I.id)
      | M.Prefix (I.Decl (g, d), I.Decl (m, M.Top), I.Decl (b_, b)) ->
          let M.Prefix (g', m', b'), s' =
            createEVars (M.Prefix (g, m, b_))
          in
          ( M.Prefix
              ( I.Decl (g', I.decSub d s'),
                I.Decl (m', M.Top),
                I.Decl (b', b) ),
            I.dot1 s' )
      | M.Prefix (I.Decl (g, I.Dec (_, v)), I.Decl (m, M.Bot), I.Decl (b, _))
        ->
          let M.Prefix (g', m', b'), s' =
            createEVars (M.Prefix (g, m, b))
          in
          let x = I.newEVar g' (I.EClo (v, s')) in
          (M.Prefix (g', m', b'), I.Dot (I.Exp x, s'))

    let apply (M.State (name, gm, v)) a =
      let (M.Prefix (g', m', b') as gm'), s' = createEVars gm in
      let u', vs' = M.createAtomConst g' (I.Const a) in
      A.abstract
        (M.State
           ( name,
             gm',
             I.Pi ((I.Dec (None, u'), I.No), I.EClo (v, I.comp s' I.shift))
           ))
  end

  (* createEVars (G, M, B) = ((G', M', B'), s')

       Invariant:
       If   |- G ctx
       then |- G' ctx
       and  . |- s' : G
       M and B are mode and bound contexts matching G, and similarly for M' and B'.
    *)
  (* apply (((G, M), V), a) = ((G', M'), V')

       Invariant:
       If   |- G ctx
       and  G |- M mtx
       and  a is a type constant of type Va: Sigma (a) = Va
       then |- G' ctx
       and  G' |- M' mtx
       and  G' |- S' : Va > type
       and  G' |- s' : G
       and  G' |- V' = {a S'}. V[s' o ^]
       and  ((G', M'), V') is a state
    *)
  (* Vs' = type *)
  let apply = apply
end
(* local *)
(* functor lemma *)

(* # 1 "src/m2/Lemma.sml.ml" *)
