open! Basis

(* Lemma *)
(* Author: Carsten Schuermann *)
module Lemma (Lemma__0 : sig
  module MetaSyn' : METASYN
  module MetaAbstract : METAABSTRACT
end) : LEMMA = struct
  module MetaSyn = MetaSyn'

  exception Error of string

  open! struct
    module A = MetaAbstract
    module M = MetaSyn
    module I = IntSyn

    let rec createEVars = function
      | M.Prefix (null_, null_, null_) ->
          (M.Prefix (I.null_, I.null_, I.null_), I.id)
      | M.Prefix (I.Decl (g_, d_), I.Decl (m_, top_), I.Decl (b_, b)) ->
          let M.Prefix (g'_, m'_, b'_), s' =
            createEVars (M.Prefix (g_, m_, b_))
          in
          ( M.Prefix
              ( I.Decl (g'_, I.decSub (d_, s')),
                I.Decl (m'_, M.top_),
                I.Decl (b'_, b) ),
            I.dot1 s' )
      | M.Prefix (I.Decl (g_, I.Dec (_, v_)), I.Decl (m_, bot_), I.Decl (b_, _))
        ->
          let M.Prefix (g'_, m'_, b'_), s' =
            createEVars (M.Prefix (g_, m_, b_))
          in
          let x_ = I.newEVar (g'_, I.EClo (v_, s')) in
          (M.Prefix (g'_, m'_, b'_), I.Dot (I.Exp x_, s'))

    let rec apply (M.State (name, gm_, v_), a) =
      let (M.Prefix (g'_, m'_, b'_) as gm'_), s' = createEVars gm_ in
      let u'_, vs'_ = M.createAtomConst (g'_, I.Const a) in
      A.abstract
        (M.State
           ( name,
             gm'_,
             I.Pi ((I.Dec (None, u'_), I.no_), I.EClo (v_, I.comp (s', I.shift)))
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
