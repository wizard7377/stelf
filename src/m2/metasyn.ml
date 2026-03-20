(* # 1 "src/m2/metasyn.sig.ml" *)
open! Basis

(* Meta syntax *)
(* Author: Carsten Schuermann *)
module type METASYN = sig
  (*! structure IntSyn : INTSYN !*)
  type mode = Bot | Top [@@deriving eq, ord, show]

  (* Mode                       *)
  (* M ::= Bot                  *)
  (*     | Top                  *)
  type prefix = Prefix of IntSyn.dctx * mode IntSyn.ctx * int IntSyn.ctx

  (* Mtx modes                  *)
  (* G   declarations           *)

  (* Prefix P := *)
  (* Btx splitting depths       *)
  type state = State of string * prefix * IntSyn.exp

  (*             G; Mtx; Btx    *)
  (*             [name]         *)

  (* State S :=                 *)
  (*             |- V           *)
  type sgn = SgnEmpty | ConDec of IntSyn.conDec * sgn

  (* Interface signature        *)
  (* IS ::= .                   *)
  (*      | c:V, IS             *)
  val createAtomConst : IntSyn.dctx * IntSyn.head -> IntSyn.exp * IntSyn.eclo
  val createAtomBVar : IntSyn.dctx * int -> IntSyn.exp * IntSyn.eclo
end
(* signature METASYN *)

(* # 1 "src/m2/metasyn.fun.ml" *)
open! Basis

(* Meta syntax *)
(* Author: Carsten Schuermann *)
module Make_MetaSyn (MetaSyn__0 : sig
  module Whnf : WHNF
end) : METASYN = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  type nonrec var = int
  type mode = Bot | Top [@@deriving eq, ord, show]

  (* Mode                       *)
  (* M ::= Bot                  *)
  (*     | Top                  *)
  type prefix = Prefix of IntSyn.dctx * mode IntSyn.ctx * int IntSyn.ctx

  (* Mtx modes                  *)
  (* G   declarations           *)

  (* Prefix P := *)
  (* Btx splitting depths       *)
  type state = State of string * prefix * IntSyn.exp

  (*             G; Mtx; Btx    *)
  (*             [name]         *)

  (* State S :=                 *)
  (*             |- V           *)
  type sgn = SgnEmpty | ConDec of IntSyn.conDec * sgn

  (* Interface signature        *)
  (* IS ::= .                   *)
  (*      | c:V, IS             *)
  open! struct
    module I = IntSyn

    let rec createEVarSpine (g_, vs_) = createEVarSpineW (g_, Whnf.whnf vs_)

    and createEVarSpineW = function
      | g_, ((I.Uni I.Type, s) as vs_) -> (I.Nil, vs_)
      | g_, ((I.Root _, s) as vs_) -> (I.Nil, vs_)
      | g_, (I.Pi (((I.Dec (_, v1_) as d_), _), v2_), s) ->
          let x_ = I.newEVar (g_, I.EClo (v1_, s)) in
          let s_, vs_ = createEVarSpine (g_, (v2_, I.Dot (I.Exp x_, s))) in
          (I.App (x_, s_), vs_)

    let rec createAtomConst (g_, h_) =
      let cid =
        begin match h_ with I.Const cid -> cid | I.Skonst cid -> cid
        end
      in
      let v_ = I.constType cid in
      let s_, vs_ = createEVarSpine (g_, (v_, I.id)) in
      (I.Root (h_, s_), vs_)

    let rec createAtomBVar (g_, k) =
      let (I.Dec (_, v_)) = I.ctxDec (g_, k) in
      let s_, vs_ = createEVarSpine (g_, (v_, I.id)) in
      (I.Root (I.BVar k, s_), vs_)
  end

  (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
  (* s = id *)
  (* s = id *)
  (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
  let createAtomConst = createAtomConst
  let createAtomBVar = createAtomBVar
end
(*! structure IntSyn' : INTSYN !*)
(*! sharing Whnf.IntSyn = IntSyn' !*)
(* functor MetaSyn *)

(* # 1 "src/m2/metasyn.sml.ml" *)
