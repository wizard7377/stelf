open! Intsyn.Lambda_

(* # 1 "src/m2/Metasyn.sig.ml" *)

(* Meta syntax *)
(* Author: Carsten Schuermann *)
include METASYN
(* signature METASYN *)

(* # 1 "src/m2/Metasyn.fun.ml" *)
open! Basis

(* Meta syntax *)
(* Author: Carsten Schuermann *)

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Make_MetaSyn (Whnf : WHNF) : METASYN = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

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

    let rec createEVarSpine (g, vs) = createEVarSpineW (g, Whnf.whnf vs)

    and createEVarSpineW (g, a) = match a with
      | ((I.Uni I.Type, s) as vs) -> (I.Nil, vs)
      | ((I.Root _, s) as vs) -> (I.Nil, vs)
      | (I.Pi (((I.Dec (_, v1) as d), _), v2), s) ->
          let x = I.newEVar g (I.EClo (v1, s)) in
          let s_, vs = createEVarSpine (g, (v2, I.Dot (I.Exp x, s))) in
          (I.App (x, s_), vs)

    let createAtomConst g h =
      let cid =
        begin match h with
        | I.Const cid -> cid
        | I.Skonst cid -> cid
        | I.Def cid -> cid
        | _ -> assert false
        end
      in
      let v = I.constType cid in
      let s, vs = createEVarSpine (g, (v, I.id)) in
      (I.Root (h, s), vs)

    let createAtomBVar g k =
      let (I.Dec (_, v)) = I.ctxDec g k in
      let s, vs = createEVarSpine (g, (v, I.id)) in
      (I.Root (I.BVar k, s), vs)
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

(* # 1 "src/m2/Metasyn.sml.ml" *)
