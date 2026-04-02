(* # 1 "src/m2/Init.sig.ml" *)
open! Basis
open Metasyn

(* Initialization *)
(* Author: Carsten Schuermann *)
include Init_intf
(* signature INIT *)

(* # 1 "src/m2/Init.fun.ml" *)
open! Basis
open Metasyn
open MetaAbstract

(* Initialization *)
(* Author: Carsten Schuermann *)
module Init (Init__0 : sig
  module MetaSyn' : Metasyn.METASYN
  module MetaAbstract : MetaAbstract_intf.METAABSTRACT with module MetaSyn = MetaSyn'
end) : INIT with module MetaSyn = Init__0.MetaSyn' = struct
  open Init__0
  module MetaSyn = MetaAbstract.MetaSyn

  exception Error of string

  open! struct
    module M = MetaSyn
    module I = IntSyn

    let rec init' cid =
      let v_, _ = M.createAtomConst (I.Null, I.Const cid) in
      MetaAbstract.abstract
        (M.State
           ( ("/" ^ I.conDecName (I.sgnLookup cid)) ^ "/",
             M.Prefix (I.Null, I.Null, I.Null),
             v_ ))

    let rec init cidList = map init' cidList
  end

  (* init c = S'

       Invariant:
       If   c is type constant identifier
       then S' is initial prover State.
    *)
  (* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover State.
    *)
  let init = init
end
(* local *)
(* functor Init *)

(* # 1 "src/m2/Init.sml.ml" *)
