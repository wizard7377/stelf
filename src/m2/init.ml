(* # 1 "src/m2/init.sig.ml" *)
open! Basis
open Metasyn

(* Initialization *)
(* Author: Carsten Schuermann *)
module type INIT = sig
  module MetaSyn : METASYN

  exception Error of string

  val init : IntSyn.cid list -> MetaSyn.state list
end
(* signature INIT *)

(* # 1 "src/m2/init.fun.ml" *)
open! Basis
open Metasyn
open Meta_abstract

(* Initialization *)
(* Author: Carsten Schuermann *)
module Init (Init__0 : sig
  module MetaSyn' : METASYN
  module MetaAbstract : METAABSTRACT with module MetaSyn = MetaSyn'
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
       then S' is initial prover state.
    *)
  (* init c1 .. cn = S1 .. Sn

       Invariant:
       If   c1 .. cn are mutually recursive
       then S1 .. Sn is an initial prover state.
    *)
  let init = init
end
(* local *)
(* functor Init *)

(* # 1 "src/m2/init.sml.ml" *)
