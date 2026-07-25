(* # 1 "src/thm/Thmsyn.sig.ml" *)
open! Basis

(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

module type THMSYN = sig
  module Names : NAMES

  exception Error of string

  (*! type Param = string option !*)
  type order = Varg of string list | Lex of order list | Simul of order list

  (* -bp *)
  type predicate = Less | Leq | Eq
  type redOrder = RedOrder of predicate * order * order
  type callpats = Callpats of (IntSyn.cid * string option list) list

  (* Termination declaration *)
  type tDecl = TDecl of order * callpats

  (* -bp *)
  (* Reduction declaration *)
  type rDecl = RDecl of redOrder * callpats

  (* Tabled declaration *)
  type tabledDecl = TabledDecl of IntSyn.cid

  (* KeepTable declaration *)
  type keepTableDecl = KeepTableDecl of IntSyn.cid

  (* Theorem declaration  *)
  type thDecl =
    | ThDecl of
        (IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx) list
        * IntSyn.dec IntSyn.ctx
        * ModeSyn.mode IntSyn.ctx
        * int

  (* Proof declaration *)
  type pDecl = PDecl of int * tDecl

  (* World declaration *)
  (*  datatype WDecl = 
    WDecl of (IntSyn.Dec IntSyn.Ctx * 
	      IntSyn.Dec IntSyn.Ctx) list * Callpats
*)
  type wDecl = WDecl of Names.qid list * callpats

  val theoremDecToConDec :
    (string * thDecl) * Paths.region ->
    (IntSyn.dec IntSyn.ctx * IntSyn.dec IntSyn.ctx) list * IntSyn.conDec

  val theoremDecToModeSpine :
    (string * thDecl) * Paths.region -> ModeSyn.modeSpine
end
