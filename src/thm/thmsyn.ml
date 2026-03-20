(* # 1 "src/thm/thmsyn.sig.ml" *)
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
(* signature THMSYN *)

(* # 1 "src/thm/thmsyn.fun.ml" *)
open! Basis

(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module ThmSyn (ThmSyn__0 : sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure ModeSyn' : MODESYN !*)
  (*! sharing ModeSyn'.IntSyn = IntSyn !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module Names' : NAMES
end) : THMSYN with module Names = ThmSyn__0.Names' = struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure ModeSyn = ModeSyn' *)
  (*! structure Paths = Paths' !*)
  module Names = ThmSyn__0.Names'

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type nonrec param = string option
  type order = Varg of string list | Lex of order list | Simul of order list

  (* -bp *)
  type predicate = Less | Leq | Eq
  type redOrder = RedOrder of predicate * order * order
  type callpats = Callpats of (IntSyn.cid * param list) list

  (* Termination declaration *)
  type tDecl = TDecl of order * callpats

  (* -bp *)
  (* Reduction declaration *)
  type rDecl = RDecl of redOrder * callpats

  (* Tabled declaration *)
  type tabledDecl = TabledDecl of IntSyn.cid

  (* KeepTable declaration *)
  type keepTableDecl = KeepTableDecl of IntSyn.cid

  (* Theorem declaration *)
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
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)
  type wDecl = WDecl of Names.qid list * callpats

  open! struct
    module I = IntSyn
    module M = ModeSyn

    let rec theoremDecToConDec ((name, ThDecl (gBs_, g_, mg_, i)), r) =
      let rec theoremToConDec' = function
        | I.Null, v_ -> v_
        | I.Decl (g_, d_), v_ -> begin
            if Abstract.closedDec (g_, (d_, I.id)) then
              theoremToConDec'
                ( g_,
                  Abstract.piDepend ((Whnf.normalizeDec (d_, I.id), I.Maybe), v_)
                )
            else error (r, "Free variables in theorem declaration")
          end
      in
      ( gBs_,
        I.ConDec
          (name, None, i, I.Normal, theoremToConDec' (g_, I.Uni I.Type), I.Kind)
      )

    let rec theoremDecToModeSpine ((name, ThDecl (gBs_, g_, mg_, i)), r) =
      let rec theoremToModeSpine' = function
        | I.Null, I.Null, mS -> mS
        | I.Decl (g_, I.Dec (x, _)), I.Decl (mg_, m), mS ->
            theoremToModeSpine' (g_, mg_, M.Mapp (M.Marg (m, x), mS))
      in
      theoremToModeSpine' (g_, mg_, M.Mnil)
  end

  (* theoremDecToConDec (name, T) = D'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then D' is a constant type declaration of this theorem
    *)
  (* theoremToConDec' G V = V'

             Invariant:
             If   G = V1 .. Vn
             and  G |- V : kind
             then V' = {V1} .. {Vn} V
             and  . |-  V' : kind
          *)
  (* theoremDecToModeSpine (name, T) = mS'

       Invariant:
       If   name is the name of a theorem
       and  T is the declaration of a theorem
       then mS' is a mode spine reflecting the
         quantifier information for the theorem
    *)
  let theoremDecToConDec = theoremDecToConDec
  let theoremDecToModeSpine = theoremDecToModeSpine
end
(*! sharing Names'.IntSyn = IntSyn !*)
(* local *)
(* functor ThmSyn *)

(* # 1 "src/thm/thmsyn.sml.ml" *)
