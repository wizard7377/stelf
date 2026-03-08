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
end) : THMSYN = struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure ModeSyn = ModeSyn' *)
  (*! structure Paths = Paths' !*)
  module Names = ThmSyn__0.Names'

  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  type nonrec param_ = string option

  type order_ =
    | Varg of string list
    | Lex of order_ list
    | Simul of order_ list

  (* -bp *)
  type predicate_ = Less | Leq | Eq
  type redOrder_ = RedOrder of predicate_ * order_ * order_
  type callpats_ = Callpats of (IntSyn.cid * param_ list) list

  (* Termination declaration *)
  type tDecl_ = TDecl of order_ * callpats_

  (* -bp *)
  (* Reduction declaration *)
  type rDecl_ = RDecl of redOrder_ * callpats_

  (* Tabled declaration *)
  type tabledDecl_ = TabledDecl of IntSyn.cid

  (* KeepTable declaration *)
  type keepTableDecl_ = KeepTableDecl of IntSyn.cid

  (* Theorem declaration *)
  type thDecl_ =
    | ThDecl of
        (IntSyn.dec_ IntSyn.ctx_ * IntSyn.dec_ IntSyn.ctx_) list
        * IntSyn.dec_ IntSyn.ctx_
        * ModeSyn.mode_ IntSyn.ctx_
        * int

  (* Proof declaration *)
  type pDecl_ = PDecl of int * tDecl_

  (* World declaration *)
  (*  datatype WDecl =
    WDecl of (IntSyn.Dec IntSyn.Ctx *
              IntSyn.Dec IntSyn.Ctx) list * Callpats *)
  type wDecl_ = WDecl of Names.qid_ list * callpats_

  open! struct
    module I = IntSyn
    module M = ModeSyn

    let rec theoremDecToConDec ((name, ThDecl (gBs_, g_, mg_, i)), r) =
      let rec theoremToConDec' = function
        | null_, v_ -> v_
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
