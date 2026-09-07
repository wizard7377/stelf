open! Intsyn.Lambda_
open! Names.Names_
open! Modes__Modes_
open! Paths.Paths_

(* # 1 "src/thm/Thmsyn.sig.ml" *)

(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
include THMSYN
(* signature THMSYN *)

(* # 1 "src/thm/Thmsyn.fun.ml" *)
open! Basis

(* Theorems *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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

  exception Error = Error

  let error r msg = raise (Error (Paths.wrap r msg))

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

    let theoremDecToConDec name (ThDecl (gBs, g, mg, i)) r =
      let rec theoremToConDec' (a, v) = match a with
        | I.Null -> v
        | I.Decl (g, d) ->
            begin if Abstract.closedDec g (d, I.id) then
              theoremToConDec'
                ( g,
                  Abstract.piDepend (Whnf.normalizeDec d I.id) I.Maybe v
                )
            else error r ("Free variables in theorem declaration")
            end
      in
      ( gBs,
        I.ConDec
          (name, None, i, I.Normal, theoremToConDec' (g, I.Uni I.Type), I.Kind)
      )

    let theoremDecToModeSpine name (ThDecl (gBs, g, mg, i)) r =
      let rec theoremToModeSpine' (a, b, mS) = match a, b with
        | I.Null, I.Null -> mS
        | I.Decl (g, I.Dec (x, _)), I.Decl (mg, m) ->
            theoremToModeSpine' (g, mg, M.Mapp (M.Marg (m, x), mS))
      in
      theoremToModeSpine' (g, mg, M.Mnil)
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

(* # 1 "src/thm/Thmsyn.sml.ml" *)
