(* # 1 "src/meta/funsyn.sig.ml" *)
open! Basis

(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

module type FUNSYN = sig
  (*! structure IntSyn : INTSYN !*)
  (* make abstract *)
  type nonrec label = int
  type nonrec lemma = int
  type labelDec = LabelDec of string * IntSyn.dec list * IntSyn.dec list

  (* ContextBody                *)
  (* BB ::= l: SOME Theta. Phi  *)
  type ctxBlock = CtxBlock of label option * IntSyn.dctx

  (* ContextBlocks              *)
  (* B ::= l : Phi              *)
  type lFDec = Prim of IntSyn.dec | Block of ctxBlock

  (* Contexts                   *)
  (* LD ::= x :: A              *)
  (*      | B                   *)
  (* ??? *)
  type nonrec lfctx = lFDec IntSyn.ctx

  (* Psi ::= . | Psi, LD        *)
  type for_ =
    | All of lFDec * for_
    | Ex of IntSyn.dec * for_
    | True
    | And of for_ * for_

  (* Formulas                   *)
  (* F ::= All LD. F            *)
  (*     | Ex  D. F             *)
  (*     | T                    *)
  (*     | F1 ^ F2              *)
  type pro =
    | Lam of lFDec * pro
    | Inx of IntSyn.exp * pro
    | Unit
    | Rec of mDec * pro
    | Let of decs * pro
    | Case of opts
    | Pair of pro * pro

  and opts = Opts of (lfctx * IntSyn.sub * pro) list
  and mDec = MDec of string option * for_

  and decs =
    | Empty
    | Split of int * decs
    | New of ctxBlock * decs
    | App of (int * IntSyn.exp) * decs
    | PApp of (int * int) * decs
    | Lemma of lemma * decs
    | Left of int * decs
    | Right of int * decs

  (* Programs                   *)
  (* P ::= lam LD. P            *)
  (*     | <M, P>               *)
  (*     | <>                   *)
  (*     | mu xx. P             *)
  (*     | let Ds in P          *)
  (*     | case O               *)
  (*     | <P1, P2>             *)
  (* Option list                *)
  (* O ::= (Psi' |> s |-> P     *)
  (* Meta Declaration:          *)
  (* DD ::= xx : F              *)
  (* Declarations               *)
  (* Ds ::= .                   *)
  (*      | <x, yy> = P, Ds     *)
  (*      | nu B. Ds            *)
  (*      | xx = yy M, Ds       *)
  (*      | xx = yy Phi, Ds     *)
  (*      | xx = cc, Ds         *)
  (*      | xx = pi1 yy, Ds     *)
  (*      | xx = pi2 yy, Ds     *)
  type lemmaDec = LemmaDec of string list * pro * for_

  (* Lemmas                     *)
  (* L ::= c:F = P              *)
  (* ??? *)
  type nonrec mctx = mDec IntSyn.ctx

  (* Delta ::= . | Delta, xx : F*)
  val labelLookup : label -> labelDec
  val labelAdd : labelDec -> label
  val labelSize : unit -> int
  val labelReset : unit -> unit
  val lemmaLookup : lemma -> lemmaDec
  val lemmaAdd : lemmaDec -> lemma
  val lemmaSize : unit -> int
  val mdecSub : mDec * IntSyn.sub -> mDec
  val makectx : lfctx -> IntSyn.dctx
  val lfctxLength : lfctx -> int
  val lfctxLFDec : lfctx * int -> lFDec * IntSyn.sub
  val dot1n : IntSyn.dctx * IntSyn.sub -> IntSyn.sub
  val convFor : (for_ * IntSyn.sub) * (for_ * IntSyn.sub) -> bool
  val forSub : for_ * IntSyn.sub -> for_
  val normalizeFor : for_ * IntSyn.sub -> for_
  val listToCtx : IntSyn.dec list -> IntSyn.dctx
  val ctxToList : IntSyn.dctx -> IntSyn.dec list
end
