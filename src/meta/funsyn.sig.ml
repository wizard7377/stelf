open! Basis

(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module type FUNSYN = sig
  (*! structure IntSyn : INTSYN !*)
  (* make abstract *)
  type nonrec label = int
  type nonrec lemma = int
  type labelDec_ = LabelDec of string * IntSyn.dec_ list * IntSyn.dec_ list

  (* ContextBody                *)
  (* BB ::= l: SOME Theta. Phi  *)
  type ctxBlock_ = CtxBlock of label option * IntSyn.dctx

  (* ContextBlocks              *)
  (* B ::= l : Phi              *)
  type lFDec_ = Prim of IntSyn.dec_ | Block of ctxBlock_

  (* Contexts                   *)
  (* LD ::= x :: A              *)
  (*      | B                   *)
  (* ??? *)
  type nonrec lfctx = lFDec_ IntSyn.ctx_

  (* Psi ::= . | Psi, LD        *)
  type for_ =
    | All of lFDec_ * for_
    | Ex of IntSyn.dec_ * for_
    | True
    | And of for_ * for_

  (* Formulas                   *)
  (* F ::= All LD. F            *)
  (*     | Ex  D. F             *)
  (*     | T                    *)
  (*     | F1 ^ F2              *)
  type pro_ =
    | Lam of lFDec_ * pro_
    | Inx of IntSyn.exp_ * pro_
    | Unit
    | Rec of mDec_ * pro_
    | Let of decs_ * pro_
    | Case of opts_
    | Pair of pro_ * pro_

  and opts_ = Opts of (lfctx * IntSyn.sub_ * pro_) list
  and mDec_ = MDec of string option * for_

  and decs_ =
    | Empty
    | Split of int * decs_
    | New of ctxBlock_ * decs_
    | App of (int * IntSyn.exp_) * decs_
    | PApp of (int * int) * decs_
    | Lemma of lemma * decs_
    | Left of int * decs_
    | Right of int * decs_

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
  type lemmaDec_ = LemmaDec of string list * pro_ * for_

  (* Lemmas                     *)
  (* L ::= c:F = P              *)
  (* ??? *)
  type nonrec mctx = mDec_ IntSyn.ctx_

  (* Delta ::= . | Delta, xx : F*)
  val labelLookup : label -> labelDec_
  val labelAdd : labelDec_ -> label
  val labelSize : unit -> int
  val labelReset : unit -> unit
  val lemmaLookup : lemma -> lemmaDec_
  val lemmaAdd : lemmaDec_ -> lemma
  val lemmaSize : unit -> int
  val mdecSub : mDec_ * IntSyn.sub_ -> mDec_
  val makectx : lfctx -> IntSyn.dctx
  val lfctxLength : lfctx -> int
  val lfctxLFDec : lfctx * int -> lFDec_ * IntSyn.sub_
  val dot1n : IntSyn.dctx * IntSyn.sub_ -> IntSyn.sub_
  val convFor : (for_ * IntSyn.sub_) * (for_ * IntSyn.sub_) -> bool
  val forSub : for_ * IntSyn.sub_ -> for_
  val normalizeFor : for_ * IntSyn.sub_ -> for_
  val listToCtx : IntSyn.dec_ list -> IntSyn.dctx
  val ctxToList : IntSyn.dctx -> IntSyn.dec_ list
end
(* Signature FUNSYN *)
