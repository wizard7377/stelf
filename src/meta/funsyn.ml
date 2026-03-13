(* # 1 "src/meta/funsyn.sig.ml" *)
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

(* # 1 "src/meta/funsyn.fun.ml" *)
open! Global
open! Basis

(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)
module Make_FunSyn (FunSyn__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Conv : CONV
end) : FUNSYN = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  type nonrec label = int
  type nonrec name = string
  type nonrec lemma = int
  type nonrec dlist = IntSyn.dec_ list
  type labelDec_ = LabelDec of name * dlist * dlist

  (* ContextBody                *)
  (* BB ::= l: SOME Theta. Phi  *)
  type ctxBlock_ = CtxBlock of label option * IntSyn.dctx

  (* ContextBlocks              *)
  (* B ::= l : Phi              *)
  type lFDec_ = Prim of IntSyn.dec_ | Block of ctxBlock_

  (* Contexts                   *)
  (* LD ::= x :: A              *)
  (*      | B                   *)
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
  and mDec_ = MDec of name option * for_

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
  type lemmaDec_ = LemmaDec of name list * pro_ * for_

  (* Lemmas                     *)
  (* L ::= c:F = P              *)
  type nonrec mctx = mDec_ IntSyn.ctx_

  (* Delta ::= . | Delta, xx : F*)
  open! struct
    module I = IntSyn

    let maxLabel = Global.maxCid
    let maxLemma = Global.maxCid

    let labelArray =
      (Array.array (maxLabel + 1, LabelDec ("", [], []))
        : labelDec_ Array.array)

    let nextLabel = ref 0

    let lemmaArray =
      (Array.array (maxLemma + 1, LemmaDec ([], Unit, True))
        : lemmaDec_ Array.array)

    let nextLemma = ref 0
    let rec labelLookup label = Array.sub (labelArray, label)

    let rec labelAdd labelDec =
      let label = !nextLabel in
      begin if label > maxLabel then
        raise
          (Error
             (("Global signature size " ^ Int.toString (maxLabel + 1))
             ^ " exceeded"))
      else begin
        Array.update (labelArray, label, labelDec);
        begin
          nextLabel := label + 1;
          label
        end
      end
      end

    let rec labelSize () = !nextLabel
    let rec labelReset () = nextLabel := 0
    let rec lemmaLookup lemma = Array.sub (lemmaArray, lemma)

    let rec lemmaAdd lemmaDec =
      let lemma = !nextLemma in
      begin if lemma > maxLemma then
        raise
          (Error
             (("Global signature size " ^ Int.toString (maxLemma + 1))
             ^ " exceeded"))
      else begin
        Array.update (lemmaArray, lemma, lemmaDec);
        begin
          nextLemma := lemma + 1;
          lemma
        end
      end
      end

    let rec lemmaSize () = !nextLemma

    let rec listToCtx gin_ =
      let rec listToCtx' = function
        | g_, [] -> g_
        | g_, d_ :: ds_ -> listToCtx' (I.Decl (g_, d_), ds_)
      in
      listToCtx' (I.null_, gin_)

    let rec ctxToList gin_ =
      let rec ctxToList' = function
        | null_, g_ -> g_
        | I.Decl (g_, d_), g'_ -> ctxToList' (g_, d_ :: g'_)
      in
      ctxToList' (gin_, [])

    let rec union = function
      | g_, null_ -> g_
      | g_, I.Decl (g'_, d_) -> I.Decl (union (g_, g'_), d_)

    let rec makectx = function
      | null_ -> I.null_
      | I.Decl (g_, Prim d_) -> I.Decl (makectx g_, d_)
      | I.Decl (g_, Block (CtxBlock (l, g'_))) -> union (makectx g_, g'_)

    let rec lfctxLength = function
      | null_ -> 0
      | I.Decl (psi_, Prim _) -> lfctxLength psi_ + 1
      | I.Decl (psi_, Block (CtxBlock (_, g_))) ->
          lfctxLength psi_ + I.ctxLength g_

    let rec lfctxLFDec (psi_, k) =
      let rec lfctxLFDec' = function
        | I.Decl (psi'_, (Prim (I.Dec (x, v'_)) as ld_)), 1 -> (ld_, I.Shift k)
        | I.Decl (psi'_, Prim _), k' -> lfctxLFDec' (psi'_, k' - 1)
        | I.Decl (psi'_, (Block (CtxBlock (_, g_)) as ld_)), k' ->
            let l = I.ctxLength g_ in
            begin if k' <= l then (ld_, I.Shift (k - k' + 1))
            else lfctxLFDec' (psi'_, k' - l)
            end
      in
      lfctxLFDec' (psi_, k)

    let rec dot1n = function
      | null_, s -> s
      | I.Decl (g_, _), s -> I.dot1 (dot1n (g_, s))

    let rec convFor = function
      | (True, _), (True, _) -> true
      | (All (Prim d1_, f1_), s1), (All (Prim d2_, f2_), s2) ->
          Conv.convDec ((d1_, s1), (d2_, s2))
          && convFor ((f1_, I.dot1 s1), (f2_, I.dot1 s2))
      | ( (All (Block (CtxBlock (_, g1_)), f1_), s1),
          (All (Block (CtxBlock (_, g2_)), f2_), s2) ) ->
          convForBlock ((ctxToList g1_, f1_, s1), (ctxToList g1_, f2_, s2))
      | (Ex (d1_, f1_), s1), (Ex (d2_, f2_), s2) ->
          Conv.convDec ((d1_, s1), (d2_, s2))
          && convFor ((f1_, I.dot1 s1), (f2_, I.dot1 s2))
      | (And (f1_, f1'_), s1), (And (f2_, f2'_), s2) ->
          convFor ((f1_, s1), (f2_, s2)) && convFor ((f1'_, s1), (f2'_, s2))
      | _ -> false

    and convForBlock = function
      | ([], f1_, s1), ([], f2_, s2) -> convFor ((f1_, s1), (f2_, s2))
      | (d1_ :: g1_, f1_, s1), (d2_ :: g2_, f2_, s2) ->
          Conv.convDec ((d1_, s1), (d2_, s2))
          && convForBlock ((g1_, f1_, I.dot1 s1), (g2_, f2_, I.dot1 s2))
      | _ -> false

    let rec ctxSub = function
      | null_, s -> (I.null_, s)
      | I.Decl (g_, d_), s ->
          let g'_, s' = ctxSub (g_, s) in
          (I.Decl (g'_, I.decSub (d_, s')), I.dot1 s)

    let rec forSub = function
      | All (Prim d_, f_), s ->
          All (Prim (I.decSub (d_, s)), forSub (f_, I.dot1 s))
      | All (Block (CtxBlock (name, g_)), f_), s ->
          let g'_, s' = ctxSub (g_, s) in
          All (Block (CtxBlock (name, g'_)), forSub (f_, s'))
      | Ex (d_, f_), s -> Ex (I.decSub (d_, s), forSub (f_, I.dot1 s))
      | True, s -> True
      | And (f1_, f2_), s -> And (forSub (f1_, s), forSub (f2_, s))

    let rec mdecSub (MDec (name, f_), s) = MDec (name, forSub (f_, s))

    let rec normalizeFor = function
      | All (Prim d_, f_), s ->
          All (Prim (Whnf.normalizeDec (d_, s)), normalizeFor (f_, I.dot1 s))
      | Ex (d_, f_), s ->
          Ex (Whnf.normalizeDec (d_, s), normalizeFor (f_, I.dot1 s))
      | And (f1_, f2_), s -> And (normalizeFor (f1_, s), normalizeFor (f2_, s))
      | True, _ -> True
  end

  (* hack!!! improve !!!! *)
  (* union (G, G') = G''

       Invariant:
       G'' = G, G'
    *)
  (* makectx Psi = G

       Invariant:
       G is Psi, where the Prim/Block information is discarded.
    *)
  (* lfctxDec (Psi, k) = (LD', w')
       Invariant:
       If      |Psi| >= k, where |Psi| is size of Psi,
       and     Psi = Psi1, LD, Psi2
       then    Psi |- k = LD or Psi |- k in LD  (if LD is a contextblock
       then    LD' = LD
       and     Psi |- w' : Psi1, LD\1   (w' is a weakening substitution)
       and     LD\1 is LD if LD is prim, and LD\1 = x:A if LD = G, x:A
   *)
  (* lfctxDec' (Null, k')  should not occur by invariant *)
  (* dot1n (G, s) = s'

       Invariant:
       If   G1 |- s : G2
       then G1, G |- s' : G2, G
       where s' = 1.(1.  ...     s) o ^ ) o ^
                        |G|-times
    *)
  (* conv ((F1, s1), (F2, s2)) = B

       Invariant:
       If   G |- s1 : G1
       and  G1 |- F1 : formula
       and  G |- s2 : G2
       and  G2 |- F2 : formula
       and  (F1, F2 do not contain abstraction over contextblocks )
       then B holds iff G |- F1[s1] = F2[s2] formula
    *)
  (* SOME l1 *)
  (* SOME l2 *)
  (* l1 = l2 andalso *)
  (* omission! check that the block numbers are the same!!!! *)
  let labelLookup = labelLookup
  let labelAdd = labelAdd
  let labelSize = labelSize
  let labelReset = labelReset
  let lemmaLookup = lemmaLookup
  let lemmaAdd = lemmaAdd
  let lemmaSize = lemmaSize
  let mdecSub = mdecSub
  let makectx = makectx
  let lfctxLength = lfctxLength
  let lfctxLFDec = lfctxLFDec
  let dot1n = dot1n
  let convFor = convFor
  let forSub = forSub
  let normalizeFor = normalizeFor
  let ctxToList = ctxToList
  let listToCtx = listToCtx
end

(*! sharing Conv.IntSyn = IntSyn' !*)
(* functor FunSyn *)
module FunSyn = Make_FunSyn (struct
  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Conv = Conv
end)

(* # 1 "src/meta/funsyn.sml.ml" *)
