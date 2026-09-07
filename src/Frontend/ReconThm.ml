open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths.Paths_
open! Print.Print_
open! Modes.Modes_
open! Thm

(* # 1 "src/frontend/ReconThm.sig.ml" *)

(* External Syntax for meta theorems *)
(* Author: Carsten Schuermann *)
include RECONTHM

(*  val wdecl : (decs * decs) list * callpats -> wdecl *)
(* signature THMEXTSYN *)
(* signature RECON_THM *)

(* # 1 "src/frontend/ReconThm.fun.ml" *)
open! Basis

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module ReconThm (ReconThm__0 : sig
  (* Reconstruct Termination Information *)
  (* Author: Carsten Schuermann *)
  (* Modified: Brigitte Pientka *)
  module Global : GLOBAL

  (* structure IntSyn : INTSYN *)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn !*)
  module Constraints : CONSTRAINTS
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module ThmSyn' : Thmsyn.THMSYN with module Names = Names
  module ReconTerm' : RECONTERM.RECON_TERM

  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
  (*! sharing ReconTerm'.Paths = Paths'  !*)
  module Print : PRINT
end) : RECON_THM with module ThmSyn = ReconThm__0.ThmSyn' = struct
  module ThmSyn = ReconThm__0.ThmSyn'

  (*! structure Paths = Paths' !*)
  module ExtSyn = ReconThm__0.ReconTerm'

  exception Error = Error

  open! struct
    module M = ModeSyn
    module I = IntSyn
    module L = ThmSyn
    module P = Paths
    module T = ReconThm__0.ReconTerm'

    let error r msg = raise (Error (P.wrap r msg))

    type nonrec order = ThmSyn.order * Paths.region

    let varg r l = (ThmSyn.Varg l, r)

    let lex r0 l =
      let rec lex' = function
        | [] -> ([], r0)
        | (o, r) :: l ->
            let os, r' = lex' l in
            (o :: os, Paths.join r r')
      in
      let os, r1 = lex' l in
      (ThmSyn.Lex os, r1)

    let simul r0 l =
      let rec simul' = function
        | [] -> ([], r0)
        | (o, r) :: l ->
            let os, r' = simul' l in
            (o :: os, Paths.join r r')
      in
      let os, r1 = simul' l in
      (ThmSyn.Simul os, r1)

    type nonrec callpats = (string * string option list * Paths.region) list

    let rec checkArgNumber (i, a, b, r) = match i, a, b with
      | 0, I.Uni I.Type, [] -> ()
      | 0, I.Pi (_, v2), arg :: args -> checkArgNumber (0, v2, args, r)
      | 0, I.Pi (_, v2), [] -> error r ("Missing arguments in call pattern")
      | 0, I.Uni I.Type, arg :: args ->
          error r ("Extraneous arguments in call pattern")
      | i, I.Pi (_, v2), args -> checkArgNumber (i - 1, v2, args, r)

    let checkCallPat (b, p, r) = match b with
      | I.ConDec (_, _, i, I.Normal, v, I.Kind) ->
          checkArgNumber (i, v, p, r)
      | I.ConDec (a, _, _, I.Constraint _, _, _) ->
          error r (("Illegal constraint constant " ^ a) ^ " in call pattern")
      | I.ConDec (a, _, _, I.Foreign _, _, _) ->
          error r (("Illegal foreign constant " ^ a) ^ " in call pattern")
      | I.ConDec (a, _, _, _, _, I.Type) ->
          error r (("Constant " ^ a) ^ " in call pattern not a type family")
      | I.ConDef (a, _, _, _, _, _, _) ->
          error r (("Illegal defined constant " ^ a) ^ " in call pattern")
      | I.AbbrevDef (a, _, _, _, _, _) ->
          error r (("Illegal abbreviation " ^ a) ^ " in call pattern")
      | I.BlockDec (a, _, _, _) ->
          error r (("Illegal block identifier " ^ a) ^ " in call pattern")
      | I.SkoDec (a, _, _, _, _) ->
          error r (("Illegal Skolem constant " ^ a) ^ " in call pattern")

    let resolveCallPat (name, p, r) =
          let qid = Names.Qid ([], name) in
          begin match Names.constLookup qid with
          | None ->
              error
                r (("Undeclared identifier "
                  ^ Names.qidToString (valOf (Names.constUndef qid)))
                  ^ " in call pattern")
          | Some cid ->
              checkCallPat (I.sgnLookup cid, p, r);
              ((cid, p), r)
          end

    let resolveCallpats l =
      let rec callpats' = function
        | [] -> ([], [])
        | cp :: l ->
            let cps, rs = callpats' l in
            let cp', r = resolveCallPat cp in
            (cp' :: cps, r :: rs)
      in
      let cps, rs = callpats' l in
      (ThmSyn.Callpats cps, rs)

    let callpats l = l

    type nonrec tdecl = (ThmSyn.order * callpats) * Paths.region

    let tdecl (o, r) c = ((o, c), r)

    let tdeclTotDecl (a, r) = match a with
      | (o, c) ->
          let c', rs = resolveCallpats c in
          (ThmSyn.TDecl (o, c'), (r, rs))

    type nonrec predicate = ThmSyn.predicate * Paths.region

    let predicate a1 b1 = match a1, b1 with
      | "LESS", r -> (ThmSyn.Less, r)
      | "LEQ", r -> (ThmSyn.Leq, r)
      | "EQUAL", r -> (ThmSyn.Eq, r)

    type nonrec rdecl =
      (ThmSyn.predicate * ThmSyn.order * ThmSyn.order * callpats) * Paths.region

    let rdecl (p, r0) (o1, r1) (o2, r2) c =
      let r = Paths.join r1 r2 in
      ((p, o1, o2, c), Paths.join r0 r)

    let rdeclTorDecl (a, r) = match a with
      | (p, o1, o2, c) ->
          let c', rs = resolveCallpats c in
          (ThmSyn.RDecl (ThmSyn.RedOrder (p, o1, o2), c'), (r, rs))

    type nonrec tableddecl = string * Paths.region

    let tableddecl a b = (a, b)

    let tableddeclTotabledDecl (name, r) =
          let qid = Names.Qid ([], name) in
          begin match Names.constLookup qid with
          | None ->
              error
                r (("Undeclared identifier "
                  ^ Names.qidToString (valOf (Names.constUndef qid)))
                  ^ " in call pattern")
          | Some cid -> (ThmSyn.TabledDecl cid, r)
          end

    type nonrec keepTabledecl = string * Paths.region

    let keepTabledecl a b = (a, b)

    let keepTabledeclToktDecl (name, r) =
          let qid = Names.Qid ([], name) in
          begin match Names.constLookup qid with
          | None ->
              error
                r (("Undeclared identifier "
                  ^ Names.qidToString (valOf (Names.constUndef qid)))
                  ^ " in call pattern")
          | Some cid -> (ThmSyn.KeepTableDecl cid, r)
          end

    type nonrec prove = ThmSyn.pDecl * (Paths.region * Paths.region list)

    let prove n td =
      let td_, rrs = tdeclTotDecl td in
      (ThmSyn.PDecl (n, td_), rrs)

    let proveToProve p = p

    type nonrec establish = ThmSyn.pDecl * (Paths.region * Paths.region list)

    let establish n td =
      let td_, rrs = tdeclTotDecl td in
      (ThmSyn.PDecl (n, td_), rrs)

    let establishToEstablish p = p

    type nonrec assert_ = callpats

    let assert_ cp = cp
    let assertToAssert cp = resolveCallpats cp

    type nonrec decs = ExtSyn.dec I.ctx

    let null = IntSyn.Null
    let decl g d = I.Decl (g, d)

    type nonrec labeldec = decs * decs

    type nonrec thm =
      labeldec list * ExtSyn.dec I.ctx * ModeSyn.mode I.ctx * int

    type nonrec theorem = thm -> thm
    type nonrec theoremdec = string * theorem

    let dec (name, t) = (name, t)

    let rec ctxAppend (g, a) = match a with
      | IntSyn.Null -> g
      | I.Decl (g', d) -> I.Decl (ctxAppend (g, g'), d)

    let rec ctxMap arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | f, IntSyn.Null -> IntSyn.Null
      | f, I.Decl (g, d) -> I.Decl (ctxMap f g, f d)
      end

    let ctxBlockToString (g0, (g1, g2)) =
      ignore (Names.varReset IntSyn.Null);
      let g0' = Names.ctxName g0 in
      let g1' = Names.ctxLUName g1 in
      let g2' = Names.ctxLUName g2 in
      (((Print.ctxToString IntSyn.Null g0' ^ "\n")
       ^ begin match g1' with
       | IntSyn.Null -> ""
       | _ -> ("some " ^ Print.ctxToString g0' g1') ^ "\n"
       end)
      ^ "pi ")
      ^ Print.ctxToString (ctxAppend (g0', g1')) g2'

    let checkFreevars (g0, a, r) = match g0, a with
      | IntSyn.Null, (g1, g2) -> ()
      | g0, (g1, g2) ->
          ignore (Names.varReset IntSyn.Null);
          let g0' = Names.ctxName g0 in
          let g1' = Names.ctxLUName g1 in
          let g2' = Names.ctxLUName g2 in
          error
            r ("Free variables in context block after term reconstruction:\n"
              ^ ctxBlockToString (g0', (g1', g2')))

    let abstractCtxPair (g1, g2) =
      let r =
        begin match (T.ctxRegion g1, T.ctxRegion g2) with
        | Some r1, Some r2 -> Paths.join r1 r2
        | _, Some r2 -> r2
        end
      in
      let (T.JWithCtx (g1_, T.JWithCtx (g2_, _))) =
        T.recon (T.jwithctx g1 (T.jwithctx g2 T.jnothing))
      in
      let g0, [ g1'; g2' ] =
        try Abstract.abstractCtxs [ g1_; g2_ ]
        with Constraints.Error c ->
          error
            r ((("Constraints remain in context block after term reconstruction:\n"
               ^ ctxBlockToString (IntSyn.Null, (g1_, g2_)))
              ^ "\n")
              ^ Print.cnstrsToString c)
      in
      ignore (checkFreevars (g0, (g1', g2'), r));
      (g1', g2')

    let top (gBs, g, m, k) = (gBs, g, m, k)

    let exists g' t (gBs, g, m, k) =
      t
        ( gBs,
          ctxAppend (g, g'),
          ctxAppend (m, ctxMap (function _ -> M.Minus) g'),
          k )

    let forall g' t (gBs, g, m, k) =
      t
        ( gBs,
          ctxAppend (g, g'),
          ctxAppend (m, ctxMap (function _ -> M.Plus) g'),
          k )

    let forallStar g' t (gBs, g, m, _) =
      t
        ( gBs,
          ctxAppend (g, g'),
          ctxAppend (m, ctxMap (function _ -> M.Plus) g'),
          I.ctxLength g' )

    let forallG gbs (t : thm -> thm) (_ : thm) =
      (t (gbs, IntSyn.Null, IntSyn.Null, 0) : thm)

    let theoremToTheorem t =
      let gbs, g, m, k = t ([], IntSyn.Null, IntSyn.Null, 0) in
      ignore (Names.varReset IntSyn.Null);
      let gBs = List.map abstractCtxPair gbs in
      let (T.JWithCtx (g_, _)) = T.recon (T.jwithctx g T.jnothing) in
      L.ThDecl (gBs, g_, m, k)

    let theoremDecToTheoremDec (name, t) = (name, theoremToTheorem t)

    let abstractWDecl w =
      let w' = List.map (fun (ids, id) -> ThmSyn.Names.Qid (ids, id)) w in
      w'

    type nonrec wdecl = (string list * string) list * callpats

    let wdecl a b = (a, b)

    let wdeclTowDecl (w, cp) =
          let cp', rs = resolveCallpats cp in
          (ThmSyn.WDecl (abstractWDecl w, cp'), rs)
  end

  (* everything else should be impossible! *)
  (* check whether they are families here? *)
  (* -bp *)
  (* predicate *)
  (* reduces declaration *)
  (* tabled declaration *)
  (* check whether they are families here? *)
  (* keepTable declaration *)
  (* check whether they are families here? *)
  (* Theorem and prove declarations *)
  (* each block reconstructed independent of others *)
  (* closed nf *)
  (* World checker *)
  (* avoid this re-copying? -fp *)
  type nonrec order = order

  let varg = varg
  let lex = lex
  let simul = simul

  type nonrec callpats = callpats

  let callpats = callpats

  type nonrec tdecl = tdecl

  let tdecl = tdecl

  (* -bp *)
  type nonrec predicate = predicate

  let predicate = predicate

  (* -bp *)
  type nonrec rdecl = rdecl

  let rdecl = rdecl

  type nonrec tableddecl = tableddecl

  let tableddecl = tableddecl

  type nonrec keepTabledecl = keepTabledecl

  let keepTabledecl = keepTabledecl

  type nonrec prove = prove

  let prove = prove

  type nonrec establish = establish

  let establish = establish

  type nonrec assert_ = assert_

  let assert_ = assert_
  let tdeclTotDecl = tdeclTotDecl
  let rdeclTorDecl = rdeclTorDecl
  let tableddeclTotabledDecl = tableddeclTotabledDecl
  let keepTabledeclToktDecl = keepTabledeclToktDecl
  let proveToProve = proveToProve
  let establishToEstablish = establishToEstablish
  let assertToAssert = assertToAssert

  type nonrec decs = decs

  let null = null
  let decl = decl

  type nonrec theorem = theorem

  let top = top
  let forallStar = forallStar
  let forall = forall
  let exists = exists
  let forallG = forallG
  let theoremToTheorem = theoremToTheorem

  type nonrec theoremdec = theoremdec

  let dec (name, t) = (name, t)
  let theoremDecToTheoremDec = theoremDecToTheoremDec

  type nonrec wdecl = wdecl

  let wdeclTowDecl = wdeclTowDecl
  let wdecl = wdecl
end
(*! sharing Print.IntSyn = IntSyn !*)
(* local *)
(* functor ReconThm *)

(* # 1 "src/frontend/ReconThm.sml.ml" *)
