open! Basis
open! Timing
open! Timing.Timing_
open! Stream
open! Stream.Stream_
open! Global
open! Global.Global_
open! Table
open! Table.Table_
open! Tabling
open! Intsyn
open! Intsyn.Lambda_
open! Names
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Print
open! Print.Print_
open! Typecheck
open! Typecheck.Typecheck_
open! Style
open! Style.Style_
open! Modes
open! Modes.Modes_
open! Terminate
open! Terminate.Terminate_
open! Index
open! Index.Index_
open! Thm
open! Thm.Thm_
open! M2
open! M2.M2_
open! Compile
open! Compile.Compile_
open! Opsem
open! Opsem.Opsem_
open! Subordinate
open! Subordinate
open! Modules
open! Modules.Modules_
open! Meta
open! Meta.Meta_
open! Solvers
open! Solvers.Solvers_
open! Worldcheck
open! Worldcheck.Worldcheck_
open! Unique
open! Unique.Unique_
open! Cover
open! Cover.Cover_
open! Tomega_lib
open! Tomega_lib.Tomega_
open! Prover
open! Flit
open! Flit.Flit_
open! Msg
open! Msg.Msg_

(* # 1 "src/frontend/ReconThm.sig.ml" *)
open! Basis

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

    let varg r l_ = (ThmSyn.Varg l_, r)

    let lex r0 l_ =
      let rec lex' = function
        | [] -> ([], r0)
        | (o_, r) :: l_ ->
            let os_, r' = lex' l_ in
            (o_ :: os_, Paths.join r r')
      in
      let os_, r1 = lex' l_ in
      (ThmSyn.Lex os_, r1)

    let simul r0 l_ =
      let rec simul' = function
        | [] -> ([], r0)
        | (o_, r) :: l_ ->
            let os_, r' = simul' l_ in
            (o_ :: os_, Paths.join r r')
      in
      let os_, r1 = simul' l_ in
      (ThmSyn.Simul os_, r1)

    type nonrec callpats = (string * string option list * Paths.region) list

    let rec checkArgNumber (i, a, b, r) = match i, a, b with
      | 0, I.Uni I.Type, [] -> ()
      | 0, I.Pi (_, v2_), arg :: args -> checkArgNumber (0, v2_, args, r)
      | 0, I.Pi (_, v2_), [] -> error r ("Missing arguments in call pattern")
      | 0, I.Uni I.Type, arg :: args ->
          error r ("Extraneous arguments in call pattern")
      | i, I.Pi (_, v2_), args -> checkArgNumber (i - 1, v2_, args, r)

    let checkCallPat (b, p_, r) = match b with
      | I.ConDec (_, _, i, I.Normal, v_, I.Kind) ->
          checkArgNumber (i, v_, p_, r)
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

    let resolveCallPat (name, p_, r) =
          let qid = Names.Qid ([], name) in
          begin match Names.constLookup qid with
          | None ->
              error
                r (("Undeclared identifier "
                  ^ Names.qidToString (valOf (Names.constUndef qid)))
                  ^ " in call pattern")
          | Some cid ->
              checkCallPat (I.sgnLookup cid, p_, r);
              ((cid, p_), r)
          end

    let resolveCallpats l_ =
      let rec callpats' = function
        | [] -> ([], [])
        | cp :: l_ ->
            let cps, rs = callpats' l_ in
            let cp', r = resolveCallPat cp in
            (cp' :: cps, r :: rs)
      in
      let cps, rs = callpats' l_ in
      (ThmSyn.Callpats cps, rs)

    let callpats l_ = l_

    type nonrec tdecl = (ThmSyn.order * callpats) * Paths.region

    let tdecl (o_, r) c_ = ((o_, c_), r)

    let tdeclTotDecl (a, r) = match a with
      | (o_, c_) ->
          let c'_, rs = resolveCallpats c_ in
          (ThmSyn.TDecl (o_, c'_), (r, rs))

    type nonrec predicate = ThmSyn.predicate * Paths.region

    let predicate a1 b1 = match a1, b1 with
      | "LESS", r -> (ThmSyn.Less, r)
      | "LEQ", r -> (ThmSyn.Leq, r)
      | "EQUAL", r -> (ThmSyn.Eq, r)

    type nonrec rdecl =
      (ThmSyn.predicate * ThmSyn.order * ThmSyn.order * callpats) * Paths.region

    let rdecl ((p_, r0), (o1_, r1), (o2_, r2), c_) =
      let r = Paths.join r1 r2 in
      ((p_, o1_, o2_, c_), Paths.join r0 r)

    let rdeclTorDecl (a, r) = match a with
      | (p_, o1_, o2_, c_) ->
          let c'_, rs = resolveCallpats c_ in
          (ThmSyn.RDecl (ThmSyn.RedOrder (p_, o1_, o2_), c'_), (r, rs))

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

    let proveToProve p_ = p_

    type nonrec establish = ThmSyn.pDecl * (Paths.region * Paths.region list)

    let establish n td =
      let td_, rrs = tdeclTotDecl td in
      (ThmSyn.PDecl (n, td_), rrs)

    let establishToEstablish p_ = p_

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

    let rec ctxAppend (g_, a) = match a with
      | IntSyn.Null -> g_
      | I.Decl (g'_, d_) -> I.Decl (ctxAppend (g_, g'_), d_)

    let rec ctxMap arg__1 arg__2 =
      begin match (arg__1, arg__2) with
      | f, IntSyn.Null -> IntSyn.Null
      | f, I.Decl (g_, d_) -> I.Decl (ctxMap f g_, f d_)
      end

    let ctxBlockToString (g0_, (g1_, g2_)) =
      ignore (Names.varReset IntSyn.Null);
      let g0'_ = Names.ctxName g0_ in
      let g1'_ = Names.ctxLUName g1_ in
      let g2'_ = Names.ctxLUName g2_ in
      (((Print.ctxToString IntSyn.Null g0'_ ^ "\n")
       ^ begin match g1'_ with
       | IntSyn.Null -> ""
       | _ -> ("some " ^ Print.ctxToString g0'_ g1'_) ^ "\n"
       end)
      ^ "pi ")
      ^ Print.ctxToString (ctxAppend (g0'_, g1'_)) g2'_

    let checkFreevars (g0_, a, r) = match g0_, a with
      | IntSyn.Null, (g1_, g2_) -> ()
      | g0_, (g1_, g2_) ->
          ignore (Names.varReset IntSyn.Null);
          let g0'_ = Names.ctxName g0_ in
          let g1'_ = Names.ctxLUName g1_ in
          let g2'_ = Names.ctxLUName g2_ in
          error
            r ("Free variables in context block after term reconstruction:\n"
              ^ ctxBlockToString (g0'_, (g1'_, g2'_)))

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
      let g0_, [ g1'_; g2'_ ] =
        try Abstract.abstractCtxs [ g1_; g2_ ]
        with Constraints.Error c_ ->
          error
            r ((("Constraints remain in context block after term reconstruction:\n"
               ^ ctxBlockToString (IntSyn.Null, (g1_, g2_)))
              ^ "\n")
              ^ Print.cnstrsToString c_)
      in
      ignore (checkFreevars (g0_, (g1'_, g2'_), r));
      (g1'_, g2'_)

    let top (gBs, g, m_, k) = (gBs, g, m_, k)

    let exists g' t (gBs, g, m_, k) =
      t
        ( gBs,
          ctxAppend (g, g'),
          ctxAppend (m_, ctxMap (function _ -> M.Minus) g'),
          k )

    let forall g' t (gBs, g, m_, k) =
      t
        ( gBs,
          ctxAppend (g, g'),
          ctxAppend (m_, ctxMap (function _ -> M.Plus) g'),
          k )

    let forallStar g' t (gBs, g, m_, _) =
      t
        ( gBs,
          ctxAppend (g, g'),
          ctxAppend (m_, ctxMap (function _ -> M.Plus) g'),
          I.ctxLength g' )

    let forallG gbs (t : thm -> thm) (_ : thm) =
      (t (gbs, IntSyn.Null, IntSyn.Null, 0) : thm)

    let theoremToTheorem t =
      let gbs, g, m_, k = t ([], IntSyn.Null, IntSyn.Null, 0) in
      ignore (Names.varReset IntSyn.Null);
      let gBs = List.map abstractCtxPair gbs in
      let (T.JWithCtx (g_, _)) = T.recon (T.jwithctx g T.jnothing) in
      L.ThDecl (gBs, g_, m_, k)

    let theoremDecToTheoremDec (name, t) = (name, theoremToTheorem t)

    let abstractWDecl w_ =
      let w'_ = List.map (fun (ids, id) -> ThmSyn.Names.Qid (ids, id)) w_ in
      w'_

    type nonrec wdecl = (string list * string) list * callpats

    let wdecl a b = (a, b)

    let wdeclTowDecl (w_, cp) =
          let cp'_, rs = resolveCallpats cp in
          (ThmSyn.WDecl (abstractWDecl w_, cp'_), rs)
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
