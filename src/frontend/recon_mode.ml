(* # 1 "src/frontend/recon_mode.sig.ml" *)
open! Basis

(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)
module type EXTMODES = sig
  module ExtSyn : Recon_term.EXTSYN

  (*! structure Paths : PATHS  !*)
  type nonrec mode

  val plus : Paths.region -> mode
  val star : Paths.region -> mode
  val minus : Paths.region -> mode
  val minus1 : Paths.region -> mode

  type nonrec modedec

  module Short : sig
    type nonrec mterm
    type nonrec mspine

    val mnil : Paths.region -> mspine
    val mapp : (mode * string option) * mspine -> mspine
    val mroot : string list * string * Paths.region * mspine -> mterm
    val toModedec : mterm -> modedec
  end

  module Full : sig
    type nonrec mterm

    val mroot : ExtSyn.term * Paths.region -> mterm
    val mpi : mode * ExtSyn.dec * mterm -> mterm
    val toModedec : mterm -> modedec
  end
end

(* signature EXTMODES *)
module type RECON_MODE = sig
  (*! structure ModeSyn : MODESYN !*)
  include EXTMODES

  exception Error of string

  val modeToMode : modedec -> (IntSyn.cid * ModeSyn.modeSpine_) * Paths.region
end
(* signature RECON_MODE *)

(* # 1 "src/frontend/recon_mode.fun.ml" *)
open! Basis

(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)
module ReconMode (ReconMode__0 : sig
  module Global : GLOBAL

  (*! structure ModeSyn' : MODESYN !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = ModeSyn'.IntSyn !*)
  (*! structure Paths' : PATHS !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
  module ModePrint : Modeprint.MODEPRINT

  (*! sharing ModePrint.ModeSyn = ModeSyn' !*)
  module ModeDec : Modedec.MODEDEC
  module ReconTerm' : Recon_term.RECON_TERM
end) : RECON_MODE = struct
  (*! structure ModeSyn = ModeSyn' !*)
  module ExtSyn = ReconMode__0.ReconTerm'

  (*! structure Paths = Paths' !*)
  exception Error of string

  let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

  open! struct
    module M = ModeSyn
    module I = IntSyn
    module T = ReconMode__0.ReconTerm'
    module P = Paths

    type nonrec mode = M.mode_ * P.region

    let rec plus r = (M.Plus, r)
    let rec star r = (M.Star, r)
    let rec minus r = (M.Minus, r)
    let rec minus1 r = (M.Minus1, r)

    type nonrec modedec = (I.cid * M.modeSpine_) * P.region

    module Short = struct
      type nonrec mterm = (I.cid * M.modeSpine_) * P.region
      type nonrec mspine = M.modeSpine_ * P.region

      let rec mnil r = (M.Mnil, r)

      let rec mapp (((m, r1), name), (mS, r2)) =
        (M.Mapp (M.Marg (m, name), mS), P.join (r1, r2))

      let rec mroot (ids, id, r1, (mS, r2)) =
        let r = P.join (r1, r2) in
        let qid = Names.Qid (ids, id) in
        begin match Names.constLookup qid with
        | None ->
            error
              ( r,
                ("Undeclared identifier "
                ^ Names.qidToString (valOf (Names.constUndef qid)))
                ^ " in mode declaration" )
        | Some cid -> ((cid, ModeDec.shortToFull (cid, mS, r)), r)
        end

      let rec toModedec nmS = nmS
    end

    module Full = struct
      type nonrec mterm =
        T.dec I.ctx_ * M.mode_ I.ctx_ -> (I.cid * M.modeSpine_) * P.region

      let rec mpi ((m, _), d, t) (g, d_) = t (I.Decl (g, d), I.Decl (d_, m))

      let rec mroot (tm, r) (g, d_) =
        let (T.JWithCtx (g_, T.JOf ((v_, _), _, _))) =
          T.recon (T.jwithctx (g, T.jof (tm, T.typ r)))
        in
        let _ = T.checkErrors r in
        let rec convertSpine = function
          | nil_ -> M.Mnil
          | I.App (u_, s_) ->
              let k =
                try Whnf.etaContract u_
                with eta_ ->
                  error
                    ( r,
                      ("Argument " ^ Print.expToString (g_, u_))
                      ^ " not a variable" )
              in
              let (I.Dec (name, _)) = I.ctxLookup (g_, k) in
              let mode = I.ctxLookup (d_, k) in
              M.Mapp (M.Marg (mode, name), convertSpine s_)
        in
        let rec convertExp = function
          | I.Root (I.Const a, s_) -> (a, convertSpine s_)
          | I.Root (I.Def d, s_) -> (d, convertSpine s_)
          | _ -> error (r, "Call pattern not an atomic type")
        in
        let a, mS = convertExp (Whnf.normalize (v_, I.id)) in
        begin
          ModeDec.checkFull (a, mS, r);
          ((a, mS), r)
        end

      let rec toModedec t =
        let _ = Names.varReset I.null_ in
        let t' = t (I.null_, I.null_) in
        t'
    end

    let rec modeToMode (m, r) = (m, r)
  end

  (* structure Short *)
  (* convert term spine to mode spine *)
  (* Each argument must be contractible to variable *)
  (* print U? -fp *)
  (* yes, print U. -gaw *)
  (* convert root expression to head constant and mode spine *)
  (* error is signalled later in ModeDec.checkFull *)
  (* convertExp (I.Root (I.Skonst _, S)) can't occur *)
  (* structure Full *)
  type nonrec mode = mode

  let plus = plus
  let star = star
  let minus = minus
  let minus1 = minus1

  type nonrec modedec = modedec

  module Short = Short
  module Full = Full

  let modeToMode = modeToMode
end
(*! sharing ReconTerm'.IntSyn = ModeSyn'.IntSyn !*)
(*! sharing ReconTerm'.Paths = Paths' !*)
(* local ... *)
(* functor ReconMode *)

(* # 1 "src/frontend/recon_mode.sml.ml" *)
