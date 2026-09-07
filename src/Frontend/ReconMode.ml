open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths.Paths_
open! Print.Print_
open! Modes
open! Modes.Modes_

(* # 1 "src/frontend/ReconMode.sig.ml" *)

(* External Syntax of Mode Declarations *)
(* Author: Carsten Schuermann *)
include RECONMODE

(* signature EXTMODES *)
(* signature RECON_MODE *)

(* # 1 "src/frontend/ReconMode.fun.ml" *)
open! Basis

(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

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
  module ReconTerm' : RECONTERM.RECON_TERM
end) : RECON_MODE = struct
  (*! structure ModeSyn = ModeSyn' !*)
  module ExtSyn = ReconMode__0.ReconTerm'

  (*! structure Paths = Paths' !*)
  exception Error = Error

  let error r msg = raise (Error (Paths.wrap r msg))

  open! struct
    module M = Modes.Modesyn.ModeSyn
    module I = IntSyn
    module T = ReconMode__0.ReconTerm'
    module P = Paths

    type nonrec mode = M.mode * P.region

    let plus r = (M.Plus, r)
    let star r = (M.Star, r)
    let minus r = (M.Minus, r)
    let minus1 r = (M.Minus1, r)

    type nonrec modedec =
      (I.cid option * (string list * string) option * M.modeSpine) * P.region

    module Short = struct
      type nonrec mterm = modedec
      type nonrec mspine = M.modeSpine * P.region

      let mnil r = (M.Mnil, r)

      let mapp (m, r1) name (mS, r2) =
        (M.Mapp (M.Marg (m, name), mS), P.join r1 r2)

      let mroot (ids, id, r1, (mS, r2)) =
        let r = P.join r1 r2 in
        (((None, Some (ids, id), mS), r) : mterm)

      let toModedec nmS = nmS
    end

    module Full = struct
      type nonrec mterm =
        T.dec I.ctx * M.mode I.ctx -> (I.cid * M.modeSpine) * P.region

      let mpi (m, _) d t (g, d_) = t (I.Decl (g, d), I.Decl (d_, m))

      let mroot tm r (g, d_) =
        let (T.JWithCtx (g_, T.JOf ((v, _), _, _))) =
          T.recon (T.jwithctx g (T.jof tm (T.typ r)))
        in
        ignore (T.checkErrors r);
        let rec convertSpine = function
          | I.Nil -> M.Mnil
          | I.App (u, s) ->
              let k =
                try Whnf.etaContract u
                with eta ->
                  error
                    r (("Argument " ^ Print.expToString g_ u)
                      ^ " not a variable")
              in
              let (I.Dec (name, _)) = I.ctxLookup g_ k in
              let mode = I.ctxLookup d_ k in
              M.Mapp (M.Marg (mode, name), convertSpine s)
        in
        let convertExp = function
          | I.Root (I.Const a, s) -> (a, convertSpine s)
          | I.Root (I.Def d, s) -> (d, convertSpine s)
          | _ -> error r ("Call pattern not an atomic type")
        in
        let a, mS = convertExp (Whnf.normalize (v, I.id)) in
        ModeDec.checkFull a mS r;
        ((a, mS), r)

      let toModedec t =
        ignore (Names.varReset I.Null);
        let (a, mS), r = t (I.Null, I.Null) in
        ((Some a, None, mS), r)
    end

    let modeToMode = function
      | (Some a, None, mS), r -> ((a, mS), r)
      | (None, Some (ids, id), mS), r ->
          let qid = Names.Qid (ids, id) in
          begin match Names.constLookup qid with
          | None ->
              error
                r (("Undeclared identifier "
                  ^ Names.qidToString (valOf (Names.constUndef qid)))
                  ^ " in mode declaration")
          | Some cid -> ((cid, ModeDec.shortToFull cid mS r), r)
          end
      | _ -> error (Paths.Reg (0, 0)) ("Internal mode declaration state")
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

(* # 1 "src/frontend/ReconMode.sml.ml" *)
