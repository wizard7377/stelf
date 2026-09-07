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

(* # 1 "src/frontend/Twelf_.fun.ml" *)
open! Version
open! Solve
open! Parser
open! Fquery
open! Basis
open Unknownexn

module type STELF = TWELF.STELF

(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow *)
(* Modified: Brigitte Pientka, Roberto Virga *)
module Stelf (Twelf__0 : sig
  module Global : GLOBAL
  module Timers : Timers.TIMERS
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn' !*)
  module Print : PRINT

  (*! sharing Print.IntSyn = IntSyn' !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS

  (*! sharing Origins.Paths = Paths !*)
  module Lexer : Lexer.LEXER

  (*! sharing Lexer.Paths = Paths !*)
  (*! structure Parsing : PARSING !*)
  (*! sharing Lexer = Lexer !*)
  module Parser : PARSER with module Names = Names

  (*! sharing Parser.ExtSyn.Paths = Paths !*)
  module TypeCheck : TYPECHECK
  module Strict : STRICT

  (*! sharing Strict.IntSyn = IntSyn' !*)
  (*! sharing Strict.Paths = Paths !*)
  module Constraints : CONSTRAINTS

  (*! sharing Constraints.IntSyn = IntSyn' !*)
  module Abstract : ABSTRACT

  (*! sharing Abstract.IntSyn = IntSyn' !*)
  module ReconTerm : RECONTERM.RECON_TERM

  (*! sharing ReconTerm.IntSyn = IntSyn' !*)
  (*! sharing ReconTerm.Paths = Paths !*)
  (* sharing type ReconTerm.Paths.occConDec = Origins.Paths.occConDec *)
  module ReconConDec :
    RECONCONDEC.RECON_CONDEC with type condec = Parser.ExtConDec.condec

  (*! sharing ReconConDec.IntSyn = IntSyn' !*)
  (*! sharing ReconConDec.Paths = Paths !*)
  module ReconQuery : RECONQUERY.RECON_QUERY
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = IntSyn' !*)
  module ModeCheck : Modecheck.MODECHECK

  (*! sharing ModeCheck.IntSyn = IntSyn' !*)
  (*! sharing ModeCheck.ModeSyn = ModeSyn !*)
  (*! sharing ModeCheck.Paths = Paths !*)
  module ReconMode :
    RECONMODE.RECON_MODE with type modedec = Parser.ExtModes.modedec

  (*! sharing ReconMode.ModeSyn = ModeSyn !*)
  (*! sharing ReconMode.Paths = Paths !*)
  module ModePrint : Modeprint.MODEPRINT

  (*! sharing ModePrint.ModeSyn = ModeSyn !*)
  module ModeDec : Modedec.MODEDEC

  (*! sharing ModeDec.ModeSyn = ModeSyn !*)
  (*! sharing ModeDec.Paths = Paths !*)
  module StyleCheck : Style_.STYLECHECK
  module Unique : Unique_.UNIQUE

  (*! sharing Unique.ModeSyn = ModeSyn !*)
  module UniqueTable : Modetable.MODETABLE
  module Cover : Cover_.COVER

  (*! sharing Cover.IntSyn = IntSyn' !*)
  (*! sharing Cover.ModeSyn = ModeSyn !*)
  module Converter : module type of Tomega_.Converter

  (*! sharing Converter.IntSyn = IntSyn' !*)
  (*! sharing Converter.Tomega = Tomega !*)
  module TomegaPrint : Tomegaprint.TOMEGAPRINT

  (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
  (*! sharing TomegaPrint.Tomega = Tomega !*)
  module TomegaCoverage : Coverage.TOMEGACOVERAGE

  (*! sharing TomegaCoverage.IntSyn = IntSyn' !*)
  (*! sharing TomegaCoverage.Tomega = Tomega !*)
  module TomegaTypeCheck : TOMEGATYPECHECK.TOMEGATYPECHECK

  (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
  (*! sharing TomegaTypeCheck.Tomega = Tomega !*)
  module Total : module type of Cover_.Total

  (*! sharing Total.IntSyn = IntSyn' !*)
  module Reduces : module type of Terminate_.Reduces

  (*! sharing Reduces.IntSyn = IntSyn' !*)
  module Index : Index_.INDEX

  (*! sharing Index.IntSyn = IntSyn' !*)
  module IndexSkolem : Index_.INDEX

  (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
  module Subordinate : Subordinate_.SUBORDINATE

  (*! sharing Subordinate.IntSyn = IntSyn' !*)
  (*! structure CompSyn' : COMPSYN !*)
  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
  module Compile : Compile_.COMPILE

  (*! sharing Compile.IntSyn = IntSyn' !*)
  (*! sharing Compile.CompSyn = CompSyn' !*)
  module AbsMachine : Absmachine.ABSMACHINE

  (*! sharing AbsMachine.IntSyn = IntSyn' !*)
  (*! sharing AbsMachine.CompSyn = CompSyn' !*)
  (*! structure TableParam : TABLEPARAM !*)
  module Tabled : TabledMachine.TABLED

  (*! sharing Tabled.IntSyn = IntSyn' !*)
  (*! sharing Tabled.CompSyn = CompSyn' !*)
  module Solve : SOLVE with module ExtQuery = Parser.ExtQuery

  (*! sharing Solve.IntSyn = IntSyn' !*)
  module Fquery : FQUERY with module ExtQuery = Parser.ExtQuery

  (*! sharing Fquery.IntSyn = IntSyn' !*)
  (*! sharing Solve.Paths = Paths !*)
  module ThmSyn : Thmsyn.THMSYN with module Names = Names

  (*! sharing ThmSyn.Paths = Paths !*)
  module Thm : Thm_.THM with module ThmSyn = ThmSyn

  (*! sharing Thm.Paths = Paths !*)
  module ReconThm :
    RECONTHM.RECON_THM
      with module ThmSyn = ThmSyn
       and type tdecl = Parser.ThmExtSyn.tdecl
       and type rdecl = Parser.ThmExtSyn.rdecl
       and type wdecl = Parser.ThmExtSyn.wdecl
       and type tableddecl = Parser.ThmExtSyn.tableddecl
       and type keepTabledecl = Parser.ThmExtSyn.keepTabledecl
       and type prove = Parser.ThmExtSyn.prove
       and type establish = Parser.ThmExtSyn.establish
       and type assert_ = Parser.ThmExtSyn.assert_
       and type theoremdec = Parser.ThmExtSyn.theoremdec

  (*! sharing ReconThm.Paths = Paths !*)
  (*! sharing ReconThm.ThmSyn.ModeSyn = ModeSyn !*)
  (* -bp *)
  (* -bp *)
  (* -bp *)
  module ThmPrint : Thmprint.THMPRINT with module ThmSyn = ThmSyn
  module TabledSyn : Tabledsyn.TABLEDSYN

  (*! sharing TabledSyn.IntSyn = IntSyn' !*)
  module WorldSyn : WORLDSYN

  (*! sharing WorldSyn.IntSyn = IntSyn' !*)
  module Worldify : WORLDIFY

  (*   structure WorldPrint : WORLDPRINT *)
  (*! sharing WorldPrint.Tomega = Tomega !*)
  module ModSyn : Modsyn.MODSYN

  (*! sharing ModSyn.IntSyn = IntSyn' !*)
  (*! sharing ModSyn.Paths = Paths !*)
  module ReconModule :
    RECONMODULE.RECON_MODULE
      with module ModSyn = ModSyn
       and type sigdef = Parser.ModExtSyn.sigdef
       and type structdec = Parser.ModExtSyn.structdec
       and type sigexp = Parser.ModExtSyn.sigexp
       and type strexp = Parser.ModExtSyn.strexp

  module MetaGlobal : METAGLOBAL.METAGLOBAL

  (*! structure FunSyn : FUNSYN !*)
  (*! sharing FunSyn.IntSyn = IntSyn' !*)
  module Skolem : module type of M2_.Skolem

  (*! sharing Skolem.IntSyn = IntSyn' !*)
  module Prover : PROVER

  (*! sharing Prover.IntSyn = IntSyn' !*)
  module ClausePrint : CLAUSEPRINT.CLAUSEPRINT

  (*! sharing ClausePrint.IntSyn = IntSyn' !*)
  module Trace : TRACE.TRACE
  module PrintTeX : PRINT

  (*! sharing PrintTeX.IntSyn = IntSyn' !*)
  module ClausePrintTeX : CLAUSEPRINT.CLAUSEPRINT

  (*! sharing ClausePrintTeX.IntSyn = IntSyn' !*)
  module CsManager : CsManager.CS_MANAGER

  (*! sharing CsManager.IntSyn = IntSyn' !*)
  (*! sharing CsManager.ModeSyn = ModeSyn !*)
  module CSInstaller : CS_INSTALLER

  (* module Compat : COMPAT *)
  module UnknownExn : UNKNOWN_EXN
  module Msg : MSG
end) : TWELF.STELF = struct
  open Twelf__0
  module Names = Names
  module Parser = Parser

  type status = Ok | Abort

  open! struct
    module CompSyn = CompSyn.CompSyn
    module FunSyn = Funsyn.FunSyn
    module TableParam = TableParam.TableParam
    module S = Parser.Stream

    let msg s = Msg.message s
    let chmsg n s = if !Global.chatter >= n then msg (s ())

    let fileOpenMsg fileName =
      begin match !Global.chatter with
      | 0 -> ()
      | 1 -> msg (("[Loading file " ^ fileName) ^ " ...")
      | _ -> msg (("[Opening file " ^ fileName) ^ "]\n")
      end

    let fileCloseMsg fileName =
      begin match !Global.chatter with
      | 0 -> ()
      | 1 -> msg "]\n"
      | _ -> msg (("[Closing file " ^ fileName) ^ "]\n")
      end

    type 'a result = Value of 'a | Exception of exn

    let withOpenIn fileName scope =
      let instream = TextIO.openIn (Stdlib.String.trim fileName) in
      ignore (fileOpenMsg fileName);
      let result = scope instream in
      ignore (fileCloseMsg fileName);
      ignore (TextIO.closeIn instream);
      result

    let evarInstToString xs_ =
      begin if !Global.chatter >= 3 then Print.evarInstToString xs_ else ""
      end

    let expToString gu =
      begin if !Global.chatter >= 3 then (let g__, u__ = gu in Print.expToString g__ u__) else ""
      end

    let printProgTeX () =
      begin
        msg "\\begin{bigcode}\n";
        begin
          ClausePrintTeX.printSgn ();
          msg "\\end{bigcode}\n"
        end
      end

    let printSgnTeX () =
      begin
        msg "\\begin{bigcode}\n";
        begin
          PrintTeX.printSgn ();
          msg "\\end{bigcode}\n"
        end
      end

    let abort chlev msg =
      begin
        chmsg chlev (function () -> msg);
        Abort
      end

    let abortFileMsg chlev (fileName, msg) =
      abort chlev (((fileName ^ ":") ^ msg) ^ "\n")

    let abortIO (fileName, _) = begin
          msg (("IO Error on file " ^ fileName) ^ "\n");
          Abort
        end

    let rec joinregion (r, a) = match a with
      | [] -> r
      | r' :: rs -> joinregion (Paths.join r r', rs)

    let joinregions (r :: rs) = joinregion (r, rs)

    let constraintsMsg cnstrL =
      "Typing ambiguous -- unresolved constraints\n"
      ^ Print.cnstrsToString cnstrL

    let handleExceptions chlev fileName (f : 'a -> status) (x : 'a) =
      try f x with
      | ReconTerm.Error msg -> abortFileMsg chlev (fileName, msg)
      | ReconConDec.Error msg -> abortFileMsg chlev (fileName, msg)
      | ReconQuery.Error msg -> abortFileMsg chlev (fileName, msg)
      | ReconMode.Error msg -> abortFileMsg chlev (fileName, msg)
      | ReconThm.Error msg -> abortFileMsg chlev (fileName, msg)
      | ReconModule.Error msg -> abortFileMsg chlev (fileName, msg)
      | TypeCheck.Error msg ->
          let bt = Printexc.get_backtrace () in
          Printf.eprintf "TYPECHECK ERROR backtrace:\n%s\n%!" bt;
          abort 0
            ((("Double-checking types fails: " ^ msg) ^ "\n")
            ^ "This indicates a bug in Stelf.\n")
      | Abstract.Error msg -> abortFileMsg chlev (fileName, msg)
      | Total.Error msg -> abort chlev (msg ^ "\n")
      | Reduces.Error msg -> abort chlev (msg ^ "\n")
      | Compile.Error msg -> abortFileMsg chlev (fileName, msg)
      | Thm.Error msg -> abortFileMsg chlev (fileName, msg)
      | ModeTable.Error msg -> abortFileMsg chlev (fileName, msg)
      | ModeCheck.Error msg -> abort chlev (msg ^ "\n")
      | ModeDec.Error msg -> abortFileMsg chlev (fileName, msg)
      | Unique.Error msg -> abortFileMsg chlev (fileName, msg)
      | Cover.Error msg -> abortFileMsg chlev (fileName, msg)
      | Parsing.Parsing.Error msg -> abortFileMsg chlev (fileName, msg)
      | Lexer.Error msg -> abortFileMsg chlev (fileName, msg)
      | IntSyn.Error msg -> abort chlev (("Signature error: " ^ msg) ^ "\n")
      | Names.Error msg -> abortFileMsg chlev (fileName, msg)
      | Solve.AbortQuery msg -> abortFileMsg chlev (fileName, msg)
      | ThmSyn.Error msg -> abortFileMsg chlev (fileName, msg)
      | Prover.Error msg -> abortFileMsg chlev (fileName, msg)
      | Strict.Error msg -> abortFileMsg chlev (fileName, msg)
      | Subordinate.Error msg -> abortFileMsg chlev (fileName, msg)
      | WorldSyn.Error msg -> abort chlev (msg ^ "\n")
      | Worldify.Error msg -> abort chlev (msg ^ "\n")
      | ModSyn.Error msg -> abortFileMsg chlev (fileName, msg)
      | Converter.Error msg -> abortFileMsg chlev (fileName, msg)
      | CsManager.Error msg ->
          abort chlev (("Constraint Solver Manager error: " ^ msg) ^ "\n")

    let context : ModSyn.Names.namespace option ref = ref None

    let installConst fromCS (cid, fileNameocOpt) =
      ignore (Origins.installOrigin cid fileNameocOpt);
      ignore (Index.install fromCS (IntSyn.Const cid));
      ignore (IndexSkolem.install fromCS (IntSyn.Const cid));
      ignore (Timers.time Timers.compiling Compile.install fromCS cid);
      ignore (Timers.time Timers.subordinate Subordinate.install cid);
      ignore (Timers.time Timers.subordinate Subordinate.installDef cid);
      ()

    let installConDec fromCS (conDec, ((fileName, ocOpt) as fileNameocOpt), r) =
      ignore (Timers.time Timers.modes
          (fun () -> ModeCheck.checkD conDec fileName ocOpt)
          ());
      let cid = IntSyn.sgnAdd conDec in
      ignore (try
          begin match (fromCS, !context) with
          | IntSyn.Ordinary, Some namespace ->
              ModSyn.Names.insertConst namespace cid
          | IntSyn.Clause, Some namespace ->
              ModSyn.Names.insertConst namespace cid
          | _ -> ()
          end
        with Names.Error msg -> raise (Names.Error (Paths.wrap r msg)));
      ignore (Names.installConstName cid);
      ignore (try installConst fromCS (cid, fileNameocOpt)
        with Subordinate.Error msg ->
          raise (Subordinate.Error (Paths.wrap r msg)));
      ignore (Origins.installLinesInfo fileName (Paths.getLinesInfo ()));
      ignore begin if !Global.style >= 1 then StyleCheck.checkConDec cid else ()
        end;
      cid

    let installBlockDec fromCS (conDec, ((fileName, ocOpt) as fileNameocOpt), r)
        =
      let cid = IntSyn.sgnAdd conDec in
      ignore (try
          begin match (fromCS, !context) with
          | IntSyn.Ordinary, Some namespace ->
              ModSyn.Names.insertConst namespace cid
          | _ -> ()
          end
        with Names.Error msg -> raise (Names.Error (Paths.wrap r msg)));
      ignore (Names.installConstName cid);
      ignore (try Timers.time Timers.subordinate Subordinate.installBlock cid
        with Subordinate.Error msg ->
          raise (Subordinate.Error (Paths.wrap r msg)));
      ignore (Origins.installLinesInfo fileName (Paths.getLinesInfo ()));
      cid

    let installBlockDef fromCS (conDec, ((fileName, ocOpt) as fileNameocOpt), r)
        =
      let cid = IntSyn.sgnAdd conDec in
      ignore (try
          begin match (fromCS, !context) with
          | IntSyn.Ordinary, Some namespace ->
              ModSyn.Names.insertConst namespace cid
          | _ -> ()
          end
        with Names.Error msg -> raise (Names.Error (Paths.wrap r msg)));
      ignore (Names.installConstName cid);
      ignore (Origins.installLinesInfo fileName (Paths.getLinesInfo ()));
      cid

    let installStrDec (strdec, module_, r, isDef) =
      let installAction ((cid, _) as data) =
        begin
          installConst IntSyn.Ordinary data;
          Display.chatter_s 4
            (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n")
        end
      in
      ignore (try
          ModSyn.installStruct (strdec, module_, !context, installAction, isDef)
        with Names.Error msg -> raise (Names.Error (Paths.wrap r msg)));
      ()

    let includeSig (module_, r, isDef) =
      let installAction ((cid, _) as data) =
        begin
          installConst IntSyn.Ordinary data;
          Display.chatter_s 4
            (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n")
        end
      in
      ignore (try ModSyn.installSig (module_, !context, installAction, isDef)
        with Names.Error msg -> raise (Names.Error (Paths.wrap r msg)));
      ()

    let cidToString a = Names.qidToString (Names.constQid a)

    let invalidate uninstallFun cids msg =
      let uninstalledCids = List.filter (function a -> uninstallFun a) cids in
      ignore begin match uninstalledCids with
        | [] -> ()
        | _ ->
            chmsg 4 (function () ->
                (("Invalidated " ^ msg) ^ " properties of families")
                ^ List.foldr
                    (function a, s -> (" " ^ cidToString a) ^ s)
                    "\n" uninstalledCids)
        end;
      ()

    let rec install1 a3 b3 = match a3, b3 with
      | fileName, (Parser.ConDec condec_, r) -> (
          try
            let optConDec, ocOpt =
              ReconConDec.condecToConDec
                condec_ (Paths.Loc (fileName, r)) false
            in
            let icd = function
              | Some (IntSyn.BlockDec _ as conDec) ->
                  let cid =
                    installBlockDec IntSyn.Ordinary
                      (conDec, (fileName, ocOpt), r)
                  in
                  ()
              | Some (IntSyn.BlockDef _ as conDec) ->
                  let cid =
                    installBlockDef IntSyn.Ordinary
                      (conDec, (fileName, ocOpt), r)
                  in
                  ()
              | Some conDec ->
                  let cid =
                    installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
                  in
                  ()
              | None -> ()
            in
            icd optConDec
          with Constraints.Error eqns ->
            raise (ReconTerm.Error (Paths.wrap r (constraintsMsg eqns))))
      | fileName, (Parser.AbbrevDec condec_, r) -> (
          try
            let optConDec, ocOpt =
              ReconConDec.condecToConDec condec_ (Paths.Loc (fileName, r)) true
            in
            let icd = function
              | Some conDec ->
                  let cid =
                    installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
                  in
                  ()
              | None -> ()
            in
            icd optConDec
          with Constraints.Error eqns ->
            raise (ReconTerm.Error (Paths.wrap r (constraintsMsg eqns))))
      | fileName, (Parser.ClauseDec condec_, r) -> (
          try
            let optConDec, ocOpt =
              ReconConDec.condecToConDec
                condec_ (Paths.Loc (fileName, r)) false
            in
            let icd = function
              | Some conDec ->
                  let cid =
                    installConDec IntSyn.Clause (conDec, (fileName, ocOpt), r)
                  in
                  ()
              | None -> ()
            in
            icd optConDec
          with Constraints.Error eqns ->
            raise (ReconTerm.Error (Paths.wrap r (constraintsMsg eqns))))
      | fileName, (Parser.Solve (defines, solve_), r) -> (
          try
            let conDecL =
              try Solve.solve defines solve_ (Paths.Loc (fileName, r))
              with Solve.AbortQuery msg ->
                raise (Solve.AbortQuery (Paths.wrap r msg))
            in
            let icd (conDec, ocOpt) =
              let cid =
                installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
              in
              ()
            in
            List.app icd conDecL
          with Constraints.Error eqns ->
            raise (ReconTerm.Error (Paths.wrap r (constraintsMsg eqns))))
      | fileName, (Parser.Query (expected, try_, query_), r) -> (
          try Solve.query expected try_ query_ (Paths.Loc (fileName, r))
          with Solve.AbortQuery msg ->
            raise (Solve.AbortQuery (Paths.wrap r msg)))
      | fileName, (Parser.FQuery query_, r) -> (
          try Fquery.run query_ (Paths.Loc (fileName, r))
          with Fquery.AbortQuery msg ->
            raise (Fquery.AbortQuery (Paths.wrap r msg)))
      | fileName, (Parser.Querytabled (numSol, try_, query_), r) -> (
          try Solve.querytabled numSol try_ query_ (Paths.Loc (fileName, r))
          with Solve.AbortQuery msg ->
            raise (Solve.AbortQuery (Paths.wrap r msg)))
      | fileName, (Parser.TrustMe (dec_, r'), r) ->
          ignore begin if not !Global.unsafe then
              raise (Thm.Error "%trustme not safe: Toggle `unsafe' flag")
            else ()
            end;
          ignore (chmsg 3 (function () -> "[%trustme ...\n"));
          ignore begin match
              handleExceptions 4 fileName
                (function
                  | fn__, dr__ -> begin
                      install1 fn__ dr__;
                      Ok
                    end)
                (fileName, (dec_, r))
            with
            | Ok -> chmsg 3 (function () -> "trustme subject succeeded\n")
            | Abort ->
                chmsg 3 (function () -> "trustme subject failed; continuing\n")
            end;
          ignore (chmsg 3 (function () -> "%]\n"));
          ()
      | fileName, (Parser.SubordDec qidpairs, r) ->
          let toCid qid =
            begin match Names.constLookup qid with
            | None ->
                raise
                  (Names.Error
                     (("Undeclared identifier "
                      ^ Names.qidToString (valOf (Names.constUndef qid)))
                     ^ " in subord declaration"))
            | Some cid -> cid
            end
          in
          let cidpairs =
            try
              List.map
                (function qid1, qid2 -> (toCid qid1, toCid qid2))
                qidpairs
            with Names.Error msg -> raise (Names.Error (Paths.wrap r msg))
          in
          ignore (try List.app (fun (a__, b__) -> Subordinate.addSubord a__ b__) cidpairs
            with Subordinate.Error msg ->
              raise (Subordinate.Error (Paths.wrap r msg)));
          Display.chatter_s 3
            ("%subord"
            ^ List.foldr
                (function
                  | (a1, a2), s ->
                      ((((" (" ^ Names.qidToString (Names.constQid a1)) ^ " ")
                       ^ Names.qidToString (Names.constQid a2))
                      ^ ")")
                      ^ s)
                ".\n" cidpairs)
      | fileName, (Parser.FreezeDec qids, r) ->
          let toCid qid =
            begin match Names.constLookup qid with
            | None ->
                raise
                  (Names.Error
                     (("Undeclared identifier "
                      ^ Names.qidToString (valOf (Names.constUndef qid)))
                     ^ " in freeze declaration"))
            | Some cid -> cid
            end
          in
          let cids =
            try List.map toCid qids
            with Names.Error msg -> raise (Names.Error (Paths.wrap r msg))
          in
          let frozen =
            try Subordinate.freeze cids
            with Subordinate.Error msg ->
              raise (Subordinate.Error (Paths.wrap r msg))
          in
          Display.chatter_s 3
            ("%freeze"
            ^ List.foldr
                (function
                  | a, s -> (" " ^ Names.qidToString (Names.constQid a)) ^ s)
                ".\n" cids);
          Display.chatter_s 4
            ("Frozen:"
            ^ List.foldr
                (function
                  | a, s -> (" " ^ Names.qidToString (Names.constQid a)) ^ s)
                "\n" frozen)
      | fileName, (Parser.ThawDec qids, r) ->
          ignore begin if not !Global.unsafe then
              raise (ThmSyn.Error "%thaw not safe: Toggle `unsafe' flag")
            else ()
            end;
          let toCid qid =
            begin match Names.constLookup qid with
            | None ->
                raise
                  (Names.Error
                     (("Undeclared identifier "
                      ^ Names.qidToString (valOf (Names.constUndef qid)))
                     ^ " in thaw declaration"))
            | Some cid -> cid
            end
          in
          let cids =
            try List.map toCid qids
            with Names.Error msg -> raise (Names.Error (Paths.wrap r msg))
          in
          let thawed =
            try Subordinate.thaw cids
            with Subordinate.Error msg ->
              raise (Subordinate.Error (Paths.wrap r msg))
          in
          ignore (Display.chatter_s 3
              ("%thaw"
              ^ List.foldr
                  (function a, s -> (" " ^ cidToString a) ^ s)
                  ".\n" cids));
          ignore (Display.chatter_s 4
              ("Thawed"
              ^ List.foldr
                  (function a, s -> (" " ^ cidToString a) ^ s)
                  "\n" thawed));
          ignore (invalidate WorldSyn.uninstall thawed "world");
          ignore (invalidate Thm.uninstallTerminates thawed "termination");
          ignore (invalidate Thm.uninstallReduces thawed "reduction");
          ignore (invalidate UniqueTable.uninstallMode thawed "uniqueness");
          ignore (invalidate Total.uninstall thawed "totality");
          ()
      | fileName, (Parser.DeterministicDec qids, r) ->
          let toCid qid =
            begin match Names.constLookup qid with
            | None ->
                raise
                  (Names.Error
                     (("Undeclared identifier "
                      ^ Names.qidToString (valOf (Names.constUndef qid)))
                     ^ " in deterministic declaration"))
            | Some cid -> cid
            end
          in
          let insertCid cid = CompSyn.detTableInsert cid true in
          let cids =
            try List.map toCid qids
            with Names.Error msg -> raise (Names.Error (Paths.wrap r msg))
          in
          List.app insertCid cids;
          Display.chatter_s 3
            ((begin if !Global.chatter >= 4 then "%" else ""
              end
             ^ "%deterministic")
            ^ List.foldr
                (function
                  | a, s -> (" " ^ Names.qidToString (Names.constQid a)) ^ s)
                ".\n" cids)
      | fileName, (Parser.Compile qids, r) ->
          let toCid qid =
            begin match Names.constLookup qid with
            | None ->
                raise
                  (Names.Error
                     (("Undeclared identifier "
                      ^ Names.qidToString (valOf (Names.constUndef qid)))
                     ^ " in compile assertion"))
            | Some cid -> cid
            end
          in
          let cids =
            try List.map toCid qids
            with Names.Error msg -> raise (Names.Error (Paths.wrap r msg))
          in
          let rec checkFreeOut = function
            | [] -> ()
            | a :: la_ ->
                let (Some ms) = ModeTable.modeLookup a in
                ignore (ModeCheck.checkFreeOut a ms);
                checkFreeOut la_
          in
          ignore (checkFreeOut cids);
          let lemma, projs, sels = Converter.installPrg cids in
          let p_ = Tomega.lemmaDef lemma in
          let f_ = Converter.convertFor cids in
          ignore (TomegaTypeCheck.checkPrg IntSyn.Null (p_, f_));
          let f cid = IntSyn.conDecName (IntSyn.sgnLookup cid) in
          ignore (Display.chatter_s 2
              (("\n" ^ TomegaPrint.funToString (map f cids) projs p_) ^ "\n"));
          ignore (Display.chatter_s 3
              ((begin if !Global.chatter >= 4 then "%" else ""
                end
               ^ "%compile")
              ^ List.foldr
                  (function
                    | a, s -> (" " ^ Names.qidToString (Names.constQid a)) ^ s)
                  ".\n" cids));
          ()
      | fileName, (Parser.FixDec ((qid, r), fixity), _) ->
          begin match Names.constLookup qid with
          | None ->
              raise
                (Names.Error
                   (("Undeclared identifier "
                    ^ Names.qidToString (valOf (Names.constUndef qid)))
                   ^ " in fixity declaration"))
          | Some cid -> (
              try
                begin
                  Names.installFixity cid fixity;
                  Display.chatter_s 3
                    ((((begin if !Global.chatter >= 4 then "%" else ""
                        end
                       ^ Names.Fixity.toString fixity)
                      ^ " ")
                     ^ Names.qidToString (Names.constQid cid))
                    ^ ".\n")
                end
              with Names.Error msg ->
                raise (Names.Error (Paths.wrap r msg)))
          end
      | fileName, (Parser.NamePref ((qid, r), namePref), _) ->
          begin match Names.constLookup qid with
          | None ->
              raise
                (Names.Error
                   (("Undeclared identifier "
                    ^ Names.qidToString (valOf (Names.constUndef qid)))
                   ^ " in name preference"))
          | Some cid -> (
              try Names.installNamePref cid namePref
              with Names.Error msg ->
                raise (Names.Error (Paths.wrap r msg)))
          end
      | fileName, (Parser.ModeDec mterms, r) ->
          let mdecs = List.map ReconMode.modeToMode mterms in
          ignore (ReconTerm.checkErrors r);
          ignore (List.app
              (function
                | ((a, _) as mdec), r ->
                    begin match ModeTable.modeLookup a with
                    | None -> ()
                    | Some _ ->
                        begin if Subordinate.frozen [ a ] then
                          raise
                            (ModeTable.Error
                               (Paths.wrap
                                  r ("Cannot redeclare mode for frozen constant "
                                    ^ Names.qidToString (Names.constQid a))))
                        else ()
                        end
                    end)
              mdecs);
          ignore (List.app
              (function
                | (a, mS), r -> (
                    try
                      begin match IntSyn.conDecStatus (IntSyn.sgnLookup a) with
                      | normal_ -> ModeTable.installMode a mS
                      | _ ->
                          raise
                            (ModeTable.Error
                               "Cannot declare modes for foreign constants")
                      end
                    with ModeTable.Error msg ->
                      raise (ModeTable.Error (Paths.wrap r msg))))
              mdecs);
          ignore
            (List.app
               (function (a__, ms__), r -> ModeDec.checkPure a__ ms__ r)
               mdecs);
          ignore (List.app
              (function
                | (a, mS), r -> (
                    try ModeCheck.checkMode a mS
                    with ModeCheck.Error msg -> raise (ModeCheck.Error msg)))
              mdecs);
          ignore (Display.chatter_s 3
              (("%mode "
               ^ ModePrint.modesToString
                   (List.map (function mdec, r -> mdec) mdecs))
              ^ ".\n"));
          ()
      | fileName, (Parser.UniqueDec mterms, r) ->
          let mdecs = List.map ReconMode.modeToMode mterms in
          ignore (ReconTerm.checkErrors r);
          ignore (List.app
              (function
                | (a, mS), r -> (
                    try
                      begin match IntSyn.conDecStatus (IntSyn.sgnLookup a) with
                      | normal_ -> UniqueTable.installMode a mS
                      | _ ->
                          raise
                            (UniqueTable.Error
                               "Cannot declare modes for foreign constants")
                      end
                    with UniqueTable.Error msg ->
                      raise (Unique.Error (Paths.wrap r msg))))
              mdecs);
          ignore (List.app
              (function
                | (a__, ms__), r -> (
                    try
                      Timers.time Timers.coverage
                        (fun () -> Unique.checkUnique a__ ms__) ()
                    with Unique.Error msg ->
                      raise (Unique.Error (Paths.wrap r msg))))
              mdecs);
          ignore (Display.chatter_s 3
              (("%unique "
               ^ ModePrint.modesToString
                   (List.map (function mdec, r -> mdec) mdecs))
              ^ ".\n"));
          ()
      | fileName, (Parser.CoversDec mterms, r) ->
          let mdecs = List.map ReconMode.modeToMode mterms in
          ignore (ReconTerm.checkErrors r);
          ignore
            (List.app
               (function (a__, ms__), r -> ModeDec.checkPure a__ ms__ r)
               mdecs);
          ignore (List.app
              (function
                | (a__, ms__), r -> (
                    try
                      Timers.time Timers.coverage
                        (fun () -> Cover.checkCovers a__ ms__) ()
                    with Cover.Error msg ->
                      raise (Cover.Error (Paths.wrap r msg))))
              mdecs);
          ignore (Display.chatter_s 3
              (("%covers "
               ^ ModePrint.modesToString
                   (List.map (function mdec, r -> mdec) mdecs))
              ^ ".\n"));
          ()
      | fileName, (Parser.TotalDec lterm, r) ->
          let t_, ((r, rs) as rrs) = ReconThm.tdeclTotDecl lterm in
          let la_ = Thm.installTotal t_ rrs in
          ignore (map Total.install la_);
          ignore (try map Total.checkFam la_ with
            | Total.Error msg -> raise (Total.Error msg)
            | Cover.Error msg -> raise (Cover.Error (Paths.wrap r msg))
            | Reduces.Error msg -> raise (Reduces.Error msg)
            | Subordinate.Error msg ->
                raise (Subordinate.Error (Paths.wrap r msg)));
          ignore (Display.chatter_s 3 (("%total " ^ ThmPrint.tDeclToString t_) ^ ".\n"));
          ()
      | fileName, (Parser.TerminatesDec lterm, _) ->
          let t_, ((r, rs) as rrs) = ReconThm.tdeclTotDecl lterm in
          let (ThmSyn.TDecl (_, ThmSyn.Callpats callpats)) = t_ in
          let la_ = Thm.installTerminates t_ rrs in
          ignore (map (Timers.time Timers.terminate Reduces.checkFam) la_);
          ignore begin if !Global.autoFreeze then begin
              ignore (Subordinate.freeze la_);
              ()
            end
            else ()
            end;
          ignore (Display.chatter_s 3
              (("%terminates " ^ ThmPrint.tDeclToString t_) ^ ".\n"));
          ()
      | fileName, (Parser.ReducesDec lterm, _) ->
          let r_, ((r, rs) as rrs) = ReconThm.rdeclTorDecl lterm in
          let (ThmSyn.RDecl (_, ThmSyn.Callpats callpats)) = r_ in
          let la_ = Thm.installReduces r_ rrs in
          ignore (map (Timers.time Timers.terminate Reduces.checkFamReduction) la_);
          ignore begin if !Global.autoFreeze then begin
              ignore (Subordinate.freeze la_);
              ()
            end
            else ()
            end;
          ignore begin if !Global.chatter >= 3 then
              msg (("%reduces " ^ ThmPrint.rDeclToString r_) ^ ".\n")
            else ()
            end;
          ()
      | fileName, (Parser.TabledDec tdecl, _) ->
          let t_, r = ReconThm.tableddeclTotabledDecl tdecl in
          let la_ = Thm.installTabled t_ in
          ignore (Display.chatter_s 3
              (("%tabled " ^ ThmPrint.tabledDeclToString t_) ^ ".\n"));
          ()
      | fileName, (Parser.KeepTableDec tdecl, _) ->
          let t_, r = ReconThm.keepTabledeclToktDecl tdecl in
          let la_ = Thm.installKeepTable t_ in
          ignore (Display.chatter_s 3
              (("%keeptabled " ^ ThmPrint.keepTableDeclToString t_) ^ ".\n"));
          ()
      | fileName, (Parser.TheoremDec tdec, r) ->
          let tname, tdecl = ReconThm.theoremDecToTheoremDec tdec in
          ignore (ReconTerm.checkErrors r);
          let gBs, (IntSyn.ConDec (name, _, k, _, v_, l_) as e_) =
            ThmSyn.theoremDecToConDec tname tdecl r
          in
          ignore (FunSyn.labelReset ());
          ignore (List.foldr
              (function
                | (g1_, g2_), k ->
                    FunSyn.labelAdd
                      (FunSyn.LabelDec
                         ( Int.toString k,
                           FunSyn.ctxToList g1_,
                           FunSyn.ctxToList g2_ )))
              0 gBs);
          let cid = installConDec IntSyn.Ordinary (e_, (fileName, None), r) in
          let ms_ = ThmSyn.theoremDecToModeSpine tname tdecl r in
          let convert_mode = function
            | ModeSyn.Plus -> Modes.Modesyn.ModeSyn.Plus
            | ModeSyn.Star -> Modes.Modesyn.ModeSyn.Star
            | ModeSyn.Minus -> Modes.Modesyn.ModeSyn.Minus
            | ModeSyn.Minus1 -> Modes.Modesyn.ModeSyn.Minus1
          in
          let rec convert_mode_spine = function
            | ModeSyn.Mnil -> Modes.Modesyn.ModeSyn.Mnil
            | ModeSyn.Mapp (ModeSyn.Marg (m, name), tail) ->
                Modes.Modesyn.ModeSyn.Mapp
                  ( Modes.Modesyn.ModeSyn.Marg (convert_mode m, name),
                    convert_mode_spine tail )
          in
          ignore (ModeTable.installMode cid (convert_mode_spine ms_));
          ignore (Display.chatter_s 3 (("%theorem " ^ Print.conDecToString e_) ^ "\n"));
          ()
      | fileName, (Parser.ProveDec lterm, r) ->
          let ThmSyn.PDecl (depth, t_), rrs = ReconThm.proveToProve lterm in
          let la_ = Thm.installTerminates t_ rrs in
          ignore (Display.chatter_s 3
              (((("%prove " ^ Int.toString depth) ^ " ")
               ^ ThmPrint.tDeclToString t_)
              ^ ".\n"));
          ignore (Prover.init depth la_);
          ignore (if !Global.chatter >= 3 then
              map
                (function
                  | a ->
                      Display.chatter_s 3
                        (("%mode "
                         ^ ModePrint.modeToString
                             a (valOf (ModeTable.modeLookup a)))
                        ^ ".\n"))
                la_
            else [ () ]);
          ignore (try Prover.auto ()
            with Prover.Error msg ->
              raise (Prover.Error (Paths.wrap (joinregion rrs) msg)));
          ignore (Display.chatter_s 3 "%QED\n");
          begin
            Prover.install (function e_ ->
                installConDec IntSyn.Ordinary (e_, (fileName, None), r));
            Skolem.install la_
          end
      | fileName, (Parser.EstablishDec lterm, r) ->
          let ThmSyn.PDecl (depth, t_), rrs =
            ReconThm.establishToEstablish lterm
          in
          let la_ = Thm.installTerminates t_ rrs in
          ignore begin if !Global.chatter >= 3 then
              msg
                (((("%prove " ^ Int.toString depth) ^ " ")
                 ^ ThmPrint.tDeclToString t_)
                ^ ".\n")
            else ()
            end;
          ignore (Prover.init depth la_);
          ignore (if !Global.chatter >= 3 then
              map
                (function
                  | a ->
                      Display.chatter_s 3
                        (("%mode "
                         ^ ModePrint.modeToString
                             a (valOf (ModeTable.modeLookup a)))
                        ^ ".\n"))
                la_
            else [ () ]);
          ignore (try Prover.auto ()
            with Prover.Error msg ->
              raise (Prover.Error (Paths.wrap (joinregion rrs) msg)));
          Prover.install (function e_ ->
              installConDec IntSyn.Ordinary (e_, (fileName, None), r))
      | fileName, (Parser.AssertDec aterm, _) ->
          ignore begin if not !Global.unsafe then
              raise (ThmSyn.Error "%assert not safe: Toggle `unsafe' flag")
            else ()
            end;
          let (ThmSyn.Callpats l_ as cp), rrs = ReconThm.assertToAssert aterm in
          let la_ = map (function c, p_ -> c) l_ in
          ignore (Display.chatter_s 3
              (("%assert " ^ ThmPrint.callpatsToString cp) ^ ".\n"));
          ignore (if !Global.chatter >= 3 then
              map
                (function
                  | a ->
                      Display.chatter_s 3
                        (("%mode "
                         ^ ModePrint.modeToString
                             a (valOf (ModeTable.modeLookup a)))
                        ^ ".\n"))
                la_
            else [ () ]);
          Skolem.install la_
      | fileName, (Parser.WorldDec wdecl, _) ->
          let ThmSyn.WDecl (qids, (ThmSyn.Callpats cpa as cp)), rs =
            ReconThm.wdeclTowDecl wdecl
          in
          ignore (ListPair.app
              (function
                | (a, _), r ->
                    begin if Subordinate.frozen [ a ] then
                      raise
                        (WorldSyn.Error
                           (Paths.wrapLoc
                              (Paths.Loc (fileName, r)) ("Cannot declare worlds for frozen family "
                                ^ Names.qidToString (Names.constQid a))))
                    else ()
                    end)
              (cpa, rs));
          let rec flatten arg__1 arg__2 =
            begin match (arg__1, arg__2) with
            | [], f_ -> f_
            | cid :: l_, f_ ->
                begin match IntSyn.sgnLookup cid with
                | IntSyn.BlockDec _ -> flatten l_ (cid :: f_)
                | IntSyn.BlockDef (_, _, l'_) -> flatten (l_ @ l'_) f_
                end
            end
          in
          let w_ =
            Tomega.Worlds
              (flatten
                 (List.map
                    (function
                      | qid ->
                          begin match Names.constLookup qid with
                          | None ->
                              raise
                                (Names.Error
                                   (("Undeclared label "
                                    ^ Names.qidToString
                                        (valOf (Names.constUndef qid)))
                                   ^ "."))
                          | Some cid -> cid
                          end)
                    qids)
                 [])
          in
          ignore (try List.app (function a, _ -> WorldSyn.install a w_) cpa
            with WorldSyn.Error msg ->
              raise
                (WorldSyn.Error
                   (Paths.wrapLoc (Paths.Loc (fileName, joinregions rs)) msg)));
          ignore begin if !Global.autoFreeze then begin
              ignore (Subordinate.freeze (List.map (function a, _ -> a) cpa));
              ()
            end
            else ()
            end;
          ignore (Display.chatter_s 3
              (((("%worlds " ^ Print.worldsToString w_) ^ " ")
               ^ ThmPrint.callpatsToString cp)
              ^ ".\n"));
          begin
            Timers.time Timers.worlds
              (List.app (function a, _ -> WorldSyn.worldcheck w_ a))
              cpa;
            ()
          end
      | fileName, ((Parser.SigDef _, _) as declr) ->
          install1WithSig (fileName, None, declr)
      | fileName, ((Parser.StructDec _, _) as declr) ->
          install1WithSig (fileName, None, declr)
      | fileName, ((Parser.Include _, _) as declr) ->
          install1WithSig (fileName, None, declr)
      | fileName, ((Parser.Open _, _) as declr) ->
          install1WithSig (fileName, None, declr)
      | fileName, (Parser.Use name, r) ->
          begin match !context with
          | None -> CsManager.useSolver name
          | _ ->
              raise
                (ModSyn.Error
                   (Paths.wrap r ("%use declaration needs to be at top level")))
          end

    and install1WithSig (fileName, moduleOpt, a) = match moduleOpt, a with
      | moduleOpt, (Parser.SigDef sigdef, r) ->
          let idOpt, module_, wherecls =
            ReconModule.sigdefToSigdef sigdef moduleOpt
          in
          let module' =
            foldl
              (function
                | inst, module_ -> ReconModule.moduleWhere module_ inst)
              module_ wherecls
          in
          let name =
            try
              begin match idOpt with
              | Some id -> begin
                  ModSyn.installSigDef id module';
                  id
                end
              | None -> "_"
              end
            with ModSyn.Error msg ->
              raise (ModSyn.Error (Paths.wrap r msg))
          in
          ignore (Display.chatter_s 3 (("%sig " ^ name) ^ " = { ... }.\n"));
          ()
      | moduleOpt, (Parser.StructDec structdec, r) ->
          begin match
            ReconModule.structdecToStructDec structdec moduleOpt
          with
          | ReconModule.StructDec (idOpt, module_, wherecls) ->
              let module' =
                foldl
                  (function
                    | inst, module_ -> ReconModule.moduleWhere module_ inst)
                  module_ wherecls
              in
              let name =
                begin match idOpt with
                | Some id -> begin
                    installStrDec (IntSyn.StrDec (id, None), module', r, false);
                    id
                  end
                | None -> "_"
                end
              in
              ignore begin if !Global.chatter = 3 then
                  msg (("%struct " ^ name) ^ " : { ... }.\n")
                else ()
                end;
              ()
          | ReconModule.StructDef (idOpt, mid) ->
              let ns = ModSyn.Names.getComponents mid in
              let module_ = ModSyn.abstractModule ns (Some mid) in
              let name =
                begin match idOpt with
                | Some id -> begin
                    installStrDec (IntSyn.StrDec (id, None), module_, r, true);
                    id
                  end
                | None -> "_"
                end
              in
              ignore begin if !Global.chatter = 3 then
                  msg
                    (((("%struct " ^ name) ^ " = ")
                     ^ Names.qidToString (Names.structQid mid))
                    ^ ".\n")
                else ()
                end;
              ()
          end
      | moduleOpt, (Parser.Include sigexp, r) ->
          let module_, wherecls =
            ReconModule.sigexpToSigexp sigexp moduleOpt
          in
          let module' =
            foldl
              (function
                | inst, module_ -> ReconModule.moduleWhere module_ inst)
              module_ wherecls
          in
          ignore (includeSig (module', r, false));
          ignore begin if !Global.chatter = 3 then msg "%include { ... }.\n" else ()
            end;
          ()
      | None, (Parser.Open strexp, r) ->
          let mid = ReconModule.strexpToStrexp strexp in
          let ns = ModSyn.Names.getComponents mid in
          let module_ = ModSyn.abstractModule ns (Some mid) in
          ignore (includeSig (module_, r, true));
          ignore begin if !Global.chatter = 3 then
              msg (("%open " ^ Names.qidToString (Names.structQid mid)) ^ ".\n")
            else ()
            end;
          ()

    let rec installSubsig (fileName, s) =
      let namespace = ModSyn.Names.newNamespace () in
      let mark, markStruct = IntSyn.sgnSize () in
      let markSigDef = ModSyn.sigDefSize () in
      let oldContext = !context in
      ignore (context := Some namespace);
      ignore (Display.chatter_s 4 "\n% begin subsignature\n");
      let rec install s = install' (Timers.time Timers.parsing S.expose s)
      and install' = function
        | S.Cons ((beginSubsig, _), s') ->
            install (installSubsig (fileName, s'))
        | S.Cons ((endSubsig, _), s') -> s'
        | S.Cons (declr, s') -> begin
            install1 fileName declr;
            install s'
          end
      in
      let result =
        try
          let s' = install s in
          let module_ = ModSyn.abstractModule namespace None in
          ignore (Display.chatter_s 4 "% end subsignature\n\n");
          Value (module_, s')
        with exn -> Exception exn
      in
      ignore (context := oldContext);
      ignore (Names.resetFrom mark markStruct);
      ignore (Index.resetFrom mark);
      ignore (IndexSkolem.resetFrom mark);
      ignore (ModSyn.resetFrom markSigDef);
      begin match result with
      | Value (module_, s') ->
          let (S.Cons (declr, s'')) = Timers.time Timers.parsing S.expose s' in
          install1WithSig (fileName, Some module_, declr);
          s''
      | Exception exn -> raise exn
      end

    (* Load a file *)
    let loadFile fileName =
      handleExceptions 0 fileName (withOpenIn fileName) (function instream ->
          ignore (ReconTerm.resetErrors fileName);
          let rec install s = install' (Timers.time Timers.parsing S.expose s)
          and install' = function
            | S.Empty -> Ok
            | S.Cons ((Parser.BeginSubsig, _), s') ->
                install (installSubsig (fileName, s'))
            | S.Cons (decl, s') -> begin
                install1 fileName decl;
                install s'
              end
          in
          install (Parser.parseStream instream))

    let loadString str =
      let tmpFile = ".stelf-load-string.tmp" in
      let outstream = TextIO.openOut tmpFile in
      ignore (TextIO.output (outstream, str));
      ignore (TextIO.closeOut outstream);
      let result =
        handleExceptions 0 "string" (withOpenIn tmpFile) (function instream ->
            ignore (ReconTerm.resetErrors "string");
            let rec install s = install' (Timers.time Timers.parsing S.expose s)
            and install' = function
              | empty_ -> Ok
              | S.Cons ((beginSubsig, _), s') ->
                  install (installSubsig ("string", s'))
              | S.Cons (decl, s') -> begin
                  install1 ("string") decl;
                  install s'
                end
            in
            install (Parser.parseStream instream))
      in
      ignore (Sys.remove tmpFile);
      result

    let sLoop () =
      begin if Solve.qLoop () then Ok else Abort
      end

    let rec topLoop () =
      begin match handleExceptions 0 "stdIn" sLoop () with
      | Abort -> topLoop ()
      | Ok -> ()
      end

    let top () = topLoop ()

    let installCSMDec (conDec, optFixity, mdecL) =
      let convert_mode = function
        | Modes.Modes_.ModeSyn.Plus -> Modes.Modesyn.ModeSyn.Plus
        | Modes.Modes_.ModeSyn.Star -> Modes.Modesyn.ModeSyn.Star
        | Modes.Modes_.ModeSyn.Minus -> Modes.Modesyn.ModeSyn.Minus
        | Modes.Modes_.ModeSyn.Minus1 -> Modes.Modesyn.ModeSyn.Minus1
      in
      let rec convert_mode_spine = function
        | Modes.Modes_.ModeSyn.Mnil -> Modes.Modesyn.ModeSyn.Mnil
        | Modes.Modes_.ModeSyn.Mapp (Modes.Modes_.ModeSyn.Marg (m, name), tail)
          ->
            Modes.Modesyn.ModeSyn.Mapp
              ( Modes.Modesyn.ModeSyn.Marg (convert_mode m, name),
                convert_mode_spine tail )
      in
      let convert_assoc = function
        | CsManager.Fixity.Left -> Names.Fixity.Left
        | CsManager.Fixity.Right -> Names.Fixity.Right
        | CsManager.Fixity.None -> Names.Fixity.None
      in
      let convert_prec = function
        | CsManager.Fixity.Strength n -> Names.Fixity.Strength n
      in
      let convert_fixity = function
        | CsManager.Fixity.Nonfix -> Names.Fixity.Nonfix
        | CsManager.Fixity.Infix (p, a) ->
            Names.Fixity.Infix (convert_prec p, convert_assoc a)
        | CsManager.Fixity.Prefix p -> Names.Fixity.Prefix (convert_prec p)
        | CsManager.Fixity.Postfix p -> Names.Fixity.Postfix (convert_prec p)
      in
      ignore (ModeCheck.checkD conDec ("%use") None);
      let cid =
        installConDec IntSyn.FromCS (conDec, ("", None), Paths.Reg (0, 0))
      in
      ignore begin if !Global.chatter >= 3 then
          msg (Print.conDecToString conDec ^ "\n")
        else ()
        end;
      ignore begin match optFixity with
        | Some fixity -> begin
            let fixity' = convert_fixity fixity in
            Names.installFixity cid fixity';
            Display.chatter_s 3
              ((((begin if !Global.chatter >= 4 then "%" else ""
                  end
                 ^ Names.Fixity.toString fixity')
                ^ " ")
               ^ Names.qidToString (Names.constQid cid))
              ^ ".\n")
          end
        | None -> ()
        end;
      ignore (List.app
          (function
            | mdec -> ModeTable.installMmode cid (convert_mode_spine mdec))
          mdecL);
      cid

    let _ = CsManager.setInstallFN installCSMDec

    let reset () =
      begin
        IntSyn.sgnReset ();
        begin
          Names.reset ();
          begin
            Origins.reset ();
            begin
              ModeTable.reset ();
              begin
                UniqueTable.reset ();
                begin
                  Index.reset ();
                  begin
                    IndexSkolem.reset ();
                    begin
                      Subordinate.reset ();
                      begin
                        Total.reset ();
                        begin
                          WorldSyn.reset ();
                          begin
                            Reduces.reset ();
                            begin
                              TabledSyn.reset ();
                              begin
                                FunSyn.labelReset ();
                                begin
                                  CompSyn.sProgReset ();
                                  begin
                                    CompSyn.detTableReset ();
                                    begin
                                      Compile.sProgReset ();
                                      begin
                                        ModSyn.reset ();
                                        begin
                                          CsManager.resetSolvers ();
                                          context := None
                                        end
                                      end
                                    end
                                  end
                                end
                              end
                            end
                          end
                        end
                      end
                    end
                  end
                end
              end
            end
          end
        end
      end

    let readDecl () =
      handleExceptions 0 "stdIn"
        (function
          | () ->
              ignore (ReconTerm.resetErrors "stdIn");
              let rec install s =
                install' (Timers.time Timers.parsing S.expose s)
              and install' = function
                | empty_ -> Abort
                | S.Cons ((beginSubsig, _), s') -> begin
                    ignore (installSubsig ("stdIn", s'));
                    Ok
                  end
                | S.Cons (decl, s') -> begin
                    install1 ("stdIn") decl;
                    Ok
                  end
              in
              install (Parser.parseStream TextIO.stdIn))
        ()

    let rec decl id =
      begin match Names.stringToQid id with
      | None -> begin
          msg (id ^ " is not a well-formed qualified identifier\n");
          Abort
        end
      | Some qid ->
          begin match Names.constLookup qid with
          | None -> begin
              msg
                (Names.qidToString (valOf (Names.constUndef qid))
                ^ " has not been declared\n");
              Abort
            end
          | Some cid -> decl' cid
          end
      end

    and decl' cid =
      let conDec = IntSyn.sgnLookup cid in
      msg (Print.conDecToString conDec ^ "\n");
      Ok

    module ModFile : sig
      type mfile

      val create : string -> mfile
      val fileName : mfile -> string
      val editName : (string -> string) -> mfile -> mfile
      val modified : mfile -> bool
      val makeModified : mfile -> unit
      val makeUnmodified : mfile -> unit
    end = struct
      type nonrec mfile = string * Time.time option ref

      let create file = (file, ref None)
      let fileName (file, _) = file
      let editName edit (file, mtime) = (edit file, mtime)

      let modified (_, a) = match a with
        | { contents = None } -> true
        | { contents = Some _ } -> false

      let makeModified (_, mtime) = mtime := None
      let makeUnmodified (_, mtime) = mtime := Some Time.zeroTime
    end

    module Config = struct
      type nonrec config = string * ModFile.mfile list

      let suffix = ref "cfg"

      let mkRel (prefix, path) =
        OS.Path.mkCanonical
          begin if OS.Path.isAbsolute path then path
          else OS.Path.concat (prefix, path)
          end

      let read config =
        let appendUniq (l1, l2) =
          let rec appendUniq' = function
            | x :: l2 ->
                begin if List.exists (function y -> x = y) l1 then
                  appendUniq' l2
                else x :: appendUniq' l2
                end
            | [] -> List.rev l1
          in
          List.rev (appendUniq' (List.rev l2))
        in
        let isConfig item =
          let suffix_size = String.size !suffix + 1 in
          let suffix_start = String.size item - suffix_size in
          suffix_start >= 0
          && String.substring (item, suffix_start, suffix_size) = "." ^ !suffix
        in
        let fromUnixPath path =
          let vol = OS.Path.getVolume config in
          let isAbs = String.isPrefix "/" path in
          let arcs = String.tokens (function c -> c = '/') path in
          OS.Path.toString { isAbs; vol; arcs }
        in
        let rec read' (sources, configs) config =
          withOpenIn config (function instream ->
              let configDir = OS.Path.dir config in
              let parseItem (sources, configs) item =
                begin if isConfig item then
                  begin if
                    List.exists (function config' -> item = config') configs
                  then (sources, configs)
                  else read' (sources, item :: configs) item
                  end
                else
                  begin if
                    List.exists (function source' -> item = source') sources
                  then (sources, configs)
                  else (sources @ [ item ], configs)
                  end
                end
              in
              let rec parseLine (sources, configs) line =
                begin if Substring.isEmpty line then (sources, configs)
                else
                  let line' = Substring.dropl Char.isSpace line in
                  parseLine' (sources, configs) line'
                end
              and parseLine' (sources, configs) line =
                begin if Substring.isEmpty line || Substring.sub (line, 0) = '%'
                then parseStream (sources, configs)
                else
                  let line' =
                    Substring.string
                      (Substring.takel (fun x -> not (Char.isSpace x)) line)
                  in
                  let item = mkRel (configDir, fromUnixPath line') in
                  parseStream (parseItem (sources, configs) item)
                end
              and parseStream (sources, configs) =
                let line =
                  Substring.full
                    (match TextIO.inputLine instream with
                    | Some s -> s
                    | None -> "")
                in
                parseLine (sources, configs) line
              in
              parseStream (sources, configs))
        in
        let pwdir = OS.FileSys.getDir () in
        ( pwdir,
          List.map ModFile.create
            ((fun (r, _) -> r) (read' ([], [ config ]) config)) )

      let readWithout s c =
        let d, fs = read s in
        let d', fs' = c in
        let fns' = map (function m -> mkRel (d', ModFile.fileName m)) fs' in
        let redundant m =
          let n = mkRel (d, ModFile.fileName m) in
          List.exists (function n' -> n = n') fns'
        in
        (d, List.filter (fun x -> not (redundant x)) fs)

      let loadAbort (mfile, a) = match a with
        | Ok ->
            let status = loadFile (ModFile.fileName mfile) in
            begin match status with
            | Ok -> ModFile.makeUnmodified mfile
            | _ -> ()
            end;
            status
        | Abort -> Abort

      let rec load ((_, sources) as config) =
        begin
          reset ();
          begin
            List.app ModFile.makeModified sources;
            append config
          end
        end

      and append (pwdir, sources) =
        let rec fromFirstModified = function
          | [] -> []
          | x :: xs as sources ->
              begin if ModFile.modified x then sources else fromFirstModified xs
              end
        in
        let mkAbsolute p =
          (* (* Compat. *)  *)
          OS.Path.mkAbsolute { path = p; relativeTo = pwdir }
        in
        let sources' =
          begin if pwdir = OS.FileSys.getDir () then sources
          else List.map (ModFile.editName mkAbsolute) sources
          end
        in
        let sources'' = fromFirstModified sources' in
        List.foldl loadAbort Ok sources''

      let define sources =
        (OS.FileSys.getDir (), List.map ModFile.create sources)
    end

    let make fileName = Config.load (Config.read fileName)
  end

  (*! structure IntSyn = IntSyn' !*)
  (* result of a computation *)
  (* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)
  (* withOpenIn fileName (fn instream => body) = x
       opens fileName for input to obtain instream and evaluates body.
       The file is closed during normal and abnormal exit of body.
    *)
  (* evarInstToString Xs = msg
       formats instantiated EVars as a substitution.
       Abbreviate as empty string if chatter level is < 3.
    *)
  (* expToString (G, U) = msg
       formats expression as a string.
       Abbreviate as empty string if chatter level is < 3.
    *)
  (* status ::= OK | ABORT  is the return status of various operations *)
  (* should move to paths, or into the prover module... but not here! -cs *)
  (* val handleExceptions : int -> string -> ('a -> Status) -> 'a -> Status *)
  (* handleExceptions chlev filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued if chatter level is greater or equal to chlev.
       Unrecognized exceptions are re-raised.
    *)
  (* | Constraints.Error (cnstrL) => abortFileMsg (fileName, constraintsMsg cnstrL) *)
  (* Total includes filename *)
  (* Reduces includes filename *)
  (* ModeCheck includes filename *)
  (* - Not supported in polyML ABP - 4/20/03
              * | IO.Io (ioError) => abortIO (fileName, ioError)
              *)
  (* includes filename *)
  (* includes filename *)
  (* During elaboration of a signature expression, each constant
       that that the user declares is added to this Table.  At top level,
       however, the reference holds NONE (in particular, shadowing is
       allowed).
    *)
  (* installConDec fromCS (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
       Note: if fromCS = FromCS then the declaration comes from a Constraint
       Solver and some limitations on the types are lifted.
    *)
  (* (Clause, _) should be impossible *)
  (* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
  (* (Clause, _) should be impossible *)
  (* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
  (* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)
  (* Constant declarations c : V, c : V = U plus variations *)
  (* allocate new cid. *)
  (* allocate new cid. *)
  (* names are assigned in ReconConDec *)
  (* val conDec' = nameConDec (conDec) *)
  (* should print here, not in ReconConDec *)
  (* allocate new cid after checking modes! *)
  (* anonymous definition for type-checking *)
  (* Abbreviations %abbrev c = U and %abbrev c : V = U *)
  (* names are assigned in ReconConDec *)
  (* val conDec' = nameConDec (conDec) *)
  (* should print here, not in ReconConDec *)
  (* allocate new cid after checking modes! *)
  (* anonymous definition for type-checking *)
  (* Clauses %clause c = U or %clause c : V = U or %clause c : V *)
  (* these are like definitions, but entered into the program table *)
  (* val _ = print ""%clause "" *)
  (* anonymous definition for type-checking: ignore %clause *)
  (* Solve declarations %solve c : A *)
  (* should print here, not in ReconQuery *)
  (* allocate new cid after checking modes! *)
  (* allocate cid after strictness has been checked! *)
  (* %query <expected> <try> A or %query <expected> <try> X : A *)
  (* Solve.query might raise Solve.AbortQuery (msg) *)
  (* %fquery <expected> <try> A or %fquery <expected> <try> X : A *)
  (* Solve.query might raise Fquery.AbortQuery (msg) *)
  (* %queryTabled <expected> <try> A or %query <expected> <try> X : A *)
  (* Solve.query might raise Solve.AbortQuery (msg) *)
  (* %trustme <decl> *)
  (* %subord (<qid> <qid>) ... *)
  (* %freeze <qid> ... *)
  (* Subordinate.installFrozen cids *)
  (* %thaw <qid> ... *)
  (* invalidate prior meta-theoretic properteis of signatures *)
  (* exempt only %mode [incremental], %covers [not stored] *)
  (* %deterministic <qid> ... *)
  (* %compile <qids> *)
  (* -ABP 4/4/03 *)
  (* MOVED -- ABP 4/4/03 *)
  (* ******************************************* *)
  (* ******************************************* *)
  (* Fixity declaration for operator precedence parsing *)
  (* Name preference declaration for printing *)
  (* Mode declaration *)
  (* exception comes with location *)
  (* Unique declaration *)
  (* convert all UniqueTable.Error to Unique.Error *)
  (* Timing added to coverage --- fix !!! -fp Sun Aug 17 12:17:51 2003 *)
  (* %unique does not auto-freeze, since family must already be frozen *)
  (* Coverage declaration *)
  (* MERGE Fri Aug 22 13:43:12 2003 -cs *)
  (* Total declaration *)
  (* time activities separately in Total.fun *)
  (* Mon Dec  2 17:20:18 2002 -fp *)
  (* coverage checker appears to be safe now *)
  (*
          val _ = if not (!Global.unsafe)
                    then raise Total.Error (Paths.wrapLoc (Paths.Loc (fileName, r), ""%total not safe: Toggle `unsafe' flag""))
                  else ()
          *)
  (* ******************************************* *)
  (*  Temporarily disabled -- cs Thu Oct 30 12:46:44 2003
          fun checkFreeOut nil = ()
            | checkFreeOut (a :: La) =
              let
                val SOME ms = ModeTable.modeLookup a
                val _ = ModeCheck.checkFreeOut (a, ms)
              in
                checkFreeOut La
              end
          val _ = checkFreeOut La
          val (lemma, projs, sels) = Converter.installPrg La


           ABP 2/28/03 -- factoring 
          val _ = if (!Global.chatter >= 4) then print (""[Factoring ..."") else ()
          val P = Redundant.convert (Tomega.lemmaDef lemma)
          val _ = if (!Global.chatter >= 4) then print (""]\n"") else ()

          val F = Converter.convertFor La

          val _ = if !Global.chatter >= 2
                    then print (TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (IntSyn.sgnLookup cid)) La,
                                                          projs), P) ^ ""\n"")
                  else ()

          val _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, F))

          val result1 = (TomegaCoverage.coverageCheckPrg (WorldSyn.lookup (hd La), IntSyn.Null, P); NONE)
                        handle TomegaCoverage.Error msg => SOME msg


      val result1 = NONE 

          fun covererror (SOME msg1, msg2) = raise Cover.Error (Paths.wrap (r, ""Functional and relational coverage checker report coverage error:\n[Functional] ""
                                                                            ^ msg1 ^ ""\n[Relational] "" ^ msg2))
            | covererror (NONE, msg2)      = raise Cover.Error (Paths.wrap (r, ""Functional coverage succeeds, relationals fails:\n[Relational] "" ^ msg2))

7 ******************************************* *)
  (* pre-install for recursive checking *)
  (* include region and file *)
  (*                     | Cover.Error (msg) => covererror (result1, msg)  disabled -cs Thu Jan 29 16:35:13 2004 *)
  (* includes filename *)
  (*        val _ = case (result1)
                    of NONE => ()
                     | SOME msg => raise Cover.Error (Paths.wrap (r, ""Relational coverage succeeds, funcational fails:\n This indicates a bug in the functional checker.\n[Functional] "" ^ msg))
*)
  (* %total does not auto-freeze, since the predicate must already be frozen *)
  (* Termination declaration *)
  (* allow re-declaration since safe? *)
  (* Thu Mar 10 13:45:42 2005 -fp *)
  (*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookup a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ "":""
                                       ^ Paths.wrap (r, ""Cannot redeclare termination order for frozen constant ""
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
  (* -bp *)
  (* Reduces declaration *)
  (* allow re-declaration since safe? *)
  (* Thu Mar 10 14:06:13 2005 -fp *)
  (*
          val _ = ListPair.app (fn ((a, _), r) =>
                            if Subordinate.frozen [a]
                              andalso ((Order.selLookupROrder a; true) handle Order.Error _ => false)
                            then raise Total.Error (fileName ^ "":""
                                       ^ Paths.wrap (r, ""Cannot redeclare reduction order for frozen constant ""
                                                   ^ Names.qidToString (Names.constQid a)))
                            else ())
                  (callpats, rs)
          *)
  (*  -bp6/12/99.   *)
  (* Tabled declaration *)
  (*  -bp6/12/99.   *)
  (* %keepTable declaration *)
  (* Theorem declaration *)
  (* Prove declaration *)
  (* La is the list of type constants *)
  (* mode must be declared!*)
  (* times itself *)
  (* Establish declaration *)
  (* La is the list of type constants *)
  (* mode must be declared!*)
  (* times itself *)
  (* Assert declaration *)
  (* La is the list of type constants *)
  (* mode must be declared!*)
  (* error location inaccurate here *)
  (*if !Global.doubleCheck
             then (map (fn (a,_) => Worldify.worldify a) cpa; ())
           else  ()  --cs Sat Aug 27 22:04:29 2005 *)
  (* Signature declaration *)
  (* FIX: should probably time this -kw *)
  (* anonymous *)
  (* Structure declaration *)
  (* anonymous *)
  (* anonymous *)
  (* Include declaration *)
  (* Open declaration *)
  (* val _ = ModeTable.resetFrom mark *)
  (* val _ = Total.resetFrom mark *)
  (* val _ = Subordinate.resetFrom mark  ouch!  *)
  (* val _ = Reduces.resetFrom mark *)
  (* Origins, CompSyn, FunSyn harmless? -kw *)
  (* val _ = IntSyn.resetFrom (mark, markStruct)
             FIX: DON'T eliminate out-of-scope cids for now -kw *)
  (* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
  (* Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) *)
  (* now done in installConDec *)
  (* loadString (str) = status
       reads and processes declarations from str, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
  (* Interactive Query Top Level *)
  (* ""stdIn"" as fake fileName *)
  (* top () = () starts interactive query loop *)
  (* put a more reasonable region here? -kw *)
  (* reset () = () clears all global tables, including the signature *)
  (* -fp Wed Mar  9 20:24:45 2005 *)
  (* -fp *)
  (* -fp *)
  (* -bp *)
  (* -bp *)
  (* necessary? -fp; yes - bp*)
  (*  -bp *)
  (* resetting substitution trees *)
  (* decl (id) = () prints declaration of constant id *)
  (* val fixity = Names.getFixity (cid) *)
  (* can't get name preference right now *)
  (* val mode = ModeTable.modeLookup (cid) *)
  (* can't get termination declaration *)
  (* Support tracking file modification times for smart re-appending. *)
  (* config = [""fileName1"",...,""fileName<n>""] *)
  (* Files will be read in the order given! *)
  (* A configuration (pwdir, sources) consists of an absolute directory
         pwdir and a list of source file names (which are interpreted
         relative to pwdir) along with their modification times.
         pwdir will be the current working directory
         when a configuration is loaded, which may not be same as the
         directory in which the configuration file is located.

         This representation allows shorter file names in chatter and
         error messages.
      *)
  (* suffix of configuration files: ""cfg"" by default *)
  (* mkRel transforms a relative path into an absolute one
               by adding the specified prefix. If the path is already
               absolute, no prefix is added to it.
            *)
  (* more efficient recursive version  Sat 08/26/2002 -rv *)
  (* appendUniq (list1, list2) appends list2 to list1, removing all
               elements of list2 which are already in list1.
            *)
  (* isConfig (item) is true iff item has the suffix of a
               configuration file.
            *)
  (* fromUnixPath path transforms path (assumed to be in Unix form)
               to the local OS conventions.
            *)
  (* we have already read this one *)
  (* we have already collected this one *)
  (* end of file *)
  (* empty line *)
  (* comment *)
  (*
            handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
          *)
  (* Read a config file s but omit everything that is already in config c
         XXX: naive and inefficient implementation *)
  (* load (config) = Status
         resets the global signature and then reads the files in config
         in order, stopping at the first error.
      *)
  (* append (config) = Status
         reads the files in config in order, beginning at the first
         modified file, stopping at the first error.
      *)
  (* allow shorter messages if safe *)
  (* structure Config *)
  (* make (configFile)
       read and then load configuration from configFile
    *)

  (** re-exporting environment parameters and utilities defined elsewhere *)
  module Print : sig
    val implicit : bool ref

    val printInfix : bool ref
    (** false, print implicit args *)

    val depth : int option ref
    (** false, print fully explicit form infix when possible *)

    val length : int option ref
    (** NONE, limit print depth *)

    val indent : int ref
    (** NONE, limit argument length *)

    val width : int ref
    (** 3, indentation of subterms *)

    val noShadow : bool ref
    (** 80, line width *)

    val sgn : unit -> unit
    (** if true, don't print shadowed constants as ""%const%"" *)

    val prog : unit -> unit
    (** print signature *)

    val subord : unit -> unit
    (** print signature as program *)

    val def : unit -> unit
    (** print subordination relation *)

    val domains : unit -> unit
    (** print information about definitions *)

    (** print available constraint domains *)
    module TeX : sig
      val sgn : unit -> unit
      (** print in TeX format *)

      val prog : unit -> unit
      (** print signature *)
    end
  end = struct
    let implicit = Print.implicit
    let printInfix = Print.printInfix
    let depth = Print.printDepth
    let length = Print.printLength
    let indent = Print.Formatter.indent
    let width = Print.Formatter.pagewidth
    let noShadow = Print.noShadow
    let sgn () = Print.printSgn ()
    let prog () = ClausePrint.printSgn ()
    let subord () = Subordinate.show ()
    let def () = Subordinate.showDef ()
    let domains () = msg CSInstaller.version

    module TeX = struct
      let sgn () = printSgnTeX ()
      let prog () = printProgTeX ()
    end
  end

  (** print signature as program *)
  module Trace : sig
    type 'a spec = None | Some of 'a list | All

    (* trace specification: no tracing | list of clauses/families | trace all *)
    val trace : string spec -> unit

    val break : string spec -> unit
    (** clauses and families *)

    val detail : int ref
    (** clauses and families *)

    val show : unit -> unit
    (** 0 = none, 1 = default, 2 = unify *)

    val reset : unit -> unit
    (** show trace, break, and detail *)
  end =
    Trace

  (** reset trace, break, and detail *)
  module Timers : sig
    val show : unit -> unit

    val reset : unit -> unit
    (** show and reset timers *)

    val check : unit -> unit
    (** reset timers *)
  end =
    Timers

  (** display, but not no reset *)
  module OS : sig
    val chDir : string -> unit

    val getDir : unit -> string
    (** change working directory *)

    val exit : unit -> unit
    (** get working directory *)
  end = struct
    let chDir = OS.FileSys.chDir
    let getDir = OS.FileSys.getDir
    let exit () = OS.Process.exit OS.Process.success
  end

  (** exit Stelf and ML *)
  module Compile : sig
    type opt = CompSyn.opt = No | LinearHeads | Indexing

    val optimize : opt ref
  end = struct
    type opt = CompSyn.opt = No | LinearHeads | Indexing

    let optimize = CompSyn.optimize
  end

  module Recon : sig
    type traceMode = ReconTerm.traceMode = Progressive | Omniscient

    val trace : bool ref
    val traceMode : traceMode ref
  end = struct
    type traceMode = ReconTerm.traceMode = Progressive | Omniscient

    let trace = ReconTerm.trace
    let traceMode = ReconTerm.traceMode
  end

  module Prover : sig
    (** F=Filling, R=Recursion, S=Splitting *)
    type strategy = MetaGlobal.strategy = Rfs | Frs

    val strategy : strategy ref
    (** FRS or RFS *)

    val maxSplit : int ref
    (** FRS, strategy used for %prove *)

    val maxRecurse : int ref
    (** 2, bound on splitting *)
  end = struct
    type strategy = MetaGlobal.strategy = Rfs | Frs

    (** FRS or RFS *)
    let strategy = MetaGlobal.strategy

    let maxSplit = MetaGlobal.maxSplit
    let maxRecurse = MetaGlobal.maxRecurse
  end

  (** 10, bound on recursion *)
  let chatter : int ref = Global.chatter

  let doubleCheck : bool ref = Global.doubleCheck
  let unsafe : bool ref = Global.unsafe
  let autoFreeze : bool ref = Global.autoFreeze
  let timeLimit : Time.time option ref = Global.timeLimit
  let reset = reset
  let loadFile = loadFile
  let loadString = loadString
  let readDecl = readDecl
  let decl = decl
  let top = top
  let install1 = install1

  module Config : sig
    type config

    val suffix : string ref
    (** configuration *)

    val read : string -> config
    (** suffix of configuration files *)

    val readWithout : string -> config -> config
    (** read configuration from config file *)

    val load : config -> status
    (** read config file, minus contents of another *)

    val append : config -> status
    (** reset and load configuration *)

    val define : string list -> config
    (** load configuration (w/o reset) *)
  end =
    Config

  (** explicitly define configuration *)
  let make = make

  let version = Version.version_string

  module Table : sig
    type strategy = TableParam.strategy = Variant | Subsumption

    val strategy : strategy ref
    val strengthen : bool ref
    val resetGlobalTable : unit -> unit
    val top : unit -> unit
  end = struct
    type strategy = TableParam.strategy = Variant | Subsumption

    let strategy = TableParam.strategy
    let strengthen = TableParam.strengthen
    let resetGlobalTable = TableParam.resetGlobalTable

    (** top () = () starts interactive query loop *)
    let top () =
      let sLoopT () =
        begin if Solve.qLoopT () then Ok else Abort
        end
      in
      let rec topLoopT () =
        begin match handleExceptions 0 "stdIn" sLoopT () with
        | Abort -> topLoopT ()
        | Ok -> ()
        end
        (* ""stdIn"" as fake fileName *)
      in
      topLoopT ()
  end
end
(* local *)
(* functor Stelf *)

(* # 1 "src/frontend/Twelf_.sml.ml" *)
