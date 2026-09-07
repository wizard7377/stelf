open! Timing
open! Global.Global_
open! Tabling
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Print
open! Print.Print_
open! Typecheck.Typecheck_
open! Style
open! Modes
open! Terminate
open! Index
open! Thm
open! M2
open! Compile
open! Opsem
open! Subordinate
open! Modules
open! Solvers
open! Solvers.Solvers_
open! Worldcheck.Worldcheck_
open! Unique
open! Cover
open! Tomega_lib
open! Prover
open! Msg

module type STELF = TWELF.STELF

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
  module Parser : PARSER.PARSER with module Names = Names

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
  module Solve : SOLVE.SOLVE with module ExtQuery = Parser.ExtQuery

  (*! sharing Solve.IntSyn = IntSyn' !*)
  module Fquery : FQUERY.FQUERY with module ExtQuery = Parser.ExtQuery

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
  module CSInstaller : SOLVERS.CS_INSTALLER

  (* module Compat : COMPAT *)
  module UnknownExn : UNKNOWNEXN.UNKNOWN_EXN
  module Msg : MSG.MSG
end) : TWELF.STELF
