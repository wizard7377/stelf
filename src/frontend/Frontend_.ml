(* # 1 "src/frontend/Frontend_.sig.ml" *)

(* # 1 "src/frontend/Frontend_.fun.ml" *)

(* # 1 "src/frontend/Frontend_.sml.ml" *)
open! Basis

(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Presently, we do not memoize the token stream returned *)
(* by the Lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
(* Now in Lexer.fun *)
(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)
(* Now in Parsing.fun *)
(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)
(* Re-export module type before Stelf name shadowing. *)
module type LEXER = Lexer.LEXER
module type STELF = Twelf_.STELF

module ReconTerm = ReconTerm.ReconTerm (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Thm_.ThmSyn.Names

  (*! structure Paths' = Paths !*)
  module Approx = Approx
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Abstract = Abstract
  module Print = Print

  (*! structure CsManager = CsManager !*)
  module StringTree = TableInstances.StringRedBlackTree
  module Msg = Msg
end)

module ReconConDec = ReconCondec.ReconConDec (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Abstract = Abstract

  (*! structure Paths' = Paths !*)
  module ReconTerm' = ReconTerm
  module Constraints = Constraints
  module Strict = Strict
  module TypeCheck = TypeCheck
  module Timers = Timers.Timers
  module Print = Print
  module Msg = Msg
end)

module ReconQuery = ReconQuery.ReconQuery (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Abstract = Abstract

  (*! structure Paths' = Paths !*)
  module ReconTerm' = ReconTerm
  module TypeCheck = TypeCheck
  module Strict = Strict
  module Timers = Timers.Timers
  module Print = Print
end)

module ReconMode = ReconMode.ReconMode (struct
  module Global = Global

  (*! structure ModeSyn' = ModeSyn !*)
  module Whnf = Whnf

  (*! structure Paths' = Paths !*)
  module Names = Names
  module ModePrint = ModePrint
  module ModeDec = ModeDec
  module ReconTerm' = ReconTerm
end)

module ThmSyn = Thmsyn.ThmSyn (struct
  module Abstract = Abstract
  module Whnf = Whnf
  module Paths' = Paths
  module Names' = Names
end)

module ThmPrint = Thmprint.ThmPrint (struct
  module ThmSyn' = ThmSyn
  module Formatter = Formatter
end)

module FrontendTabledSyn =
  Tabledsyn.MakeTabledSyn
    (Names)
    (TableInstances.IntRedBlackTree)
    (Index)

module Thm =
  Thm_.Make_Thm
    (Global)
    (ThmSyn)
    (FrontendTabledSyn)
    (ModeTable)
    (Order)
    (ThmPrint)

module ReconThm = ReconThm.ReconThm (struct
  module Global = Global
  module IntSyn = IntSyn
  module Abstract = Abstract
  module Constraints = Constraints

  (*! structure ModeSyn = ModeSyn !*)
  module Names = Names

  (*! structure Paths' = Paths !*)
  module ThmSyn' = ThmSyn
  module ReconTerm' = ReconTerm
  module Print = Print
end)

module ReconModule = ReconModule.ReconModule (struct
  module Global = Global
  module IntSyn = IntSyn

  (*! structure Paths' = Paths !*)
  module ReconTerm' = ReconTerm
  module ModSyn' = ModSyn
  module Names = ModSyn'.Names
  module IntTree = TableInstances.IntRedBlackTree
end)

module ParseTermFunctor = ParseTerm

module ParseTerm = ParseTermFunctor.ParseTerm (struct
  (*! structure Parsing' = Parsing !*)
  module ExtSyn' = ReconTerm
  module Names = Names
end)

module ParseTermConDec :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconConDec.ExtSyn =
ParseTermFunctor.ParseTerm (struct
  module ExtSyn' = ReconConDec.ExtSyn
  module Names = Names
end)

module ParseTermQuery :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconQuery.ExtSyn =
ParseTermFunctor.ParseTerm (struct
  module ExtSyn' = ReconQuery.ExtSyn
  module Names = Names
end)

module ParseTermMode :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconMode.ExtSyn =
ParseTermFunctor.ParseTerm (struct
  module ExtSyn' = ReconMode.ExtSyn
  module Names = Names
end)

module ParseTermThm :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconThm.ExtSyn =
ParseTermFunctor.ParseTerm (struct
  module ExtSyn' = ReconThm.ExtSyn
  module Names = Names
end)

module ParseTermModule :
  ParseTerm_intf.PARSE_TERM with module ExtSyn = ReconModule.ExtSyn =
ParseTermFunctor.ParseTerm (struct
  module ExtSyn' = ReconModule.ExtSyn
  module Names = Names
end)

module ParseConDec = ParseCondec.ParseConDec (struct
  (*! structure Parsing' = Parsing !*)
  module ExtConDec' = ReconConDec
  module ParseTerm = ParseTermConDec
end)

module ParseQuery = ParseQuery.ParseQuery (struct
  (*! structure Parsing' = Parsing !*)
  module ExtQuery' = ReconQuery
  module ParseTerm = ParseTermQuery
end)

module ParseFixity = ParseFixity.ParseFixity (struct
  (*! structure Parsing' = Parsing !*) module Names' = Names
end)

module ParseMode = ParseMode.ParseMode (struct
  (*! structure Parsing' = Parsing !*)
  module ExtModes' = ReconMode

  (*! structure Paths = Paths !*)
  module ParseTerm = ParseTermMode
end)

module ParseThm = ParseThm.ParseThm (struct
  (*! structure Parsing' = Parsing !*)
  module ThmExtSyn' = ReconThm
  module ParseTerm = ParseTermThm
end)

(*! structure Paths = Paths !*)
module ParseModule = ParseModule.ParseModule (struct
  (*! structure Parsing' = Parsing !*)
  module ModExtSyn' = ReconModule
  module ParseTerm = ParseTermModule
end)

(*! structure Paths = Paths !*)
module Parser = Parser.Parser (struct
  (*! structure Parsing' = Parsing !*)
  module Stream' = Stream
  module ExtSyn' = ParseTerm.ExtSyn
  module Names' = Names
  module ExtConDec' = ReconConDec
  module ExtQuery' = ReconQuery
  module ExtModes' = ReconMode
  module ThmExtSyn' = ReconThm
  module ModExtSyn' = ReconModule
  module ParseConDec = ParseConDec
  module ParseQuery = ParseQuery
  module ParseFixity = ParseFixity
  module ParseMode = ParseMode
  module ParseThm = ParseThm
  module ParseModule = ParseModule
  module ParseTerm = ParseTerm
end)

module Solve = Solve.Solve (struct
  module Global = Global

  (*! structure IntSyn' = IntSyn !*)
  module Names = Names
  module Parser = Parser
  module ReconQuery = ReconQuery
  module Timers = Timers.Timers

  (*! structure CompSyn = CompSyn !*)
  module Compile = Compile
  module CPrint = CPrint

  (*! structure CsManager = CsManager !*)
  module AbsMachine = SwMachine
  module PtRecon = PtRecon
  module AbsMachineSbt = AbsMachineSbt

  (*! structure TableParam = TableParam !*)
  module Tabled = Tabled_

  (*	 structure TableIndex = TableIndex *)
  (*	 structure MemoTable = MemoTable *)
  module Print = Print
  module Msg = Msg
end)

module Fquery = Fquery.Fquery (struct
  module Global = Global
  module Names = Names
  module ReconQuery = ReconQuery
  module Timers = Timers.Timers
  module Print = Print
end)

module Stelf = Twelf_.Stelf (struct
  module Global = Global
  module Timers = Timers.Timers

  (*! structure IntSyn' = IntSyn !*)
  module Whnf = Whnf
  module Print = Print
  module Names = Names

  (*! structure Paths = Paths !*)
  module Origins = Origins
  module Lexer = Lexer.Lexer

  (*! structure Parsing = Parsing !*)
  module Parser = Parser
  module TypeCheck = TypeCheck
  module Strict = Strict
  module Constraints = Constraints
  module Abstract = Abstract
  module ReconTerm = ReconTerm
  module ReconConDec = ReconConDec
  module ReconQuery = ReconQuery
  module ModeTable = ModeTable
  module ModeCheck = ModeCheck
  module ModeDec = ModeDec
  module ReconMode = ReconMode
  module ModePrint = ModePrint
  module Unique = Unique
  module UniqueTable = UniqueTable
  module Cover = Cover
  module Converter = Converter
  module TomegaPrint = TomegaPrint
  module TomegaCoverage = TomegaCoverage
  module TomegaTypeCheck = TomegaTypeCheck
  module Total = Total
  module Reduces = Reduces
  module Index = Index
  module IndexSkolem = IndexSkolem
  module Subordinate = Subordinate.Subordinate_.Subordinate

  (*! structure CompSyn' = CompSyn !*)
  module Compile = Compile
  module CPrint = CPrint
  module AbsMachine = SwMachine

  (*! structure TableParam = TableParam !*)
  module Tabled = Tabled_
  module Solve = Solve
  module Fquery = Fquery
  module StyleCheck = StyleCheck
  module ThmSyn = ThmSyn
  module Thm = Thm
  module ReconThm = ReconThm
  module ThmPrint = ThmPrint
  module TabledSyn = FrontendTabledSyn
  module WorldSyn = WorldSyn

  (*	 structure WorldPrint = WorldPrint *)
  module Worldify = Worldify
  module ModSyn = ModSyn
  module ReconModule = ReconModule
  module MetaGlobal = MetaGlobal.MetaGlobal

  (*! structure FunSyn = FunSyn !*)
  module Skolem = Skolem
  module Prover = M2_.M2Prover
  module ClausePrint = ClausePrint
  module Trace = Trace
  module PrintTeX = PrintTeX
  module ClausePrintTeX = ClausePrintTeX
  module CsManager = CsManager
  module CSInstaller = CSInstaller

  (* unused -- creates necessary CM dependency *)
  module Compat = Compat
  module UnknownExn = UnknownexnSmlnj.UnknownExn
  module Msg = Msg
end)
