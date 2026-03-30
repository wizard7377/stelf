(* # 1 "src/frontend/frontend_.sig.ml" *)

(* # 1 "src/frontend/frontend_.fun.ml" *)

(* # 1 "src/frontend/frontend_.sml.ml" *)
open! Basis

(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
(* Now in lexer.fun *)
(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)
(* Now in parsing.fun *)
(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)
(* Re-export module type before Stelf name shadowing. *)
module type LEXER = Lexer.LEXER
module type STELF = Twelf_.STELF

module ReconTerm = Recon_term.ReconTerm (struct
  (*! structure IntSyn' = IntSyn !*)
  module Names = Names

  (*! structure Paths' = Paths !*)
  module Approx = Approx
  module Whnf = Whnf
  module Unify = UnifyTrail
  module Abstract = Abstract
  module Print = Print

  (*! structure Cs_manager = Cs_manager !*)
  module StringTree = Table_instances.StringRedBlackTree
  module Msg = Msg
end)

module ReconConDec = Recon_condec.ReconConDec (struct
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

module ReconQuery = Recon_query.ReconQuery (struct
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

module ReconMode = Recon_mode.ReconMode (struct
  module Global = Global

  (*! structure ModeSyn' = ModeSyn !*)
  module Whnf = Whnf

  (*! structure Paths' = Paths !*)
  module Names = Names
  module ModePrint = ModePrint
  module ModeDec = ModeDec
  module ReconTerm' = ReconTerm
end)

module ReconThm = Recon_thm.ReconThm (struct
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

module ReconModule = Recon_module.ReconModule (struct
  module Global = Global
  module IntSyn = IntSyn

  (*! structure Paths' = Paths !*)
  module ReconTerm' = ReconTerm
  module ModSyn' = ModSyn
  module Names = ModSyn'.Names
  module IntTree = Table_instances.IntRedBlackTree
end)

module ParseTerm = Parse_term.ParseTerm (struct
  (*! structure Parsing' = Parsing !*)
  module ExtSyn' = ReconTerm
  module Names = Names
end)

module ParseTermConDec :
  Parse_term.PARSE_TERM with module ExtSyn = ReconConDec.ExtSyn =
Parse_term.ParseTerm (struct
  module ExtSyn' = ReconConDec.ExtSyn
  module Names = Names
end)

module ParseTermQuery :
  Parse_term.PARSE_TERM with module ExtSyn = ReconQuery.ExtSyn =
Parse_term.ParseTerm (struct
  module ExtSyn' = ReconQuery.ExtSyn
  module Names = Names
end)

module ParseTermMode :
  Parse_term.PARSE_TERM with module ExtSyn = ReconMode.ExtSyn =
Parse_term.ParseTerm (struct
  module ExtSyn' = ReconMode.ExtSyn
  module Names = Names
end)

module ParseTermThm :
  Parse_term.PARSE_TERM with module ExtSyn = ReconThm.ExtSyn =
Parse_term.ParseTerm (struct
  module ExtSyn' = ReconThm.ExtSyn
  module Names = Names
end)

module ParseTermModule :
  Parse_term.PARSE_TERM with module ExtSyn = ReconModule.ExtSyn =
Parse_term.ParseTerm (struct
  module ExtSyn' = ReconModule.ExtSyn
  module Names = Names
end)

module ParseConDec = Parse_condec.ParseConDec (struct
  (*! structure Parsing' = Parsing !*)
  module ExtConDec' = ReconConDec
  module ParseTerm = ParseTermConDec
end)

module ParseQuery = Parse_query.ParseQuery (struct
  (*! structure Parsing' = Parsing !*)
  module ExtQuery' = ReconQuery
  module ParseTerm = ParseTermQuery
end)

module ParseFixity = Parse_fixity.ParseFixity (struct
  (*! structure Parsing' = Parsing !*) module Names' = Names
end)

module ParseMode = Parse_mode.ParseMode (struct
  (*! structure Parsing' = Parsing !*)
  module ExtModes' = ReconMode

  (*! structure Paths = Paths !*)
  module ParseTerm = ParseTermMode
end)

module ParseThm = Parse_thm.ParseThm (struct
  (*! structure Parsing' = Parsing !*)
  module ThmExtSyn' = ReconThm
  module ParseTerm = ParseTermThm
end)

(*! structure Paths = Paths !*)
module ParseModule = Parse_module.ParseModule (struct
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

  (*! structure Cs_manager = Cs_manager !*)
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
  module Subordinate = Subordinate

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
  module TabledSyn = TabledSyn
  module WorldSyn = WorldSyn

  (*	 structure WorldPrint = WorldPrint *)
  module Worldify = Worldify
  module ModSyn = ModSyn
  module ReconModule = ReconModule
  module MetaGlobal = Meta_global.MetaGlobal

  (*! structure FunSyn = FunSyn !*)
  module Skolem = Skolem
  module Prover = CombiProver
  module ClausePrint = ClausePrint
  module Trace = Trace
  module PrintTeX = PrintTeX
  module ClausePrintTeX = ClausePrintTeX
  module Cs_manager = Cs_manager
  module CSInstaller = CSInstaller

  (* unused -- creates necessary CM dependency *)
  module Compat = Compat
  module UnknownExn = Unknownexn_smlnj.UnknownExn
  module Msg = Msg
end)
