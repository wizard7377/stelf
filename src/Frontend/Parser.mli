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
include module type of PARSER

module Parser (Parser__0 : sig
  (*! structure Parsing' : PARSING !*)
  module Stream' : STREAM

  (* result stream *)
  module ExtSyn' : RECONTERM.EXTSYN

  (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
  module Names' : NAMES
  module ExtConDec' : RECONCONDEC.EXTCONDEC
  module ExtQuery' : RECONQUERY.EXTQUERY
  module ExtModes' : RECONMODE.EXTMODES
  module ThmExtSyn' : RECONTHM.THMEXTSYN
  module ModExtSyn' : RECONMODULE.MODEXTSYN

  module ParseConDec :
    PARSECONDEC.PARSE_CONDEC with module ExtConDec = ExtConDec'

  (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
  module ParseQuery : PARSEQUERY.PARSE_QUERY with module ExtQuery = ExtQuery'

  (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
  module ParseFixity : PARSEFIXITY.PARSE_FIXITY with module Names = Names'

  (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
  module ParseMode : PARSEMODE.PARSE_MODE with module ExtModes = ExtModes'

  (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
  module ParseThm : PARSETHM.PARSE_THM with module ThmExtSyn = ThmExtSyn'

  (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
  module ParseModule :
    PARSEMODULE.PARSE_MODULE with module ModExtSyn = ModExtSyn'

  (*! sharing ParseModule.Parsing = Parsing' !*)
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ExtSyn'
end) :
  PARSER
    with module ExtQuery = Parser__0.ExtQuery'
     and module Names = Parser__0.Names'
     and module ExtConDec = Parser__0.ExtConDec'
     and module ExtModes = Parser__0.ExtModes'
     and module ThmExtSyn = Parser__0.ThmExtSyn'
     and module ModExtSyn = Parser__0.ModExtSyn'
     and module Stream = Parser__0.Stream'
     and module ExtSyn = Parser__0.ExtSyn'
