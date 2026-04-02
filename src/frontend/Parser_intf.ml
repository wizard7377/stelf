(* # 1 "src/frontend/Parser.sig.ml" *)
open! Basis

(* Top-Level Parser *)
(* Author: Frank Pfenning *)

module type PARSER = sig
  (*! structure Parsing : PARSING !*)
  module Stream : STREAM
  module ExtSyn : ReconTerm_intf.EXTSYN
  module Names : NAMES
  module ExtConDec : ReconCondec_intf.EXTCONDEC
  module ExtQuery : ReconQuery_intf.EXTQUERY
  module ExtModes : ReconMode_intf.EXTMODES
  module ThmExtSyn : ReconThm_intf.THMEXTSYN
  module ModExtSyn : ReconModule_intf.MODEXTSYN

  type fileParseResult =
    | ConDec of ExtConDec.condec
    | FixDec of (Names.qid * Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.qid * Paths.region) * (string list * string list)
    | ModeDec of ExtModes.modedec list
    | UniqueDec of ExtModes.modedec list
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl
    | TabledDec of ThmExtSyn.tableddecl
    | KeepTableDec of ThmExtSyn.keepTabledecl
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert_
    | Query of int option * int option * ExtQuery.query
    | FQuery of ExtQuery.query
    | Compile of Names.qid list
    | Querytabled of int option * int option * ExtQuery.query
    | Solve of ExtQuery.define list * ExtQuery.solve
    | AbbrevDec of ExtConDec.condec
    | TrustMe of fileParseResult * Paths.region
    | SubordDec of (Names.qid * Names.qid) list
    | FreezeDec of Names.qid list
    | ThawDec of Names.qid list
    | DeterministicDec of Names.qid list
    | ClauseDec of ExtConDec.condec
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig
    | EndSubsig
    | Use of string
  [@@deriving eq, ord, show]

  (* -fp 8/17/03 *)
  (* -bp *)
  (* expected, try, A *)
  (* A *)
  (* -ABP 4/4/03 *)
  (* expected, try, A *)
  (* -fp *)
  (* -gaw *)
  (* -rv *)
  (* -fp *)
  (* enter/leave a new context *)
  (* Further declarations to be added here *)
  val parseStream :
    TextIO.instream -> (fileParseResult * Paths.region) Stream.stream

  val parseTerminalQ : string * string -> ExtQuery.query Stream.stream
end
