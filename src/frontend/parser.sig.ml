open! Basis

(* Top-Level Parser *)
(* Author: Frank Pfenning *)
module type PARSER = sig
  (*! structure Parsing : PARSING !*)
  module Stream : STREAM
  module ExtSyn : EXTSYN
  module Names : NAMES
  module ExtConDec : EXTCONDEC
  module ExtQuery : EXTQUERY
  module ExtModes : EXTMODES
  module ThmExtSyn : THMEXTSYN
  module ModExtSyn : MODEXTSYN

  type fileParseResult =
    | ConDec of ExtConDec.condec
    | FixDec of (Names.qid_ * Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.qid_ * Paths.region) * (string list * string list)
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
    | Compile of Names.qid_ list
    | Querytabled of int option * int option * ExtQuery.query
    | Solve of ExtQuery.define list * ExtQuery.solve
    | AbbrevDec of ExtConDec.condec
    | TrustMe of fileParseResult * Paths.region
    | SubordDec of (Names.qid_ * Names.qid_) list
    | FreezeDec of Names.qid_ list
    | ThawDec of Names.qid_ list
    | DeterministicDec of Names.qid_ list
    | ClauseDec of ExtConDec.condec
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig
    | EndSubsig
    | Use of string

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
(* reads from std input *)
(* signature PARSER *)
