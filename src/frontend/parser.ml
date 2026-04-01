(* # 1 "src/frontend/parser.sig.ml" *)
open! Basis

(* Top-Level Parser *)
(* Author: Frank Pfenning *)
include Parser_intf
(* reads from std input *)
(* signature PARSER *)

(* # 1 "src/frontend/parser.fun.ml" *)
open! Parsing
open! Basis

(* Top-Level Parser *)
(* Author: Frank Pfenning *)
module Parser (Parser__0 : sig
  (*! structure Parsing' : PARSING !*)
  module Stream' : STREAM

  (* result stream *)
  module ExtSyn' : Recon_term.EXTSYN

  (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
  module Names' : NAMES
  module ExtConDec' : Recon_condec.EXTCONDEC
  module ExtQuery' : Recon_query.EXTQUERY
  module ExtModes' : Recon_mode.EXTMODES
  module ThmExtSyn' : Recon_thm.THMEXTSYN
  module ModExtSyn' : Recon_module.MODEXTSYN

  module ParseConDec :
    Parse_condec.PARSE_CONDEC with module ExtConDec = ExtConDec'

  (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
  module ParseQuery : Parse_query.PARSE_QUERY with module ExtQuery = ExtQuery'

  (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
  module ParseFixity : Parse_fixity.PARSE_FIXITY with module Names = Names'

  (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
  module ParseMode : Parse_mode.PARSE_MODE with module ExtModes = ExtModes'

  (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
  module ParseThm : Parse_thm.PARSE_THM with module ThmExtSyn = ThmExtSyn'

  (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
  module ParseModule :
    Parse_module.PARSE_MODULE with module ModExtSyn = ModExtSyn'

  (*! sharing ParseModule.Parsing = Parsing' !*)
  module ParseTerm : Parse_term.PARSE_TERM with module ExtSyn = ExtSyn'
end) :
  PARSER
    with module ExtQuery = Parser__0.ExtQuery'
     and module Names = Parser__0.Names'
     and module ExtConDec = Parser__0.ExtConDec'
     and module ExtModes = Parser__0.ExtModes'
     and module ThmExtSyn = Parser__0.ThmExtSyn'
     and module ModExtSyn = Parser__0.ModExtSyn'
     and module Stream = Parser__0.Stream'
     and module ExtSyn = Parser__0.ExtSyn' = struct
  (*! structure Parsing = Parsing' !*)
  module Stream = Parser__0.Stream'
  module ExtSyn = Parser__0.ExtSyn'
  module Names = Parser__0.Names'

  module ExtConDec = struct
    include Parser__0.ExtConDec'

    let equal_condec _ _ = true
    let compare_condec _ _ = 0
    let pp_condec ppf _ = Format.pp_print_string ppf "<condec>"
  end

  module ExtQuery = struct
    include Parser__0.ExtQuery'

    let equal_query _ _ = true
    let compare_query _ _ = 0
    let pp_query ppf _ = Format.pp_print_string ppf "<query>"
    let equal_define _ _ = true
    let compare_define _ _ = 0
    let pp_define ppf _ = Format.pp_print_string ppf "<define>"
    let equal_solve _ _ = true
    let compare_solve _ _ = 0
    let pp_solve ppf _ = Format.pp_print_string ppf "<solve>"
  end

  module ExtModes = struct
    include Parser__0.ExtModes'

    let equal_modedec _ _ = true
    let compare_modedec _ _ = 0
    let pp_modedec ppf _ = Format.pp_print_string ppf "<modedec>"
  end

  module ThmExtSyn = struct
    include Parser__0.ThmExtSyn'

    let equal_tdecl _ _ = true
    let compare_tdecl _ _ = 0
    let pp_tdecl ppf _ = Format.pp_print_string ppf "<tdecl>"
    let equal_wdecl _ _ = true
    let compare_wdecl _ _ = 0
    let pp_wdecl ppf _ = Format.pp_print_string ppf "<wdecl>"
    let equal_rdecl _ _ = true
    let compare_rdecl _ _ = 0
    let pp_rdecl ppf _ = Format.pp_print_string ppf "<rdecl>"
    let equal_tableddecl _ _ = true
    let compare_tableddecl _ _ = 0
    let pp_tableddecl ppf _ = Format.pp_print_string ppf "<tableddecl>"
    let equal_keepTabledecl _ _ = true
    let compare_keepTabledecl _ _ = 0
    let pp_keepTabledecl ppf _ = Format.pp_print_string ppf "<keepTabledecl>"
    let equal_theoremdec _ _ = true
    let compare_theoremdec _ _ = 0
    let pp_theoremdec ppf _ = Format.pp_print_string ppf "<theoremdec>"
    let equal_prove _ _ = true
    let compare_prove _ _ = 0
    let pp_prove ppf _ = Format.pp_print_string ppf "<prove>"
    let equal_establish _ _ = true
    let compare_establish _ _ = 0
    let pp_establish ppf _ = Format.pp_print_string ppf "<establish>"
    let equal_assert_ _ _ = true
    let compare_assert_ _ _ = 0
    let pp_assert_ ppf _ = Format.pp_print_string ppf "<assert>"
  end

  module ModExtSyn = struct
    include Parser__0.ModExtSyn'

    let equal_strexp _ _ = true
    let compare_strexp _ _ = 0
    let pp_strexp ppf _ = Format.pp_print_string ppf "<strexp>"
    let equal_sigexp _ _ = true
    let compare_sigexp _ _ = 0
    let pp_sigexp ppf _ = Format.pp_print_string ppf "<sigexp>"
    let equal_sigdef _ _ = true
    let compare_sigdef _ _ = 0
    let pp_sigdef ppf _ = Format.pp_print_string ppf "<sigdef>"
    let equal_structdec _ _ = true
    let compare_structdec _ _ = 0
    let pp_structdec ppf _ = Format.pp_print_string ppf "<structdec>"
  end

  module ParseConDec = Parser__0.ParseConDec
  module ParseQuery = Parser__0.ParseQuery
  module ParseFixity = Parser__0.ParseFixity
  module ParseMode = Parser__0.ParseMode
  module ParseThm = Parser__0.ParseThm
  module ParseModule = Parser__0.ParseModule
  module ParseTerm = Parser__0.ParseTerm

  module Paths = struct
    include Paths

    let equal_region _ _ = true
    let compare_region _ _ = 0
    let pp_region ppf _ = Format.pp_print_string ppf "<region>"
  end

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
  (* expected, try, A *)
  (* -ABP 4/4/03 *)
  (* numSol, try, A *)
  (* -fp *)
  (* -gaw *)
  (* -rv *)
  (* -fp *)
  (* enter/leave a new context *)
  (* Further pragmas to be added later here *)
  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream

    let rec stripDot = function
      | LS.Cons ((L.Dot, r), s) -> s
      | LS.Cons ((L.Rparen, r), s) ->
          Parsing.error (r, "Unexpected right parenthesis")
      | LS.Cons ((L.Rbrace, r), s) -> Parsing.error (r, "Unexpected right brace")
      | LS.Cons ((L.Rbracket, r), s) ->
          Parsing.error (r, "Unexpected right bracket")
      | LS.Cons ((L.Eof, r), s) -> Parsing.error (r, "Unexpected end of file")
      | LS.Cons ((L.Equal, r), s) -> Parsing.error (r, "Unexpected `='")
      | LS.Cons ((t, r), s) ->
          Parsing.error (r, "Expected `.', found " ^ L.toString t)

    let rec parseBound' = function
      | LS.Cons ((L.Id (_, "*"), r), s') -> (None, s')
      | LS.Cons ((L.Id (_, name), r), s') -> (
          try (Some (L.stringToNat name), s') with
          | Overflow -> Parsing.error (r, "Bound too large")
          | L.NotDigit _ ->
              Parsing.error
                (r, ("Bound `" ^ name) ^ "' neither `*' nor a natural number"))
      | LS.Cons ((t, r), s') ->
          Parsing.error
            (r, "Expected bound `*' or natural number, found " ^ L.toString t)

    let rec recParse (s, recparser, theSigParser, sc) =
      Stream.delay (function () ->
          recParse' (LS.expose s, recparser, theSigParser, sc))

    and recParse' (f, recparser, theSigParser, sc) =
      begin match recparser f with
      | Parsing.Done x, f' -> sc (x, f')
      | Parsing.Continuation k, LS.Cons ((L.Lbrace, r1), s') ->
          let rec finish = function
            | LS.Cons ((L.Rbrace, r2), s'') ->
                Stream.Cons
                  ((EndSubsig, r2), recParse (s'', k, theSigParser, sc))
            | LS.Cons ((t, r), _) ->
                Parsing.error (r, "Expected `}', found " ^ L.toString t)
          in
          Stream.Cons ((BeginSubsig, r1), theSigParser (s', finish))
      | Parsing.Continuation _, LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected `{', found " ^ L.toString t)
      end

    let rec parseStream (s, sc) =
      Stream.delay (function () -> parseStream' (LS.expose s, sc))

    and parseStream' = function
      | (LS.Cons ((L.Id (idCase, name), r0), s') as f), sc ->
          parseConDec' (f, sc)
      | (LS.Cons ((L.Abbrev, r), s') as f), sc -> parseAbbrev' (f, sc)
      | (LS.Cons ((L.Underscore, r), s') as f), sc -> parseConDec' (f, sc)
      | (LS.Cons ((L.Infix, r), s') as f), sc -> parseFixity' (f, sc)
      | (LS.Cons ((L.Prefix, r), s') as f), sc -> parseFixity' (f, sc)
      | (LS.Cons ((L.Postfix, r), s') as f), sc -> parseFixity' (f, sc)
      | (LS.Cons ((L.Name, r1), s') as f), sc ->
          let namePref, (LS.Cons ((_, r2), _) as f') =
            ParseFixity.parseNamePref' f
          in
          let r = Paths.join (r1, r2) in
          let namePrefQid, namePrefStrings = namePref in
          Stream.Cons
            ( (NamePref (namePrefQid, namePrefStrings), r),
              parseStream (stripDot f', sc) )
      | (LS.Cons ((L.Define, r), s') as f), sc -> parseSolve' (f, sc)
      | (LS.Cons ((L.Solve, r), s') as f), sc -> parseSolve' (f, sc)
      | LS.Cons ((L.Query, r0), s'), sc ->
          let expected, s1 = parseBound' (LS.expose s') in
          let try_, s2 = parseBound' (LS.expose s1) in
          let query, (LS.Cons ((_, r'), _) as f3) =
            ParseQuery.parseQuery' (LS.expose s2)
          in
          let r = Paths.join (r0, r') in
          Stream.Cons
            ((Query (expected, try_, query), r), parseStream (stripDot f3, sc))
      | LS.Cons ((L.Fquery, r0), s'), sc ->
          let query, (LS.Cons ((_, r'), _) as f3) =
            ParseQuery.parseQuery' (LS.expose s')
          in
          let r = Paths.join (r0, r') in
          Stream.Cons ((FQuery query, r), parseStream (stripDot f3, sc))
      | LS.Cons ((L.Querytabled, r0), s'), sc ->
          let numSol, s1 = parseBound' (LS.expose s') in
          let try_, s2 = parseBound' (LS.expose s1) in
          let query, (LS.Cons ((_, r'), _) as f3) =
            ParseQuery.parseQuery' (LS.expose s2)
          in
          let r = Paths.join (r0, r') in
          Stream.Cons
            ( (Querytabled (numSol, try_, query), r),
              parseStream (stripDot f3, sc) )
      | (LS.Cons ((L.Mode, r), s') as f), sc -> parseMode' (f, sc)
      | (LS.Cons ((L.Unique, r), s') as f), sc -> parseUnique' (f, sc)
      | (LS.Cons ((L.Covers, r), s') as f), sc -> parseCovers' (f, sc)
      | (LS.Cons ((L.Total, r), s') as f), sc -> parseTotal' (f, sc)
      | (LS.Cons ((L.Terminates, r), s') as f), sc -> parseTerminates' (f, sc)
      | (LS.Cons ((L.Block, r), s') as f), sc -> parseConDec' (f, sc)
      | (LS.Cons ((L.Worlds, r), s') as f), sc -> parseWorlds' (f, sc)
      | (LS.Cons ((L.Reduces, r), s') as f), sc -> parseReduces' (f, sc)
      | (LS.Cons ((L.Tabled, r), s') as f), sc -> parseTabled' (f, sc)
      | (LS.Cons ((L.Keeptable, r), s') as f), sc -> parseKeepTable' (f, sc)
      | (LS.Cons ((L.Theorem, r), s') as f), sc -> parseTheorem' (f, sc)
      | (LS.Cons ((L.Prove, r), s') as f), sc -> parseProve' (f, sc)
      | (LS.Cons ((L.Establish, r), s') as f), sc -> parseEstablish' (f, sc)
      | (LS.Cons ((L.Assert, r), s') as f), sc -> parseAssert' (f, sc)
      | (LS.Cons ((L.Trustme, r), s') as f), sc -> parseTrustMe' (f, sc)
      | (LS.Cons ((L.Freeze, r), s') as f), sc -> parseFreeze' (f, sc)
      | (LS.Cons ((L.Subord, r), s') as f), sc -> parseSubord' (f, sc)
      | (LS.Cons ((L.Thaw, r), s') as f), sc -> parseThaw' (f, sc)
      | (LS.Cons ((L.Deterministic, r), s') as f), sc ->
          parseDeterministic' (f, sc)
      | (LS.Cons ((L.Compile, r), s') as f), sc -> parseCompile' (f, sc)
      | (LS.Cons ((L.Clause, r), s') as f), sc -> parseClause' (f, sc)
      | (LS.Cons ((L.Sig, r), s') as f), sc -> parseSigDef' (f, sc)
      | (LS.Cons ((L.Struct, r), s') as f), sc -> parseStructDec' (f, sc)
      | (LS.Cons ((L.Include, r), s') as f), sc -> parseInclude' (f, sc)
      | (LS.Cons ((L.Open, r), s') as f), sc -> parseOpen' (f, sc)
      | (LS.Cons ((L.Use, r), s') as f), sc -> parseUse' (LS.expose s', sc)
      | (LS.Cons ((L.Eof, _), _) as f), sc -> sc f
      | (LS.Cons ((L.Rbrace, _), _) as f), sc -> sc f
      | LS.Cons ((t, r), s'), sc ->
          Parsing.error
            ( r,
              "Expected constant name or pragma keyword, found " ^ L.toString t
            )

    and parseConDec' ((LS.Cons ((_, r0), _) as f), sc) =
      let conDec, (LS.Cons ((_, r'), _) as f') = ParseConDec.parseConDec' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((ConDec conDec, r), parseStream (stripDot f', sc))

    and parseAbbrev' ((LS.Cons ((_, r0), _) as f), sc) =
      let conDec, (LS.Cons ((_, r'), _) as f') = ParseConDec.parseAbbrev' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((AbbrevDec conDec, r), parseStream (stripDot f', sc))

    and parseClause' ((LS.Cons ((_, r0), _) as f), sc) =
      let conDec, (LS.Cons ((_, r'), _) as f') = ParseConDec.parseClause' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((ClauseDec conDec, r), parseStream (stripDot f', sc))

    and parseFixity' ((LS.Cons ((_, r0), _) as f), sc) =
      let fdec, (LS.Cons ((_, r'), _) as f') = ParseFixity.parseFixity' f in
      let r = Paths.join (r0, r') in
      let fixQid, fixity = fdec in
      Stream.Cons ((FixDec (fixQid, fixity), r), parseStream (stripDot f', sc))

    and parseSolve' ((LS.Cons ((_, r0), _) as f), sc) =
      let defnssolve, (LS.Cons ((_, r'), _) as f') = ParseQuery.parseSolve' f in
      let r = Paths.join (r0, r') in
      let defs, solve = defnssolve in
      Stream.Cons ((Solve (defs, solve), r), parseStream (stripDot f', sc))

    and parseMode' ((LS.Cons ((_, r0), _) as f), sc) =
      let mdecs, (LS.Cons ((_, r'), _) as f') = ParseMode.parseMode' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((ModeDec mdecs, r), parseStream (stripDot f', sc))

    and parseUnique' ((LS.Cons ((_, r0), _) as f), sc) =
      let mdecs, (LS.Cons ((_, r'), _) as f') = ParseMode.parseMode' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((UniqueDec mdecs, r), parseStream (stripDot f', sc))

    and parseCovers' ((LS.Cons ((_, r0), _) as f), sc) =
      let mdecs, (LS.Cons ((_, r'), _) as f') = ParseMode.parseMode' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((CoversDec mdecs, r), parseStream (stripDot f', sc))

    and parseTotal' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseTotal' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((TotalDec ldec, r), parseStream (stripDot f', sc))

    and parseTerminates' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseTerminates' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((TerminatesDec ldec, r), parseStream (stripDot f', sc))

    and parseReduces' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseReduces' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((ReducesDec ldec, r), parseStream (stripDot f', sc))

    and parseTabled' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseTabled' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((TabledDec ldec, r), parseStream (stripDot f', sc))

    and parseKeepTable' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseKeepTable' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((KeepTableDec ldec, r), parseStream (stripDot f', sc))

    and parseWorlds' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseWorlds' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((WorldDec ldec, r), parseStream (stripDot f', sc))

    and parseTheorem' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseTheoremDec' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((TheoremDec ldec, r), parseStream (stripDot f', sc))

    and parseProve' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseProve' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((ProveDec ldec, r), parseStream (stripDot f', sc))

    and parseEstablish' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseEstablish' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((EstablishDec ldec, r), parseStream (stripDot f', sc))

    and parseAssert' ((LS.Cons ((_, r0), _) as f), sc) =
      let ldec, (LS.Cons ((_, r'), _) as f') = ParseThm.parseAssert' f in
      let r = Paths.join (r0, r') in
      Stream.Cons ((AssertDec ldec, r), parseStream (stripDot f', sc))

    and parseTrustMe' ((LS.Cons ((_, r0), s) as f), sc) =
      let rec parseNextDec' = function
        | Stream.Cons ((dec, r), s') -> Stream.Cons ((TrustMe (dec, r), r0), s')
        | empty_ -> Parsing.error (r0, "No declaration after `%trustme'")
      in
      parseNextDec' (parseStream' (LS.expose s, sc))

    and parseSubord' ((LS.Cons ((_, r0), s) as f), sc) =
      let qidpairs, (LS.Cons ((_, r'), _) as f') =
        ParseTerm.parseSubord' (LS.expose s)
      in
      let r = Paths.join (r0, r') in
      let qidpairs =
        map
          (function
            | (ids1, name1), (ids2, name2) ->
                (Names.Qid (ids1, name1), Names.Qid (ids2, name2)))
          qidpairs
      in
      Stream.Cons ((SubordDec qidpairs, r), parseStream (stripDot f', sc))

    and parseFreeze' ((LS.Cons ((_, r0), s) as f), sc) =
      let qids, (LS.Cons ((_, r'), _) as f') =
        ParseTerm.parseFreeze' (LS.expose s)
      in
      let r = Paths.join (r0, r') in
      let qids = map (function ids, name -> Names.Qid (ids, name)) qids in
      Stream.Cons ((FreezeDec qids, r), parseStream (stripDot f', sc))

    and parseThaw' ((LS.Cons ((_, r0), s) as f), sc) =
      let qids, (LS.Cons ((_, r'), _) as f') =
        ParseTerm.parseThaw' (LS.expose s)
      in
      let r = Paths.join (r0, r') in
      let qids = map (function ids, name -> Names.Qid (ids, name)) qids in
      Stream.Cons ((ThawDec qids, r), parseStream (stripDot f', sc))

    and parseDeterministic' ((LS.Cons ((_, r0), s) as f), sc) =
      let qids, (LS.Cons ((_, r'), _) as f') =
        ParseTerm.parseDeterministic' (LS.expose s)
      in
      let r = Paths.join (r0, r') in
      let qids = map (function ids, name -> Names.Qid (ids, name)) qids in
      Stream.Cons ((DeterministicDec qids, r), parseStream (stripDot f', sc))

    and parseCompile' ((LS.Cons ((_, r0), s) as f), sc) =
      let qids, (LS.Cons ((_, r'), _) as f') =
        ParseTerm.parseCompile' (LS.expose s)
      in
      let r = Paths.join (r0, r') in
      let qids = map (function ids, name -> Names.Qid (ids, name)) qids in
      Stream.Cons ((Compile qids, r), parseStream (stripDot f', sc))

    and parseSigDef' ((LS.Cons ((_, r1), _) as f), sc) =
      let rec finish (sigdef, (LS.Cons ((_, r2), _) as f')) =
        Stream.Cons
          ((SigDef sigdef, Paths.join (r1, r2)), parseStream (stripDot f', sc))
      in
      recParse' (f, ParseModule.parseSigDef', parseStream, finish)

    and parseStructDec' ((LS.Cons ((_, r1), _) as f), sc) =
      let rec finish (structdec, (LS.Cons ((_, r2), _) as f')) =
        Stream.Cons
          ( (StructDec structdec, Paths.join (r1, r2)),
            parseStream (stripDot f', sc) )
      in
      recParse' (f, ParseModule.parseStructDec', parseStream, finish)

    and parseInclude' ((LS.Cons ((_, r1), _) as f), sc) =
      let rec finish (sigexp, (LS.Cons ((_, r2), _) as f')) =
        Stream.Cons
          ((Include sigexp, Paths.join (r1, r2)), parseStream (stripDot f', sc))
      in
      recParse' (f, ParseModule.parseInclude', parseStream, finish)

    and parseOpen' ((LS.Cons ((_, r1), _) as f), sc) =
      let strexp, (LS.Cons ((_, r2), _) as f') = ParseModule.parseOpen' f in
      Stream.Cons
        ((Open strexp, Paths.join (r1, r2)), parseStream (stripDot f', sc))

    and parseUse' = function
      | LS.Cons ((L.Id (_, name), r0), s), sc ->
          let (LS.Cons ((_, r'), _) as f) = LS.expose s in
          let r = Paths.join (r0, r') in
          Stream.Cons ((Use name, r), parseStream (stripDot f, sc))
      | LS.Cons ((_, r), _), sc ->
          Parsing.error (r, "Constraint solver name expected")

    let rec parseQ s = Stream.delay (function () -> parseQ' (LS.expose s))

    and parseQ' f =
      let query, f' = ParseQuery.parseQuery' f in
      Stream.Cons (query, parseQ (stripDot f'))

    let rec lexStreamToParsing s =
      LS.delay (function () ->
          (match L.Stream.expose s with
          | L.Stream.Empty -> LS.Empty
          | L.Stream.Cons (x, s') -> LS.Cons (x, lexStreamToParsing s')))

    let rec parseTLStream instream =
      let rec finish = function
        | LS.Cons ((L.Eof, r), s) -> Stream.Empty
        | LS.Cons ((L.Rbrace, r), s) -> Parsing.error (r, "Unmatched `}'")
      in
      parseStream (lexStreamToParsing (L.lexStream instream), finish)
  end

  (* Everything else should be impossible *)
  (*
    fun stripOptionalDot (LS.Cons ((L.DOT,r), s)) = s
      | stripOptionalDot f = LS.delay (fn () => f)
    *)
  (* pass parseStream as theSigParser in order to be able to use
       this function polymorphically in the definition of parseStream *)
  (* parseStream' : lexResult front -> fileParseResult front *)
  (* parseStream' switches between various specialized parsers *)
  (* -fp *)
  (* -cs *)
  (* -bp *)
  (* -bp *)
  (* -bp *)
  (* -rv *)
  (* -ABP 4/4/03 *)
  (* -fp *)
  (* ABP 4/4/03 *)
  let parseStream = parseTLStream

  let rec parseTerminalQ prompts =
    parseQ (lexStreamToParsing (L.lexTerminal prompts))
end
(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
(* local ... in *)
(* functor Parser *)

(* # 1 "src/frontend/parser.sml.ml" *)
