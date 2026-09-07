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

(* # 1 "src/frontend/ParseFixity.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)
include PARSEFIXITY
(* signature PARSE_FIXITY *)

(* # 1 "src/frontend/ParseFixity.fun.ml" *)
open! Parsing
open! Basis

(* Parsing Fixity and Name Preference Declarations *)
(* Author: Frank Pfenning *)
module ParseFixity (ParseFixity__0 : sig
  module Names' : NAMES
end) : PARSE_FIXITY with module Names = ParseFixity__0.Names' = struct
  (*! structure Parsing = Parsing' !*)
  module Names = ParseFixity__0.Names'

  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream
    module FX = Names.Fixity

    let fixToString (FX.Strength p) = Int.toString p

    let idToPrec (r, (_, name)) =
      let prec =
        try FX.Strength (L.stringToNat name) with
        | Overflow -> Parsing.error r ("Precedence too large")
        | L.NotDigit _ -> Parsing.error r ("Precedence not a natural number")
      in
      begin if FX.less prec FX.minPrec || FX.less FX.maxPrec prec then
        Parsing.error
          r (((("Precedence out of range [" ^ fixToString FX.minPrec) ^ ",")
            ^ fixToString FX.maxPrec)
            ^ "]")
      else prec
      end

    let parseFixCon (fixity, a) = match a with
      | LS.Cons ((L.Id (_, name), r), s') ->
          (((Names.Qid ([], name), r), fixity), LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            r ("Expected identifier to assign fixity, found " ^ L.toString t)

    let parseFixPrec (fixity, a) = match a with
      | LS.Cons ((L.Id (id_case, name), r), s') ->
          parseFixCon (fixity (idToPrec (r, (id_case, name))), LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error r ("Expected precedence, found " ^ L.toString t)

    let parseInfix = function
      | LS.Cons ((L.Id (L.Lower, "none"), r), s') ->
          parseFixPrec ((fun p -> FX.Infix (p, FX.None)), LS.expose s')
      | LS.Cons ((L.Id (L.Lower, "left"), r), s') ->
          parseFixPrec ((fun p -> FX.Infix (p, FX.Left)), LS.expose s')
      | LS.Cons ((L.Id (L.Lower, "right"), r), s') ->
          parseFixPrec ((fun p -> FX.Infix (p, FX.Right)), LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            r ("Expected associatitivy `left', `right', or `none', found "
              ^ L.toString t)

    let parsePrefix f = parseFixPrec ((fun p -> FX.Prefix p), f)
    let parsePostfix f = parseFixPrec ((fun p -> FX.Postfix p), f)

    let parseFixity' = function
      | LS.Cons ((L.Infix, r), s') -> parseInfix (LS.expose s')
      | LS.Cons ((L.Prefix, r), s') -> parsePrefix (LS.expose s')
      | LS.Cons ((L.Postfix, r), s') -> parsePostfix (LS.expose s')

    let parseFixity s = parseFixity' (LS.expose s)

    let rec parseName5 (name, r0, prefENames, prefUNames, a) = match a with
      | LS.Cons ((L.Id (_, prefUName), r), s')
        ->
          parseName5
            (name, r0, prefENames, prefUNames @ [ prefUName ], LS.expose s')
      | LS.Cons ((L.Rparen, r), s') ->
          (((Names.Qid ([], name), r0), (prefENames, prefUNames)), LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error r
            ("Expected name preference or ')', found " ^ L.toString t)

    let parseName3 (name, r0, prefEName, f) = match f with
      | LS.Cons ((L.Id (_, prefUName), r), s') ->
          ( ((Names.Qid ([], name), r0), (prefEName, [ prefUName ])),
            LS.expose s' )
      | LS.Cons ((L.Lparen, r), s') ->
          parseName5 (name, r0, prefEName, [], LS.expose s')
      | f ->
          (((Names.Qid ([], name), r0), (prefEName, [])), f)

    let rec parseName4 (name, r0, prefENames, a) = match a with
      | LS.Cons ((L.Id (_, prefEName), r), s') ->
          begin if L.isUpper prefEName then
            parseName4 (name, r0, prefENames @ [ prefEName ], LS.expose s')
          else
            Parsing.error r ("Expected uppercase identifer, found " ^ prefEName)
          end
      | LS.Cons ((L.Rparen, r), s') ->
          parseName3 (name, r0, prefENames, LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error r
            ("Expected name preference or ')', found " ^ L.toString t)

    let parseName2 (name, r0, a) = match a with
      | LS.Cons ((L.Id (_, prefEName), r), s') ->
          begin if L.isUpper prefEName then
            parseName3 (name, r0, [ prefEName ], LS.expose s')
          else
            Parsing.error r ("Expected uppercase identifer, found " ^ prefEName)
          end
      | LS.Cons ((L.Lparen, r), s') ->
          parseName4 (name, r0, [], LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error r ("Expected name preference, found " ^ L.toString t)

    let parseName1 = function
      | LS.Cons ((L.Id (_, name), r), s') -> parseName2 (name, r, LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            r ("Expected identifer to assign name preference, found "
              ^ L.toString t)

    let parseNamePref' (LS.Cons ((L.Name, r), s')) = parseName1 (LS.expose s')
    let parseNamePref s = parseNamePref' (LS.expose s)
  end

  (* some shorthands *)
  (* idToPrec (region, (idCase, name)) = n
       where n is the precedence indicated by name, which should consists
       of all digits.  Raises error otherwise, or if precedence it too large
    *)
  (*-----------------------------*)
  (* Parsing fixity declarations *)
  (*-----------------------------*)
  (* parseFixCon ""id"" *)
  (* parseFixPrec ""n id"" where n is precedence *)
  (* parseInfix ""none|left|right n id"" where n is precedence *)
  (* parsePrefix ""n id"" where n is precedence *)
  (* parsePostfix ""n id"" where n is precedence *)
  (* parseFixity' : lexResult stream -> (name,fixity) * lexResult stream
       Invariant: token stream starts with %infix, %prefix or %postfix
    *)
  (* anything else should be impossible *)
  (*------------------------------------*)
  (* Parsing name preferences %name ... *)
  (*------------------------------------*)
  (* parseName5 ""string ... )"" or "")"" *)
  (* prefUName should be lower case---not enforced *)
  (* parseName3 ""string"" or """" *)
  (* prefUName should be lower case---not enforced *)
  (* parseName4 ""string ... )"" or "")"" *)
  (* parseName2 ""string"" or ""string string""
              or ""(string ... ) string""  or "" string (string ...)""
              or ""(string ... ) (string ...)"" *)
  (* parseName1 ""id string"" or ""id string string"" *)
  (* parseNamePref' ""%name id string"" or ""%name id string string""
       Invariant: token stream starts with %name
    *)
  let parseFixity' = parseFixity'
  let parseNamePref' = parseNamePref'
end
(*! structure Parsing' : PARSING !*)
(* local ... in *)
(* functor ParseFixity *)

(* # 1 "src/frontend/ParseFixity.sml.ml" *)
