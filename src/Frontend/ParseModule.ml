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

(* # 1 "src/frontend/ParseModule.sig.ml" *)
open! Basis
open! Parsing

(* Parsing modules *)
(* Author: Kevin Watkins *)
include PARSEMODULE

(* # 1 "src/frontend/ParseModule.fun.ml" *)
open! Parsing
open! Basis

module ParseModule (ParseModule__0 : sig
  (* Parsing modules *)
  (* Author: Kevin Watkins *)
  (*! structure Paths : PATHS !*)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ModExtSyn' : RECONMODULE.MODEXTSYN

  (*! sharing ModExtSyn'.Paths = Paths !*)
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ModExtSyn'.ExtSyn
end) : PARSE_MODULE with module ModExtSyn = ParseModule__0.ModExtSyn' = struct
  (*! structure Parsing = Parsing' !*)
  module ModExtSyn = ParseModule__0.ModExtSyn'
  module ParseTerm = ParseModule__0.ParseTerm
  module L = Lexer
  module LS = Parsing.Stream
  module E = ModExtSyn

  let parseStructExp' = function
    | LS.Cons ((L.Id _, r0), _) as f ->
        let (ids, (L.Id (_, id), r1)), f' = ParseTerm.parseQualId' f in
        (E.strexp ids id (Paths.join r0 r1), f')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          r ("Expected structure identifier, found token " ^ L.toString t)

  let parseColonEqual' = function
    | LS.Cons ((L.Colon, r1), s') ->
        begin match LS.expose s' with
        | LS.Cons ((L.Equal, _), s'') -> ((), LS.expose s'')
        | LS.Cons ((t, r2), s'') ->
            Parsing.error r2 ("Expected `=', found token " ^ L.toString t)
        end
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected `:=', found token " ^ L.toString t)

  let parseDot' = function
    | LS.Cons ((L.Dot, r), s') -> (r, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected `.', found token " ^ L.toString t)

  let parseConInst' = function
    | LS.Cons ((L.Id _, r0), _) as f ->
        let (ids, (L.Id (_, id), r1)), f1 = ParseTerm.parseQualId' f in
        let _, f2 = parseColonEqual' f1 in
        let tm, f3 = ParseTerm.parseTerm' f2 in
        let r2, f4 = parseDot' f3 in
        (E.coninst ids id (Paths.join r0 r1) tm (Paths.join r0 r2), f4)
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected identifier, found token " ^ L.toString t)

  let parseStrInst2' (r0, a) = match a with
    | (LS.Cons ((L.Id _, r1), _) as f) ->
        let (ids, (L.Id (_, id), r2)), f1 = ParseTerm.parseQualId' f in
        let _, f2 = parseColonEqual' f1 in
        let strexp, f3 = parseStructExp' f2 in
        let r3, f4 = parseDot' f3 in
        ( E.strinst ids id (Paths.join r1 r2) strexp (Paths.join r0 r3),
          f4 )
    | LS.Cons ((t, r), s') ->
        Parsing.error
          r ("Expected structure identifier, found token " ^ L.toString t)

  let parseStrInst' = function
    | LS.Cons ((L.Struct, r), s') -> parseStrInst2' (r, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected `%struct', found token " ^ L.toString t)

  let rec parseInsts' = function
    | LS.Cons ((L.Id _, _), _) as f ->
        let inst, f' = parseConInst' f in
        let insts, f'' = parseInsts' f' in
        (inst :: insts, f'')
    | LS.Cons ((L.Struct, _), _) as f ->
        let inst, f' = parseStrInst' f in
        let insts, f'' = parseInsts' f' in
        (inst :: insts, f'')
    | LS.Cons ((L.Rbrace, _), s') -> ([], LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          r ("Expected identifier or `%struct', found token " ^ L.toString t)

  let parseInstantiate' = function
    | LS.Cons ((L.Lbrace, _), s') as f -> parseInsts' (LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected `{', found token " ^ L.toString t)

  let rec parseWhereClauses' (a, sigexp) = match a with
    | (LS.Cons ((L.Where, _), s') as f) ->
        let insts, f' = parseInstantiate' (LS.expose s') in
        parseWhereClauses' (f', E.wheresig sigexp insts)
    | f -> (sigexp, f)

  let parseSigExp' = function
    | LS.Cons ((L.Id (_, id), r), s) ->
        let sigexp, f' = parseWhereClauses' (LS.expose s, E.sigid id r) in
        (Parsing.Done sigexp, f')
    | LS.Cons ((L.Lbrace, r), _) as f ->
        ( Parsing.Continuation
            (function
            | f' ->
                let sigexp, f'' = parseWhereClauses' (f', E.thesig) in
                (Parsing.Done sigexp, f'')),
          f )
    | LS.Cons ((t, r), _) ->
        Parsing.error
          r ("Expected signature name or expression, found token " ^ L.toString t)

  let parseSgEqual' (idOpt, a) = match a with
    | LS.Cons ((L.Equal, r), s') ->
        Parsing.recwith
          parseSigExp' (function sigexp -> E.sigdef idOpt sigexp)
          (LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected `=', found token " ^ L.toString t)

  let parseSgDef' = function
    | LS.Cons ((L.Id (_, id), r), s') -> parseSgEqual' (Some id, LS.expose s')
    | LS.Cons ((L.Underscore, r), s') -> parseSgEqual' (None, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          r ("Expected signature identifier, found token " ^ L.toString t)

  let parseSigDef' (LS.Cons ((L.Sig, r), s')) = parseSgDef' (LS.expose s')

  let parseStrDec2' (idOpt, a) = match a with
    | LS.Cons ((L.Colon, r), s') ->
        Parsing.recwith
          parseSigExp' (function sigexp -> E.structdec idOpt sigexp)
          (LS.expose s')
    | LS.Cons ((L.Equal, r), s') ->
        let strexp, f' = parseStructExp' (LS.expose s') in
        (Parsing.Done (E.structdef idOpt strexp), f')
    | LS.Cons ((t, r), s') ->
        Parsing.error r ("Expected `:' or `=', found token " ^ L.toString t)

  let parseStrDec' = function
    | LS.Cons ((L.Id (_, id), r), s') -> parseStrDec2' (Some id, LS.expose s')
    | LS.Cons ((L.Underscore, r), s') -> parseStrDec2' (None, LS.expose s')
    | LS.Cons ((t, r), s') ->
        Parsing.error
          r ("Expected structure identifier, found token " ^ L.toString t)

  let parseStructDec' (LS.Cons ((L.Struct, r), s')) =
    parseStrDec' (LS.expose s')

  let parseInclude' (LS.Cons ((L.Include, r), s')) = parseSigExp' (LS.expose s')
  let parseOpen' (LS.Cons ((L.Open, r), s')) = parseStructExp' (LS.expose s')
end
(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)

(* # 1 "src/frontend/ParseModule.sml.ml" *)
