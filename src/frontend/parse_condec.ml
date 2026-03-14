(* # 1 "src/frontend/parse_condec.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Signature Entries *)
(* Author: Frank Pfenning *)
module type PARSE_CONDEC = sig
  (*! structure Parsing : PARSING !*)
  module ExtConDec : Recon_condec.EXTCONDEC

  val parseConDec' : ExtConDec.condec Parsing.parser
  val parseAbbrev' : ExtConDec.condec Parsing.parser
  val parseClause' : ExtConDec.condec Parsing.parser
end
(* signature PARSE_CONDEC *)

(* # 1 "src/frontend/parse_condec.fun.ml" *)
open! Parsing
open! Basis

(* Parsing Signature Entries *)
(* Author: Frank Pfenning *)
module ParseConDec (ParseConDec__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtConDec' : Recon_condec.EXTCONDEC

  module ParseTerm :
    Parse_term.PARSE_TERM with module ExtSyn = ExtConDec'.ExtSyn
end) : PARSE_CONDEC with module ExtConDec = ParseConDec__0.ExtConDec' = struct
  (*! structure Parsing = Parsing' !*)
  module ExtConDec = ParseConDec__0.ExtConDec'
  module ParseTerm = ParseConDec__0.ParseTerm

  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream

    let rec parseConDec3 (optName, optTm, s) =
      let tm', f' = ParseTerm.parseTerm' (LS.expose s) in
      (ExtConDec.condef (optName, tm', optTm), f')

    let rec parseConDec2 = function
      | optName, (tm, LS.Cons ((L.Equal, r), s')) ->
          parseConDec3 (optName, Some tm, s')
      | Some name, (tm, f) -> (ExtConDec.condec (name, tm), f)
      | None, (tm, LS.Cons ((t, r), s')) ->
          Parsing.error (r, "Illegal anonymous declared constant")

    let rec parseConDec1 = function
      | optName, LS.Cons ((L.Colon, r), s') ->
          parseConDec2 (optName, ParseTerm.parseTerm' (LS.expose s'))
      | optName, LS.Cons ((L.Equal, r), s') -> parseConDec3 (optName, None, s')
      | optName, LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)

    let rec parseBlock = function
      | LS.Cons ((L.Id (_, "block"), r), s') ->
          ParseTerm.parseCtx' (LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `block', found " ^ L.toString t)

    let rec parseSome = function
      | name, LS.Cons ((L.Id (_, "some"), r), s') ->
          let g1, f' = ParseTerm.parseCtx' (LS.expose s') in
          let g2, f'' = parseBlock f' in
          (ExtConDec.blockdec (name, g1, g2), f'')
      | name, (LS.Cons ((L.Id (_, "block"), r), s') as f) ->
          let g2, f' = parseBlock f in
          (ExtConDec.blockdec (name, [], g2), f')
      | name, LS.Cons ((t, r), s') ->
          Parsing.error (r, "Expected `some' or `block', found " ^ L.toString t)

    let rec parseBlockDec1 = function
      | name, LS.Cons ((L.Colon, r), s') -> parseSome (name, LS.expose s')
      | name, LS.Cons ((L.Equal, r), s') ->
          let g, f = ParseTerm.parseQualIds' (LS.expose s') in
          (ExtConDec.blockdef (name, g), f)
      | name, LS.Cons ((t, r), s') ->
          Parsing.error (r, "`:' expected, found token " ^ L.toString t)

    let rec parseBlockDec' = function
      | LS.Cons ((L.Id (idCase, name), r), s') ->
          parseBlockDec1 (name, LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            (r, "Label identifier expected, found token " ^ L.toString t)

    let rec parseConDec' = function
      | LS.Cons ((L.Id (idCase, name), r), s') ->
          parseConDec1 (Some name, LS.expose s')
      | LS.Cons ((L.Underscore, r), s') -> parseConDec1 (None, LS.expose s')
      | LS.Cons ((L.Block, r), s') -> parseBlockDec' (LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            ( r,
              "Constant or block declaration expected, found token "
              ^ L.toString t )

    let rec parseConDec s = parseConDec' (LS.expose s)
    let rec parseAbbrev' (LS.Cons ((L.Abbrev, r), s)) = parseConDec s
    let rec parseClause' (LS.Cons ((L.Clause, r), s)) = parseConDec s
  end

  (* parseConDec3  ""U"" *)
  (* parseConDec2  ""= U"" | """" *)
  (* parseConDec1  "": V = U"" | ""= U"" *)
  (* BlockDec parser *)
  (* added as a feature request by Carl  -- Wed Mar 16 16:11:44 2011  cs *)
  (* parseConDec' : lexResult front -> ExtConDec.ConDec * lexResult front
       Invariant: first token in exposed input stream is an identifier or underscore
    *)
  (* parseConDec --- currently not exported *)
  (* -fp *)
  let parseConDec' = parseConDec'
  let parseAbbrev' = parseAbbrev'
  let parseClause' = parseClause'
end
(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
(* local ... in *)
(* functor ParseConDec *)

(* # 1 "src/frontend/parse_condec.sml.ml" *)
