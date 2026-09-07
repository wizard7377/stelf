
(* # 1 "src/frontend/ParseCondec.sig.ml" *)
open! Parsing

(* Parsing Signature Entries *)
(* Author: Frank Pfenning *)
include PARSECONDEC
(* signature PARSE_CONDEC *)

(* # 1 "src/frontend/ParseCondec.fun.ml" *)
open! Basis

(* Parsing Signature Entries *)
(* Author: Frank Pfenning *)
module ParseConDec (ParseConDec__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtConDec' : RECONCONDEC.EXTCONDEC
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ExtConDec'.ExtSyn
end) : PARSE_CONDEC with module ExtConDec = ParseConDec__0.ExtConDec' = struct
  (*! structure Parsing = Parsing' !*)
  module ExtConDec = ParseConDec__0.ExtConDec'
  module ParseTerm = ParseConDec__0.ParseTerm

  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream

    let parseConDec3 (optName, optTm, s) =
      let tm', f' = ParseTerm.parseTerm' (LS.expose s) in
      (ExtConDec.condef optName tm' optTm, f')

    let parseConDec2 = function
      | optName, (tm, LS.Cons ((L.Equal, r), s')) ->
          parseConDec3 (optName, Some tm, s')
      | Some name, (tm, f) -> (ExtConDec.condec (name, tm), f)
      | None, (tm, LS.Cons ((t, r), s')) ->
          Parsing.error r ("Illegal anonymous declared constant")

    let parseConDec1 (optName, a) = match a with
      | LS.Cons ((L.Colon, r), s') ->
          parseConDec2 (optName, ParseTerm.parseTerm' (LS.expose s'))
      | LS.Cons ((L.Equal, r), s') -> parseConDec3 (optName, None, s')
      | LS.Cons ((t, r), s') ->
          Parsing.error r ("Expected `:' or `=', found " ^ L.toString t)

    let parseBlock = function
      | LS.Cons ((L.Id (_, "block"), r), s') ->
          ParseTerm.parseCtx' (LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error r ("Expected `block', found " ^ L.toString t)

    let parseSome (name, a) = match a with
      | LS.Cons ((L.Id (_, "some"), r), s') ->
          let g1, f' = ParseTerm.parseCtx' (LS.expose s') in
          let g2, f'' = parseBlock f' in
          (ExtConDec.blockdec name g1 g2, f'')
      | (LS.Cons ((L.Id (_, "block"), r), s') as f) ->
          let g2, f' = parseBlock f in
          (ExtConDec.blockdec name [] g2, f')
      | LS.Cons ((t, r), s') ->
          Parsing.error r ("Expected `some' or `block', found " ^ L.toString t)

    let parseBlockDec1 (name, a) = match a with
      | LS.Cons ((L.Colon, r), s') -> parseSome (name, LS.expose s')
      | LS.Cons ((L.Equal, r), s') ->
          let g, f = ParseTerm.parseQualIds' (LS.expose s') in
          (ExtConDec.blockdef name g, f)
      | LS.Cons ((t, r), s') ->
          Parsing.error r ("`:' expected, found token " ^ L.toString t)

    let parseBlockDec' = function
      | LS.Cons ((L.Id (idCase, name), r), s') ->
          parseBlockDec1 (name, LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            r ("Label identifier expected, found token " ^ L.toString t)

    let parseConDec' = function
      | LS.Cons ((L.Id (idCase, name), r), s') ->
          parseConDec1 (Some name, LS.expose s')
      | LS.Cons ((L.Underscore, r), s') -> parseConDec1 (None, LS.expose s')
      | LS.Cons ((L.Block, r), s') -> parseBlockDec' (LS.expose s')
      | LS.Cons ((t, r), s') ->
          Parsing.error
            r ("Constant or block declaration expected, found token "
              ^ L.toString t)

    let parseConDec s = parseConDec' (LS.expose s)
    let parseAbbrev' (LS.Cons ((L.Abbrev, r), s)) = parseConDec s
    let parseClause' (LS.Cons ((L.Clause, r), s)) = parseConDec s
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

(* # 1 "src/frontend/ParseCondec.sml.ml" *)
