open! Parsing
open! Basis

(* Parsing Queries *)
(* Author: Frank Pfenning *)
module ParseQuery (ParseQuery__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtQuery' : Recon_query.EXTQUERY

  (*! sharing ExtQuery'.Paths = Parsing'.Lexer.Paths !*)
  module ParseTerm : Parse_term.PARSE_TERM with module ExtSyn = ExtQuery'.ExtSyn
end) : PARSE_QUERY with module ExtQuery = ParseQuery__0.ExtQuery' = struct
  (*! structure Parsing = Parsing' !*)
  module ExtQuery = ParseQuery__0.ExtQuery'
  module ParseTerm = ParseQuery__0.ParseTerm

  open! struct
    module L = Parsing.Lexer
    module LS = Parsing.Stream
    module P = Paths

    let rec returnQuery (optName, (tm, f)) = (ExtQuery.query (optName, tm), f)

    let rec parseQuery1 = function
      | name, f, LS.Cons ((colon_, r), s') ->
          returnQuery (Some name, ParseTerm.parseTerm' (LS.expose s'))
      | name, f, _ -> returnQuery (None, ParseTerm.parseTerm' f)

    let rec parseQuery' = function
      | LS.Cons ((L.Id (upper_, name), r), s') as f ->
          parseQuery1 (name, f, LS.expose s')
      | f -> returnQuery (None, ParseTerm.parseTerm' f)

    let rec parseQuery s = parseQuery' (LS.expose s)

    let rec parseDefine4 (optName, optT, s) =
      let tm', f' = ParseTerm.parseTerm' (LS.expose s) in
      (ExtQuery.define (optName, tm', optT), f')

    let rec parseDefine3 = function
      | optName, (tm, LS.Cons ((equal_, r), s')) ->
          parseDefine4 (optName, Some tm, s')
      | _, (tm, LS.Cons ((t, r), _)) ->
          Parsing.error (r, "Expected `=', found " ^ L.toString t)

    let rec parseDefine2 = function
      | optName, LS.Cons ((colon_, r), s') ->
          parseDefine3 (optName, ParseTerm.parseTerm' (LS.expose s'))
      | optName, LS.Cons ((equal_, r), s') -> parseDefine4 (optName, None, s')
      | _, LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)

    let rec parseDefine1 = function
      | LS.Cons ((L.Id (idCase, name), r), s') ->
          parseDefine2 (Some name, LS.expose s')
      | LS.Cons ((underscore_, r), s') -> parseDefine2 (None, LS.expose s')
      | LS.Cons ((t, r), _) ->
          Parsing.error (r, "Expected identifier or `_', found " ^ L.toString t)

    let rec parseSolve3 = function
      | defns, nameOpt, LS.Cons ((colon_, r), s'), r0 ->
          let tm, (LS.Cons ((_, r), _) as f') =
            ParseTerm.parseTerm' (LS.expose s')
          in
          ((List.rev defns, ExtQuery.solve (nameOpt, tm, P.join (r0, r))), f')
      | _, _, LS.Cons ((t, r), s'), r0 ->
          Parsing.error (r, "Expected `:', found " ^ L.toString t)

    let rec parseSolve2 = function
      | defns, LS.Cons ((underscore_, r), s'), r0 ->
          parseSolve3 (defns, None, LS.expose s', r0)
      | defns, LS.Cons ((L.Id (_, name), r), s'), r0 ->
          parseSolve3 (defns, Some name, LS.expose s', r0)
      | _, LS.Cons ((t, r), s'), r0 ->
          Parsing.error (r, "Expected identifier or `_', found " ^ L.toString t)

    and parseSolve1 = function
      | defns, LS.Cons ((solve_, r0), s') ->
          parseSolve2 (defns, LS.expose s', r0)
      | defns, LS.Cons ((define_, r0), s') ->
          let defn, f' = parseDefine1 (LS.expose s') in
          parseSolve1 (defn :: defns, f')
      | defns, LS.Cons ((t, r), s) ->
          Parsing.error (r, "Expected %define or %solve, found " ^ L.toString t)

    and parseSolve' f = parseSolve1 ([], f)
  end

  (* parseQuery1 (name, f, f')   "": A"" from f' or ""V"" from f. *)
  (* parseQuery' : lexResult front -> ExtQuery.query * lexResult front *)
  (* parseQuery'  ""X : A"" | ""A"" *)
  (* Query parsing is ambiguous, since a term ""V"" might have the form ""U' : V'"" *)
  (* We look for an uppercase variable X followed by a `:'.
       If we find this, we parse a query of the form ""X : A"".
       Otherwise we parse a query of the form ""A"".
    *)
  (* parseQuery --- currently not exported *)
  (* parseDefine4 parses the definition body *)
  (* ""U"" *)
  (* parseDefine3 parses the equal sign in a long form define *)
  (* ""= U"" *)
  (* parseDefine2 switches between short and long form *)
  (* "": V = U"" | ""= U"" *)
  (* parseDefine1 parses the name of the constant to be defined *)
  (* ""c : V = U"" | ""_ : V = U"" | ""c = U"" | ""_ = U"" *)
  let parseQuery' = parseQuery'
  let parseSolve' = parseSolve'
end
(*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
(* local ... in *)
(* functor ParseQuery *)
