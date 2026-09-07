include module type of PARSEQUERY

module ParseQuery (ParseQuery__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtQuery' : RECONQUERY.EXTQUERY

  (*! sharing ExtQuery'.Paths = Parsing'.Lexer.Paths !*)
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ExtQuery'.ExtSyn
end) : PARSE_QUERY with module ExtQuery = ParseQuery__0.ExtQuery'
