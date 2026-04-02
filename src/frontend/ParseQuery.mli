include module type of ParseQuery_intf

module ParseQuery (ParseQuery__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtQuery' : ReconQuery_intf.EXTQUERY

  (*! sharing ExtQuery'.Paths = Parsing'.Lexer.Paths !*)
  module ParseTerm : ParseTerm_intf.PARSE_TERM with module ExtSyn = ExtQuery'.ExtSyn
end) : PARSE_QUERY with module ExtQuery = ParseQuery__0.ExtQuery'
