include module type of Parse_query_intf

module ParseQuery (ParseQuery__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtQuery' : Recon_query.EXTQUERY

  (*! sharing ExtQuery'.Paths = Parsing'.Lexer.Paths !*)
  module ParseTerm : Parse_term.PARSE_TERM with module ExtSyn = ExtQuery'.ExtSyn
end) : PARSE_QUERY with module ExtQuery = ParseQuery__0.ExtQuery'
