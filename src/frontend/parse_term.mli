include module type of Parse_term_intf

module ParseTerm (ParseTerm__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtSyn' : Recon_term.EXTSYN

  (*! sharing Parsing'.Lexer.Paths = ExtSyn'.Paths !*)
  module Names : NAMES
end) : PARSE_TERM with module ExtSyn = ParseTerm__0.ExtSyn'
