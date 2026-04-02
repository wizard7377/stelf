include module type of ParseTerm_intf

module ParseTerm (ParseTerm__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtSyn' : ReconTerm_intf.EXTSYN

  (*! sharing Parsing'.Lexer.Paths = ExtSyn'.Paths !*)
  module Names : NAMES
end) : PARSE_TERM with module ExtSyn = ParseTerm__0.ExtSyn'
