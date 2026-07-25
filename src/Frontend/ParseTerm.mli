include module type of PARSETERM

module ParseTerm (ParseTerm__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtSyn' : RECONTERM.EXTSYN

  (*! sharing Parsing'.Lexer.Paths = ExtSyn'.Paths !*)
  module Names : NAMES
end) : PARSE_TERM with module ExtSyn = ParseTerm__0.ExtSyn'
