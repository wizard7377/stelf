include module type of ParseThm_intf

module ParseThm (ParseThm__0 : sig
  (*! structure Paths : PATHS *)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ThmExtSyn' : ReconThm_intf.THMEXTSYN

  (*! sharing ThmExtSyn'.Paths = Paths !*)
  (*! sharing ThmExtSyn'.ExtSyn.Paths = Paths !*)
  module ParseTerm :
    ParseTerm_intf.PARSE_TERM with module ExtSyn = ThmExtSyn'.ExtSyn
end) : PARSE_THM with module ThmExtSyn = ParseThm__0.ThmExtSyn'
