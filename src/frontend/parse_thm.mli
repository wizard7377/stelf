include module type of Parse_thm_intf

module ParseThm (ParseThm__0 : sig
  (*! structure Paths : PATHS *)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ThmExtSyn' : Recon_thm.THMEXTSYN

  (*! sharing ThmExtSyn'.Paths = Paths !*)
  (*! sharing ThmExtSyn'.ExtSyn.Paths = Paths !*)
  module ParseTerm :
    Parse_term.PARSE_TERM with module ExtSyn = ThmExtSyn'.ExtSyn
end) : PARSE_THM with module ThmExtSyn = ParseThm__0.ThmExtSyn'
