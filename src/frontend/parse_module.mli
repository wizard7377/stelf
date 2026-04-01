include module type of Parse_module_intf

module ParseModule (ParseModule__0 : sig
  (* Parsing modules *)
  (* Author: Kevin Watkins *)
  (*! structure Paths : PATHS !*)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ModExtSyn' : Recon_module.MODEXTSYN

  (*! sharing ModExtSyn'.Paths = Paths !*)
  module ParseTerm :
    Parse_term.PARSE_TERM with module ExtSyn = ModExtSyn'.ExtSyn
end) : PARSE_MODULE with module ModExtSyn = ParseModule__0.ModExtSyn'
