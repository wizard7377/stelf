include module type of ParseModule_intf

module ParseModule (ParseModule__0 : sig
  (* Parsing modules *)
  (* Author: Kevin Watkins *)
  (*! structure Paths : PATHS !*)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ModExtSyn' : ReconModule_intf.MODEXTSYN

  (*! sharing ModExtSyn'.Paths = Paths !*)
  module ParseTerm :
    ParseTerm_intf.PARSE_TERM with module ExtSyn = ModExtSyn'.ExtSyn
end) : PARSE_MODULE with module ModExtSyn = ParseModule__0.ModExtSyn'
