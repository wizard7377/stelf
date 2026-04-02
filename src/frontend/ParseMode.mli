include module type of ParseMode_intf

module ParseMode (ParseMode__0 : sig
  (*! structure Paths : PATHS !*)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ExtModes' : ReconMode_intf.EXTMODES

  (*! sharing ExtModes'.Paths = Paths !*)
  (*! sharing ExtModes'.ExtSyn.Paths = Paths !*)
  module ParseTerm : ParseTerm_intf.PARSE_TERM with module ExtSyn = ExtModes'.ExtSyn
end) : PARSE_MODE with module ExtModes = ParseMode__0.ExtModes'
