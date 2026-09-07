include module type of PARSEMODE

module ParseMode (ParseMode__0 : sig
  (*! structure Paths : PATHS !*)
  (*! structure Parsing' : PARSING !*)
  (*! sharing Parsing'.Lexer.Paths = Paths !*)
  module ExtModes' : RECONMODE.EXTMODES

  (*! sharing ExtModes'.Paths = Paths !*)
  (*! sharing ExtModes'.ExtSyn.Paths = Paths !*)
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ExtModes'.ExtSyn
end) : PARSE_MODE with module ExtModes = ParseMode__0.ExtModes'
