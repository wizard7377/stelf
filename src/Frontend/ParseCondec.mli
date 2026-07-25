include module type of PARSECONDEC

module ParseConDec (ParseConDec__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtConDec' : RECONCONDEC.EXTCONDEC
  module ParseTerm : PARSETERM.PARSE_TERM with module ExtSyn = ExtConDec'.ExtSyn
end) : PARSE_CONDEC with module ExtConDec = ParseConDec__0.ExtConDec'
