include module type of ParseCondec_intf

module ParseConDec (ParseConDec__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtConDec' : ReconCondec_intf.EXTCONDEC

  module ParseTerm :
    ParseTerm_intf.PARSE_TERM with module ExtSyn = ExtConDec'.ExtSyn
end) : PARSE_CONDEC with module ExtConDec = ParseConDec__0.ExtConDec'
