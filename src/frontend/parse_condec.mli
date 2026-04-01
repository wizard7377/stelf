include module type of Parse_condec_intf

module ParseConDec (ParseConDec__0 : sig
  (*! structure Parsing' : PARSING !*)
  module ExtConDec' : Recon_condec.EXTCONDEC

  module ParseTerm :
    Parse_term.PARSE_TERM with module ExtSyn = ExtConDec'.ExtSyn
end) : PARSE_CONDEC with module ExtConDec = ParseConDec__0.ExtConDec'
