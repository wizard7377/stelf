include module type of Parse_fixity_intf

module ParseFixity (ParseFixity__0 : sig
  module Names' : NAMES
end) : PARSE_FIXITY with module Names = ParseFixity__0.Names'
