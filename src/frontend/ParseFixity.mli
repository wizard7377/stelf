include module type of ParseFixity_intf

module ParseFixity (ParseFixity__0 : sig
  module Names' : NAMES
end) : PARSE_FIXITY with module Names = ParseFixity__0.Names'
