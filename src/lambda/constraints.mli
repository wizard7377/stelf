open Conv_intf
include module type of Constraints_intf

module MakeConstraints (Constraints__0 : sig
  module Conv : CONV
end) : CONSTRAINTS
