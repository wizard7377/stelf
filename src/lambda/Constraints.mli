open Conv_intf
include module type of Constraints_intf

module MakeConstraints (Conv : CONV) : CONSTRAINTS
