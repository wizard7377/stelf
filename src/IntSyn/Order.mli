include module type of ORDER

module MakeOrder (Order__0 : sig
  module Table : TABLE with type key = int
end) : ORDER

module Order : ORDER
include ORDER
