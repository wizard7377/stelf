include module type of Order_intf

module MakeOrder (Table : TABLE with type key = int) : ORDER

module Order : ORDER
include ORDER
