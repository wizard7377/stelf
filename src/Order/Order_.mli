include module type of ORDER
module MakeOrder (Table : TABLE with type key = int) : ORDER
module Order : ORDER
include ORDER
