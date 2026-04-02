include module type of CompSyn_intf

module Make_CompSyn
    (Global_ : GLOBAL)
    (Names_ : NAMES)
    (Table_ : TABLE with type key = int) :
  COMPSYN

module CompSyn : COMPSYN

include COMPSYN
