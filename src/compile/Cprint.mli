include module type of Cprint_intf

module Make_CPrint
    (Print_ : PRINT)
    (Formatter_ : FORMATTER)
    (Names_ : NAMES) :
  CPRINT
