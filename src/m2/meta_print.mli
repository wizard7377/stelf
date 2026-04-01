include module type of Meta_print_intf

module MetaPrint (MetaPrint__0 : sig
  module Global : GLOBAL
  module MetaSyn' : Metasyn.METASYN
  module Formatter : FORMATTER
  module Print : PRINT

  (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
  module ClausePrint : Clause_print.CLAUSEPRINT
end) : METAPRINT with module MetaSyn = MetaPrint__0.MetaSyn'
