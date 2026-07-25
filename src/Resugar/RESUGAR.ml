module type S = sig
  module Syntax : Syntax.SYNTAX
  module Cst : Cst.CST
  module Names : Names.NAMES.NAMES
end

module type RESUGAR = sig
  module Syntax : Syntax.SYNTAX
  module Cst : Cst.CST

  type t
  type u

  val register : t -> u -> unit
  val resugar : t -> u
end
