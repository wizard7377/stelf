module type COMMON = sig
  module Global : Global.Global_intf.GLOBAL
  module Syntax : Syntax.SYNTAX 

                      end
