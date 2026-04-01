include module type of Index_intf

module MakeIndex (Index__0 : sig
  module Global : GLOBAL
  module Queue : Queue.QUEUE
end) : INDEX

module Index : INDEX
include INDEX
