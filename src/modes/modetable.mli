include module type of Modetable_intf

module MakeModeTable (ModeTable__0 : sig
  module Table : TABLE with type key = int
end) : MODETABLE
