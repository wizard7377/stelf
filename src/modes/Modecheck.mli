include module type of Modecheck_intf

module MakeModeCheck (ModeCheck__0 : sig
  (*! structure IntSyn : INTSYN !*)
  module ModeTable : Modetable.MODETABLE

  (*! sharing ModeSyn.IntSyn = IntSyn !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn !*)
  module Index : INDEX

  (*! sharing Index.IntSyn = IntSyn !*)
  (*! structure Paths : PATHS !*)
  module Origins : Origins.ORIGINS
end) : MODECHECK
