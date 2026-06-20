module type NAMES = NAMES
include module type of Names_
module Names_ : module type of Names_
module Names = Names_
