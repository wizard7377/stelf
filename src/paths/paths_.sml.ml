open! Basis
(* Now in paths.fun *)
(*
structure Paths = Paths ();
*)
(* Commented out to break dependency cycle with origins
module Origins = (Origins)(struct
                             module Global = Global;;
                             module Table = StringHashTable;;
                             end);;
*)
(*! structure IntSyn' = IntSyn !*)
(*! structure Paths' = Paths !*)
