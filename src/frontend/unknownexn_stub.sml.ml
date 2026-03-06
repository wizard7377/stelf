open! Basis;;
(* A do-nothing stub for SML implementations without an SML/NJ-like
   exnHistory function.
*);;
module UnknownExn = (UnknownExn)(struct
                                   let exnHistory = function 
                                                             | exn -> [];;
                                   end);;