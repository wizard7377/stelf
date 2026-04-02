(* # 1 "src/frontend/ParseMode.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

module type PARSE_MODE = sig
  (*! structure Parsing : PARSING !*)
  module ExtModes : ReconMode_intf.EXTMODES

  val parseMode' : ExtModes.modedec list Parsing.parser
end
