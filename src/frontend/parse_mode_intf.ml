(* # 1 "src/frontend/parse_mode.sig.ml" *)
open! Basis
open! Parsing

(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

module type PARSE_MODE = sig
  (*! structure Parsing : PARSING !*)
  module ExtModes : Recon_mode.EXTMODES

  val parseMode' : ExtModes.modedec list Parsing.parser
end
