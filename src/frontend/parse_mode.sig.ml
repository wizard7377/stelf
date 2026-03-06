open! Basis;;
(* Parsing Mode Declarations *);;
(* Author: Carsten Schuermann *);;
module type PARSE_MODE = sig
                         (*! structure Parsing : PARSING !*)
                         module ExtModes : EXTMODES
                         val parseMode' : ExtModes.modedec list
                           Parsing.parser
                         end;;
(* signature PARSE_MODE *);;