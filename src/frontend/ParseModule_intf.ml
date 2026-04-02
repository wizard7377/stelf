(* # 1 "src/frontend/ParseModule.sig.ml" *)
open! Basis
open! Parsing

(* Parsing modules *)
(* Author: Kevin Watkins *)

module type PARSE_MODULE = sig
  (*! structure Parsing : PARSING !*)
  module ModExtSyn : ReconModule_intf.MODEXTSYN

  (* val parseSigExp' : ModExtSyn.sigexp Parsing.recparser *)
  val parseSigDef' : ModExtSyn.sigdef Parsing.recparser

  (* val parseStructExp' : ModExtSyn.strexp Parsing.parser *)
  val parseStructDec' : ModExtSyn.structdec Parsing.recparser
  val parseInclude' : ModExtSyn.sigexp Parsing.recparser
  val parseOpen' : ModExtSyn.strexp Parsing.parser
end
