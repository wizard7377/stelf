open! Basis

(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)
module type PRINT = sig
  (*! structure IntSyn : INTSYN !*)
  module Formatter : FORMATTER

  val implicit : bool ref
  val printInfix : bool ref
  val printDepth : int option ref
  val printLength : int option ref
  val noShadow : bool ref
  val formatDec : IntSyn.dctx * IntSyn.dec_ -> Formatter.format
  val formatDecList : IntSyn.dctx * IntSyn.dec_ list -> Formatter.format

  val formatDecList' :
    IntSyn.dctx * (IntSyn.dec_ list * IntSyn.sub_) -> Formatter.format

  val formatExp : IntSyn.dctx * IntSyn.exp_ -> Formatter.format
  val formatSpine : IntSyn.dctx * IntSyn.spine_ -> Formatter.format list
  val formatConDec : IntSyn.conDec_ -> Formatter.format
  val formatConDecI : IntSyn.conDec_ -> Formatter.format
  val formatCnstr : IntSyn.cnstr_ -> Formatter.format
  val formatCtx : IntSyn.dctx * IntSyn.dctx -> Formatter.format
  val decToString : IntSyn.dctx * IntSyn.dec_ -> string
  val expToString : IntSyn.dctx * IntSyn.exp_ -> string
  val conDecToString : IntSyn.conDec_ -> string
  val cnstrToString : IntSyn.cnstr_ -> string
  val cnstrsToString : IntSyn.cnstr list -> string

  (* assigns names in contexts *)
  val ctxToString : IntSyn.dctx * IntSyn.dctx -> string
  val evarInstToString : (IntSyn.exp_ * string) list -> string
  val evarCnstrsToStringOpt : (IntSyn.exp_ * string) list -> string option
  val formatWorlds : Tomega.worlds_ -> Formatter.format
  val worldsToString : Tomega.worlds_ -> string
  val printSgn : unit -> unit
end
(* signature PRINT *)
