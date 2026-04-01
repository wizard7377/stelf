(* # 1 "src/opsem/tabled_machine.sig.ml" *)
open! Basis

(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)

module type TABLED = sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  val solve :
    (CompSyn.goal * IntSyn.sub) * CompSyn.dProg * (CompSyn.pskeleton -> unit) ->
    unit

  val updateGlobalTable : CompSyn.goal * bool -> unit
  val keepTable : IntSyn.cid -> bool
  val fillTable : unit -> unit
  val nextStage : unit -> bool
  val reset : unit -> unit
  val tableSize : unit -> int
  val suspGoalNo : unit -> int
end
