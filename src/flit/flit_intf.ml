(* # 1 "src/flit/flit_.sig.ml" *)
open! Basis

(* Flit DAG generator *)

(** Author: Roberto Virga *)

module type FLIT = sig
  val init : string -> unit
  (** init (sym_table_file) *)

  val initForText : unit -> unit
  (** initForText () *)

  val dump : string * string -> int
  (** dump (symbol, dag_file) *)

  val dumpText : string * string -> unit
  (** dumpText (outputSemant, outputChecker) *)

  val setFlag : unit -> unit
  (** setFlag () *)

  val setEndTcb : unit -> unit
  (** setEndTcb () *)

  val dumpFlagged : string -> unit
  (** dumpFlagged (dag_file) *)

  val dumpSymTable : string * string * string -> unit
  (** dumpSynTable (start_sym, end_sym, sym_table_file) *)
end
