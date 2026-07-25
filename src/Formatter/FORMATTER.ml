open Basis

(*
   ForML Version 0.6 - 25 January 1993 - er@Cs.cmu.edu
   File Formatter.sig with signature FORMATTER.
*)
module type FORMATTER = sig
  val indent : int ref
  (* Default values. These may be changed by the user. *)

  val blanks : int ref
  val skip : int ref
  val pagewidth : int ref

  val bailout : bool ref
  (** flag specifying whether bailouts should occur when page too narrow *)

  val bailoutIndent : int ref
  val bailoutSpot : int ref

  (*
\subsection{Formats}
*)

  type format
  (** The Format datatype *)

  val width : format -> int * int
  (** return the minimum/maximum width of a format *)

  (* routines to create a format *)

  val break : format
  (** Note: the xxxx0 functions take extra arguments *)

  val break0 : int -> int -> format

  val string : string -> format
  (** blanks, indent *)

  val string0 : int -> string -> format

  val space : format
  (** output width *)

  val spaces : int -> format
  val newline : unit -> format
  val newlines : int -> format
  val newpage : unit -> format
  val vbox : format list -> format
  val vbox0 : int -> int -> format list -> format

  val hbox : format list -> format
  (** indent, skip *)

  val hbox0 : int -> format list -> format

  val hVbox : format list -> format
  (** blanks *)

  val hVbox0 : int -> int -> int -> format list -> format

  val hOVbox : format list -> format
  (** blanks, indent, skip *)

  val hOVbox0 : int -> int -> int -> format list -> format

  val break_ : format
  (** blanks, indent, skip *)

  val makestring_fmt : format -> string
  (* Output routines. *)

  val print_fmt : format -> unit

  type fmtstream

  val open_fmt : TextIO.outstream -> fmtstream
  val close_fmt : fmtstream -> TextIO.outstream
  val output_fmt : fmtstream * format -> unit
  val file_open_fmt : string -> (unit -> unit) * fmtstream
  val with_open_fmt : string -> (fmtstream -> 'a) -> 'a
end
