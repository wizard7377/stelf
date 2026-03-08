open! Basis

(*
% ForML Version 0.6 - 25 January 1993 - er@cs.cmu.edu
%*********************************************************************
{\bf File {\tt formatter.sig} with signature {\tt FORMATTER}.}
%*********************************************************************
*)
module type FORMATTER = sig
  (*
\subsection{Default values}
These may may be changed by the user.
*)
  val indent : int ref
  val blanks : int ref
  val skip : int ref
  val pagewidth : int ref

  (* flag specifying whether bailouts should occur when page too narrow *)
  val bailout : bool ref
  val bailoutIndent : int ref
  val bailoutSpot : int ref

  (*
\subsection{Formats}
*)
  (* The Format datatype *)
  type nonrec format

  (* return the minimum/maximum width of a format *)
  val width : format -> int * int

  (* routines to create a format *)
  (* Note: the xxxx0 functions take extra arguments *)
  val break : format
  val break0 : int -> int -> format

  (* blanks, indent *)
  val string : string -> format
  val string0 : int -> string -> format

  (* output width *)
  val space : format
  val spaces : int -> format
  val newline : unit -> format
  val newlines : int -> format
  val newpage : unit -> format
  val vbox : format list -> format
  val vbox0 : int -> int -> format list -> format

  (* indent, skip *)
  val hbox : format list -> format
  val hbox0 : int -> format list -> format

  (* blanks *)
  val hVbox : format list -> format
  val hVbox0 : int -> int -> int -> format list -> format

  (* blanks, indent, skip *)
  val hOVbox : format list -> format
  val hOVbox0 : int -> int -> int -> format list -> format

  (* blanks, indent, skip *)
  (*
\subsection{Output routines}
*)
  val makestring_fmt : format -> string
  val print_fmt : format -> unit

  type nonrec fmtstream

  val open_fmt : TextIO.outstream -> fmtstream
  val close_fmt : fmtstream -> TextIO.outstream
  val output_fmt : fmtstream * format -> unit
  val file_open_fmt : string -> (unit -> unit) * fmtstream
  val with_open_fmt : string -> (fmtstream -> 'a) -> 'a
end
