(* # 1 "src/paths/Paths_.sig.ml" *)
open! Basis

(* Paths, Occurrences, and Error Locations *)

(** Author: Frank Pfenning *)

module type PATHS = sig
  type region = Reg of int * int [@@deriving show]

  (* r ::= (i,j) is interval [i,j) *)
  type location = Loc of string * region

  (* loc ::= (filename, region) *)

  type linesInfo
  (** line numbering, used when printing regions *)

  val resetLines : unit -> unit
  (** mapping from character positions to lines in a file *)

  val newLine : int -> unit
  (** reset line numbering *)

  val getLinesInfo : unit -> linesInfo
  (** new line starts at character i *)

  val join : region * region -> region
  (** get lines info for current file *)

  val toString : region -> string
  (** join(r1,r2) = smallest region enclosing r1 and r2 *)

  val wrap : region * string -> string
  (** line1.col1-line2.col2, parsable by Emacs *)

  val wrapLoc : location * string -> string
  (** add region to error message, parsable by Emacs *)

  val wrapLoc' : location * linesInfo option * string -> string
  (** add location to error message, also parsable *)

  (* add location to error message in line.col format *)
  (* Paths, occurrences and occurrence trees only work well for normal forms *)
  (* In the general case, regions only approximate true source location *)

  (** Follow path through a term to obtain subterm *)
  type path = Label of path | Body of path | Head | Arg of int * path | Here

  (* [x:#] U or {x:#} V *)
  (* [x:V] # or {x:V} # *)
  (* # @ S, term in normal form *)
  (* H @ S1; ...; #; ...; Sn; Nil *)
  (* #, covers Uni, EVar, Redex(?) *)

  type occ
  (** Construct an occurrence when traversing a term. The resulting occurrence
      can be translated to a region via an occurrence tree stored with the term.

      An occurrence is a path in reverse Order. *)

  val top : occ
  val label : occ -> occ
  val body : occ -> occ
  val head : occ -> occ
  val arg : int * occ -> occ

  type occExp
  (** An occurrence tree is a data structure mapping occurrences in a term to
      regions in an input Stream. Occurrence trees are constructed during
      Parsing. *)

  and occSpine

  (* occurrence tree for u expressions *)

  val leaf : region -> occExp
  (** occurrence tree for s spines *)

  val bind : region * occExp option * occExp -> occExp
  (** could be _ or identifier *)

  val root : region * occExp * int * int * occSpine -> occExp
  val app : occExp * occSpine -> occSpine
  val nils : occSpine

  type occConDec

  val dec : int * occExp -> occConDec
  (** occurrence tree for constant declarations *)

  val def : int * occExp * occExp option -> occConDec
  (** (#implicit, v) in c : V *)

  val toRegion : occExp -> region
  (** (#implicit, u, v) in c : V = U *)

  val toRegionSpine : occSpine * region -> region
  val posToPath : occExp -> int -> path
  val occToRegionExp : occExp -> occ -> region
  val occToRegionDec : occConDec -> occ -> region

  val occToRegionDef1 : occConDec -> occ -> region
  (** into v for c : V *)

  val occToRegionDef2 : occConDec -> occ -> region
  (** into u for c : V = U *)

  val occToRegionClause : occConDec -> occ -> region
  (** into v for c : V = U *)
end
