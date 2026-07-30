type t = {
  implicit : bool;
      (** Show implicit arguments, and show substitutions on existential
          variables instead of applying them. *)
  print_infix : bool;
      (** Under [implicit], still render declared infix operators infix. *)
  print_depth : int option;
      (** Replace anything nested deeper than this with a cutoff marker. *)
  print_length : int option;
      (** Replace arguments past this many with an ellipsis marker. *)
  no_shadow : bool;
      (** Name constants by their canonical path rather than by the shortest
          name that currently resolves to them. *)
  show_const_path : bool;  (** Qualify constant names with their namespace. *)
  arrow_sugar : bool;
      (** Render anonymous non-dependent [Pi]s as an arrow chain. *)
  eta_expand : bool;
      (** Eta-expand a constant applied to fewer arguments than its fixity
          takes, so it can still be rendered as an operator. *)
}
(** What resugaring is allowed to hide.

    An explicit record rather than the global refs in [Print]: round-trip tests
    have to pin these regardless of what a preceding [%set] left behind, library
    callers cannot reasonably be asked to save and restore six pieces of global
    state, and one of the six ([arrow_sugar]) already lives in a different
    module from the rest. [Print] keeps its refs and snapshots them into one of
    these per call, so no caller has to change. *)

(** Everything shown, nothing elided. *)
let default : t =
  {
    implicit = false;
    print_infix = false;
    print_depth = None;
    print_length = None;
    no_shadow = false;
    show_const_path = true;
    arrow_sugar = false;
    eta_expand = true;
  }
