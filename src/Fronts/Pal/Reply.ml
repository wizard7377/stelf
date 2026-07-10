(** Structured results produced by the command pipeline ([Impl]).

    Commands used to print their results directly through [Display]; they now
    return values of this type so that each frontend (CLI, TUI, LSP, a future JS
    environment, or a library consumer) decides how to present them. Rendering
    for the current frontends lives in {!Render}. *)

type t =
  | Installed of Intsyn.IntSyn.cid list
      (** New constants added to the global signature. *)
  | Decl of Intsyn.IntSyn.conDec  (** A declaration looked up with [%decl]. *)
  | Response of string
      (** Textual answer to an informational command ([%help], [%version],
          [%get], ...). *)
  | Solutions of int
      (** Number of solutions a query found. (The solution terms themselves are
          still rendered by the query engine via [Display]; they move here once
          query execution takes a solution callback.) *)
  | Quit  (** The session should terminate. *)

type error = { stage : Error.Error.stage; message : Display.form }
(** A failed load: the pipeline stage that failed and its diagnostic. *)

type outcome = { replies : t list; error : error option }
(** Result of loading a string, file, or project config: everything the commands
    produced, plus the error that stopped the load, if any. [error = None] means
    the load succeeded. *)

let ok (replies : t list) : outcome = { replies; error = None }

let fail ?(replies = []) (error : error) : outcome =
  { replies; error = Some error }

let failed (o : outcome) : bool = Option.is_some o.error
let quit_requested = List.exists (function Quit -> true | _ -> false)
