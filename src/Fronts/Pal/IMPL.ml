open! Basis

module type IMPL = sig


  module Cst : Cst.CST
  (** Concrete syntax tree: the CST used by the modern parser. *)

  module Names : Names.NAMES.NAMES
  (** Shared Names module; equals Cmd.Modern.Names. *)

  module Cmd : Modern.CMD.CMD with module Cst = Cst and module Modern.Names = Names
  (** New parser layer: command-level parsing using the Modern parser. *)

  module Recon : Recon.RECON
  (** New elaboration layer: reconstruction / type-inference sub-modules. *)

  (** Input source for loading: a file path or an inline string. *)
  type source = File of Fpath.t | Input of string

  val mode : [ `Repl | `Lsp | `Other ] ref
  (** Operating mode: affects error formatting and REPL behaviour. *)

  (* -------------------------------------------------------------------- *)
  (** {1 Global flags} *)

  val chatter : int ref
  (** Verbosity level: 0 = silent, 1 = minimal, 2+ = progressively louder. *)

  val double_check : bool ref
  (** Re-typecheck declarations after reconstruction; catches reconstructor
      bugs. *)

  val unsafe : bool ref
  (** Permit [%assert] and [%trustme] directives. *)

  val auto_freeze : bool ref
  (** Automatically freeze families after [%terminates] / [%worlds] checks. *)

  val time_limit : Time.time option ref
  (** Optional wall-clock limit in seconds for proof search. *)

  (* -------------------------------------------------------------------- *)
  (** {1 Result status} *)

  type status =
    | Ok
    | Abort  (** Return status of loading and evaluation operations. *)

  (* -------------------------------------------------------------------- *)
  (** {1 Signature installation} *)

  module Install : sig
    val install1 : ?path:Fpath.t option -> Names.namespace -> Cst.cmd -> unit
    (** Install a single parsed command into the global signature. *)

    val install : ?path:Fpath.t option -> Names.namespace -> Cst.cmd list -> unit
    (** Install a list of commands in order. *)

    val reset : unit -> unit
    (** Erase the entire global state: signature, name tables, indices, etc. *)
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Loading} *)

  val load : Names.namespace -> source -> status
  (** Parse and install all declarations from a source. *)

  val read_decl : unit -> status
  (** Read and install a single declaration typed interactively on stdin. *)

  val decl : string -> status
  (** Print the declaration of the constant identified by a qualified name. *)

  val top : unit -> unit
  (** Enter the interactive query loop. *)

  (* -------------------------------------------------------------------- *)
  (** {1 Configuration file management} *)

  module Config : sig
    type t = Project.Format.file
    (** The type of configuration objects. *)
    val read : source -> t 
    val load : t -> status

  end

  val make : source -> status
  (** Convenience: {!Config.read} then {!Config.load} in one step. *)

  (* -------------------------------------------------------------------- *)
  (** {1 Print settings} *)

  module Print : sig
    val implicit : bool ref
    (** Print implicit arguments (default: false). *)

    val print_infix : bool ref
    (** Use infix notation when a fixity is declared (default: true). *)

    val depth : int option ref
    (** Maximum print depth; [None] = unlimited. *)

    val length : int option ref
    (** Maximum argument-list length per sub-expression; [None] = unlimited. *)

    val indent : int ref
    (** Indentation width for sub-terms (default: 3). *)

    val width : int ref
    (** Line width for the pretty-printer (default: 80). *)

    val no_shadow : bool ref
    (** When true, shadowed constants are printed with a [%…%] marker. *)

    val sgn : unit -> unit
    (** Print the full signature. *)

    val prog : unit -> unit
    (** Print the signature as a compiled logic program. *)

    val subord : unit -> unit
    (** Print the subordination relation. *)

    val def : unit -> unit
    (** Print information about defined constants. *)

    val domains : unit -> unit
    (** Print registered constraint-solver domains. *)

    module Tex : sig
      val sgn : unit -> unit
      (** Print the signature in LaTeX format. *)

      val prog : unit -> unit
      (** Print the logic program in LaTeX format. *)
    end
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Reconstruction (elaboration) settings} *)

  module ReconOpts : sig
    type trace_mode =
      | Progressive
      | Omniscient
          (** [Progressive]: emit constraint events as they are added.
              [Omniscient]: emit them after constraint solving completes. *)

    val trace : bool ref
    (** Enable reconstruction tracing. *)

    val trace_mode : trace_mode ref
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Execution-trace settings} *)

  module Trace : sig
    type 'a spec =
      | None
      | Some of 'a list
      | All
          (** [None] = no tracing; [Some ids] = trace named clauses/families;
              [All] = trace every clause/family. *)

    val trace : string spec -> unit
    (** Set the trace specification. *)

    val break : string spec -> unit
    (** Set the breakpoint specification. *)

    val detail : int ref
    (** Trace detail level: 0 = none, 1 = default, 2 = unification steps. *)

    val show : unit -> unit
    (** Display current trace / break / detail settings. *)

    val reset : unit -> unit
    (** Clear all trace settings. *)
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Timers} *)

  module Timers : sig
    val show : unit -> unit
    (** Print accumulated timings. *)

    val reset : unit -> unit
    (** Reset all timers. *)

    val check : unit -> unit
    (** Display timings without resetting them. *)
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Compilation / optimisation} *)

  module Compile : sig
    type opt = No | Linear_heads | Indexing

    val optimize : opt ref
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Meta-theorem prover} *)

  module Prover : sig
    type strategy =
      | Rfs
      | Frs
          (** [Rfs] = Recursion-Filling-Splitting; [Frs] =
              Filling-Recursion-Splitting. *)

    val strategy : strategy ref
    (** Proof-search strategy (default: [Frs]). *)

    val max_split : int ref
    (** Bound on case-splitting per step (default: 2). *)

    val max_recurse : int ref
    (** Bound on recursive unfolding per step (default: 10). *)
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Tabling (memoisation for [%querytabled])} *)

  module Table : sig
    type strategy = Variant | Subsumption

    val strategy : strategy ref
    val strengthen : bool ref

    val reset_global_table : unit -> unit
    (** Discard the global tabling memo table. *)

    val top : unit -> unit
    (** Enter the interactive tabled-query loop. *)
  end

  (* -------------------------------------------------------------------- *)
  (** {1 OS utilities} *)

  module OS : sig
    val chdir : string -> unit
    val getdir : unit -> string
    val exit : unit -> unit
  end

  (* -------------------------------------------------------------------- *)
  (** {1 REPL options store} *)

  module Options : sig
    val get : string -> string option
    (** Retrieve a named runtime option. *)

    val set : string -> string -> unit
    (** Assign a named runtime option. *)
  end

  (* -------------------------------------------------------------------- *)
  (** {1 Interactive evaluation} *)

  module Eval : sig
    val eval : Cst.cmd -> unit
    (** Evaluate a single parsed command (used by REPL and LSP handlers). *)
  end

  val version : string
  (** Human-readable version string. *)

  val run : unit -> unit
  (** Complete top-level entry point: parse argv and dispatch to REPL / file
      loading. *)
end
