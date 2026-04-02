(* # 1 "src/frontend/Twelf_.sig.ml" *)
open! Basis

(* Front End Interface *)
(* Author: Frank Pfenning *)
module type STELF = sig
  module Names : NAMES
  module Parser : Parser.PARSER with module Names = Names

  module Print : sig
    val implicit : bool ref

    val printInfix : bool ref
    (** false, print implicit args *)

    val depth : int option ref
    (** false, print fully explicit form infix when possible *)

    val length : int option ref
    (** NONE, limit print depth *)

    val indent : int ref
    (** NONE, limit argument length *)

    val width : int ref
    (** 3, indentation of subterms *)

    val noShadow : bool ref
    (** 80, line width *)

    val sgn : unit -> unit
    (** if true, don't print shadowed constants as ""%const%"" *)

    val prog : unit -> unit
    (** print signature *)

    val subord : unit -> unit
    (** print signature as program *)

    val def : unit -> unit
    (** print subordination relation *)

    val domains : unit -> unit
    (** print information about definitions *)

    (** print available constraint domains *)
    module TeX : sig
      val sgn : unit -> unit
      (** print in TeX format *)

      val prog : unit -> unit
      (** print signature *)
    end
  end

  (** print signature as program *)
  module Trace : sig
    type 'a spec = None | Some of 'a list | All

    (* trace and breakpoint spec:
       no tracing (default) | list of clauses/families | all clauses/families *)
    val trace : string spec -> unit

    val break : string spec -> unit
    (** trace clauses and families *)

    val detail : int ref
    (** break at clauses and families *)

    val show : unit -> unit
    (** 0 = none, 1 = default, 2 = unify *)

    val reset : unit -> unit
    (** show trace, break, and detail *)
  end

  (** reset trace, break, and detail *)
  module Table : sig
    type strategy = Variant | Subsumption

    val strategy : strategy ref
    (** Variant | Subsumption *)

    val strengthen : bool ref
    (** strategy used for %querytabled *)

    val resetGlobalTable : unit -> unit
    (** strengthenng used %querytabled *)

    val top : unit -> unit
    (** reset global table *)
  end

  (** top-level for interactive tabled queries *)
  module Timers : sig
    val show : unit -> unit

    val reset : unit -> unit
    (** show and reset timers *)

    val check : unit -> unit
    (** reset timers *)
  end

  (** display, but not no reset *)
  module OS : sig
    val chDir : string -> unit

    val getDir : unit -> string
    (** change working directory *)

    val exit : unit -> unit
    (** get working directory *)
  end

  (** exit Stelf and ML *)
  module Compile : sig
    type opt = No | LinearHeads | Indexing

    val optimize : opt ref
  end

  module Recon : sig
    type traceMode = Progressive | Omniscient

    val trace : bool ref
    val traceMode : traceMode ref
  end

  module Prover : sig
    type strategy = Rfs | Frs

    val strategy : strategy ref
    (** F=Filling, R=Recursion, S=Splitting *)

    val maxSplit : int ref
    (** FRS, strategy used for %prove *)

    val maxRecurse : int ref
    (** 2, bound on splitting *)
  end

  val chatter : int ref
  (** 10, bound on recursion *)

  val doubleCheck : bool ref
  (** 3, chatter level *)

  val unsafe : bool ref
  (** false, check after reconstruction *)

  val autoFreeze : bool ref
  (** false, allows %assert *)

  val timeLimit : Time.time option ref
  (** false, freezes families in meta-theorems *)

  (** NONEe, allows timeLimit in seconds *)
  type status = Ok | Abort

  val reset : unit -> unit
  (** return status *)

  val loadFile : string -> status
  (** reset global signature *)

  val loadString : string -> status
  (** load file *)

  val readDecl : unit -> status
  (** load string *)

  val decl : string -> status
  (** read declaration interactively *)

  val top : unit -> unit
  (** print declaration of constant *)

  (** top-level for interactive queries *)
  module Config : sig
    type config

    val suffix : string ref
    (** configuration *)

    val read : string -> config
    (** suffix of configuration files *)

    val readWithout : string * config -> config
    (** read config file *)

    val load : config -> status
    (** read config file, minus contents of another *)

    val append : config -> status
    (** reset and load configuration *)

    val define : string list -> config
    (** load configuration (w/o reset) *)
  end

  val make : string -> status
  (** explicitly define configuration *)

  val install1 : string * (Parser.fileParseResult * Paths.region) -> unit

  (* read and load configuration *)
  val version : string
end

(* Stelf version *)
(* signature STELF *)

