open! Basis;;
(* Front End Interface *);;
(* Author: Frank Pfenning *);;
module type TWELF = sig
                    module Print : sig
                                   val implicit : bool ref
                                   (* false, print implicit args *)
                                   val printInfix : bool ref
                                   (* false, print fully explicit form infix when possible *)
                                   val depth : int option ref
                                   (* NONE, limit print depth *)
                                   val length : int option ref
                                   (* NONE, limit argument length *)
                                   val indent : int ref
                                   (* 3, indentation of subterms *)
                                   val width : int ref
                                   (* 80, line width *)
                                   val noShadow : bool ref
                                   (* if true, don't print shadowed constants as ""%const%"" *)
                                   val sgn : unit -> unit
                                   (* print signature *)
                                   val prog : unit -> unit
                                   (* print signature as program *)
                                   val subord : unit -> unit
                                   (* print subordination relation *)
                                   val def : unit -> unit
                                   (* print information about definitions *)
                                   val domains : unit -> unit
                                   (* print available constraint domains *)
                                   module TeX : sig
                                                (* print in TeX format *)
                                                val sgn : unit -> unit
                                                (* print signature *)
                                                val prog : unit -> unit
                                                end
                                   end
                    (* print signature as program *)
                    module Trace : sig
                                   type 'a spec_ =
                                     | None 
                                     | Some of 'a list 
                                     | All 
                                   (* trace and breakpoint spec *)
                                   (* no tracing, default *)
                                   (* list of clauses and families *)
                                   (* trace all clauses and families *)
                                   val trace : string spec_ -> unit
                                   (* trace clauses and families *)
                                   val break : string spec_ -> unit
                                   (* break at clauses and families *)
                                   val detail : int ref
                                   (* 0 = none, 1 = default, 2 = unify *)
                                   val show : unit -> unit
                                   (* show trace, break, and detail *)
                                   val reset : unit -> unit
                                   end
                    (* reset trace, break, and detail *)
                    module Table : sig
                                   type strategy_ = | Variant 
                                                    | Subsumption 
                                   (* Variant | Subsumption *)
                                   val strategy : strategy_ ref
                                   (* strategy used for %querytabled *)
                                   val strengthen : bool ref
                                   (* strengthenng used %querytabled *)
                                   val resetGlobalTable : unit -> unit
                                   (* reset global table           *)
                                   val top : unit -> unit
                                   end
                    (* top-level for interactive tabled queries *)
                    module Timers : sig
                                    val show : unit -> unit
                                    (* show and reset timers *)
                                    val reset : unit -> unit
                                    (* reset timers *)
                                    val check : unit -> unit
                                    end
                    (* display, but not no reset *)
                    module OS : sig
                                val chDir : string -> unit
                                (* change working directory *)
                                val getDir : unit -> string
                                (* get working directory *)
                                val exit : unit -> unit
                                end
                    (* exit Twelf and ML *)
                    module Compile : sig
                                     type opt_ =
                                       | No 
                                       | LinearHeads 
                                       | Indexing 
                                     val optimize : opt_ ref
                                     end
                    module Recon : sig
                                   type traceMode_ =
                                     | Progressive 
                                     | Omniscient 
                                   val trace : bool ref
                                   val traceMode : traceMode_ ref
                                   end
                    module Prover : sig
                                    type strategy_ = | Rfs 
                                                     | Frs 
                                    (* F=Filling, R=Recursion, S=Splitting *)
                                    val strategy : strategy_ ref
                                    (* FRS, strategy used for %prove *)
                                    val maxSplit : int ref
                                    (* 2, bound on splitting  *)
                                    val maxRecurse : int ref
                                    end
                    (* 10, bound on recursion *)
                    val chatter : int ref
                    (* 3, chatter level *)
                    val doubleCheck : bool ref
                    (* false, check after reconstruction *)
                    val unsafe : bool ref
                    (* false, allows %assert *)
                    val autoFreeze : bool ref
                    (* false, freezes families in meta-theorems *)
                    val timeLimit : Time.time option ref
                    (* NONEe, allows timeLimit in seconds *)
                    type status_ = | Ok 
                                   | Abort 
                    (* return status *)
                    val reset : unit -> unit
                    (* reset global signature *)
                    val loadFile : string -> status_
                    (* load file *)
                    val loadString : string -> status_
                    (* load string *)
                    val readDecl : unit -> status_
                    (* read declaration interactively *)
                    val decl : string -> status_
                    (* print declaration of constant *)
                    val top : unit -> unit
                    (* top-level for interactive queries *)
                    module Config : sig
                                    type nonrec config
                                    (* configuration *)
                                    val suffix : string ref
                                    (* suffix of configuration files *)
                                    val read : string -> config
                                    (* read config file *)
                                    val
                                      readWithout : (string * config) ->
                                                    config
                                    (* read config file, minus contents of another *)
                                    val load : config -> status_
                                    (* reset and load configuration *)
                                    val append : config -> status_
                                    (* load configuration (w/o reset) *)
                                    val define : string list -> config
                                    end
                    (* explicitly define configuration *)
                    val make : string -> status_
                    (* read and load configuration *)
                    val version : string
                    end;;
(* Twelf version *);;
(* signature TWELF *);;