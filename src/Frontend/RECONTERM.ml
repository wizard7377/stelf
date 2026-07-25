open! Basis

(* External Syntax and Type Reconstruction *)
(* Author: Frank Pfenning *)
(* signature EXTSYN
   provides the interface for type reconstruction as seen
   by the parser
*)
module type EXTSYN = sig
  (*! structure Paths : PATHS !*)
  type term

  (* term *)
  type dec

  (* variable declaration *)
  val lcid : string list * string * Paths.region -> term

  (* lower case id *)
  val ucid : string list * string * Paths.region -> term

  (* upper case id *)
  val quid : string list * string * Paths.region -> term

  (* quoted id, currently not parsed *)
  val scon : string * Paths.region -> term

  (* string constant *)
  (* unconditionally interpreted as such *)
  val evar : string * Paths.region -> term
  val fvar : string * Paths.region -> term
  val typ : Paths.region -> term

  (* type, region for ""type"" *)
  val arrow : term * term -> term

  (* tm -> tm *)
  val backarrow : term * term -> term

  (* tm <- tm *)
  val pi : dec * term -> term

  (* {d} tm *)
  val lam : dec * term -> term

  (* [d] tm *)
  val app : term * term -> term

  (* tm tm *)
  val hastype : term * term -> term

  (* tm : tm *)
  val omitted : Paths.region -> term

  (* _ as object, region for ""_"" *)
  (* region for ""{dec}"" ""[dec]"" etc. *)
  val dec : string option * term * Paths.region -> dec

  (* id : tm | _ : tm *)
  val dec0 : string option * Paths.region -> dec
end

(* id | _  (type omitted) *)
(* signature EXTSYN *)
(* signature RECON_TERM
   provides the interface to type reconstruction seen by Stelf
*)
module type RECON_TERM = sig
  (*! structure IntSyn : INTSYN !*)
  include EXTSYN

  exception Error of string

  val resetErrors : string -> unit

  (* filename -fp *)
  val checkErrors : Paths.region -> unit

  type traceMode = Progressive | Omniscient

  val trace : bool ref
  val traceMode : traceMode ref

  (* Reconstruction jobs *)
  type job

  val jnothing : job
  val jand : job * job -> job
  val jwithctx : dec IntSyn.ctx * job -> job
  val jterm : term -> job
  val jclass : term -> job
  val jof : term * term -> job
  val jof' : term * IntSyn.exp -> job

  type job_ =
    | JNothing
    | JAnd of job_ * job_
    | JWithCtx of IntSyn.dec IntSyn.ctx * job_
    | JTerm of (IntSyn.exp * Paths.occExp) * IntSyn.exp * IntSyn.uni
    | JClass of (IntSyn.exp * Paths.occExp) * IntSyn.uni
    | JOf of
        (IntSyn.exp * Paths.occExp) * (IntSyn.exp * Paths.occExp) * IntSyn.uni

  val recon : job -> job_
  val reconQuery : job -> job_
  val reconWithCtx : IntSyn.dctx * job -> job_
  val reconQueryWithCtx : IntSyn.dctx * job -> job_
  val termRegion : term -> Paths.region
  val decRegion : dec -> Paths.region
  val ctxRegion : dec IntSyn.ctx -> Paths.region option

  (* unimplemented for the moment *)
  val internalInst : 'a -> 'b
  val externalInst : 'a -> 'b
end
