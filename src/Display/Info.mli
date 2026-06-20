type src =
  | Approx
  | Check
  | Compile
  | Typecheck
  | Unify
  | Cover
  | Parse
  | Reduce
  | Meta
  | Pal
  | Default
  | Recon
  | Prove
  | Total

type kind = Debug | Info | Warning | Error | Response

(* Corresponds to chatter 5 4 3 2 1 0, respectively *)
type level = Exhaustive | Detailed | Normal | Terse | Minimal | Off

module Form : module type of Form.Form

type form = Form.t

val from_chatter : int -> level

type t = { src : src option; kind : kind option; level : level; msg : form }

val msg : ?src:src -> ?kind:kind -> ?level:level -> form -> t
val to_int : level -> int
val ( >= ) : level -> level -> bool
val ( > ) : level -> level -> bool
val ( =< ) : level -> level -> bool
val ( < ) : level -> level -> bool
