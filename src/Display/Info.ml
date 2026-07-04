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

let from_chatter x =
  assert (x >= 0);
  match x with
  | 0 -> Off
  | 1 -> Minimal
  | 2 -> Terse
  | 3 -> Normal
  | 4 -> Detailed
  | _ -> Exhaustive

type form = Format.formatter -> unit
type t = { src : src option; kind : kind option; level : level; msg : form }

let msg ?(src : src option) ?(kind : kind option) ?(level = Normal) (fmt : form)
    : t =
  { src; kind; level; msg = fmt }

let to_int : level -> int = function
  | Off -> 0
  | Minimal -> 1
  | Terse -> 2
  | Normal -> 3
  | Detailed -> 4
  | Exhaustive -> 5

let ( >= ) x y = to_int x >= to_int y
let ( > ) x y = to_int x > to_int y
let ( =< ) x y = to_int x <= to_int y
let ( < ) x y = to_int x < to_int y
