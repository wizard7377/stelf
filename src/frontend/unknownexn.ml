(* # 1 "src/frontend/unknownexn.sig.ml" *)
open! Basis
include Unknownexn_intf
(* # 1 "src/frontend/unknownexn.fun.ml" *)
open! Basis

(* Print an informative message on receipt of an unhandled exception. *)
module MakeUnknownExn (UnknownExn__0 : sig
  val exnHistory : exn -> string list
end) : UNKNOWN_EXN = struct
  let rec unknownExn exn =
    let history = rev (UnknownExn__0.exnHistory exn) in
    let rec wrap1 x = ("  raised at: " ^ x) ^ "\n" in
    let rec wrapn x = ("             " ^ x) ^ "\n" in
    concat
      ("Unrecognized exception " :: exnName exn :: "\n"
      :: begin match history with
      | [] -> [ "" ]
      | x :: xs -> wrap1 x :: map wrapn xs
      end)
end

(* # 1 "src/frontend/unknownexn.sml.ml" *)
