(* # 1 "src/lambda/fgnopn.sig.ml" *)
open! Basis

(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)
module type FGN_OPN = sig
  type nonrec csid = int
  type nonrec rep = exn
  type nonrec arg
  type nonrec result
  type nonrec func = rep -> arg -> result

  val install : csid * func -> unit
  val apply : csid * rep -> arg -> result
end

(* # 1 "src/lambda/fgnopn.fun.ml" *)

(* # 1 "src/lambda/fgnopn.sml.ml" *)
