(* # 1 "src/lambda/Fgnopntable.sig.ml" *)

(* # 1 "src/lambda/Fgnopntable.fun.ml" *)
open! Basis
open Fgnopn

module FgnOpnTable (FgnOpnTable__0 : sig
  (* Extensible operation on foreign matter *)
  (* Author: Aleksey Kliger *)
  type arg
  type result
end) :
  FGN_OPN
    with type arg = FgnOpnTable__0.arg
     and type result = FgnOpnTable__0.result = struct
  open FgnOpnTable__0

  type nonrec csid = int
  type nonrec rep = exn
  type nonrec arg = arg
  type nonrec result = result
  type nonrec func = rep -> arg -> result
  type nonrec table = func array

  let rec initializeTable tbl =
    let exception CSfunNotInstalled of csid in
    let maxCSid = 50 in
    let rec unimplemented csid = function
      | _ -> raise (CSfunNotInstalled csid)
    in
    Array.tabulate (maxCSid + 1, unimplemented)
  (*Global.maxCSid*)

  let table : table = initializeTable ()
  let rec install (csid, f) = Array.update (table, csid, f)
  let rec apply (csid, rep) = Array.sub (table, csid) rep
end

(* # 1 "src/lambda/Fgnopntable.sml.ml" *)
