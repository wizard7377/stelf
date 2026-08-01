open! Basis
open! Global
open! Global.Global_
open! Trail
open! Trail.Trail_
open! Table
open! Table.Table_

(* # 1 "src/lambda/Fgnopn.sig.ml" *)
open! Basis

(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)

module type FGN_OPN = sig
  type nonrec csid = int
  type nonrec rep = exn
  type arg
  type result
  type nonrec func = rep -> arg -> result

  val install : csid -> func -> unit
  val apply : csid -> rep -> arg -> result
end
