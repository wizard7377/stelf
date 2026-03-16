(* # 1 "src/domains/field.sig.ml" *)

open Basis
open Int_inf
open Int_inf.Int_inf_

(* Field *)
(* Author: Roberto Virga *)
module type FIELD = sig
  (* Name of the set *)
  val name : string

  (* Main type *)
  type nonrec number

  (* Non-invertible element *)
  exception Div

  (* Constants *)
  val zero : number
  val one : number

  (* Operators *)
  val ( ~- ) : number -> number
  val ( + ) : number -> number -> number
  val ( - ) : number -> number -> number
  val ( * ) : number -> number -> number
  val inverse : number -> number

  (* raises Div *)
  (* Conversions *)
  val fromInt : int -> number
  val fromString : string -> number option
  val toString : number -> string
end
(* signature FIELD *)

(* # 1 "src/domains/field.fun.ml" *)

(* # 1 "src/domains/field.sml.ml" *)
