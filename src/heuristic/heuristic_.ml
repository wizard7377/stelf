(* # 1 "src/heuristic/heuristic_.sig.ml" *)

open Basis

(* Heuristics : Version 1.3 *)

(** Author: Carsten Schuermann *)
module type HEURISTIC = sig
  type nonrec __0 = {
    sd : int;
    ind : int option;
    c : int;
    m : int;
    r : int;
    p : int;
  }

  type nonrec index = __0

  val compare : index * index -> order
  (** Position (left to right) *)

  val indexToString : index -> string
end
(* signature HEURISTIC *)

(* # 1 "src/heuristic/heuristic_.fun.ml" *)

(* Heuristics : Version 1.3 *)
(* Author: Carsten Schuermann *)
module Heuristic : HEURISTIC = struct
  type nonrec __0 = {
    sd : int;
    ind : int option;
    c : int;
    m : int;
    r : int;
    p : int;
  }

  type nonrec index = __0

  (* Position (left to right) *)
  open! struct
    (* Workaround: int_compare returns Basis__General.order instead of order *)
    let int_compare (a, b) =
      if a < b then Less else if a = b then Equal else Greater

    let compare = function
      | ( { sd = k1; ind = None; c = c1; m = m1; r = r1; p = p1 },
          { sd = k2; ind = None; c = c2; m = m2; r = r2; p = p2 } ) -> begin
          match
            ( int_compare (c1 * m2, c2 * m1),
              int_compare (k2, k1),
              int_compare (r1, r2),
              int_compare (p1, p2) )
          with
          | Equal, Equal, Equal, result -> result
          | Equal, Equal, result, _ -> result
          | Equal, result, _, _ -> result
          | result, _, _, _ -> result
        end
      | ( { sd = _k1; ind = None; c = c1; m = m1; r = _r1; p = _p1 },
          { sd = _k2; ind = Some _i2; c = c2; m = m2; r = _r2; p = _p2 } ) ->
        begin
          match int_compare (c1 * m2, c2 * m1) with
          | Less -> Less
          | Equal -> Greater
          | Greater -> Greater
        end
      | ( { sd = _k1; ind = Some _i1; c = c1; m = m1; r = _r1; p = _p1 },
          { sd = _k2; ind = None; c = c2; m = m2; r = _r2; p = _p2 } ) -> begin
          match int_compare (c1 * m2, c2 * m1) with
          | Less -> Less
          | Equal -> Less
          | Greater -> Greater
        end
      | ( { sd = k1; ind = Some i1; c = c1; m = m1; r = r1; p = p1 },
          { sd = k2; ind = Some i2; c = c2; m = m2; r = r2; p = p2 } ) -> begin
          match
            ( int_compare (c1 * m2, c2 * m1),
              int_compare (k2, k1),
              int_compare (r1, r2),
              int_compare (i1, i2),
              int_compare (p1, p2) )
          with
          | Equal, Equal, Equal, Equal, result -> result
          | Equal, Equal, Equal, result, _ -> result
          | Equal, Equal, result, _, _ -> result
          | Equal, result, _, _, _ -> result
          | result, _, _, _, _ -> result
        end

    let recToString = function 0 -> "non-rec" | 1 -> "rec"

    (* TODO: Real.fmt not available in Basis *)
    let realFmt r = Printf.sprintf "%.2f" r

    (* NOTE: Real.( + ) and Real.( / ) are int->int->int due to basis bug; use Stdlib float ops *)
    let ratio (c, m) = Real.fromInt c /. Real.fromInt m

    let sum = function
      | { sd = k1; ind = None; c = c1; m = m1; r = r1; p = _p1 } ->
          realFmt (Real.fromInt k1 +. ratio (m1, c1) +. Real.fromInt r1)
      | { sd = k1; ind = Some i1; c = c1; m = m1; r = r1; p = _p1 } ->
          realFmt
            (Real.fromInt k1
            +. ratio (1, i1)
            +. ratio (m1, c1)
            +. Real.fromInt r1)

    let indexToString = function
      | { sd = s1; ind = None; c = c1; m = m1; r = r1; p = p1 } ->
          ((((((((((((("(c/m=" ^ Int.toString c1) ^ "/") ^ Int.toString m1)
                   ^ "=")
                  ^ realFmt (ratio (c1, m1)))
                 ^ ", ind=., sd=")
                ^ Int.toString s1)
               ^ ", ")
              ^ recToString r1)
             ^ ", p=")
            ^ Int.toString p1)
           ^ "sum = ")
          ^ sum { sd = s1; ind = None; c = c1; m = m1; r = r1; p = p1 })
          ^ " )"
      | { sd = s1; ind = Some idx; c = c1; m = m1; r = r1; p = p1 } ->
          ((((((((((((((("(c/m=" ^ Int.toString c1) ^ "/") ^ Int.toString m1)
                     ^ "=")
                    ^ realFmt (ratio (c1, m1)))
                   ^ ", ind=")
                  ^ Int.toString idx)
                 ^ ", sd=")
                ^ Int.toString s1)
               ^ ", ")
              ^ recToString r1)
             ^ ", p=")
            ^ Int.toString p1)
           ^ " sum = ")
          ^ sum { sd = s1; ind = Some idx; c = c1; m = m1; r = r1; p = p1 })
          ^ ")"
  end

  let compare = compare
  let indexToString = indexToString
end
(* functor Heuristic *)

(* # 1 "src/heuristic/heuristic_.sml.ml" *)
