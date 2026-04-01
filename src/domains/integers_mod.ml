(* # 1 "src/domains/integers_mod.sig.ml" *)

(* # 1 "src/domains/integers_mod.fun.ml" *)
open Basis
open Field

(* Integers Modulo a Prime Number *)
(* Author: Roberto Virga *)
module IntegersMod (IntegersMod__0 : sig
  val p : int
end) : FIELD = struct
  open IntegersMod__0

  let name = "integer" ^ Int.toString p

  type nonrec number = int

  let normalize n = n mod p
  let zero = 0
  let one = 1

  exception Div

  let ( ~- ) n = Int.( - ) p n
  let ( + ) m n = normalize (Int.( + ) m n)
  let ( - ) m n = normalize (Int.( - ) m n)
  let ( * ) m n = normalize (Int.( * ) m n)

  let inverse = function
    | 0 -> raise Div
    | n ->
        let rec inverse' i =
          begin if normalize (Int.( * ) n i) = 1 then i
          else inverse' (Int.( + ) i 1)
          end
        in
        inverse' 1
  (* alternative: compute n^(p-2) *)

  let fromInt n = normalize n

  let fromString str =
    let check = List.all Char.isDigit in
    begin if check (String.explode str) then begin
      match Int.fromString str with
      | Some n -> begin if n < p then Some n else None end
      | None -> None
    end
    else None
    end

  let toString = Int.toString
end
(* functor IntegersMod *)

(* # 1 "src/domains/integers_mod.sml.ml" *)
