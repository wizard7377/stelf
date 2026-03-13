(* # 1 "src/table/string_hash.sig.ml" *)
open! Basis

(* String Hash Table *)
(* Author: Frank Pfenning *)
module type STRING_HASH = sig
  val stringHash : string -> int
end

(* # 1 "src/table/string_hash.fun.ml" *)

(* # 1 "src/table/string_hash.sml.ml" *)
open! Basis

(* String Hash Table *)
(* Author: Frank Pfenning *)
module StringHash : STRING_HASH = struct
  let rec stringHash s =
    let rec num i = Char.ord (String.sub (s, i)) mod 128 in
    let n = String.size s in
    begin if n = 0 then 0
    else
      let a = n - 1 in
      let b = Int.div (n, 2) in
      let c = Int.div (b, 2) in
      let d = b + c in
      num a + (128 * (num b + (128 * (num c + (128 * num d)))))
    end
  (* sample 4 characters from string *)
end
(* structure StringHash *)
