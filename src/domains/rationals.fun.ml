open! Basis;;
(* Rationals *);;
(* Author: Roberto Virga *);;
module Rationals(Integers: INTEGERS) : RATIONALS =
  struct
    module Integers = Integers;;
    let name = "rational";;
    exception Div = Div;;
    open!
      struct
        module I = Integers;;
        type number = | Fract of Int.int * I.int * I.int ;;
        let zero = (Fract (0, I.fromInt 0, I.fromInt 1));;
        let one = (Fract (1, I.fromInt 1, I.fromInt 1));;
        exception Div ;;
        let rec normalize =
          function 
                   | Fract (0, _, _) -> zero
                   | Fract (s, n, d)
                       -> let rec gcd (m, n) = begin
                            if m = (I.fromInt 0) then n else begin
                            if n = (I.fromInt 0) then m else begin
                            if (I.( > ) (m, n)) then
                            gcd (I.( mod ) (m, n), n) else
                            gcd (m, I.( mod ) (n, m)) end end end
                            in let g = gcd (n, d)
                                 in (Fract (s, I.div (n, g), I.div (d, g)));;
        let rec ( ~- ) (Fract (s, n, d)) = (Fract ((Int.( ~- ) s), n, d));;
        let rec ( + ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let n =
            (I.( + )
             ((I.( * ) ((I.( * ) (I.fromInt s1, n1)), d2)),
              (I.( * ) ((I.( * ) (I.fromInt s2, n2)), d1))))
            in normalize ((Fract (I.sign n, I.abs n, (I.( * ) (d1, d2)))));;
        let rec ( - ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          let n =
            (I.( - )
             ((I.( * ) ((I.( * ) (I.fromInt s1, n1)), d2)),
              (I.( * ) ((I.( * ) (I.fromInt s2, n2)), d1))))
            in normalize ((Fract (I.sign n, I.abs n, (I.( * ) (d1, d2)))));;
        let rec ( * ) (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          normalize
          ((Fract
            ((Int.( * ) (s1, s2)), (I.( * ) (n1, n2)), (I.( * ) (d1, d2)))));;
        let rec inverse =
          function 
                   | Fract (0, _, _) -> raise Div
                   | Fract (s, n, d) -> (Fract (s, d, n));;
        let rec sign (Fract (s, n, d)) = s;;
        let rec numerator (Fract (s, n, d)) = n;;
        let rec denominator (Fract (s, n, d)) = d;;
        let rec abs (Fract (s, n, d)) = (Fract (Int.abs s, n, d));;
        let rec compare (Fract (s1, n1, d1), Fract (s2, n2, d2)) =
          I.compare
          ((I.( * ) ((I.( * ) (I.fromInt s1, n1)), d2)),
           (I.( * ) ((I.( * ) (I.fromInt s2, n2)), d1)));;
        let rec ( > ) (q1, q2) = (compare (q1, q2)) = GREATER;;
        let rec ( < ) (q1, q2) = (compare (q1, q2)) = LESS;;
        let rec ( >= ) (q1, q2) = (q1 = q2) || (q1 > q2);;
        let rec ( <= ) (q1, q2) = (q1 = q2) || (q1 < q2);;
        let rec fromInt n =
          (Fract (Int.sign n, I.fromInt (Int.abs n), I.fromInt 1));;
        let rec fromString str =
          let rec check_numerator =
            function 
                     | ((c :: chars') as chars) -> begin
                         if c = '~' then List.all Char.isDigit chars' else
                         List.all Char.isDigit chars end
                     | [] -> false
            in let rec check_denominator chars = List.all Char.isDigit chars
                 in let fields = String.fields (function 
                                                         | c -> c = '/') str
                      in begin
                      if (List.length fields) = 1 then
                      let numerator = List.nth (fields, 0) in begin
                        if check_numerator (String.explode numerator) then
                        begin
                        match I.fromString numerator
                        with 
                             | Some n
                                 -> (Some
                                     ((Fract
                                       (I.sign n, I.abs n, I.fromInt 1))))
                             | _ -> None
                        end else None end
                      else begin
                      if (List.length fields) = 2 then
                      let numerator = List.nth (fields, 0)
                        in let denominator = List.nth (fields, 1) in begin
                             if
                             (check_numerator (String.explode numerator)) &&
                               (check_denominator
                                (String.explode denominator))
                             then
                             begin
                             match (I.fromString numerator,
                                    I.fromString denominator)
                             with 
                                  | (Some n, Some d)
                                      -> (Some
                                          (normalize
                                           ((Fract (I.sign n, I.abs n, d)))))
                                  | _ -> None
                             end else None end
                      else None end end;;
        let rec toString (Fract (s, n, d)) =
          let nStr = I.toString ((I.( * ) (I.fromInt s, n)))
            in let dStr = I.toString d in begin
                 if d = (I.fromInt 1) then nStr else (nStr ^ "/") ^ dStr end;;
        let rec fromInteger n = (Fract (I.sign n, I.abs n, I.fromInt 1));;
        let rec floor ((Fract (s, n, d) as q)) = begin
          if (Int.( >= ) (s, 0)) then I.quot (n, d) else
          (Integers.( ~- ) (ceiling (- q))) end
        and ceiling ((Fract (s, n, d) as q)) = begin
          if (Int.( >= ) (s, 0)) then
          I.quot ((I.( + ) (n, (I.( - ) (d, I.fromInt 1)))), d) else
          (Integers.( ~- ) (floor (- q))) end;;
        end;;
    (* Rational number:              *);;
    (* q := Fract (sign, num, denom) *);;
    type nonrec number = number;;
    let zero = zero;;
    let one = one;;
    let ( ~- ) = ( ~- );;
    let ( + ) x__op y__op = x__op + y__op;;
    let ( - ) x__op y__op = x__op - y__op;;
    let ( * ) x__op y__op = x__op * y__op;;
    let inverse = inverse;;
    let fromInt = fromInt;;
    let fromString = fromString;;
    let toString = toString;;
    let sign = sign;;
    let abs = abs;;
    let ( > ) x__op y__op = x__op > y__op;;
    let ( < ) x__op y__op = x__op < y__op;;
    let ( >= ) x__op y__op = x__op >= y__op;;
    let ( <= ) x__op y__op = x__op <= y__op;;
    let compare = compare;;
    let fromInteger = fromInteger;;
    let floor = floor;;
    let ceiling = ceiling;;
    let numerator = numerator;;
    let denominator = denominator;;
    end;;
(* structure Rationals *);;