open! Basis;;
(* Heuristics : Version 1.3 *);;
(* Author: Carsten Schuermann *);;
module Heuristic : HEURISTIC =
  struct
    type nonrec __0 = { sd: int ; ind: int option ; c: int ; m: int ;
      r: int ; p: int };;
    type nonrec index = __0;;
    (* Position (left to right) *);;
    open!
      struct
        let rec recToString = function 
                                       | 0 -> "non-rec = 2"
                                       | 1 -> "rec = 1";;
        let rec realFmt r = Real.fmt ((StringCvt.FIX ((Some 2)))) r;;
        let rec ratio =
          function 
                   | (0, 0) -> 1.0
                   | (c, 0) -> 1.1
                   | (c, m) -> (Real.fromInt c) / (Real.fromInt m);;
        let rec sqr ((x : real)) = x * x;;
        let rec sum =
          function 
                   | { sd = k1; ind = None; c = c1; m = m1; r = r1; p = p1}
                       -> begin
                       if c1 = 0 then
                       ((sqr (Real.fromInt k1)) + (5.0 - (ratio (c1, m1)))) +
                         (Real.fromInt r1)
                       else
                       ((sqr (Real.fromInt k1)) + (1.0 - (ratio (c1, m1)))) +
                         (Real.fromInt r1)
                       end
                   | { sd = k1; ind = Some 0; c = c1; m = m1; r = r1; p = p1}
                       -> begin
                       if c1 = 0 then
                       ((sqr (Real.fromInt k1)) + (5.0 - (ratio (c1, m1)))) +
                         (Real.fromInt r1)
                       else
                       (((sqr (Real.fromInt k1)) + (ratio (3, 2))) +
                          (1.0 - (ratio (c1, m1))))
                         + (Real.fromInt r1)
                       end
                   | { sd = k1; ind = Some i1; c = c1; m = m1; r = r1;
                      p = p1} -> begin
                       if c1 = 0 then
                       ((sqr (Real.fromInt k1)) + (5.0 - (ratio (c1, m1)))) +
                         (Real.fromInt r1)
                       else
                       (((sqr (Real.fromInt k1)) + (ratio (1, i1))) +
                          (1.0 - (ratio (c1, m1))))
                         + (Real.fromInt r1)
                       end;;
        let rec conv =
          function 
                   | { sd = k1; ind = i; c = c1; m = m1; r = 1; p = p1}
                       -> { sd = k1; ind = i; c = c1; m = m1; r = 1; p = p1} 
                   | { sd = k1; ind = i; c = c1; m = m1; r = 0; p = p1}
                       -> { sd = k1; ind = i; c = c1; m = m1; r = 2; p = p1} ;;
        let rec ccompare
          ({ sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1},
           { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2})
          =
          begin
          match (Real.compare
                 (sum { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2} ,
                  sum { sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1} ),
                 Int.compare (p1, p2))
          with 
               | (Equal, result) -> result
               | (result, _) -> result
          end;;
        let rec compare
          ({ sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1},
           { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2})
          =
          ccompare
          (conv { sd = k1; ind = i1; c = c1; m = m1; r = r1; p = p1} ,
           conv { sd = k2; ind = i2; c = c2; m = m2; r = r2; p = p2} );;
        let rec indexToString =
          function 
                   | { sd = s1; ind = None; c = c1; m = m1; r = 0; p = p1}
                       -> ((((((((((((((((("(sd * r =" ^
                                             (Int.toString (s1 * 3)))
                                            ^ ", sd=")
                                           ^ (Int.toString s1))
                                          ^ ", ")
                                         ^ (recToString 0))
                                        ^ " = 2")
                                       ^ ", c/m=")
                                      ^ (Int.toString c1))
                                     ^ "/")
                                    ^ (Int.toString m1))
                                   ^ "=")
                                  ^ (realFmt (1.0 - (ratio (c1, m1)))))
                                 ^ ", ind=.,")
                                ^ ", p=")
                               ^ (Int.toString p1))
                              ^ " sum = ")
                             ^
                             (realFmt
                              (sum
                               {
                               sd = s1;
                               ind = None;
                               c = c1;
                               m = m1;
                               r = 2;
                               p = p1}
                               )))
                            ^ " )"
                   | { sd = s1; ind = None; c = c1; m = m1; r = 1; p = p1}
                       -> ((((((((((((((((("(sd * r =" ^
                                             (Int.toString (s1 * 1)))
                                            ^ ", sd=")
                                           ^ (Int.toString s1))
                                          ^ ", ")
                                         ^ (recToString 1))
                                        ^ " = 1")
                                       ^ ", c/m=")
                                      ^ (Int.toString c1))
                                     ^ "/")
                                    ^ (Int.toString m1))
                                   ^ "=")
                                  ^ (realFmt (1.0 - (ratio (c1, m1)))))
                                 ^ ", ind=.,")
                                ^ ", p=")
                               ^ (Int.toString p1))
                              ^ " sum = ")
                             ^
                             (realFmt
                              (sum
                               {
                               sd = s1;
                               ind = None;
                               c = c1;
                               m = m1;
                               r = 1;
                               p = p1}
                               )))
                            ^ " )"
                   | { sd = s1; ind = Some idx; c = c1; m = m1; r = 0;
                      p = p1}
                       -> let i = begin
                            if idx = 0 then 0.0 else ratio (1, idx) end
                            in (((((((((((((((((((("(sd * r =" ^
                                                     (Int.toString (s1 * 3)))
                                                    ^ ", sd=")
                                                   ^ (Int.toString s1))
                                                  ^ ", ")
                                                 ^ (recToString 0))
                                                ^ " = 2")
                                               ^ ", c/m=")
                                              ^ (Int.toString c1))
                                             ^ "/")
                                            ^ (Int.toString m1))
                                           ^ "=")
                                          ^
                                          (realFmt (1.0 - (ratio (c1, m1)))))
                                         ^ ", ind=")
                                        ^ (Int.toString idx))
                                       ^ " = ")
                                      ^ (realFmt i))
                                     ^ ", p=")
                                    ^ (Int.toString p1))
                                   ^ " sum = ")
                                  ^
                                  (realFmt
                                   (sum
                                    {
                                    sd = s1;
                                    ind = (Some idx);
                                    c = c1;
                                    m = m1;
                                    r = 2;
                                    p = p1}
                                    )))
                                 ^ ")"
                   | { sd = s1; ind = Some idx; c = c1; m = m1; r = 1;
                      p = p1}
                       -> let i = begin
                            if idx = 0 then 0.0 else ratio (1, idx) end
                            in (((((((((((((((((((("(sd * r =" ^
                                                     (Int.toString (s1 * 1)))
                                                    ^ ", sd=")
                                                   ^ (Int.toString s1))
                                                  ^ ", ")
                                                 ^ (recToString 1))
                                                ^ " =  1")
                                               ^ ", c/m=")
                                              ^ (Int.toString c1))
                                             ^ "/")
                                            ^ (Int.toString m1))
                                           ^ "=")
                                          ^
                                          (realFmt (1.0 - (ratio (c1, m1)))))
                                         ^ ", ind=")
                                        ^ (Int.toString idx))
                                       ^ " = ")
                                      ^ (realFmt i))
                                     ^ ", p=")
                                    ^ (Int.toString p1))
                                   ^ " sum = ")
                                  ^
                                  (realFmt
                                   (sum
                                    {
                                    sd = s1;
                                    ind = (Some idx);
                                    c = c1;
                                    m = m1;
                                    r = 1;
                                    p = p1}
                                    )))
                                 ^ ")";;
        end;;
    (* sum of the parameters k1 + m1/c1 + 1/ind + r1 *);;
    (* the higher the sum the more preferred it is;  *);;
    (* - bp Sep 21 1999 - weight splitting depth higher *);;
    (* associate a higher value to non-rec than to rec  *);;
    (* p                 *);;
    let compare = compare;;
    let indexToString = indexToString;;
    end;;
(* functor Heuristic *);;