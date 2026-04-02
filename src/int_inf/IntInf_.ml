(* # 1 "src/int_inf/IntInf_.sig.ml" *)

(* # 1 "src/int_inf/IntInf_.fun.ml" *)

(* # 1 "src/int_inf/IntInf_.sml.ml" *)
open Basis
open IntInfSig

(* int-inf.sml
 *
 * COPYRIGHT (c) 1995 by AT&T Bell Laboratories. See COPYRIGHT file for details.
 *
 * This package is derived from Andrzej Filinski's bignum package.  It is versy
 * close to the definition of the optional IntInf structure in the SML'97 basis.
 * 
 * It is implemented almost totally on the abstraction presented by
 * the BigNat structure. The only concrete type information it assumes 
 * is that BigNat.bignat = 'a list and that BigNat.zero = [].
 * Some trivial additional efficiency could be obtained by assuming that
 * type bignat is really int list, and that if (v : bignat) = [d], then
 * bignat d = [d].
 *
 * At some point, this should be reimplemented to make use of Word32, or
 * have compiler/runtime support.
 *
 * Also, for booting, this module could be broken into one that has
 * all the types and arithmetic functions, but doesn't use NumScan,
 * constructing values from strings using bignum arithmetic. Various
 * integer and word scanning, such as NumScan, could then be constructed 
 * from IntInf. Finally, a user-level IntInf could be built by 
 * importing the basic IntInf, but replacing the scanning functions
 * by more efficient ones based on the functions in NumScan.
 *
 *)
(* TODO: IntInf requires Word32 and Int31 which are not yet available in the Basis library.
   The full implementation is commented out below and replaced with a stub. *)
module IntInf : INT_INF = struct
  type nonrec int = int

  let precision = Int.precision
  let minInt = Int.minInt
  let maxInt = Int.maxInt
  let toLarge = Int.toLarge
  let fromLarge = Int.fromLarge
  let toInt = Int.toInt
  let fromInt = Int.fromInt
  let ( + ) = Int.( + )
  let ( - ) = Int.( - )
  let ( * ) = Int.( * )
  let div = Int.div
  let mod_ = Int.mod_
  let quot = Int.quot
  let rem = Int.rem
  let ( < ) = Int.( < )
  let ( > ) = Int.( > )
  let ( <= ) = Int.( <= )
  let ( >= ) = Int.( >= )
  let ( ~- ) = Int.( ~- )
  let abs = Int.abs
  let min = Int.min
  let max = Int.max
  let sign = Int.sign
  let sameSign = Int.sameSign
  let compare (a, b) = if a < b then Less else if a = b then Equal else Greater
  let toString = Int.toString
  let scan = Int.scan
  let fromString = Int.fromString
  let fmt = Int.fmt
  let divmod (a, b) = (Int.div (a, b), Int.mod_ (a, b))
  let quotrem (a, b) = (Int.quot (a, b), Int.rem (a, b))

  let rec pow (base, exp) =
    if exp = 0 then 1
    else if exp = 1 then base
    else
      let half = pow (base, Int.div (exp, 2)) in
      if Int.mod_ (exp, 2) = 0 then half * half else half * half * base

  let rec log2 n = if n <= 1 then 0 else 1 + log2 (Int.div (n, 2))
end
(*
    module NumScan : sig
                     val skipWS : ((char, 'a) StringCvt.reader) -> 'a -> 'a
                     val
                       scanWord : StringCvt.radix ->
                                  ((char, 'a) StringCvt.reader) ->
                                  'a ->
                                  (Word32.word * 'a)
                                  option
                     val
                       scanInt : StringCvt.radix ->
                                 ((char, 'a) StringCvt.reader) ->
                                 'a ->
                                 (int * 'a)
                                 option
                     end
      =
      struct
        module W = Word32;;
        module I = Int31;;
        let ( < ) x__op y__op = W.( < ) x__op y__op;;
        let ( >= ) x__op y__op = W.( >= ) x__op y__op;;
        let ( + ) x__op y__op = W.( + ) x__op y__op;;
        let ( - ) x__op y__op = W.( - ) x__op y__op;;
        let ( * ) x__op y__op = W.( * ) x__op y__op;;
        let ( << ) x__op y__op = W.( x__op << y__op );;
        let largestWordDiv10 : Word32.word = 429496729;;
        (* 2^32-1 divided by 10 *);;
        let largestWordMod10 : Word32.word = 5;;
        (* remainder *);;
        let largestNegInt : Word32.word = 1073741824;;
        (* absolute value of ~2^30 *);;
        let largestPosInt : Word32.word = 1073741823;;
        (* 2^30-1 *);;
        type 'a __0 = { getc: (char, 'a) StringCvt.reader };;
        type 'a chr_strm = 'a __0;;
        (* A table for mapping digits to values.  Whitespace characters map to
       * 128, ""+"" maps to 129, ""-"",""~"" map to 130, ""."" maps to 131, and the
       * characters 0-9,A-Z,a-z map to their * base-36 value.  All other
       * characters map to 255.
       *);;
        open!
          struct
            let cvtTable =
              "\255\255\255\255\255\255\255\255\255\128\128\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\128\255\255\255\255\255\255\255\255\255\255\129\255\130\131\255\000\001\002\003\004\005\006\007\b\t\255\255\255\255\255\255\255\n\011\012\r\014\015\016\017\018\019\020\021\022\023\024\025\026\027\028\029\030\031 !\"#\255\255\255\255\255\255\n\011\012\r\014\015\016\017\018\019\020\021\022\023\024\025\026\027\028\029\030\031 !\"#\255\255\255\130\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255";;
            let ord = Char.ord;;
            end;;
        let rec code ((c : char)) =
          W.fromInt (ord (CharVector.sub (cvtTable, ord c)));;
        let wsCode : Word32.word = 128;;
        let plusCode : Word32.word = 129;;
        let minusCode : Word32.word = 130;;
        let rec skipWS ((getc : (char, 'a) StringCvt.reader)) cs =
          let rec skip cs =
            begin
            match getc cs
            with 
                 | None -> cs
                 | Some (c, cs') -> begin
                     if (code c) = wsCode then skip cs' else cs end
            end in skip cs;;
        let rec scanPrefix ((getc : (char, 'a) StringCvt.reader)) cs =
          let rec skipWS cs =
            begin
            match getc cs
            with 
                 | None -> None
                 | Some (c, cs')
                     -> let c' = code c in begin
                          if c' = wsCode then skipWS cs' else
                          (Some (c', cs')) end
            end
            in let rec getNext (neg, cs) =
                 begin
                 match getc cs
                 with 
                      | None -> None
                      | Some (c, cs)
                          -> (Some { neg; next = code c; rest = cs} )
                 end
                 in begin
                    match skipWS cs
                    with 
                         | None -> None
                         | Some (c, cs') -> begin
                             if c = plusCode then getNext (false, cs') else
                             begin
                             if c = minusCode then getNext (true, cs') else
                             (Some { neg = false; next = c; rest = cs'} ) end
                             end
                    end;;
        let rec chkOverflow mask w = begin
          if (W.andb (mask, w)) = 0 then () else raise Overflow end;;
        let rec scanBin ((getc : (char, 'a) StringCvt.reader)) cs =
          begin
          match scanPrefix getc cs
          with 
               | None -> None
               | Some { neg; next; rest}
                   -> let rec isDigit ((d : Word32.word)) = d < 2
                        in let chkOverflow = chkOverflow 0x80000000
                             in let rec cvt (w, rest) =
                                  begin
                                  match getc rest
                                  with 
                                       | None
                                           -> (Some { neg; word = w; rest} )
                                       | Some (c, rest')
                                           -> let d = code c in begin
                                                if isDigit d then
                                                begin
                                                  chkOverflow w;
                                                  cvt
                                                  ((W.( (w << 1) + d )),
                                                   rest')
                                                  
                                                  end
                                                else
                                                (Some
                                                 { neg; word = w; rest} )
                                                end
                                  end in begin
                                  if isDigit next then cvt (next, rest) else
                                  None end
          end;;
        let rec scanOct getc cs =
          begin
          match scanPrefix getc cs
          with 
               | None -> None
               | Some { neg; next; rest}
                   -> let rec isDigit ((d : Word32.word)) = d < 8
                        in let chkOverflow = chkOverflow 0xE0000000
                             in let rec cvt (w, rest) =
                                  begin
                                  match getc rest
                                  with 
                                       | None
                                           -> (Some { neg; word = w; rest} )
                                       | Some (c, rest')
                                           -> let d = code c in begin
                                                if isDigit d then
                                                begin
                                                  chkOverflow w;
                                                  cvt
                                                  ((W.( (w << 3) + d )),
                                                   rest')
                                                  
                                                  end
                                                else
                                                (Some
                                                 { neg; word = w; rest} )
                                                end
                                  end in begin
                                  if isDigit next then cvt (next, rest) else
                                  None end
          end;;
        let rec scanDec getc cs =
          begin
          match scanPrefix getc cs
          with 
               | None -> None
               | Some { neg; next; rest}
                   -> let rec isDigit ((d : Word32.word)) = d < 10
                        in let rec cvt (w, rest) =
                             begin
                             match getc rest
                             with 
                                  | None -> (Some { neg; word = w; rest} )
                                  | Some (c, rest')
                                      -> let d = code c in begin
                                           if isDigit d then
                                           begin
                                             begin
                                             if
                                             (w >= largestWordDiv10) &&
                                               ((largestWordDiv10 < w) ||
                                                  (largestWordMod10 < d))
                                             then raise Overflow else () end;
                                             cvt ((10 * w) + d, rest')
                                             end
                                           else
                                           (Some { neg; word = w; rest} ) end
                             end in begin
                             if isDigit next then cvt (next, rest) else None
                             end
          end;;
        let rec scanHex getc cs =
          begin
          match scanPrefix getc cs
          with 
               | None -> None
               | Some { neg; next; rest}
                   -> let rec isDigit ((d : Word32.word)) = d < 16
                        in let chkOverflow = chkOverflow 0xF0000000
                             in let rec cvt (w, rest) =
                                  begin
                                  match getc rest
                                  with 
                                       | None
                                           -> (Some { neg; word = w; rest} )
                                       | Some (c, rest')
                                           -> let d = code c in begin
                                                if isDigit d then
                                                begin
                                                  chkOverflow w;
                                                  cvt
                                                  ((W.( (w << 4) + d )),
                                                   rest')
                                                  
                                                  end
                                                else
                                                (Some
                                                 { neg; word = w; rest} )
                                                end
                                  end in begin
                                  if isDigit next then cvt (next, rest) else
                                  None end
          end;;
        let rec finalWord scanFn getc cs =
          begin
          match scanFn getc cs
          with 
               | None -> None
               | Some { neg = true} -> None
               | Some { neg = false; word; rest} -> (Some (word, rest))
          end;;
        let rec scanWord =
          function 
                   | Bin -> finalWord scanBin
                   | Oct -> finalWord scanOct
                   | Dec -> finalWord scanDec
                   | Hex -> finalWord scanHex;;
        let rec finalInt scanFn getc cs =
          begin
          match scanFn getc cs
          with 
               | None -> None
               | Some { neg = true; word; rest} -> begin
                   if largestNegInt < word then raise Overflow else
                   (Some ((I.( ~- ) (W.toInt word)), rest)) end
               | Some { word; rest} -> begin
                   if largestPosInt < word then raise Overflow else
                   (Some (W.toInt word, rest)) end
          end;;
        let rec scanInt =
          function 
                   | Bin -> finalInt scanBin
                   | Oct -> finalInt scanOct
                   | Dec -> finalInt scanDec
                   | Hex -> finalInt scanHex;;
        end;;
    (** should be to int32 **);;
    module NumFormat : sig
                       val fmtWord : StringCvt.radix -> Word32.word -> string
                       val fmtInt : StringCvt.radix -> int -> string
                       end
      =
      struct
        module W = Word32;;
        module I = Int;;
        let ( < ) x__op y__op = W.( < ) x__op y__op;;
        let ( - ) x__op y__op = W.( - ) x__op y__op;;
        let ( * ) x__op y__op = W.( * ) x__op y__op;;
        let ( >> ) x__op y__op = W.( x__op >> y__op );;
        let div = W.div;;
        let rec mkDigit ((w : Word32.word)) =
          CharVector.sub ("0123456789abcdef", W.toInt w);;
        let rec wordToBin w =
          let rec mkBit w = begin if (W.andb (w, 1)) = 0 then '0' else '1'
            end
            in let rec f =
                 function 
                          | (0, n, l) -> ((I.( + ) (n, 1)), ('0' :: l))
                          | (1, n, l) -> ((I.( + ) (n, 1)), ('1' :: l))
                          | (w, n, l)
                              -> f
                                 ((W.( w >> 1 )), (I.( + ) (n, 1)),
                                  (mkBit w :: l))
                 in f (w, 0, []);;
        let rec wordToOct w =
          let rec f (w, n, l) = begin
            if w < 8 then ((I.( + ) (n, 1)), (mkDigit w :: l)) else
            f
            ((W.( w >> 3 )), (I.( + ) (n, 1)),
             (mkDigit (W.andb (w, 7)) :: l))
            end in f (w, 0, []);;
        let rec wordToDec w =
          let rec f (w, n, l) = begin
            if w < 10 then ((I.( + ) (n, 1)), (mkDigit w :: l)) else
            let j = div w 10
              in f (j, (I.( + ) (n, 1)), (mkDigit (w - (10 * j)) :: l))
            end in f (w, 0, []);;
        let rec wordToHex w =
          let rec f (w, n, l) = begin
            if w < 16 then ((I.( + ) (n, 1)), (mkDigit w :: l)) else
            f
            ((W.( w >> 4 )), (I.( + ) (n, 1)),
             (mkDigit (W.andb (w, 15)) :: l))
            end in f (w, 0, []);;
        let rec fmtW =
          function 
                   | Bin -> fun x -> (fun (_, r) -> r) (wordToBin x)
                   | Oct -> fun x -> (fun (_, r) -> r) (wordToOct x)
                   | Dec -> fun x -> (fun (_, r) -> r) (wordToDec x)
                   | Hex -> fun x -> (fun (_, r) -> r) (wordToHex x);;
        let rec fmtWord radix x = String.implode (fmtW radix x);;
        let rec fmtInt radix =
          let fmtW = fmtW radix
            in let itow = W.fromInt
                 in let rec fmt i = begin
                      if (I.( < ) (i, 0)) then
                      try let digits = fmtW (itow ((I.( ~- ) i)))
                            in String.implode (('~' :: digits))
                      with 
                           | _
                               -> begin
                                  match radix
                                  with 
                                       | Bin
                                           -> "~1111111111111111111111111111111"
                                       | Oct -> "~7777777777"
                                       | Dec -> "~1073741824"
                                       | Hex -> "~3fffffff"
                                  end
                      else String.implode (fmtW (itow i)) end in fmt;;
        end;;
    module BigNat = struct
                      exception Negative ;;
                      let itow = Word.fromInt;;
                      let wtoi = Word.toIntX;;
                      let lgBase = 30;;
                      let nbase = (-0x40000000);;
                      let maxDigit = - (nbase + 1);;
                      let realBase = (real maxDigit) + 1.0;;
                      let lgHBase = Int.quot (lgBase, 2);;
                      let hbase = (Word.( << ) (1, itow lgHBase));;
                      let hmask = hbase - 1;;
                      let rec quotrem (i, j) =
                        (Int.quot (i, j), Int.rem (i, j));;
                      let rec scale i = begin
                        if i = maxDigit then 1 else div nbase (- (i + 1)) end;;
                      type nonrec bignat = int list;;
                      let zero = [];;
                      let one = [1];;
                      let rec bignat =
                        function 
                                 | 0 -> zero
                                 | i
                                     -> let notNbase = Word.notb (itow nbase)
                                          in let rec bn =
                                               function 
                                                        | 0 -> []
                                                        | i
                                                            -> let rec dmbase
                                                                 n =
                                                                 ((Word.
                                                                   ( >> )
                                                                   (n,
                                                                    itow
                                                                    lgBase)),
                                                                  Word.andb
                                                                  (n,
                                                                   notNbase))
                                                                 in let
                                                                    (q, r) =
                                                                    dmbase i
                                                                    in 
                                                                    (wtoi r
                                                                    :: 
                                                                    bn q)
                                               in begin
                                               if i > 0 then begin
                                               if i <= maxDigit then 
                                               [i] else bn (itow i) end else
                                               raise Negative end;;
                      let rec int =
                        function 
                                 | [] -> 0
                                 | (d :: []) -> d
                                 | (d :: (e :: [])) -> (- (nbase * e)) + d
                                 | (d :: r) -> (- (nbase * (int r))) + d;;
                      let rec consd =
                        function 
                                 | (0, []) -> []
                                 | (d, r) -> (d :: r);;
                      let rec hl i =
                        let w = itow i
                          in (wtoi ((Word.( ~>> ) (w, itow lgHBase))),
                              wtoi (Word.andb (w, hmask)));;
                      let rec sh i =
                        wtoi ((Word.( << ) (itow i, itow lgHBase)));;
                      let rec addOne =
                        function 
                                 | [] -> [1]
                                 | (m :: rm)
                                     -> let c = (nbase + m) + 1 in begin
                                          if c < 0 then (c - nbase :: rm)
                                          else (c :: addOne rm) end;;
                      let rec add =
                        function 
                                 | ([], digits) -> digits
                                 | (digits, []) -> digits
                                 | ((dm :: rm), (dn :: rn))
                                     -> addd ((nbase + dm) + dn, rm, rn)
                      and addd (s, m, n) = begin
                        if s < 0 then (s - nbase :: add (m, n)) else
                        (s :: addc (m, n)) end
                      and addc =
                        function 
                                 | (m, []) -> addOne m
                                 | ([], n) -> addOne n
                                 | ((dm :: rm), (dn :: rn))
                                     -> addd
                                        (((nbase + dm) + dn) + 1, rm, rn);;
                      let rec subtOne =
                        function 
                                 | (0 :: mr) -> (maxDigit :: subtOne mr)
                                 | (1 :: []) -> []
                                 | (n :: mr) -> (n - 1 :: mr)
                                 | [] -> raise ((Fail ""));;
                      let rec subt =
                        function 
                                 | (m, []) -> m
                                 | ([], n) -> raise Negative
                                 | ((dm :: rm), (dn :: rn))
                                     -> subd (dm - dn, rm, rn)
                      and subb =
                        function 
                                 | ([], n) -> raise Negative
                                 | ((dm :: rm), []) -> subd (dm - 1, rm, [])
                                 | ((dm :: rm), (dn :: rn))
                                     -> subd ((dm - dn) - 1, rm, rn)
                      and subd (d, m, n) = begin
                        if d >= 0 then consd (d, subt (m, n)) else
                        consd (d - nbase, subb (m, n)) end;;
                      let rec mul2 (m, n) =
                        let (mh, ml) = hl m
                          in let (nh, nl) = hl n
                               in let x = mh * nh
                                    in let y = (mh - ml) * (nh - nl)
                                         in let z = ml * nl
                                              in let (zh, zl) = hl z
                                                   in let (uh, ul) =
                                                        hl
                                                        ((((nbase + x) + z) -
                                                            y)
                                                           + zh)
                                                        in ((x + uh) +
                                                              (wtoi hbase),
                                                            (sh ul) + zl);;
                      let rec muld =
                        function 
                                 | (m, 0) -> []
                                 | (m, 1) -> m
                                 | (m, i)
                                     -> let rec muldc =
                                          function 
                                                   | ([], 0) -> []
                                                   | ([], c) -> [c]
                                                   | ((d :: r), c)
                                                       -> let (h, l) =
                                                            mul2 (d, i)
                                                            in let l1 =
                                                                 (l + nbase)
                                                                   + c
                                                                 in begin
                                                                 if l1 >= 0
                                                                 then
                                                                 (l1
                                                                  :: 
                                                                  muldc
                                                                  (r, h + 1))
                                                                 else
                                                                 (l1 - nbase
                                                                  :: 
                                                                  muldc
                                                                  (r, h))
                                                                 end
                                          in muldc (m, 0);;
                      let rec mult =
                        function 
                                 | (m, []) -> []
                                 | (m, (d :: [])) -> muld (m, d)
                                 | (m, (0 :: r)) -> consd (0, mult (m, r))
                                 | (m, n)
                                     -> let rec muln =
                                          function 
                                                   | [] -> []
                                                   | (d :: r)
                                                       -> add
                                                          (muld (n, d),
                                                           consd (0, muln r))
                                          in muln m;;
                      let rec divmod2 ((u, v), i) =
                        let (vh, vl) = hl v
                          in let (ih, il) = hl i
                               in let rec adj (q, r) = begin
                                    if r < 0 then adj (q - 1, r + i) else
                                    (q, r) end
                                    in let (q1, r1) = quotrem (u, ih)
                                         in let (q1, r1) =
                                              adj
                                              (q1,
                                               ((sh r1) + vh) - (q1 * il))
                                              in let (q0, r0) =
                                                   quotrem (r1, ih)
                                                   in let (q0, r0) =
                                                        adj
                                                        (q0,
                                                         ((sh r0) + vl) -
                                                           (q0 * il))
                                                        in ((sh q1) + q0, r0);;
                      let rec divmodd =
                        function 
                                 | (m, 1) -> (m, 0)
                                 | (m, i)
                                     -> let scale = scale i
                                          in let i' = i * scale
                                               in let m' = muld (m, scale)
                                                    in let rec dmi =
                                                         function 
                                                                  | []
                                                                    -> 
                                                                    ([], 0)
                                                                  | (d :: r)
                                                                    -> 
                                                                    let
                                                                    (qt, rm)
                                                                    = dmi r
                                                                    in 
                                                                    let
                                                                    (q1, r1)
                                                                    =
                                                                    divmod2
                                                                    ((rm, d),
                                                                    i')
                                                                    in 
                                                                    (consd
                                                                    (q1, qt),
                                                                    r1)
                                                         in let (q, r) =
                                                              dmi m'
                                                              in (q,
                                                                  div r scale);;
                      let rec divmod =
                        function 
                                 | (m, []) -> raise Div
                                 | ([], n) -> ([], [])
                                 | ((d :: r), (0 :: s))
                                     -> let (qt, rm) = divmod (r, s)
                                          in (qt, consd (d, rm))
                                 | (m, (d :: []))
                                     -> let (qt, rm) = divmodd (m, d)
                                          in (qt, begin
                                              if rm = 0 then [] else [rm]
                                              end)
                                 | (m, n)
                                     -> let ln = length n
                                          in let scale =
                                               scale (List.nth (n, ln - 1))
                                               in let m' = muld (m, scale)
                                                    in let n' =
                                                         muld (n, scale)
                                                         in let n1 =
                                                              List.nth
                                                              (n', ln - 1)
                                                              in let rec divl
                                                                   =
                                                                   function 
                                                                    | []
                                                                    -> ([],
                                                                    [])
                                                                    | (d
                                                                    :: r)
                                                                    -> let
                                                                    (qt, rm)
                                                                    = divl r
                                                                    in let m
                                                                    =
                                                                    consd
                                                                    (d, rm)
                                                                    in let
                                                                    rec msds
                                                                    =
                                                                    function 
                                                                    | ([], _)
                                                                    -> (0, 0)
                                                                    | ((d
                                                                    :: []),
                                                                    1)
                                                                    -> (0, d)
                                                                    | ((d2
                                                                    :: (d1
                                                                    :: [])),
                                                                    1)
                                                                    -> (d1,
                                                                    d2)
                                                                    | ((d
                                                                    :: r), i)
                                                                    -> msds
                                                                    (r,
                                                                    i - 1)
                                                                    in let
                                                                    (m1, m2)
                                                                    =
                                                                    msds
                                                                    (m, ln)
                                                                    in let tq
                                                                    = begin
                                                                    if
                                                                    m1 = n1
                                                                    then
                                                                    maxDigit
                                                                    else
                                                                    (fun 
                                                                    (r, _)
                                                                    -> r)
                                                                    (divmod2
                                                                    ((m1, m2),
                                                                    n1)) end
                                                                    in let
                                                                    rec try_
                                                                    (q, qn')
                                                                    =
                                                                    try 
                                                                    (q,
                                                                    subt
                                                                    (m, qn'))
                                                                    with 
                                                                    
                                                                    | 
                                                                    Negative
                                                                    -> 
                                                                    try_
                                                                    (q - 1,
                                                                    subt
                                                                    (qn', n'))
                                                                    in let
                                                                    (q, rr) =
                                                                    try_
                                                                    (tq,
                                                                    muld
                                                                    (n', tq))
                                                                    in (consd
                                                                    (q, qt),
                                                                    rr)
                                                                   in 
                                                                   let
                                                                    (qt, rm')
                                                                    = 
                                                                    divl m'
                                                                    in 
                                                                    let
                                                                    (rm, _) =
                                                                    divmodd
                                                                    (rm',
                                                                    scale)
                                                                    in 
                                                                    (qt, rm);;
                      let rec cmp =
                        function 
                                 | ([], []) -> Equal
                                 | (_, []) -> Greater
                                 | ([], _) -> Less
                                 | (((i : int) :: ri), (j :: rj))
                                     -> begin
                                        match cmp (ri, rj)
                                        with 
                                             | Equal -> begin
                                                 if i = j then Equal else
                                                 begin
                                                 if i < j then Less else
                                                 Greater end end
                                             | c -> c
                                        end;;
                      let rec exp =
                        function 
                                 | (_, 0) -> one
                                 | ([], n) -> begin
                                     if n > 0 then zero else raise Div end
                                 | (m, n) -> begin
                                     if n < 0 then zero else
                                     let rec expm =
                                       function 
                                                | 0 -> [1]
                                                | 1 -> m
                                                | i
                                                    -> let r = expm (div i 2)
                                                         in let r2 =
                                                              mult (r, r)
                                                              in begin
                                                              if
                                                              (i mod 2) = 0
                                                              then r2 else
                                                              mult (r2, m)
                                                              end
                                       in expm n
                                     end;;
                      open!
                        struct
                          let rec try_ n = begin
                            if n >= lgHBase then n else try_ (2 * n) end;;
                          let pow2lgHBase = try_ 1;;
                          end;;
                      let rec log2 =
                        function 
                                 | [] -> raise Domain
                                 | (h :: t)
                                     -> let rec qlog =
                                          function 
                                                   | (x, 0) -> 0
                                                   | (x, b) -> begin
                                                       if
                                                       x >=
                                                         (wtoi
                                                          ((Word.( << )
                                                            (1, itow b))))
                                                       then
                                                       b +
                                                         (qlog
                                                          (wtoi
                                                           ((Word.( >> )
                                                             (itow x, itow b))),
                                                           div b 2))
                                                       else qlog (x, div b 2)
                                                       end
                                          in let rec loop =
                                               function 
                                                        | (d, [], lg)
                                                            -> lg +
                                                                 (qlog
                                                                  (d,
                                                                   pow2lgHBase))
                                                        | (_, (h :: t), lg)
                                                            -> loop
                                                               (h, t,
                                                                lg + lgBase)
                                               in loop (h, t, 0);;
                      let rec mkPowers radix =
                        let powers =
                          let bnd = Int.quot (nbase, - radix)
                            in let rec try_ (tp, l) =
                                 try begin
                                 if tp <= bnd then
                                 try_ (radix * tp, (tp :: l)) else (tp :: l)
                                 end with 
                                          | _ -> (tp :: l)
                                 in Vector.fromList (rev (try_ (radix, [1])))
                          in let maxpow = (Vector.length powers) - 1
                               in (maxpow, Vector.sub (powers, maxpow),
                                   powers);;
                      let powers2 = mkPowers 2;;
                      let powers8 = mkPowers 8;;
                      let powers10 = mkPowers 10;;
                      let powers16 = mkPowers 16;;
                      let rec fmt (pow, radpow, puti) n =
                        let pad = StringCvt.padLeft '0' pow
                          in let rec ms0 =
                               function 
                                        | (0, a) -> (pad "" :: a)
                                        | (i, a) -> (pad (puti i) :: a)
                               in let rec ml (n, a) =
                                    begin
                                    match divmodd (n, radpow)
                                    with 
                                         | ([], d) -> (puti d :: a)
                                         | (q, d) -> ml (q, ms0 (d, a))
                                    end in concat (ml (n, []));;
                      let fmt2 =
                        fmt
                        ((fun (r, _) -> r) powers2,
                         (fun (_, r) -> r) powers2,
                         NumFormat.fmtInt StringCvt.Bin);;
                      let fmt8 =
                        fmt
                        ((fun (r, _) -> r) powers8,
                         (fun (_, r) -> r) powers8,
                         NumFormat.fmtInt StringCvt.Oct);;
                      let fmt10 =
                        fmt
                        ((fun (r, _) -> r) powers10,
                         (fun (_, r) -> r) powers10,
                         NumFormat.fmtInt StringCvt.Dec);;
                      let fmt16 =
                        fmt
                        ((fun (r, _) -> r) powers16,
                         (fun (_, r) -> r) powers16,
                         NumFormat.fmtInt StringCvt.Hex);;
                      let rec scan (bound, powers, geti) getc cs =
                        let rec get (l, cs) = begin
                          if l = bound then None else
                          begin
                          match getc cs
                          with 
                               | None -> None
                               | Some (c, cs') -> (Some (c, (l + 1, cs')))
                          end end
                          in let rec loop (acc, cs) =
                               begin
                               match geti get (0, cs)
                               with 
                                    | None -> (acc, cs)
                                    | Some (0, (sh, cs'))
                                        -> loop
                                           (add
                                            (muld
                                             (acc, Vector.sub (powers, sh)),
                                             []),
                                            cs')
                                    | Some (i, (sh, cs'))
                                        -> loop
                                           (add
                                            (muld
                                             (acc, Vector.sub (powers, sh)),
                                             [i]),
                                            cs')
                               end
                               in begin
                                  match geti get (0, cs)
                                  with 
                                       | None -> None
                                       | Some (0, (_, cs'))
                                           -> (Some (loop ([], cs')))
                                       | Some (i, (_, cs'))
                                           -> (Some (loop ([i], cs')))
                                  end;;
                      let rec scan2 getc =
                        scan
                        ((fun (r, _) -> r) powers2,
                         (fun (_, _, r) -> r) powers2,
                         NumScan.scanInt StringCvt.Bin)
                        getc;;
                      let rec scan8 getc =
                        scan
                        ((fun (r, _) -> r) powers8,
                         (fun (_, _, r) -> r) powers8,
                         NumScan.scanInt StringCvt.Oct)
                        getc;;
                      let rec scan10 getc =
                        scan
                        ((fun (r, _) -> r) powers10,
                         (fun (_, _, r) -> r) powers10,
                         NumScan.scanInt StringCvt.Dec)
                        getc;;
                      let rec scan16 getc =
                        scan
                        ((fun (r, _) -> r) powers16,
                         (fun (_, _, r) -> r) powers16,
                         NumScan.scanInt StringCvt.Hex)
                        getc;;
                      end;;
    module BN = BigNat;;
    type sign = | Pos 
                | Neg ;;
    type int = | Bi of { sign: sign ; digits: BN.bignat } ;;
    let zero = (Bi { sign = Pos; digits = BN.zero} );;
    let one = (Bi { sign = Pos; digits = BN.one} );;
    let minus_one = (Bi { sign = Neg; digits = BN.one} );;
    let rec posi digits = (Bi { sign = Pos; digits} );;
    let rec negi digits = (Bi { sign = Neg; digits} );;
    let rec zneg =
      function 
               | [] -> zero
               | digits -> (Bi { sign = Neg; digits} );;
    open!
      struct
        let minNeg = valOf Int.minInt;;
        let bigNatMinNeg = BN.addOne (BN.bignat (- (minNeg + 1)));;
        let bigIntMinNeg = negi bigNatMinNeg;;
        end;;
    let rec toInt =
      function 
               | Bi { digits = []} -> 0
               | Bi { sign = Pos; digits} -> BN.int digits
               | Bi { sign = Neg; digits}
                   -> try - (BN.int digits)
                      with 
                           | _ -> begin
                               if digits = bigNatMinNeg then minNeg else
                               raise Overflow end;;
    let rec fromInt =
      function 
               | 0 -> zero
               | i -> begin
                   if i < 0 then begin
                   if i = minNeg then bigIntMinNeg else
                   (Bi { sign = Neg; digits = BN.bignat (- i)} ) end else
                   (Bi { sign = Pos; digits = BN.bignat i} ) end;;
    open!
      struct
        let minNeg = valOf LargeInt.minInt;;
        let maxDigit = LargeInt.fromInt BN.maxDigit;;
        let nbase = LargeInt.fromInt BN.nbase;;
        let lgBase = Word.fromInt BN.lgBase;;
        let notNbase = Word32.notb (Word32.fromInt BN.nbase);;
        let rec largeNat =
          function 
                   | (0 : LargeInt.int) -> []
                   | i
                       -> let rec bn =
                            function 
                                     | (0 : Word32.word) -> []
                                     | i
                                         -> let rec dmbase n =
                                              ((Word32.( >> ) (n, lgBase)),
                                               Word32.andb (n, notNbase))
                                              in let (q, r) = dmbase i
                                                   in (Word32.toInt r
                                                       :: bn q)
                            in begin
                            if i <= maxDigit then [LargeInt.toInt i] else
                            bn (Word32.fromLargeInt i) end;;
        let rec large =
          function 
                   | [] -> 0
                   | (d :: []) -> LargeInt.fromInt d
                   | (d :: (e :: []))
                       -> (- (nbase * (LargeInt.fromInt e))) +
                            (LargeInt.fromInt d)
                   | (d :: r)
                       -> (- (nbase * (large r))) + (LargeInt.fromInt d);;
        let bigNatMinNeg = BN.addOne (largeNat (- (minNeg + 1)));;
        let bigIntMinNeg = negi bigNatMinNeg;;
        end;;
    let rec toLarge =
      function 
               | Bi { digits = []} -> 0
               | Bi { sign = Pos; digits} -> large digits
               | Bi { sign = Neg; digits}
                   -> try - (large digits)
                      with 
                           | _ -> begin
                               if digits = bigNatMinNeg then minNeg else
                               raise Overflow end;;
    let rec fromLarge =
      function 
               | 0 -> zero
               | i -> begin
                   if i < 0 then begin
                   if i = minNeg then bigIntMinNeg else
                   (Bi { sign = Neg; digits = largeNat (- i)} ) end else
                   (Bi { sign = Pos; digits = largeNat i} ) end;;
    let rec negSign = function 
                               | Pos -> Neg
                               | Neg -> Pos;;
    let rec subtNat =
      function 
               | (m, []) -> { sign = Pos; digits = m} 
               | ([], n) -> { sign = Neg; digits = n} 
               | (m, n)
                   -> try { sign = Pos; digits = BN.subt (m, n)} 
                      with 
                           | negative_
                               -> { sign = Neg; digits = BN.subt (n, m)} ;;
    let precision = None;;
    let minInt = None;;
    let maxInt = None;;
    let rec ( ~- ) =
      function 
               | (Bi { digits = []} as i) -> i
               | Bi { sign = Pos; digits} -> (Bi { sign = Neg; digits} )
               | Bi { sign = Neg; digits} -> (Bi { sign = Pos; digits} );;
    let rec ( * ) =
      function 
               | (_, Bi { digits = []}) -> zero
               | (Bi { digits = []}, _) -> zero
               | (Bi { sign = Pos; digits = d1}, Bi
                  { sign = Neg; digits = d2})
                   -> (Bi { sign = Neg; digits = BN.mult (d1, d2)} )
               | (Bi { sign = Neg; digits = d1}, Bi
                  { sign = Pos; digits = d2})
                   -> (Bi { sign = Neg; digits = BN.mult (d1, d2)} )
               | (Bi { digits = d1}, Bi { digits = d2})
                   -> (Bi { sign = Pos; digits = BN.mult (d1, d2)} );;
    let rec ( + ) =
      function 
               | (Bi { digits = []}, i2) -> i2
               | (i1, Bi { digits = []}) -> i1
               | (Bi { sign = Pos; digits = d1}, Bi
                  { sign = Neg; digits = d2}) -> (Bi (subtNat (d1, d2)))
               | (Bi { sign = Neg; digits = d1}, Bi
                  { sign = Pos; digits = d2}) -> (Bi (subtNat (d2, d1)))
               | (Bi { sign; digits = d1}, Bi { digits = d2})
                   -> (Bi { sign; digits = BN.add (d1, d2)} );;
    let rec ( - ) =
      function 
               | (i1, Bi { digits = []}) -> i1
               | (Bi { digits = []}, Bi { sign; digits})
                   -> (Bi { sign = negSign sign; digits} )
               | (Bi { sign = Pos; digits = d1}, Bi
                  { sign = Pos; digits = d2}) -> (Bi (subtNat (d1, d2)))
               | (Bi { sign = Neg; digits = d1}, Bi
                  { sign = Neg; digits = d2}) -> (Bi (subtNat (d2, d1)))
               | (Bi { sign; digits = d1}, Bi { digits = d2})
                   -> (Bi { sign; digits = BN.add (d1, d2)} );;
    let rec quotrem =
      function 
               | (Bi { sign = Pos; digits = m}, Bi { sign = Pos; digits = n})
                   -> begin
                      match BN.divmod (m, n)
                      with 
                           | (q, r) -> (posi q, posi r)
                      end
               | (Bi { sign = Pos; digits = m}, Bi { sign = Neg; digits = n})
                   -> begin
                      match BN.divmod (m, n)
                      with 
                           | (q, r) -> (zneg q, posi r)
                      end
               | (Bi { sign = Neg; digits = m}, Bi { sign = Pos; digits = n})
                   -> begin
                      match BN.divmod (m, n)
                      with 
                           | (q, r) -> (zneg q, zneg r)
                      end
               | (Bi { sign = Neg; digits = m}, Bi { sign = Neg; digits = n})
                   -> begin
                      match BN.divmod (m, n)
                      with 
                           | (q, r) -> (posi q, zneg r)
                      end;;
    let rec divmod =
      function 
               | (Bi { sign = Pos; digits = m}, Bi { sign = Pos; digits = n})
                   -> begin
                      match BN.divmod (m, n)
                      with 
                           | (q, r) -> (posi q, posi r)
                      end
               | (Bi { sign = Pos; digits = []}, Bi
                  { sign = Neg; digits = n}) -> (zero, zero)
               | (Bi { sign = Pos; digits = m}, Bi { sign = Neg; digits = n})
                   -> let (q, r) = BN.divmod (BN.subtOne m, n)
                        in (negi (BN.addOne q),
                            zneg (BN.subtOne (BN.subt (n, r))))
               | (Bi { sign = Neg; digits = m}, Bi { sign = Pos; digits = n})
                   -> let (q, r) = BN.divmod (BN.subtOne m, n)
                        in (negi (BN.addOne q),
                            posi (BN.subtOne (BN.subt (n, r))))
               | (Bi { sign = Neg; digits = m}, Bi { sign = Neg; digits = n})
                   -> begin
                      match BN.divmod (m, n)
                      with 
                           | (q, r) -> (posi q, zneg r)
                      end;;
    let rec div arg = (fun (r, _) -> r) (divmod arg);;
    let rec ( mod ) arg = (fun (_, r) -> r) (divmod arg);;
    let rec quot arg = (fun (r, _) -> r) (quotrem arg);;
    let rec rem arg = (fun (_, r) -> r) (quotrem arg);;
    let rec compare =
      function 
               | (Bi { sign = Neg}, Bi { sign = Pos}) -> Less
               | (Bi { sign = Pos}, Bi { sign = Neg}) -> Greater
               | (Bi { sign = Pos; digits = d}, Bi
                  { sign = Pos; digits = d'}) -> BN.cmp (d, d')
               | (Bi { sign = Neg; digits = d}, Bi
                  { sign = Neg; digits = d'}) -> BN.cmp (d', d);;
    let rec ( < ) arg =
      begin match compare arg with 
                                   | Less -> true
                                   | _ -> false end;;
    let rec ( > ) arg =
      begin match compare arg with 
                                   | Greater -> true
                                   | _ -> false end;;
    let rec ( <= ) arg =
      begin match compare arg with 
                                   | Greater -> false
                                   | _ -> true end;;
    let rec ( >= ) arg =
      begin match compare arg with 
                                   | Less -> false
                                   | _ -> true end;;
    let rec abs =
      function 
               | Bi { sign = Neg; digits} -> (Bi { sign = Pos; digits} )
               | i -> i;;
    let rec max arg =
      begin
      match compare arg
      with 
           | Greater -> (fun (r, _) -> r) arg
           | _ -> (fun (_, r) -> r) arg
      end;;
    let rec min arg =
      begin
      match compare arg
      with 
           | Less -> (fun (r, _) -> r) arg
           | _ -> (fun (_, r) -> r) arg
      end;;
    let rec sign =
      function 
               | Bi { sign = Neg} -> (-1)
               | Bi { digits = []} -> 0
               | _ -> 1;;
    let rec sameSign (i, j) = (sign i) = (sign j);;
    open!
      struct
        let rec fmt' fmtFn i =
          begin
          match i
          with 
               | Bi { digits = []} -> "0"
               | Bi { sign = Neg; digits} -> "~" ^ (fmtFn digits)
               | Bi { sign = Pos; digits} -> fmtFn digits
          end;;
        end;;
    let rec fmt =
      function 
               | Bin -> fmt' BN.fmt2
               | Oct -> fmt' BN.fmt8
               | Dec -> fmt' BN.fmt10
               | Hex -> fmt' BN.fmt16;;
    let toString = fmt StringCvt.Dec;;
    open!
      struct
        let rec scan' scanFn getc cs =
          let cs' = NumScan.skipWS getc cs
            in let rec cvt =
                 function 
                          | (None, _) -> None
                          | (Some (i, cs), wr) -> (Some (wr i, cs))
                 in begin
                    match getc cs'
                    with 
                         | Some ('~', cs'') -> cvt (scanFn getc cs'', zneg)
                         | Some ('-', cs'') -> cvt (scanFn getc cs'', zneg)
                         | Some ('+', cs'') -> cvt (scanFn getc cs'', posi)
                         | Some _ -> cvt (scanFn getc cs', posi)
                         | None -> None
                    end;;
        end;;
    let rec scan =
      function 
               | Bin -> scan' BN.scan2
               | Oct -> scan' BN.scan8
               | Dec -> scan' BN.scan10
               | Hex -> scan' BN.scan16;;
    let rec fromString s = StringCvt.scanString (scan StringCvt.Dec) s;;
    let rec pow =
      function 
               | (_, 0) -> one
               | (Bi { sign = Pos; digits}, n) -> posi (BN.exp (digits, n))
               | (Bi { sign = Neg; digits}, n) -> begin
                   if (Int.( mod ) (n, 2)) = 0 then posi (BN.exp (digits, n))
                   else zneg (BN.exp (digits, n)) end;;
    let rec log2 =
      function 
               | Bi { sign = Pos; digits} -> BN.log2 digits
               | _ -> raise Domain;;
    end;;
(* local *);;
(* end case *);;
(* skip leading whitespace and any sign (+, -, or ~) *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* for power of 2 bases (2, 8 & 16), we can check for overflow by looking
       * at the hi (1, 3 or 4) bits.
       *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* end case *);;
(* structure NumScan *);;
(** should be int32 **);;
(** NOTE: this currently uses 31-bit integers, but really should use 32-bit
     ** ints (once they are supported).
     **);;
(* end case *);;
(* structure NumFormat *);;
(* No. of bits per digit; must be even *);;
(* = ~2^lgBase *);;
(* half digits *);;
(* least significant digit first *);;
(* MUST sign-extend *);;
(* multiply 2 digits *);;
(* x-y+z = mh*nl + ml*nh *);;
(* can't overflow *);;
(* multiply bigint by digit *);;
(* speedup *);;
(* speedup *);;
(* speedup *);;
(* divide DP number by digit; assumes u < i , i >= base/2 *);;
(* divide bignat by digit>0 *);;
(* speedup *);;
(* From Knuth Vol II, 4.3.1, but without opt. in step D3 *);;
(* speedup *);;
(* speedup *);;
(* >= 2 *);;
(* >= base/2 *);;
(*0*);;
(* local *);;
(* find maximal maxpow s.t. radix^maxpow < base 
             * basepow = radix^maxpow
             *);;
(* structure BigNat *);;
(* local *);;
(* The following assumes LargeInt = Int32.
       * If IntInf is provided, it will be LargeInt and toLarge and fromLarge
       * will be the identity function.
       *);;
(* local *);;
(* end case *);;
(* structure IntInf *);;
*)
