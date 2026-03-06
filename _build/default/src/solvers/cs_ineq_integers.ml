# 1 "src/solvers/cs_ineq_integers.sig.ml"

# 1 "src/solvers/cs_ineq_integers.fun.ml"
open! Basis;;
module CSIneqIntegers(CSIneqIntegers__0: sig
                                         (* Solver for linear inequations, based on branch & bound *)
                                         (* Author: Roberto Virga *)
                                         module Integers : INTEGERS
                                         module Rationals : RATIONALS
                                         (*! structure IntSyn : INTSYN !*)
                                         module Trail : TRAIL
                                         module Unify : UNIFY
                                         (*! sharing Unify.IntSyn = IntSyn !*)
                                         module SparseArray : SPARSE_ARRAY
                                         module SparseArray2 : SPARSE_ARRAY2
                                         (*! structure CSManager : CS_MANAGER !*)
                                         (*! sharing CSManager.IntSyn = IntSyn !*)
                                         module CSEqIntegers : CS_EQ_INTEGERS
                                         (*! sharing CSEqIntegers.IntSyn = IntSyn !*)
                                         (*! sharing CSEqIntegers.CSManager = CSManager !*)
                                         module Compat : COMPAT
                                         end) = struct
                                                  (*! structure CSManager = CSManager !*);;
                                                  open!
                                                    struct
                                                      open IntSyn;;
                                                      open Rationals;;
                                                      open CSEqIntegers;;
                                                      module CSM = CSManager;;
                                                      module FX = CSM.Fixity;;
                                                      module MS = ModeSyn;;
                                                      module Array = SparseArray;;
                                                      module Array2 = SparseArray2;;
                                                      let zero_int =
                                                        Integers.fromInt 0;;
                                                      let one_int =
                                                        Integers.fromInt 1;;
                                                      let myID =
                                                        (ref (-1) : cid ref);;
                                                      let geqID =
                                                        (ref (-1) : cid ref);;
                                                      let rec geq (u_, v_) =
                                                        (Root
                                                         ((Const (! geqID)),
                                                          (App
                                                           (u_,
                                                            (App (v_, Nil))))));;
                                                      let rec geq0 u_ =
                                                        geq
                                                        (u_,
                                                         (Constant_ zero_int));;
                                                      let geqAddID =
                                                        (ref (-1) : cid ref);;
                                                      let rec geqAdd
                                                        (u1_, u2_, v_, w_) =
                                                        (Root
                                                         ((Const
                                                           (! geqAddID)),
                                                          (App
                                                           (u1_,
                                                            (App
                                                             (u2_,
                                                              (App
                                                               (v_,
                                                                (App
                                                                 (w_, Nil))))))))));;
                                                      let rec geqNConDec d =
                                                        (ConDec
                                                         (((Integers.toString
                                                            d) ^ ">=") ^
                                                            (Integers.toString
                                                             zero_int),
                                                          None, 0, Normal,
                                                          geq0
                                                          ((Constant_ d)),
                                                          Type));;
                                                      let rec geqNExp d =
                                                        (Root
                                                         ((FgnConst
                                                           (! myID,
                                                            geqNConDec d)),
                                                          Nil));;
                                                      let rec parseGeqN
                                                        string =
                                                        let suffix =
                                                          ">=" ^
                                                            (toString zero)
                                                          in let stringLen =
                                                               String.size
                                                               string
                                                               in let
                                                                    suffixLen
                                                                    =
                                                                    String.size
                                                                    suffix
                                                                    in 
                                                                    let
                                                                    numLen =
                                                                    (Int.
                                                                    ( - )
                                                                    (stringLen,
                                                                    suffixLen))
                                                                    in begin
                                                                    if
                                                                    ((Int.
                                                                    ( > )
                                                                    (stringLen,
                                                                    suffixLen)))
                                                                    &&
                                                                    ((String.substring
                                                                    (string,
                                                                    numLen,
                                                                    suffixLen))
                                                                    = suffix)
                                                                    then
                                                                    begin
                                                                    match 
                                                                    Integers.fromString
                                                                    (String.substring
                                                                    (string,
                                                                    0,
                                                                    numLen))
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some d
                                                                    -> begin
                                                                    if
                                                                    (Integers.
                                                                    ( >= )
                                                                    (d,
                                                                    zero_int))
                                                                    then
                                                                    (Some
                                                                    (geqNConDec
                                                                    d)) else
                                                                    None end
                                                                    | 
                                                                    None
                                                                    -> None
                                                                    end else
                                                                    None end;;
                                                      type position_ =
                                                        | Row of int 
                                                        | Col of int ;;
                                                      type owner_ =
                                                        | Var of
                                                          IntSyn.dctx * mon_ 
                                                        | Exp of
                                                          IntSyn.dctx * sum_ ;;
                                                      type restriction_ =
                                                        | Restr of
                                                          IntSyn.dctx *
                                                          IntSyn.exp_ ;;
                                                      type nonrec label =
                                                        [%record_type
                                                          type __record = {
                                                            owner: owner_ ;
                                                            tag: int ref ;
                                                            restr: restriction_
                                                              option ref ;
                                                            dead: bool ref };;];;
                                                      type operation_ =
                                                        | Insert of position_ 
                                                        | Pivot of int * int 
                                                        | Kill of position_ 
                                                        | Restrict of
                                                          position_ 
                                                        | UpdateOwner of
                                                          position_ *
                                                          owner_ *
                                                          int
                                                          ref ;;
                                                      type nonrec tableau =
                                                        [%record_type
                                                          type __record = {
                                                            rlabels: label
                                                              Array.array ;
                                                            clabels: label
                                                              Array.array ;
                                                            consts: number
                                                              Array.array ;
                                                            coeffs: number
                                                              Array2.array ;
                                                            nrows: int ref ;
                                                            ncols: int ref ;
                                                            trail: operation_
                                                              Trail.trail };;];;
                                                      exception MyFgnCnstrRep
                                                      of
                                                      int ref
                                                      ;;
                                                      exception Error ;;
                                                      open!
                                                        struct
                                                          let a = 16807.0;;
                                                          let m =
                                                            2147483647.0;;
                                                          let seed =
                                                            ref 1999.0;;
                                                          end;;
                                                      let rec rand
                                                        (min, size) =
                                                        let rec nextrand () =
                                                          let t =
                                                            (Real.( * )
                                                             (a, ! seed))
                                                            in begin
                                                                 seed :=
                                                                   ((Real.
                                                                    ( - )
                                                                    (t,
                                                                    (Real.
                                                                    ( * )
                                                                    (m,
                                                                    Real.fromInt
                                                                    (Real.floor
                                                                    (t / m)))))));
                                                                 ((Real.
                                                                   ( - )
                                                                   (! seed,
                                                                    1.0)))
                                                                   /
                                                                   ((Real.
                                                                    ( - )
                                                                    (m, 1.0)))
                                                                 
                                                                 end
                                                          in (Int.( + )
                                                              (min,
                                                               Real.floor
                                                               ((Real.
                                                                 ( * )
                                                                 (nextrand (),
                                                                  Real.fromInt
                                                                  size)))));;
                                                      let tableau =
                                                        let l =
                                                          {
                                                          owner
                                                          = (Exp
                                                             (Null,
                                                              (Sum
                                                               (zero_int, []))));
                                                          tag = ref 0;
                                                          restr = ref None;
                                                          dead = ref true}
                                                           in ({
                                                               rlabels
                                                               = Array.array
                                                                 l;
                                                               clabels
                                                               = Array.array
                                                                 l;
                                                               consts
                                                               = Array.array
                                                                 zero;
                                                               coeffs
                                                               = Array2.array
                                                                 zero;
                                                               nrows = ref 0;
                                                               ncols = ref 0;
                                                               trail
                                                               = Trail.trail
                                                                 ()}
                                                                : tableau);;
                                                      let rec rlabel i =
                                                        Array.sub
                                                        ((fun r -> r.rlabels)
                                                         tableau, i);;
                                                      let rec clabel j =
                                                        Array.sub
                                                        ((fun r -> r.clabels)
                                                         tableau, j);;
                                                      let rec const i =
                                                        Array.sub
                                                        ((fun r -> r.consts)
                                                         tableau, i);;
                                                      let rec coeff (i, j) =
                                                        Array2.sub
                                                        ((fun r -> r.coeffs)
                                                         tableau, i, j);;
                                                      let rec nRows () =
                                                        !
                                                          ((fun r -> r.nrows)
                                                           tableau);;
                                                      let rec nCols () =
                                                        !
                                                          ((fun r -> r.ncols)
                                                           tableau);;
                                                      let rec incrNRows () =
                                                        let old = nRows ()
                                                          in begin
                                                               ((fun r
                                                                   -> 
                                                                   r.nrows)
                                                                tableau) :=
                                                                 ((Int.
                                                                   ( + )
                                                                   (old, 1)));
                                                               old
                                                               end;;
                                                      let rec incrNCols () =
                                                        let old = nCols ()
                                                          in begin
                                                               ((fun r
                                                                   -> 
                                                                   r.ncols)
                                                                tableau) :=
                                                                 ((Int.
                                                                   ( + )
                                                                   (old, 1)));
                                                               old
                                                               end;;
                                                      let rec decrNRows () =
                                                        ((fun r -> r.nrows)
                                                         tableau) :=
                                                          ((Int.( - )
                                                            (nRows (), 1)));;
                                                      let rec decrNCols () =
                                                        ((fun r -> r.ncols)
                                                         tableau) :=
                                                          ((Int.( - )
                                                            (nCols (), 1)));;
                                                      let rec incrArray
                                                        (array, i, value) =
                                                        Array.update
                                                        (array, i,
                                                         (Array.sub
                                                          (array, i)) + value);;
                                                      let rec incrArray2
                                                        (array, i, j, value)
                                                        =
                                                        Array2.update
                                                        (array, i, j,
                                                         (Array2.sub
                                                          (array, i, j)) +
                                                           value);;
                                                      let rec incrArray2Row
                                                        (array, i, (j, len),
                                                         f)
                                                        =
                                                        Compat.Vector.mapi
                                                        (function 
                                                                  | (j,
                                                                    value)
                                                                    -> 
                                                                    Array2.update
                                                                    (array,
                                                                    i, j,
                                                                    value +
                                                                    (f j)))
                                                        (Array2.row
                                                         (array, i, (j, len)));;
                                                      let rec incrArray2Col
                                                        (array, j, (i, len),
                                                         f)
                                                        =
                                                        Compat.Vector.mapi
                                                        (function 
                                                                  | (i,
                                                                    value)
                                                                    -> 
                                                                    Array2.update
                                                                    (array,
                                                                    i, j,
                                                                    value +
                                                                    (f i)))
                                                        (Array2.column
                                                         (array, j, (i, len)));;
                                                      let rec clearArray2Row
                                                        (array, i, (j, len))
                                                        =
                                                        Compat.Vector.mapi
                                                        (function 
                                                                  | (j,
                                                                    value)
                                                                    -> 
                                                                    Array2.update
                                                                    (array,
                                                                    i, j,
                                                                    zero))
                                                        (Array2.row
                                                         (array, i, (j, len)));;
                                                      let rec clearArray2Col
                                                        (array, j, (i, len))
                                                        =
                                                        Compat.Vector.mapi
                                                        (function 
                                                                  | (i,
                                                                    value)
                                                                    -> 
                                                                    Array2.update
                                                                    (array,
                                                                    i, j,
                                                                    zero))
                                                        (Array2.column
                                                         (array, j, (i, len)));;
                                                      let rec label =
                                                        function 
                                                                 | Row i
                                                                    -> 
                                                                    rlabel
                                                                    i
                                                                 | Col j
                                                                    -> 
                                                                    clabel
                                                                    j;;
                                                      let rec restriction
                                                        ((l : label)) =
                                                        !
                                                          ((fun r -> r.restr)
                                                           l);;
                                                      let rec restricted
                                                        ((l : label)) =
                                                        begin
                                                        match restriction l
                                                        with 
                                                             | Some _ -> true
                                                             | None -> false
                                                        end;;
                                                      let rec dead
                                                        ((l : label)) =
                                                        !
                                                          ((fun r -> r.dead)
                                                           l);;
                                                      let rec setOwnership
                                                        (pos, owner, tag) =
                                                        let old =
                                                          (Label_ pos)
                                                          in let New_ =
                                                               {
                                                               owner;
                                                               tag;
                                                               restr
                                                               = ref
                                                                 (restriction
                                                                  old);
                                                               dead
                                                               = ref
                                                                 (dead old)}
                                                                in begin
                                                                   match pos
                                                                   with 
                                                                   
                                                                   | 
                                                                   Row i
                                                                    -> 
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    i, New_)
                                                                   | 
                                                                   Col j
                                                                    -> 
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    j, New_)
                                                                   end;;
                                                      let rec ownerContext =
                                                        function 
                                                                 | Var
                                                                    (g_, mon)
                                                                    -> g_
                                                                 | Exp
                                                                    (g_, sum)
                                                                    -> g_;;
                                                      let rec ownerSum =
                                                        function 
                                                                 | Var
                                                                    (g_, mon)
                                                                    -> 
                                                                    (Sum
                                                                    (zero_int,
                                                                    [mon]))
                                                                 | Exp
                                                                    (g_, sum)
                                                                    -> sum;;
                                                      let rec displayPos =
                                                        function 
                                                                 | Row row
                                                                    -> 
                                                                    print
                                                                    (("row "
                                                                    ^
                                                                    (Int.toString
                                                                    row)) ^
                                                                    "\n")
                                                                 | Col col
                                                                    -> 
                                                                    print
                                                                    (("column "
                                                                    ^
                                                                    (Int.toString
                                                                    col)) ^
                                                                    "\n");;
                                                      let rec displaySum =
                                                        function 
                                                                 | Sum
                                                                    (m,
                                                                    (Mon
                                                                    (n, _)
                                                                    :: monL))
                                                                    -> 
                                                                    begin
                                                                    print
                                                                    (Integers.toString
                                                                    n);
                                                                    begin
                                                                    print
                                                                    " ? + ";
                                                                    displaySum
                                                                    ((Sum
                                                                    (m, monL)))
                                                                    
                                                                    end
                                                                    end
                                                                 | Sum
                                                                    (m, [])
                                                                    -> 
                                                                    begin
                                                                    print
                                                                    (Integers.toString
                                                                    m);
                                                                    print
                                                                    " >= 0\n"
                                                                    end;;
                                                      let rec display () =
                                                        let rec printLabel
                                                          (col, (l : label))
                                                          =
                                                          begin
                                                            print "\t";
                                                            begin
                                                              begin
                                                              match (fun r
                                                                    -> r.owner)
                                                                    l
                                                              with 
                                                                   | 
                                                                   Var _
                                                                    -> 
                                                                    print
                                                                    "V"
                                                                   | 
                                                                   Exp _
                                                                    -> 
                                                                    print
                                                                    "E"
                                                              end;
                                                              begin
                                                                begin
                                                                if
                                                                restricted l
                                                                then
                                                                print ">"
                                                                else
                                                                print "*"
                                                                end;begin
                                                                if dead l
                                                                then
                                                                print "#"
                                                                else 
                                                                print "" end
                                                                end
                                                              
                                                              end
                                                            
                                                            end
                                                          in let rec printRow
                                                               (row,
                                                                (l : label))
                                                               =
                                                               let
                                                                 rec printCol
                                                                 (col,
                                                                  (d
                                                                   : number))
                                                                 =
                                                                 begin
                                                                   print "\t";
                                                                   print
                                                                   (toString
                                                                    d)
                                                                   
                                                                   end
                                                                 in let vec =
                                                                    Array2.row
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    row,
                                                                    (0,
                                                                    nCols ()))
                                                                    in 
                                                                    begin
                                                                    begin
                                                                    match 
                                                                    (fun r
                                                                    -> r.owner)
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    Var _
                                                                    -> 
                                                                    print
                                                                    "V"
                                                                    | 
                                                                    Exp _
                                                                    -> 
                                                                    print
                                                                    "E"
                                                                    end;
                                                                    begin
                                                                    begin
                                                                    if
                                                                    restricted
                                                                    l then
                                                                    print ">"
                                                                    else
                                                                    print "*"
                                                                    end;
                                                                    begin
                                                                    begin
                                                                    if 
                                                                    dead l
                                                                    then
                                                                    print "#"
                                                                    else
                                                                    print ""
                                                                    end;
                                                                    begin
                                                                    print
                                                                    "\t";
                                                                    begin
                                                                    Compat.Vector.mapi
                                                                    printCol
                                                                    vec;
                                                                    begin
                                                                    print
                                                                    "\t";
                                                                    begin
                                                                    print
                                                                    (toString
                                                                    (const
                                                                    row));
                                                                    print
                                                                    "\n"
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                               in begin
                                                                    print
                                                                    "\t";
                                                                    begin
                                                                    Array.app
                                                                    printLabel
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ());
                                                                    begin
                                                                    print
                                                                    "\n";
                                                                    begin
                                                                    Array.app
                                                                    printRow
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ());
                                                                    begin
                                                                    print
                                                                    "Columns:\n";
                                                                    begin
                                                                    Array.app
                                                                    (function 
                                                                    | (_,
                                                                    (l
                                                                    : label))
                                                                    -> displaySum
                                                                    (ownerSum
                                                                    ((fun r
                                                                    -> r.owner)
                                                                    l)))
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ());
                                                                    begin
                                                                    print
                                                                    "Rows:\n";
                                                                    Array.app
                                                                    (function 
                                                                    | (_,
                                                                    (l
                                                                    : label))
                                                                    -> displaySum
                                                                    (ownerSum
                                                                    ((fun r
                                                                    -> r.owner)
                                                                    l)))
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ())
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end;;
                                                      let rec findMon mon =
                                                        (let exception Found
                                                         of int 
                                                         in let rec find
                                                              (i,
                                                               (l : label))
                                                              =
                                                              begin
                                                              match (fun r
                                                                    -> r.owner)
                                                                    l
                                                              with 
                                                                   | 
                                                                   Var
                                                                    (g_,
                                                                    mon')
                                                                    -> begin
                                                                    if
                                                                    compatibleMon
                                                                    (mon,
                                                                    mon')
                                                                    then
                                                                    raise
                                                                    ((Found
                                                                    i)) else
                                                                    () end
                                                                   | 
                                                                   _ -> ()
                                                              end
                                                              in try 
                                                                 begin
                                                                   Array.app
                                                                   find
                                                                   ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ());
                                                                   try 
                                                                   begin
                                                                    Array.app
                                                                    find
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ());
                                                                    None
                                                                    end
                                                                   with 
                                                                   
                                                                   | 
                                                                   Found i
                                                                    -> 
                                                                    (Some
                                                                    ((Row i)))
                                                                   
                                                                   end
                                                                 with 
                                                                 
                                                                 | Found j
                                                                    -> 
                                                                    (Some
                                                                    ((Col j))));;
                                                      let rec findTag t =
                                                        (let exception Found
                                                         of int 
                                                         in let rec find
                                                              (i,
                                                               (l : label))
                                                              = begin
                                                              if
                                                              ((fun r
                                                                  -> 
                                                                  r.tag)
                                                               l) = t
                                                              then
                                                              raise
                                                              ((Found i))
                                                              else () end
                                                              in try 
                                                                 begin
                                                                   Array.app
                                                                   find
                                                                   ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ());
                                                                   try 
                                                                   begin
                                                                    Array.app
                                                                    find
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ());
                                                                    None
                                                                    end
                                                                   with 
                                                                   
                                                                   | 
                                                                   Found i
                                                                    -> 
                                                                    (Some
                                                                    ((Row i)))
                                                                   
                                                                   end
                                                                 with 
                                                                 
                                                                 | Found j
                                                                    -> 
                                                                    (Some
                                                                    ((Col j))));;
                                                      let rec isConstant row
                                                        =
                                                        Array.foldl
                                                        (function 
                                                                  | (j, l,
                                                                    rest)
                                                                    -> 
                                                                    ((dead l)
                                                                    ||
                                                                    ((coeff
                                                                    (row, j))
                                                                    = zero))
                                                                    && rest)
                                                        true
                                                        ((fun r -> r.clabels)
                                                         tableau, 0,
                                                         nCols ());;
                                                      let rec isSubsumed row
                                                        =
                                                        let constRow =
                                                          const row
                                                          in let
                                                               rec isSubsumedByRow
                                                               () =
                                                               let candidates
                                                                 =
                                                                 Array.foldl
                                                                 (function 
                                                                    | (i,
                                                                    (l
                                                                    : label),
                                                                    rest)
                                                                    -> begin
                                                                    if
                                                                    (i <> row)
                                                                    &&
                                                                    ((not
                                                                    (dead l))
                                                                    &&
                                                                    ((const i)
                                                                    =
                                                                    constRow))
                                                                    then
                                                                    (i
                                                                    :: rest)
                                                                    else rest
                                                                    end)
                                                                 []
                                                                 ((fun r
                                                                    -> 
                                                                    r.rlabels)
                                                                  tableau, 0,
                                                                  nRows ())
                                                                 in let
                                                                    rec filter
                                                                    =
                                                                    function 
                                                                    | (j, l,
                                                                    []) -> []
                                                                    | (j,
                                                                    (l
                                                                    : label),
                                                                    candidates)
                                                                    -> begin
                                                                    if
                                                                    not
                                                                    (dead l)
                                                                    then
                                                                    List.filter
                                                                    (function 
                                                                    | i
                                                                    -> (coeff
                                                                    (i, j)) =
                                                                    (coeff
                                                                    (row, j)))
                                                                    candidates
                                                                    else
                                                                    candidates
                                                                    end
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    Array.foldl
                                                                    filter
                                                                    candidates
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ())
                                                                    with 
                                                                    
                                                                    | 
                                                                    []
                                                                    -> None
                                                                    | 
                                                                    (i :: _)
                                                                    -> 
                                                                    (Some i)
                                                                    end
                                                               in let
                                                                    rec isSubsumedByCol
                                                                    () =
                                                                    begin
                                                                    if
                                                                    constRow
                                                                    = zero
                                                                    then
                                                                    let
                                                                    nonNull =
                                                                    Array.foldl
                                                                    (function 
                                                                    | (j,
                                                                    (l
                                                                    : label),
                                                                    rest)
                                                                    -> begin
                                                                    if
                                                                    not
                                                                    (dead l)
                                                                    then
                                                                    let value
                                                                    =
                                                                    coeff
                                                                    (row, j)
                                                                    in begin
                                                                    if
                                                                    value <>
                                                                    zero then
                                                                    ((j,
                                                                    value)
                                                                    :: rest)
                                                                    else rest
                                                                    end else
                                                                    rest end)
                                                                    []
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ())
                                                                    in 
                                                                    begin
                                                                    match nonNull
                                                                    with 
                                                                    
                                                                    | 
                                                                    ((j,
                                                                    value)
                                                                    :: [])
                                                                    -> begin
                                                                    if
                                                                    value =
                                                                    one then
                                                                    (Some j)
                                                                    else None
                                                                    end
                                                                    | 
                                                                    _ -> None
                                                                    end else
                                                                    None end
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    isSubsumedByRow
                                                                    ()
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some i
                                                                    -> 
                                                                    (Some
                                                                    ((Row i)))
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    begin
                                                                    match 
                                                                    isSubsumedByCol
                                                                    ()
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some j
                                                                    -> 
                                                                    (Some
                                                                    ((Col j)))
                                                                    | 
                                                                    None
                                                                    -> None
                                                                    end
                                                                    end;;
                                                      let rec findPivot row =
                                                        let rec compareScore
                                                          =
                                                          function 
                                                                   | 
                                                                   (Some d,
                                                                    Some d')
                                                                    -> 
                                                                    compare
                                                                    (d, d')
                                                                   | 
                                                                   (Some d,
                                                                    None)
                                                                    -> LESS
                                                                   | 
                                                                   (None,
                                                                    Some d')
                                                                    -> GREATER
                                                                   | 
                                                                   (None,
                                                                    None)
                                                                    -> Equal
                                                          in let
                                                               rec findPivotCol
                                                               (j,
                                                                (l : label),
                                                                ((score,
                                                                  champs) as
                                                                  result))
                                                               =
                                                               let value =
                                                                 coeff
                                                                 (row, j)
                                                                 in let
                                                                    rec findPivotRow
                                                                    sgn
                                                                    (i,
                                                                    (l
                                                                    : label),
                                                                    ((score,
                                                                    champs)
                                                                    as
                                                                    result))
                                                                    =
                                                                    let value
                                                                    =
                                                                    coeff
                                                                    (i, j)
                                                                    in begin
                                                                    if
                                                                    (not
                                                                    (dead l))
                                                                    &&
                                                                    ((i <>
                                                                    row) &&
                                                                    ((restricted
                                                                    l) &&
                                                                    (((fromInt
                                                                    sgn) *
                                                                    value) <
                                                                    zero)))
                                                                    then
                                                                    let
                                                                    score' =
                                                                    (Some
                                                                    (abs
                                                                    ((const i)
                                                                    *
                                                                    (inverse
                                                                    value))))
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    compareScore
                                                                    (score,
                                                                    score')
                                                                    with 
                                                                    
                                                                    | 
                                                                    GREATER
                                                                    -> 
                                                                    (score',
                                                                    [(i, j)])
                                                                    | 
                                                                    Equal
                                                                    -> 
                                                                    (score,
                                                                    ((i, j)
                                                                    :: champs))
                                                                    | 
                                                                    LESS
                                                                    -> result
                                                                    end else
                                                                    result
                                                                    end
                                                                    in begin
                                                                    if
                                                                    (not
                                                                    (dead l))
                                                                    &&
                                                                    ((value
                                                                    <> zero)
                                                                    &&
                                                                    ((not
                                                                    (restricted
                                                                    l)) ||
                                                                    (value >
                                                                    zero)))
                                                                    then
                                                                    let
                                                                    ((score',
                                                                    champs')
                                                                    as
                                                                    result')
                                                                    =
                                                                    Array.foldl
                                                                    (findPivotRow
                                                                    (sign
                                                                    value))
                                                                    (None,
                                                                    [(row, j)])
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ())
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    compareScore
                                                                    (score,
                                                                    score')
                                                                    with 
                                                                    
                                                                    | 
                                                                    GREATER
                                                                    -> result
                                                                    | 
                                                                    Equal
                                                                    -> 
                                                                    (score,
                                                                    champs @
                                                                    champs')
                                                                    | 
                                                                    LESS
                                                                    -> result'
                                                                    end else
                                                                    result
                                                                    end
                                                               in begin
                                                                  match 
                                                                  Array.foldl
                                                                  findPivotCol
                                                                  ((Some
                                                                    zero),
                                                                   [])
                                                                  ((fun r
                                                                    -> 
                                                                    r.clabels)
                                                                   tableau,
                                                                   0,
                                                                   nCols ())
                                                                  with 
                                                                  
                                                                  | (_, [])
                                                                    -> None
                                                                  | (_,
                                                                    champs)
                                                                    -> 
                                                                    (Some
                                                                    (List.nth
                                                                    (champs,
                                                                    rand
                                                                    (0,
                                                                    List.length
                                                                    champs))))
                                                                  end;;
                                                      let rec pivot
                                                        (row, col) =
                                                        let pCoeffInverse =
                                                          inverse
                                                          (coeff (row, col))
                                                          in let pRowVector =
                                                               Array2.row
                                                               ((fun r
                                                                   -> 
                                                                   r.coeffs)
                                                                tableau, row,
                                                                (0, nCols ()))
                                                               in let
                                                                    rec pRow
                                                                    j =
                                                                    Vector.sub
                                                                    (pRowVector,
                                                                    j)
                                                                    in 
                                                                    let
                                                                    pColVector
                                                                    =
                                                                    Array2.column
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    col,
                                                                    (0,
                                                                    nRows ()))
                                                                    in 
                                                                    let
                                                                    rec pCol
                                                                    i =
                                                                    Vector.sub
                                                                    (pColVector,
                                                                    i)
                                                                    in 
                                                                    let
                                                                    pConst =
                                                                    const row
                                                                    in 
                                                                    let
                                                                    pRLabel =
                                                                    rlabel
                                                                    row
                                                                    in 
                                                                    let
                                                                    pCLabel =
                                                                    clabel
                                                                    col
                                                                    in 
                                                                    begin
                                                                    Array.modify
                                                                    (function 
                                                                    | (i,
                                                                    value)
                                                                    -> begin
                                                                    if
                                                                    i = row
                                                                    then
                                                                    -
                                                                    (value *
                                                                    pCoeffInverse)
                                                                    else
                                                                    value -
                                                                    ((pConst
                                                                    *
                                                                    (pCol i))
                                                                    *
                                                                    pCoeffInverse)
                                                                    end)
                                                                    ((fun r
                                                                    -> r.consts)
                                                                    tableau,
                                                                    0,
                                                                    nRows ());
                                                                    begin
                                                                    Array2.modify
                                                                    Array2.colMajor_
                                                                    (function 
                                                                    | (i, j,
                                                                    value)
                                                                    -> begin
                                                                    match 
                                                                    (i = row,
                                                                    j = col)
                                                                    with 
                                                                    
                                                                    | 
                                                                    (true,
                                                                    true)
                                                                    -> pCoeffInverse
                                                                    | 
                                                                    (true,
                                                                    false)
                                                                    -> 
                                                                    -
                                                                    (value *
                                                                    pCoeffInverse)
                                                                    | 
                                                                    (false,
                                                                    true)
                                                                    -> 
                                                                    value *
                                                                    pCoeffInverse
                                                                    | 
                                                                    (false,
                                                                    false)
                                                                    -> 
                                                                    value -
                                                                    (((pRow j)
                                                                    *
                                                                    (pCol i))
                                                                    *
                                                                    pCoeffInverse)
                                                                    end)
                                                                    {
                                                                    base
                                                                    = 
                                                                    (fun r
                                                                    -> r.coeffs)
                                                                    tableau;
                                                                    row = 0;
                                                                    col = 0;
                                                                    nrows
                                                                    = 
                                                                    nRows
                                                                    ();
                                                                    ncols
                                                                    = 
                                                                    nCols
                                                                    ()}
                                                                    ;
                                                                    begin
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    row,
                                                                    pCLabel);
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    col,
                                                                    pRLabel)
                                                                    end
                                                                    end
                                                                    end;;
                                                      let rec delayMon
                                                        (Mon (n, usL_),
                                                         cnstr)
                                                        =
                                                        List.app
                                                        (function 
                                                                  | us_
                                                                    -> 
                                                                    Unify.delay
                                                                    (us_,
                                                                    cnstr))
                                                        usL_;;
                                                      let rec unifyRestr
                                                        (Restr (g_, proof),
                                                         proof')
                                                        = begin
                                                        if
                                                        Unify.unifiable
                                                        (g_, (proof, id),
                                                         (proof', id))
                                                        then () else
                                                        raise Error end;;
                                                      let rec unifySum
                                                        (g_, sum, d) = begin
                                                        if
                                                        begin
                                                          Unify.unify
                                                          (g_,
                                                           (toExp sum, id),
                                                           ((Constant_
                                                             (floor d)),
                                                            id));
                                                          true
                                                          end
                                                        then () else
                                                        raise Error end;;
                                                      type nonrec decomp =
                                                        number *
                                                        (number * position_)
                                                        list;;
                                                      let
                                                        rec unaryMinusDecomp
                                                        (d, wposL) =
                                                        (- d,
                                                         List.map
                                                         (function 
                                                                   | 
                                                                   (d, pos)
                                                                    -> 
                                                                    (- d,
                                                                    pos))
                                                         wposL);;
                                                      type maximizeResult_ =
                                                        | Nonnegative of
                                                          number 
                                                        | Unbounded of int ;;
                                                      type branchResult_ =
                                                        | BranchSucceed of
                                                          int option 
                                                        | BranchFail 
                                                        | BranchDivide of
                                                          int *
                                                          branchResult_ *
                                                          branchResult_ ;;
                                                      let rec decomposeSum
                                                        (g_, Sum (m, monL)) =
                                                        let rec monToWPos
                                                          ((Mon (n, usL_) as
                                                             mon))
                                                          =
                                                          begin
                                                          match findMon mon
                                                          with 
                                                               | Some pos
                                                                   -> 
                                                                   (fromInteger
                                                                    n, pos)
                                                               | None
                                                                   -> 
                                                                   let New_ =
                                                                    incrNCols
                                                                    ()
                                                                    in 
                                                                    let l =
                                                                    {
                                                                    owner
                                                                    = 
                                                                    (Var
                                                                    (g_,
                                                                    (Mon
                                                                    (one_int,
                                                                    usL_))));
                                                                    tag
                                                                    = 
                                                                    ref 0;
                                                                    restr
                                                                    = 
                                                                    ref
                                                                    None;
                                                                    dead
                                                                    = 
                                                                    ref
                                                                    false}
                                                                     in 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Insert
                                                                    ((Col
                                                                    New_))));
                                                                    begin
                                                                    delayMon
                                                                    (mon,
                                                                    ref
                                                                    (makeCnstr
                                                                    ((fun r
                                                                    -> r.tag)
                                                                    l)));
                                                                    begin
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    New_, l);
                                                                    (fromInteger
                                                                    n,
                                                                    (Col
                                                                    New_))
                                                                    end
                                                                    end
                                                                    end
                                                          end
                                                          in (fromInteger m,
                                                              List.map
                                                              monToWPos
                                                              monL)
                                                      and maximizeRow row =
                                                        let value = const row
                                                          in begin
                                                          if value < zero
                                                          then
                                                          begin
                                                          match findPivot row
                                                          with 
                                                               | Some 
                                                                   (i, j)
                                                                   -> begin
                                                                   if
                                                                   i <> row
                                                                   then
                                                                   begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Pivot
                                                                    (i, j)));
                                                                    begin
                                                                    pivot
                                                                    (i, j);
                                                                    maximizeRow
                                                                    row
                                                                    end
                                                                    end
                                                                   else
                                                                   (Unbounded
                                                                    j)
                                                                   end
                                                               | None
                                                                   -> 
                                                                   raise
                                                                   Error
                                                          end else
                                                          (Nonnegative value)
                                                          end
                                                      and insertDecomp
                                                        (((d, wposL) as
                                                           decomp),
                                                         owner)
                                                        =
                                                        let New_ =
                                                          incrNRows ()
                                                          in let
                                                               rec insertWPos
                                                               (d, pos) =
                                                               begin
                                                               match pos
                                                               with 
                                                                    | 
                                                                    Row row
                                                                    -> 
                                                                    begin
                                                                    incrArray2Row
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    New_,
                                                                    (0,
                                                                    nCols ()),
                                                                    function 
                                                                    | j
                                                                    -> d *
                                                                    (coeff
                                                                    (row, j)));
                                                                    incrArray
                                                                    ((fun r
                                                                    -> r.consts)
                                                                    tableau,
                                                                    New_,
                                                                    d *
                                                                    (const
                                                                    row))
                                                                    end
                                                                    | 
                                                                    Col col
                                                                    -> 
                                                                    incrArray2
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    New_,
                                                                    col, d)
                                                               end
                                                               in begin
                                                                    List.app
                                                                    insertWPos
                                                                    wposL;
                                                                    begin
                                                                    incrArray
                                                                    ((fun r
                                                                    -> r.consts)
                                                                    tableau,
                                                                    New_, d);
                                                                    begin
                                                                    match 
                                                                    isSubsumed
                                                                    New_
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some pos
                                                                    -> 
                                                                    begin
                                                                    clearArray2Row
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    New_,
                                                                    (0,
                                                                    nCols ()));
                                                                    begin
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.consts)
                                                                    tableau,
                                                                    New_,
                                                                    zero);
                                                                    begin
                                                                    decrNRows
                                                                    ();pos
                                                                    end
                                                                    end
                                                                    end
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    begin
                                                                    setOwnership
                                                                    ((Row
                                                                    New_),
                                                                    owner,
                                                                    ref 0);
                                                                    begin
                                                                    ((fun r
                                                                    -> r.dead)
                                                                    ((Label_
                                                                    ((Row
                                                                    New_)))))
                                                                    :=
                                                                    (isConstant
                                                                    New_);
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Insert
                                                                    ((Row
                                                                    New_))));
                                                                    (Row
                                                                    New_)
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                      and insert (g_, us_) =
                                                        let sum = fromExp us_
                                                          in insertDecomp
                                                             (decomposeSum
                                                              (g_, sum),
                                                              (Exp (g_, sum)))
                                                      and restrict =
                                                        function 
                                                                 | ((Col col
                                                                    as pos),
                                                                    restr)
                                                                    -> 
                                                                    let l =
                                                                    (Label_
                                                                    pos)
                                                                    in begin
                                                                    if 
                                                                    dead l
                                                                    then
                                                                    begin
                                                                    unifyRestr
                                                                    (restr,
                                                                    geqNExp
                                                                    zero_int);
                                                                    None
                                                                    end else
                                                                    begin
                                                                    match 
                                                                    restriction
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    (Restr
                                                                    (_,
                                                                    proof'))
                                                                    -> 
                                                                    begin
                                                                    unifyRestr
                                                                    (restr,
                                                                    proof');
                                                                    None
                                                                    end
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    let
                                                                    nonNull =
                                                                    Array.foldl
                                                                    (function 
                                                                    | (i,
                                                                    (l
                                                                    : label),
                                                                    rest)
                                                                    -> begin
                                                                    if
                                                                    not
                                                                    (dead l)
                                                                    then
                                                                    let value
                                                                    =
                                                                    coeff
                                                                    (i, col)
                                                                    in begin
                                                                    if
                                                                    value <>
                                                                    zero then
                                                                    (i
                                                                    :: rest)
                                                                    else rest
                                                                    end else
                                                                    rest end)
                                                                    []
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ())
                                                                    in 
                                                                    begin
                                                                    match nonNull
                                                                    with 
                                                                    
                                                                    | 
                                                                    (row
                                                                    :: _)
                                                                    -> 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Pivot
                                                                    (row,
                                                                    col)));
                                                                    begin
                                                                    pivot
                                                                    (row,
                                                                    col);
                                                                    restrict
                                                                    ((Row
                                                                    row),
                                                                    restr)
                                                                    end
                                                                    end
                                                                    | 
                                                                    []
                                                                    -> 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Restrict
                                                                    ((Col
                                                                    col))));
                                                                    begin
                                                                    ((fun r
                                                                    -> r.restr)
                                                                    ((Label_
                                                                    ((Col
                                                                    col)))))
                                                                    :=
                                                                    ((Some
                                                                    restr));
                                                                    None
                                                                    end
                                                                    end
                                                                    end
                                                                    end end
                                                                 | ((Row row
                                                                    as pos),
                                                                    restr)
                                                                    -> 
                                                                    let l =
                                                                    (Label_
                                                                    pos)
                                                                    in begin
                                                                    if 
                                                                    dead l
                                                                    then
                                                                    begin
                                                                    unifyRestr
                                                                    (restr,
                                                                    geqNExp
                                                                    (floor
                                                                    (const
                                                                    row)));
                                                                    None
                                                                    end else
                                                                    begin
                                                                    match 
                                                                    restriction
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    (Restr
                                                                    (_,
                                                                    proof'))
                                                                    -> 
                                                                    begin
                                                                    unifyRestr
                                                                    (restr,
                                                                    proof');
                                                                    None
                                                                    end
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    begin
                                                                    match 
                                                                    maximizeRow
                                                                    row
                                                                    with 
                                                                    
                                                                    | 
                                                                    Unbounded
                                                                    col
                                                                    -> 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Restrict
                                                                    ((Row
                                                                    row))));
                                                                    begin
                                                                    ((fun r
                                                                    -> r.restr)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    row))) :=
                                                                    ((Some
                                                                    restr));
                                                                    begin
                                                                    begin
                                                                    if
                                                                    (const
                                                                    row) <
                                                                    zero then
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Pivot
                                                                    (row,
                                                                    col)));
                                                                    pivot
                                                                    (row,
                                                                    col)
                                                                    end else
                                                                    () end;
                                                                    None
                                                                    end
                                                                    end
                                                                    end
                                                                    | 
                                                                    Nonnegative
                                                                    value
                                                                    -> 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Restrict
                                                                    ((Row
                                                                    row))));
                                                                    begin
                                                                    ((fun r
                                                                    -> r.restr)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    row))) :=
                                                                    ((Some
                                                                    restr));
                                                                    (Some
                                                                    row)
                                                                    end
                                                                    end
                                                                    end
                                                                    end end
                                                      and insertEqual
                                                        (g_, pos, sum) =
                                                        let (m, wposL) =
                                                          decomposeSum
                                                          (g_, sum)
                                                          in let decomp' =
                                                               (m,
                                                                ((- one, pos)
                                                                 :: wposL))
                                                               in let pos' =
                                                                    insertDecomp
                                                                    (decomp',
                                                                    (Exp
                                                                    (g_,
                                                                    (Sum
                                                                    (zero_int,
                                                                    [])))))
                                                                    in 
                                                                    let
                                                                    decomp''
                                                                    =
                                                                    unaryMinusDecomp
                                                                    decomp'
                                                                    in 
                                                                    let tag''
                                                                    =
                                                                    (fun r
                                                                    -> r.tag)
                                                                    ((Label_
                                                                    (insertDecomp
                                                                    (decomp'',
                                                                    (Exp
                                                                    (g_,
                                                                    (Sum
                                                                    (zero_int,
                                                                    []))))))))
                                                                    in 
                                                                    begin
                                                                    restrictBB
                                                                    (exploreBB
                                                                    (pos',
                                                                    (Restr
                                                                    (g_,
                                                                    geqNExp
                                                                    zero_int))));
                                                                    begin
                                                                    match 
                                                                    findTag
                                                                    tag''
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    pos''
                                                                    -> 
                                                                    restrictBB
                                                                    (exploreBB
                                                                    (pos'',
                                                                    (Restr
                                                                    (g_,
                                                                    geqNExp
                                                                    zero_int))))
                                                                    end
                                                                    end
                                                      and update
                                                        (g_, pos, sum) =
                                                        let l = (Label_ pos)
                                                          in begin
                                                               Trail.log
                                                               ((fun r
                                                                   -> 
                                                                   r.trail)
                                                                tableau,
                                                                (UpdateOwner
                                                                 (pos,
                                                                  (fun r
                                                                    -> 
                                                                    r.owner)
                                                                  l,
                                                                  (fun r
                                                                    -> 
                                                                    r.tag)
                                                                  l)));
                                                               begin
                                                                 setOwnership
                                                                 (pos,
                                                                  (Exp
                                                                   (g_, sum)),
                                                                  ref 0);
                                                                 begin
                                                                 if dead l
                                                                 then
                                                                 begin
                                                                 match pos
                                                                 with 
                                                                 
                                                                 | Row row
                                                                    -> begin
                                                                    if
                                                                    isConstant
                                                                    row then
                                                                    unifySum
                                                                    (g_, sum,
                                                                    const row)
                                                                    else
                                                                    begin
                                                                    match 
                                                                    isSubsumed
                                                                    row
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some pos'
                                                                    -> 
                                                                    update
                                                                    (g_,
                                                                    pos',
                                                                    sum)
                                                                    end end
                                                                 | Col col
                                                                    -> 
                                                                    unifySum
                                                                    (g_, sum,
                                                                    zero)
                                                                 end else
                                                                 let
                                                                   rec isVar
                                                                   =
                                                                   function 
                                                                    | Sum
                                                                    (m,
                                                                    ((Mon
                                                                    (n, _) as
                                                                    mon)
                                                                    :: []))
                                                                    -> begin
                                                                    if
                                                                    (m =
                                                                    zero_int)
                                                                    &&
                                                                    (n =
                                                                    one_int)
                                                                    then
                                                                    (Some
                                                                    mon) else
                                                                    None end
                                                                    | sum
                                                                    -> None
                                                                   in 
                                                                   begin
                                                                   match 
                                                                   isVar
                                                                   sum
                                                                   with 
                                                                   
                                                                   | 
                                                                   Some mon
                                                                    -> 
                                                                    begin
                                                                    match 
                                                                    findMon
                                                                    mon
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some _
                                                                    -> 
                                                                    insertEqual
                                                                    (g_, pos,
                                                                    sum)
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    let tag =
                                                                    ref 0
                                                                    in 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (UpdateOwner
                                                                    (pos,
                                                                    (fun r
                                                                    -> r.owner)
                                                                    l,
                                                                    (fun r
                                                                    -> r.tag)
                                                                    l)));
                                                                    begin
                                                                    setOwnership
                                                                    (pos,
                                                                    (Var
                                                                    (g_, mon)),
                                                                    tag);
                                                                    delayMon
                                                                    (mon,
                                                                    ref
                                                                    (makeCnstr
                                                                    tag))
                                                                    end
                                                                    end
                                                                    end
                                                                   | 
                                                                   None
                                                                    -> 
                                                                    insertEqual
                                                                    (g_, pos,
                                                                    sum)
                                                                   end
                                                                 end
                                                                 end
                                                               
                                                               end
                                                      and insertRestrExp
                                                        (l, ul_) =
                                                        begin
                                                        match restriction l
                                                        with 
                                                             | None -> ul_
                                                             | Some
                                                                 (Restr
                                                                  (_, _))
                                                                 -> let owner
                                                                    =
                                                                    (fun r
                                                                    -> r.owner)
                                                                    l
                                                                    in 
                                                                    let g_ =
                                                                    ownerContext
                                                                    owner
                                                                    in 
                                                                    let u_ =
                                                                    toExp
                                                                    (ownerSum
                                                                    owner)
                                                                    in 
                                                                    ((g_,
                                                                    geq0 u_)
                                                                    :: ul_)
                                                        end
                                                      and restrictions pos =
                                                        let rec member 
                                                          (x, l) =
                                                          List.exists
                                                          (function 
                                                                    | 
                                                                    y
                                                                    -> 
                                                                    x = y)
                                                          l
                                                          in let rec test l =
                                                               (restricted l)
                                                                 &&
                                                                 (not
                                                                  (dead l))
                                                               in let
                                                                    rec reachable
                                                                    =
                                                                    function 
                                                                    | (((Row
                                                                    row as
                                                                    pos)
                                                                    :: candidates),
                                                                    tried,
                                                                    closure)
                                                                    -> begin
                                                                    if
                                                                    member
                                                                    (pos,
                                                                    tried)
                                                                    then
                                                                    reachable
                                                                    (candidates,
                                                                    tried,
                                                                    closure)
                                                                    else
                                                                    let
                                                                    new_candidates
                                                                    =
                                                                    Array.foldl
                                                                    (function 
                                                                    | (col,
                                                                    _,
                                                                    candidates)
                                                                    -> begin
                                                                    if
                                                                    (coeff
                                                                    (row,
                                                                    col)) <>
                                                                    zero then
                                                                    ((Col
                                                                    col)
                                                                    :: candidates)
                                                                    else
                                                                    candidates
                                                                    end)
                                                                    []
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ())
                                                                    in 
                                                                    let
                                                                    closure'
                                                                    = begin
                                                                    if
                                                                    test
                                                                    ((Label_
                                                                    pos))
                                                                    then
                                                                    (pos
                                                                    :: closure)
                                                                    else
                                                                    closure
                                                                    end
                                                                    in 
                                                                    reachable
                                                                    (new_candidates
                                                                    @
                                                                    candidates,
                                                                    (pos
                                                                    :: tried),
                                                                    closure')
                                                                    end
                                                                    | (((Col
                                                                    col as
                                                                    pos)
                                                                    :: candidates),
                                                                    tried,
                                                                    closure)
                                                                    -> begin
                                                                    if
                                                                    member
                                                                    (pos,
                                                                    tried)
                                                                    then
                                                                    reachable
                                                                    (candidates,
                                                                    tried,
                                                                    closure)
                                                                    else
                                                                    let
                                                                    candidates'
                                                                    =
                                                                    Array.foldl
                                                                    (function 
                                                                    | (row,
                                                                    _,
                                                                    candidates)
                                                                    -> begin
                                                                    if
                                                                    (coeff
                                                                    (row,
                                                                    col)) <>
                                                                    zero then
                                                                    ((Row
                                                                    row)
                                                                    :: candidates)
                                                                    else
                                                                    candidates
                                                                    end)
                                                                    []
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ())
                                                                    in 
                                                                    let
                                                                    closure'
                                                                    = begin
                                                                    if
                                                                    test
                                                                    ((Label_
                                                                    pos))
                                                                    then
                                                                    (pos
                                                                    :: closure)
                                                                    else
                                                                    closure
                                                                    end
                                                                    in 
                                                                    reachable
                                                                    (candidates'
                                                                    @
                                                                    candidates,
                                                                    (pos
                                                                    :: tried),
                                                                    closure')
                                                                    end
                                                                    | ([], _,
                                                                    closure)
                                                                    -> closure
                                                                    in 
                                                                    let
                                                                    rec restrExp
                                                                    pos =
                                                                    let l =
                                                                    (Label_
                                                                    pos)
                                                                    in 
                                                                    let owner
                                                                    =
                                                                    (fun r
                                                                    -> r.owner)
                                                                    l
                                                                    in 
                                                                    let g_ =
                                                                    ownerContext
                                                                    owner
                                                                    in 
                                                                    let u_ =
                                                                    toExp
                                                                    (ownerSum
                                                                    owner)
                                                                    in 
                                                                    (g_,
                                                                    geq0 u_)
                                                                    in 
                                                                    List.map
                                                                    restrExp
                                                                    (reachable
                                                                    ([pos],
                                                                    [], []))
                                                      and toInternal tag () =
                                                        begin
                                                        match findTag tag
                                                        with 
                                                             | None -> []
                                                             | Some pos
                                                                 -> restrictions
                                                                    pos
                                                        end
                                                      and awake tag () =
                                                        try begin
                                                            match findTag tag
                                                            with 
                                                                 | Some pos
                                                                    -> 
                                                                    let owner
                                                                    =
                                                                    (fun r
                                                                    -> r.owner)
                                                                    ((Label_
                                                                    pos))
                                                                    in 
                                                                    let g_ =
                                                                    ownerContext
                                                                    owner
                                                                    in 
                                                                    let sum =
                                                                    normalize
                                                                    (ownerSum
                                                                    owner)
                                                                    in 
                                                                    begin
                                                                    update
                                                                    (g_, pos,
                                                                    sum);true
                                                                    end
                                                                 | None
                                                                    -> true
                                                            end
                                                        with 
                                                             | Error -> false
                                                      and simplify tag () =
                                                        begin
                                                        match toInternal
                                                              tag
                                                              ()
                                                        with 
                                                             | [] -> true
                                                             | (_ :: _)
                                                                 -> false
                                                        end
                                                      and makeCnstr tag =
                                                        (FgnCnstr
                                                         (! myID,
                                                          (MyFgnCnstrRep tag)))
                                                      and isIntegral () =
                                                        (let exception Found
                                                         of int 
                                                         in let rec find
                                                              (i,
                                                               (l : label))
                                                              = begin
                                                              if not (dead l)
                                                              then begin
                                                              if
                                                              (denominator
                                                               (const i)) <>
                                                                one_int
                                                              then
                                                              raise
                                                              ((Found i))
                                                              else () end
                                                              else () end
                                                              in try 
                                                                 begin
                                                                   Array.app
                                                                   find
                                                                   ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ());
                                                                   None
                                                                   end
                                                                 with 
                                                                 
                                                                 | Found i
                                                                    -> 
                                                                    (Some i))
                                                      and boundLower
                                                        (g_, decomp, d) =
                                                        let w_ =
                                                          newEVar
                                                          (g_, number ())
                                                          in let proof =
                                                               newEVar
                                                               (g_, geq0 w_)
                                                               in let
                                                                    (d',
                                                                    wPosL) =
                                                                    unaryMinusDecomp
                                                                    decomp
                                                                    in 
                                                                    let pos =
                                                                    insertDecomp
                                                                    ((d' + d,
                                                                    wPosL),
                                                                    (Var
                                                                    (g_,
                                                                    (Mon
                                                                    (one_int,
                                                                    [(w_, id)])))))
                                                                    in 
                                                                    (pos,
                                                                    (Restr
                                                                    (g_,
                                                                    proof)))
                                                      and boundUpper
                                                        (g_, decomp, d) =
                                                        let w_ =
                                                          newEVar
                                                          (g_, number ())
                                                          in let proof =
                                                               newEVar
                                                               (g_, geq0 w_)
                                                               in let
                                                                    (d',
                                                                    wPosL) =
                                                                    decomp
                                                                    in 
                                                                    let pos =
                                                                    insertDecomp
                                                                    ((d' - d,
                                                                    wPosL),
                                                                    (Var
                                                                    (g_,
                                                                    (Mon
                                                                    (one_int,
                                                                    [(w_, id)])))))
                                                                    in 
                                                                    (pos,
                                                                    (Restr
                                                                    (g_,
                                                                    proof)))
                                                      and exploreBB
                                                        (pos, restr) =
                                                        try let result =
                                                              restrict
                                                              (pos, restr)
                                                              in begin
                                                                 match 
                                                                 isIntegral
                                                                 ()
                                                                 with 
                                                                 
                                                                 | Some row
                                                                    -> 
                                                                    let value
                                                                    =
                                                                    const row
                                                                    in 
                                                                    let
                                                                    decomp =
                                                                    (zero,
                                                                    [(one,
                                                                    (Row row))])
                                                                    in 
                                                                    let g_ =
                                                                    ownerContext
                                                                    ((fun r
                                                                    -> r.owner)
                                                                    ((Label_
                                                                    ((Row
                                                                    row)))))
                                                                    in 
                                                                    let lower
                                                                    =
                                                                    fromInteger
                                                                    (floor
                                                                    value)
                                                                    in 
                                                                    let upper
                                                                    =
                                                                    fromInteger
                                                                    (ceiling
                                                                    value)
                                                                    in 
                                                                    let
                                                                    rec left
                                                                    () =
                                                                    exploreBB
                                                                    (boundLower
                                                                    (g_,
                                                                    decomp,
                                                                    lower))
                                                                    in 
                                                                    let
                                                                    rec right
                                                                    () =
                                                                    exploreBB
                                                                    (boundUpper
                                                                    (g_,
                                                                    decomp,
                                                                    upper))
                                                                    in 
                                                                    begin
                                                                    match 
                                                                    (CSM.trail
                                                                    left,
                                                                    CSM.trail
                                                                    right)
                                                                    with 
                                                                    
                                                                    | 
                                                                    (BranchFail,
                                                                    BranchFail)
                                                                    -> BranchFail
                                                                    | 
                                                                    (resultL,
                                                                    resultR)
                                                                    -> 
                                                                    (BranchDivide
                                                                    (row,
                                                                    resultL,
                                                                    resultR))
                                                                    end
                                                                 | None
                                                                    -> 
                                                                    (BranchSucceed
                                                                    result)
                                                                 end
                                                        with 
                                                             | Error
                                                                 -> BranchFail
                                                      and minimizeBB row =
                                                        let rec zeroColumn
                                                          (j, (l : label)) =
                                                          let decomp =
                                                            (zero,
                                                             [(one, (Col j))])
                                                            in let g_ =
                                                                 ownerContext
                                                                 ((fun r
                                                                    -> 
                                                                    r.owner)
                                                                  ((Label_
                                                                    ((Col j)))))
                                                                 in let lower
                                                                    = - one
                                                                    in 
                                                                    let upper
                                                                    = one
                                                                    in 
                                                                    let
                                                                    rec left
                                                                    () =
                                                                    exploreBB
                                                                    (boundLower
                                                                    (g_,
                                                                    decomp,
                                                                    lower))
                                                                    in 
                                                                    let
                                                                    rec right
                                                                    () =
                                                                    exploreBB
                                                                    (boundUpper
                                                                    (g_,
                                                                    decomp,
                                                                    upper))
                                                                    in begin
                                                                    if
                                                                    restricted
                                                                    l then
                                                                    (CSM.trail
                                                                    right) =
                                                                    BranchFail
                                                                    else
                                                                    ((CSM.trail
                                                                    left) =
                                                                    BranchFail)
                                                                    &&
                                                                    ((CSM.trail
                                                                    right) =
                                                                    BranchFail)
                                                                    end
                                                          in let
                                                               rec killColumn
                                                               (j,
                                                                (l : label))
                                                               = begin
                                                               if
                                                               (not (dead l))
                                                                 &&
                                                                 (((coeff
                                                                    (row, j))
                                                                    <> zero)
                                                                    &&
                                                                    (zeroColumn
                                                                    (j, l)))
                                                               then
                                                               begin
                                                                 Trail.log
                                                                 ((fun r
                                                                    -> 
                                                                    r.trail)
                                                                  tableau,
                                                                  (Kill
                                                                   ((Col j))));
                                                                 begin
                                                                   ((fun r
                                                                    -> r.dead)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    j))) :=
                                                                    true;
                                                                   begin
                                                                    begin
                                                                    match 
                                                                    restriction
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    restr
                                                                    -> 
                                                                    unifyRestr
                                                                    (restr,
                                                                    geqNExp
                                                                    zero_int)
                                                                    | 
                                                                    None
                                                                    -> ()
                                                                    end;
                                                                    begin
                                                                    match 
                                                                    (fun r
                                                                    -> r.owner)
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    (Var _ as
                                                                    owner)
                                                                    -> 
                                                                    unifySum
                                                                    (ownerContext
                                                                    owner,
                                                                    ownerSum
                                                                    owner,
                                                                    zero)
                                                                    | 
                                                                    _ -> ()
                                                                    end
                                                                    end
                                                                   
                                                                   end
                                                                 
                                                                 end
                                                               else () end
                                                               in let
                                                                    rec killRow
                                                                    (i,
                                                                    (l
                                                                    : label))
                                                                    = begin
                                                                    if
                                                                    not
                                                                    (dead l)
                                                                    then
                                                                    begin
                                                                    if
                                                                    isConstant
                                                                    i then
                                                                    begin
                                                                    begin
                                                                    if
                                                                    (denominator
                                                                    (const i))
                                                                    = one_int
                                                                    then ()
                                                                    else
                                                                    raise
                                                                    Error
                                                                    end;
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Kill
                                                                    ((Row i))));
                                                                    begin
                                                                    ((fun r
                                                                    -> r.dead)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    i))) :=
                                                                    true;
                                                                    begin
                                                                    begin
                                                                    match 
                                                                    restriction
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some
                                                                    restr
                                                                    -> begin
                                                                    if
                                                                    (denominator
                                                                    (const i))
                                                                    = one_int
                                                                    then
                                                                    unifyRestr
                                                                    (restr,
                                                                    geqNExp
                                                                    (floor
                                                                    (const i)))
                                                                    else
                                                                    raise
                                                                    Error end
                                                                    | 
                                                                    None
                                                                    -> ()
                                                                    end;
                                                                    begin
                                                                    match 
                                                                    (fun r
                                                                    -> r.owner)
                                                                    l
                                                                    with 
                                                                    
                                                                    | 
                                                                    (Var _ as
                                                                    owner)
                                                                    -> 
                                                                    unifySum
                                                                    (ownerContext
                                                                    owner,
                                                                    ownerSum
                                                                    owner,
                                                                    const i)
                                                                    | 
                                                                    _ -> ()
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                    end else
                                                                    begin
                                                                    match 
                                                                    isSubsumed
                                                                    i
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some pos'
                                                                    -> 
                                                                    let l' =
                                                                    (Label_
                                                                    pos')
                                                                    in 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Kill
                                                                    ((Row i))));
                                                                    begin
                                                                    ((fun r
                                                                    -> r.dead)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    i))) :=
                                                                    true;
                                                                    begin
                                                                    match 
                                                                    (restriction
                                                                    l,
                                                                    restriction
                                                                    l')
                                                                    with 
                                                                    
                                                                    | 
                                                                    (Some
                                                                    restr,
                                                                    Some
                                                                    (Restr
                                                                    (_,
                                                                    proof')))
                                                                    -> 
                                                                    unifyRestr
                                                                    (restr,
                                                                    proof')
                                                                    | 
                                                                    (Some _,
                                                                    None)
                                                                    -> 
                                                                    begin
                                                                    Trail.log
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau,
                                                                    (Restrict
                                                                    pos'));
                                                                    ((fun r
                                                                    -> r.restr)
                                                                    l') :=
                                                                    (restriction
                                                                    l)
                                                                    end
                                                                    | 
                                                                    (None, _)
                                                                    -> ()
                                                                    end
                                                                    end
                                                                    end
                                                                    | 
                                                                    None
                                                                    -> ()
                                                                    end end
                                                                    else ()
                                                                    end
                                                                    in 
                                                                    begin
                                                                    Array.app
                                                                    killColumn
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    0,
                                                                    nCols ());
                                                                    Array.app
                                                                    killRow
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    0,
                                                                    nRows ())
                                                                    end
                                                      and restrictBB result =
                                                        begin
                                                        match result
                                                        with 
                                                             | BranchFail
                                                                 -> raise
                                                                    Error
                                                             | BranchDivide
                                                                 (row,
                                                                  resultL,
                                                                  BranchFail)
                                                                 -> let value
                                                                    =
                                                                    fromInteger
                                                                    (floor
                                                                    (const
                                                                    row))
                                                                    in 
                                                                    let
                                                                    decomp =
                                                                    (zero,
                                                                    [(one,
                                                                    (Row row))])
                                                                    in 
                                                                    let g_ =
                                                                    ownerContext
                                                                    ((fun r
                                                                    -> r.owner)
                                                                    ((Label_
                                                                    ((Row
                                                                    row)))))
                                                                    in 
                                                                    let _ =
                                                                    restrict
                                                                    (boundLower
                                                                    (g_,
                                                                    decomp,
                                                                    value))
                                                                    in 
                                                                    restrictBB
                                                                    resultL
                                                             | BranchDivide
                                                                 (row,
                                                                  BranchFail,
                                                                  resultR)
                                                                 -> let value
                                                                    =
                                                                    fromInteger
                                                                    (ceiling
                                                                    (const
                                                                    row))
                                                                    in 
                                                                    let
                                                                    decomp =
                                                                    (zero,
                                                                    [(one,
                                                                    (Row row))])
                                                                    in 
                                                                    let g_ =
                                                                    ownerContext
                                                                    ((fun r
                                                                    -> r.owner)
                                                                    ((Label_
                                                                    ((Row
                                                                    row)))))
                                                                    in 
                                                                    let _ =
                                                                    restrict
                                                                    (boundUpper
                                                                    (g_,
                                                                    decomp,
                                                                    value))
                                                                    in 
                                                                    restrictBB
                                                                    resultR
                                                             | BranchSucceed
                                                                 result
                                                                 -> begin
                                                                    match result
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some row
                                                                    -> 
                                                                    minimizeBB
                                                                    row
                                                                    | 
                                                                    None
                                                                    -> ()
                                                                    end
                                                             | _ -> ()
                                                        end;;
                                                      let rec undo =
                                                        function 
                                                                 | Insert
                                                                    (Row row)
                                                                    -> 
                                                                    begin
                                                                    ((fun r
                                                                    -> r.dead)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.rlabels)
                                                                    tableau,
                                                                    row))) :=
                                                                    true;
                                                                    begin
                                                                    clearArray2Row
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    row,
                                                                    (0,
                                                                    nCols ()));
                                                                    begin
                                                                    Array.update
                                                                    ((fun r
                                                                    -> r.consts)
                                                                    tableau,
                                                                    row,
                                                                    zero);
                                                                    decrNRows
                                                                    ()
                                                                    end
                                                                    end
                                                                    end
                                                                 | Insert
                                                                    (Col col)
                                                                    -> 
                                                                    begin
                                                                    ((fun r
                                                                    -> r.dead)
                                                                    (Array.sub
                                                                    ((fun r
                                                                    -> r.clabels)
                                                                    tableau,
                                                                    col))) :=
                                                                    true;
                                                                    begin
                                                                    clearArray2Col
                                                                    ((fun r
                                                                    -> r.coeffs)
                                                                    tableau,
                                                                    col,
                                                                    (0,
                                                                    nRows ()));
                                                                    decrNCols
                                                                    ()
                                                                    end
                                                                    end
                                                                 | Pivot
                                                                    (row,
                                                                    col)
                                                                    -> 
                                                                    pivot
                                                                    (row,
                                                                    col)
                                                                 | Kill pos
                                                                    -> 
                                                                    ((fun r
                                                                    -> r.dead)
                                                                    ((Label_
                                                                    pos))) :=
                                                                    false
                                                                 | Restrict
                                                                    pos
                                                                    -> 
                                                                    ((fun r
                                                                    -> r.restr)
                                                                    ((Label_
                                                                    pos))) :=
                                                                    None
                                                                 | UpdateOwner
                                                                    (pos,
                                                                    owner,
                                                                    tag)
                                                                    -> 
                                                                    setOwnership
                                                                    (pos,
                                                                    owner,
                                                                    tag);;
                                                      let rec reset () =
                                                        let l =
                                                          {
                                                          owner
                                                          = (Exp
                                                             (Null,
                                                              (Sum
                                                               (zero_int, []))));
                                                          tag = ref 0;
                                                          restr = ref None;
                                                          dead = ref true}
                                                           in begin
                                                                Array.modify
                                                                (function 
                                                                    | _ -> l)
                                                                ((fun r
                                                                    -> 
                                                                    r.rlabels)
                                                                 tableau, 0,
                                                                 nRows ());
                                                                begin
                                                                  Array.modify
                                                                  (function 
                                                                    | _ -> l)
                                                                  ((fun r
                                                                    -> 
                                                                    r.clabels)
                                                                   tableau,
                                                                   0,
                                                                   nCols ());
                                                                  begin
                                                                    Array.modify
                                                                    (function 
                                                                    | _
                                                                    -> zero)
                                                                    ((fun r
                                                                    -> r.consts)
                                                                    tableau,
                                                                    0,
                                                                    nRows ());
                                                                    begin
                                                                    Array2.modify
                                                                    Array2.rowMajor_
                                                                    (function 
                                                                    | _
                                                                    -> zero)
                                                                    {
                                                                    base
                                                                    = 
                                                                    (fun r
                                                                    -> r.coeffs)
                                                                    tableau;
                                                                    row = 0;
                                                                    col = 0;
                                                                    nrows
                                                                    = 
                                                                    nRows
                                                                    ();
                                                                    ncols
                                                                    = 
                                                                    nCols
                                                                    ()}
                                                                    ;
                                                                    begin
                                                                    ((fun r
                                                                    -> r.nrows)
                                                                    tableau)
                                                                    := 0;
                                                                    begin
                                                                    ((fun r
                                                                    -> r.ncols)
                                                                    tableau)
                                                                    := 0;
                                                                    Trail.reset
                                                                    ((fun r
                                                                    -> r.trail)
                                                                    tableau)
                                                                    end
                                                                    end
                                                                    end
                                                                    end
                                                                  
                                                                  end
                                                                
                                                                end;;
                                                      let rec mark () =
                                                        Trail.mark
                                                        ((fun r -> r.trail)
                                                         tableau);;
                                                      let rec unwind () =
                                                        Trail.unwind
                                                        ((fun r -> r.trail)
                                                         tableau, undo);;
                                                      let rec fst =
                                                        function 
                                                                 | (App
                                                                    (u1_, _),
                                                                    s)
                                                                    -> 
                                                                    (u1_, s)
                                                                 | (SClo
                                                                    (s_, s'),
                                                                    s)
                                                                    -> 
                                                                    fst
                                                                    (s_,
                                                                    comp
                                                                    (s', s));;
                                                      let rec snd =
                                                        function 
                                                                 | (App
                                                                    (u1_, s_),
                                                                    s)
                                                                    -> 
                                                                    fst
                                                                    (s_, s)
                                                                 | (SClo
                                                                    (s_, s'),
                                                                    s)
                                                                    -> 
                                                                    snd
                                                                    (s_,
                                                                    comp
                                                                    (s', s));;
                                                      let rec isConstantExp
                                                        u_ =
                                                        begin
                                                        match fromExp
                                                              (u_, id)
                                                        with 
                                                             | Sum (m, [])
                                                                 -> (Some m)
                                                             | _ -> None
                                                        end;;
                                                      let rec isZeroExp u_ =
                                                        begin
                                                        match isConstantExp
                                                              u_
                                                        with 
                                                             | Some d
                                                                 -> d =
                                                                    zero_int
                                                             | None -> false
                                                        end;;
                                                      let rec solveGeq =
                                                        function 
                                                                 | (g_, s_,
                                                                    0)
                                                                    -> 
                                                                    let
                                                                    rec solveGeq0
                                                                    w_ =
                                                                    begin
                                                                    match 
                                                                    isConstantExp
                                                                    w_
                                                                    with 
                                                                    
                                                                    | 
                                                                    Some d
                                                                    -> begin
                                                                    if
                                                                    (Integers.
                                                                    ( >= )
                                                                    (d,
                                                                    zero_int))
                                                                    then
                                                                    geqNExp d
                                                                    else
                                                                    raise
                                                                    Error end
                                                                    | 
                                                                    None
                                                                    -> 
                                                                    let proof
                                                                    =
                                                                    newEVar
                                                                    (g_,
                                                                    geq0 w_)
                                                                    in 
                                                                    let _ =
                                                                    restrictBB
                                                                    (exploreBB
                                                                    (insert
                                                                    (g_,
                                                                    (w_, id)),
                                                                    (Restr
                                                                    (g_,
                                                                    proof))))
                                                                    in proof
                                                                    end
                                                                    in 
                                                                    let u1_ =
                                                                    (EClo
                                                                    (fst
                                                                    (s_, id)))
                                                                    in 
                                                                    let u2_ =
                                                                    (EClo
                                                                    (snd
                                                                    (s_, id)))
                                                                    in 
                                                                    try begin
                                                                    if
                                                                    isZeroExp
                                                                    u2_ then
                                                                    (Some
                                                                    (solveGeq0
                                                                    u1_))
                                                                    else
                                                                    let w_ =
                                                                    minus
                                                                    (u1_,
                                                                    u2_)
                                                                    in 
                                                                    let proof
                                                                    =
                                                                    solveGeq0
                                                                    w_
                                                                    in 
                                                                    (Some
                                                                    (geqAdd
                                                                    (w_,
                                                                    (Constant_
                                                                    zero_int),
                                                                    u2_,
                                                                    proof)))
                                                                    end
                                                                    with 
                                                                    
                                                                    | 
                                                                    Error
                                                                    -> None
                                                                 | (g_, s_,
                                                                    n)
                                                                    -> None;;
                                                      let rec pi
                                                        (name, u_, v_) =
                                                        (Pi
                                                         (((Dec
                                                            ((Some name), u_)),
                                                           Maybe),
                                                          v_));;
                                                      let rec arrow (u_, v_)
                                                        =
                                                        (Pi
                                                         (((Dec (None, u_)),
                                                           No),
                                                          v_));;
                                                      let
                                                        rec installFgnCnstrOps
                                                        () =
                                                        let csid = ! myID
                                                          in let _ =
                                                               FgnCnstrStd.ToInternal.install
                                                               (csid,
                                                                function 
                                                                    | MyFgnCnstrRep
                                                                    tag
                                                                    -> toInternal
                                                                    tag
                                                                    | fc
                                                                    -> raise
                                                                    ((UnexpectedFgnCnstr
                                                                    fc)))
                                                               in let _ =
                                                                    FgnCnstrStd.Awake.install
                                                                    (csid,
                                                                    function 
                                                                    | MyFgnCnstrRep
                                                                    tag
                                                                    -> awake
                                                                    tag
                                                                    | fc
                                                                    -> raise
                                                                    ((UnexpectedFgnCnstr
                                                                    fc)))
                                                                    in 
                                                                    let _ =
                                                                    FgnCnstrStd.Simplify.install
                                                                    (csid,
                                                                    function 
                                                                    | MyFgnCnstrRep
                                                                    tag
                                                                    -> simplify
                                                                    tag
                                                                    | fc
                                                                    -> raise
                                                                    ((UnexpectedFgnCnstr
                                                                    fc)))
                                                                    in ();;
                                                      let rec init
                                                        (cs, installF) =
                                                        begin
                                                          myID := cs;
                                                          begin
                                                            geqID :=
                                                              (installF
                                                               ((ConDec
                                                                 (">=", None,
                                                                  0,
                                                                  (Constraint
                                                                   (! myID,
                                                                    solveGeq)),
                                                                  (Arrow_
                                                                   (number (),
                                                                    (Arrow_
                                                                    (number
                                                                    (),
                                                                    (Uni
                                                                    Type))))),
                                                                  Kind)),
                                                                (Some
                                                                 ((FX.Infix
                                                                   (FX.minPrec,
                                                                    FX.none_)))),
                                                                [(MS.Mapp
                                                                  ((MS.Marg
                                                                    (MS.Star,
                                                                    None)),
                                                                   (MS.Mapp
                                                                    ((MS.Marg
                                                                    (MS.Star,
                                                                    None)),
                                                                    MS.Mnil))))]));
                                                            begin
                                                              geqAddID :=
                                                                (installF
                                                                 ((ConDec
                                                                   ("+>=",
                                                                    None, 2,
                                                                    Normal,
                                                                    (Pi_
                                                                    ("X",
                                                                    number (),
                                                                    (Pi_
                                                                    ("Y",
                                                                    number (),
                                                                    (Pi_
                                                                    ("Z",
                                                                    number (),
                                                                    (Arrow_
                                                                    (geq
                                                                    ((Root
                                                                    ((BVar 3),
                                                                    Nil)),
                                                                    (Root
                                                                    ((BVar 2),
                                                                    Nil))),
                                                                    geq
                                                                    (plus
                                                                    ((Root
                                                                    ((BVar 4),
                                                                    Nil)),
                                                                    (Root
                                                                    ((BVar 2),
                                                                    Nil))),
                                                                    plus
                                                                    ((Root
                                                                    ((BVar 3),
                                                                    Nil)),
                                                                    (Root
                                                                    ((BVar 2),
                                                                    Nil)))))))))))),
                                                                    Type)),
                                                                  None, []));
                                                              begin
                                                                installFgnCnstrOps
                                                                ();()
                                                                end
                                                              
                                                              end
                                                            
                                                            end
                                                          
                                                          end;;
                                                      end;;
                                                  (* CSM.ModeSyn *);;
                                                  (* useful integer values *);;
                                                  (* solver ID of this solver *);;
                                                  (* constant IDs of the declared type constants *);;
                                                  (* constructors for the declared types *);;
                                                  (* specialized constructors for the declared types *);;
                                                  (* constant IDs of the declared object constants *);;
                                                  (* constructors for the declared objects *);;
                                                  (* constant declaration for the proof object d>=0 *);;
                                                  (* foreign constant for the proof object d>=0 *);;
                                                  (* parsing proof objects d>=0 *);;
                                                  (* Position of a tableau entry       *);;
                                                  (* Owner of an entry:                *);;
                                                  (*   - monomial                      *);;
                                                  (*   - sum                           *);;
                                                  (* Restriction: (proof object)       *);;
                                                  (*   Restr (G, U)                    *);;
                                                  (* owner of the row/column (if any)  *);;
                                                  (* tag: used to keep track of the    *);;
                                                  (* position of a tableau entry       *);;
                                                  (* restriction (if any)              *);;
                                                  (* has the row/column already been   *);;
                                                  (* solved?                           *);;
                                                  (* Undoable operations:              *);;
                                                  (* insert a new row/column           *);;
                                                  (* pivot on (i, j)                   *);;
                                                  (* mark the given position solved    *);;
                                                  (* restrict the given position       *);;
                                                  (* change the owner                  *);;
                                                  (* Tableau:                          *);;
                                                  (* row labels                        *);;
                                                  (* column labels                     *);;
                                                  (* constant terms                    *);;
                                                  (* variables coefficients            *);;
                                                  (* dimensions                        *);;
                                                  (* undo mechanism                    *);;
                                                  (* FgnCnstr representation *);;
                                                  (* Representational invariants:
         rlabels[i] = vacuous
         clabels[j] = vacuous
         const[i] = zero
         coeff[i,j] = zero
       for i >= !nrows or j > !ncols, where ""vacuous"" is the vacuous label:
          #owner(vacuous) = Exp (Null, Sum (zero, nil))
          #restr(vacuous) = ref NONE
          #dead(vacuous) = ref true
    *);;
                                                  (* little random generation routine taken from Paulson '91 *);;
                                                  (* create a new (empty) tableau *);;
                                                  (* i-th tableau row label *);;
                                                  (* j-th tableau column label *);;
                                                  (* i-th tableau constant term *);;
                                                  (* coefficient in row i, column j *);;
                                                  (* number of rows *);;
                                                  (* number of columns *);;
                                                  (* increase the number of rows, and return the index of the last row *);;
                                                  (* increase the number of columns, and return the index of the last column *);;
                                                  (* decrease the number of rows *);;
                                                  (* decrease the number of columns *);;
                                                  (* increase by the given amount the element i of the array *);;
                                                  (* increase by the given amount the element (i, j) of the array *);;
                                                  (* increase by f(j') all the elements (i, j'), with j <= j' < j+len *);;
                                                  (* increase by f(i') all the elements (i', j), with i <= i' < i+len *);;
                                                  (* set the given row to zero *);;
                                                  (* set the given column to zero *);;
                                                  (* return the label at the given position (row or column) *);;
                                                  (* return the restriction on the given label *);;
                                                  (* is the given label is restricted? *);;
                                                  (* return true iff the given label has been solved *);;
                                                  (* set the ownership of the given position *);;
                                                  (* return the context of a owner *);;
                                                  (* return the owner as a sum *);;
                                                  (* debugging code - REMOVE *);;
                                                  (* debugging code - REMOVE *);;
                                                  (* debugging code - REMOVE *);;
                                                  (* find the given monomial in the tableau *);;
                                                  (* return the a position in the tableau of the tagged expression *);;
                                                  (* return true iff the given row is null at all the active columns *);;
                                                  (* return the position of the row/column of the tableau (if any) that makes the
       given row redundant *);;
                                                  (* the candidates are those (active) rows with the same constant
                       term *);;
                                                  (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *);;
                                                  (* compute the list of non-null coefficients in the row *);;
                                                  (* find the coordinates of the pivot which gives the largest increase in
        const(row) *);;
                                                  (* extend Integers.compare to deal with NONE (= infinity) *);;
                                                  (* find the best pivot candidates for the given row *);;
                                                  (* find the best pivot candidates for the given row and column *);;
                                                  (* always choose the smallest *);;
                                                  (* always choose the largest *);;
                                                  (* choose one randomly to ensure fairness *);;
                                                  (* pivot the element at the given coordinates *);;
                                                  (* same row as the pivot *);;
                                                  (* any other row *);;
                                                  (* pivot *);;
                                                  (* same row as the pivot *);;
                                                  (* same column as the pivot *);;
                                                  (* any other row/column *);;
                                                  (* delay all terms of a monomial on the given constraint *);;
                                                  (* unify two restrictions *);;
                                                  (* unify a sum with a number *);;
                                                  (* decomposition of an expression as the weighted sum of tableau positions *);;
                                                  (* change sign to the given decomposition *);;
                                                  (* Result of maximization of a row:             *);;
                                                  (* nonnegative value c                          *);;
                                                  (* manifestly unbounded, pivoting on column col *);;
                                                  (* decompose a sum in whnf into a weighted sum of tableau positions *);;
                                                  (* maximize the given row by performing pivot operations.
       Return a term of type MaximizeResult *);;
                                                  (* the tableau is unbounded *);;
                                                  (* insert the given expression in the tableau, labelling it with owner *);;
                                                  (* add the decomposition to the newly created row *);;
                                                  (* is this row trivial? *);;
                                                  (* log the creation of this row *);;
                                                  (* return its position *);;
                                                  (* insert the given (unrestricted) expression in the tableau *);;
                                                  (* restrict the given row/column to be nonnegative *);;
                                                  (* compute the list of non-null row entries *);;
                                                  (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *);;
                                                  (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *);;
                                                  (* it is an integer *);;
                                                  (* insert the equality Var(pos) = Us as two inequalities:
         Var(pos) - Us >= zero
         Us - Var(pos) >= zero
    *);;
                                                  (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *);;
                                                  (* update the tableau upon discovery that Var(pos) = sum *);;
                                                  (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *);;
                                                  (* analyze the given position to see exactly how to represent this
                 equality *);;
                                                  (* find out why it died *);;
                                                  (* row is dead because constant and equal to n *);;
                                                  (* row is dead because is subsumed by another *);;
                                                  (* column is dead because = 0 *);;
                                                  (* the nf is another variable *);;
                                                  (* recycle the current label *);;
                                                  (* insert the proof term used to restrict l (if any) at the beginning of UL *);;
                                                  (* returns the list of unsolved constraints associated with the given position *);;
                                                  (* returns the list of unsolved constraints associated with the given tag *);;
                                                  (* awake function for tableau constraints *);;
                                                  (* simplify function for tableau constraints *);;
                                                  (* create a foreign constraint for the given tag *);;
                                                  (* checks if the (primally and dually) feasible solution is an integral solution;
       returns NONE if it is, otherwise the coordinate of a non-integral component *);;
                                                  (* unbounded component *);;
                                                  (* bound the given expression below d *);;
                                                  (* bound the given expression above d *);;
                                                  (* explore the relaxed solution space looking for integer solutions *);;
                                                  (* minimize a tableau that has been determined non-minimal (but consistent) as a
       consequence of adding the given row
    *);;
                                                  (* check if the column is zero for all possible solutions *);;
                                                  (* equate the given column to zero if coeff(row, j) <> zero *);;
                                                  (* mark the column dead *);;
                                                  (* if restricted, instantiate the proof object to 0>=0 *);;
                                                  (* if owned by a monomial, unify it with zero *);;
                                                  (* find out if the given row has been made trivial by killing some columns *);;
                                                  (* row is now constant and equal to n = const(i) *);;
                                                  (* check if it is an integer *);;
                                                  (* mark the row dead *);;
                                                  (* if restricted, instantiate the proof object to n>=0 *);;
                                                  (* if owned by a monomial, unify it with n *);;
                                                  (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *);;
                                                  (* undo function for trailing tableau operations *);;
                                                  (* reset the internal status of the tableau *);;
                                                  (* trailing functions *);;
                                                  (* fst (S, s) = U1, the first argument in S[s] *);;
                                                  (* snd (S, s) = U2, the second argument in S[s] *);;
                                                  (* checks if the given foreign term can be simplified to a constant *);;
                                                  (* checks if the given foreign term can be simplified to zero *);;
                                                  (* solveGeq (G, S, n) tries to find the n-th solution to G |- '>=' @ S : type *);;
                                                  (* constructors for higher-order types *);;
                                                  (* install the signature *);;
                                                  let solver =
                                                    ({
                                                     name
                                                     = "inequality/integers";
                                                     keywords
                                                     = "arithmetic,inequality";
                                                     needs
                                                     = ["Unify";
                                                        (fun r -> r.name)
                                                        CSEqIntegers.solver];
                                                     fgnConst
                                                     = (Some
                                                        { parse = parseGeqN} );
                                                     init;
                                                     reset;
                                                     mark;
                                                     unwind}
                                                      : CSManager.solver);;
                                                  end;;
(* functor CSIneqIntegers *);;
# 1 "src/solvers/cs_ineq_integers.sml.ml"
