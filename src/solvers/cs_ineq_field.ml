(* # 1 "src/solvers/cs_ineq_field.sig.ml" *)

(* # 1 "src/solvers/cs_ineq_field.fun.ml" *)
open! Basis

module Cs_ineq_field (CSIneqField__0 : sig
  (* Solver for a linearly ordered field, based on the simplex method *)
  (* Author: Roberto Virga *)
  module OrderedField : Ordered_field.ORDERED_FIELD

  (*! structure IntSyn : INTSYN !*)
  module Trail : TRAIL
  module Unify : UNIFY

  (*! sharing Unify.IntSyn = IntSyn !*)
  module SparseArray : Sparse_array.SPARSE_ARRAY
  module SparseArray2 : Sparse_array2.SPARSE_ARRAY2

  (*! structure Cs_manager : CS_MANAGER !*)
  (*! sharing Cs_manager.IntSyn = IntSyn !*)
  module Cs_eq_field :
    Cs_eq_field.CS_EQ_FIELD with type Field.number = OrderedField.number

  (*! sharing Cs_eq_field.IntSyn = IntSyn !*)
  (*! sharing Cs_eq_field.Cs_manager = Cs_manager !*)
end) : Cs.CS = struct
  (*! structure Cs_manager = Cs_manager !*)
  module OrderedField = CSIneqField__0.OrderedField
  module Trail = CSIneqField__0.Trail
  module Unify = CSIneqField__0.Unify
  module SparseArray = CSIneqField__0.SparseArray
  module SparseArray2 = CSIneqField__0.SparseArray2
  module Cs_eq_field = CSIneqField__0.Cs_eq_field

  open! struct
    open IntSyn
    open OrderedField
    open Cs_eq_field
    module FX = Cs_manager.Fixity
    module MS = ModeSyn
    module Array = SparseArray
    module Array2 = SparseArray2

    let myID = (ref (-1) : cid ref)
    let gtID = (ref (-1) : cid ref)
    let geqID = (ref (-1) : cid ref)
    let rec gt (u_, v_) = Root (Const !gtID, App (u_, App (v_, Nil)))
    let rec geq (u_, v_) = Root (Const !geqID, App (u_, App (v_, Nil)))
    let rec gt0 u_ = gt (u_, constant zero)
    let rec geq0 u_ = geq (u_, constant zero)
    let gtAddID = (ref (-1) : cid ref)
    let geqAddID = (ref (-1) : cid ref)
    let gtGeqID = (ref (-1) : cid ref)
    let geq00ID = (ref (-1) : cid ref)

    let rec gtAdd (u1_, u2_, v_, w_) =
      Root (Const !gtAddID, App (u1_, App (u2_, App (v_, App (w_, Nil)))))

    let rec geqAdd (u1_, u2_, v_, w_) =
      Root (Const !geqAddID, App (u1_, App (u2_, App (v_, App (w_, Nil)))))

    let rec gtGeq (u_, v_, w_) =
      Root (Const !gtGeqID, App (u_, App (v_, App (w_, Nil))))

    let rec geq00 () = Root (Const !geq00ID, Nil)

    let rec gtNConDec d =
      ConDec
        ( (toString d ^ ">") ^ toString zero,
          None,
          0,
          Normal,
          gt0 (constant d),
          Type )

    let rec gtNExp d = Root (FgnConst (!myID, gtNConDec d), Nil)

    let rec geqN0 d =
      begin if d = zero then geq00 ()
      else gtGeq (constant d, constant zero, gtNExp d)
      end

    let rec parseGtN string =
      let suffix = ">" ^ toString zero in
      let stringLen = String.size string in
      let suffixLen = String.size suffix in
      let numLen = Stdlib.( - ) stringLen suffixLen in
      begin if
        Stdlib.( > ) stringLen suffixLen
        && String.substring (string, numLen, suffixLen) = suffix
      then begin
        match fromString (String.substring (string, 0, numLen)) with
        | Some d -> begin if d > zero then Some (gtNConDec d) else None end
        | None -> None
      end
      else None
      end

    type position = Row of int | Col of int
    type owner = Var of IntSyn.dctx * mon_ | Exp of IntSyn.dctx * sum_
    type restriction = Restr of IntSyn.dctx * IntSyn.exp * bool

    type nonrec label = {
      owner : owner;
      tag : int ref;
      restr : restriction option ref;
      dead : bool ref;
    }

    type operation =
      | Insert of position
      | Pivot of int * int
      | Kill of position
      | Restrict of position
      | UpdateOwner of position * owner * int ref

    type nonrec tableau = {
      rlabels : label Array.array;
      clabels : label Array.array;
      consts : number Array.array;
      coeffs : number Array2.array;
      nrows : int ref;
      ncols : int ref;
      trail : operation Trail.trail;
    }

    exception MyFgnCnstrRep of int ref
    exception Error

    open! struct
      let a = 16807.0
      let m = 2147483647.0
      let seed = ref 1999.0
    end

    let rec rand (min, size) =
      let rec nextrand () =
        let t = a *. !seed in
        begin
          seed := t -. (m *. Float.of_int (Float.to_int (t /. m)));
          (!seed -. 1.0) /. (m -. 1.0)
        end
      in
      Stdlib.( + ) min (Float.to_int (nextrand () *. Float.of_int size))

    let tableau =
      let l =
        {
          owner = Exp (Null, Sum (zero, []));
          tag = ref 0;
          restr = ref None;
          dead = ref true;
        }
      in
      ({
         rlabels = Array.array l;
         clabels = Array.array l;
         consts = Array.array zero;
         coeffs = Array2.array zero;
         nrows = ref 0;
         ncols = ref 0;
         trail = Trail.trail ();
       }
        : tableau)

    let rec rlabel i = Array.sub (tableau.rlabels, i)
    let rec clabel j = Array.sub (tableau.clabels, j)
    let rec const i = Array.sub (tableau.consts, i)
    let rec coeff (i, j) = Array2.sub (tableau.coeffs, i, j)
    let rec nRows () = !(tableau.nrows)
    let rec nCols () = !(tableau.ncols)

    let rec incrNRows () =
      let old = nRows () in
      begin
        tableau.nrows := Stdlib.( + ) old 1;
        old
      end

    let rec incrNCols () =
      let old = nCols () in
      begin
        tableau.ncols := Stdlib.( + ) old 1;
        old
      end

    let rec decrNRows () = tableau.nrows := Stdlib.( - ) (nRows ()) 1
    let rec decrNCols () = tableau.ncols := Stdlib.( - ) (nCols ()) 1

    let rec incrArray (array, i, value) =
      Array.update (array, i, Array.sub (array, i) + value)

    let rec incrArray2 (array, i, j, value) =
      Array2.update (array, i, j, Array2.sub (array, i, j) + value)

    let rec incrArray2Row (array, i, (j, len), f) =
      ignore
        (Vector.mapi
           (function j, value -> Array2.update (array, i, j, value + f j))
           (Array2.row (array, i, (j, len))))

    let rec incrArray2Col (array, j, (i, len), f) =
      ignore
        (Vector.mapi
           (function i, value -> Array2.update (array, i, j, value + f i))
           (Array2.column (array, j, (i, len))))

    let rec clearArray2Row (array, i, (j, len)) =
      ignore
        (Vector.mapi
           (function j, _value -> Array2.update (array, i, j, zero))
           (Array2.row (array, i, (j, len))))

    let rec clearArray2Col (array, j, (i, len)) =
      ignore
        (Vector.mapi
           (function i, _value -> Array2.update (array, i, j, zero))
           (Array2.column (array, j, (i, len))))

    let rec label = function Row i -> rlabel i | Col j -> clabel j
    let rec restriction (l : label) = !(l.restr)

    let rec restricted (l : label) =
      begin match restriction l with Some _ -> true | None -> false
      end

    let rec dead (l : label) = !(l.dead)

    let rec setOwnership (pos, owner, tag) =
      let old = label pos in
      let new_ =
        { owner; tag; restr = ref (restriction old); dead = ref (dead old) }
      in
      begin match pos with
      | Row i -> Array.update (tableau.rlabels, i, new_)
      | Col j -> Array.update (tableau.clabels, j, new_)
      end

    let rec ownerContext = function
      | Var (g_, _mon) -> g_
      | Exp (g_, _sum) -> g_

    let rec ownerSum = function
      | Var (_g_, mon) -> Sum (zero, [ mon ])
      | Exp (_g_, sum) -> sum

    let rec displayPos = function
      | Row row -> print (("row " ^ Int.toString row) ^ "\n")
      | Col col -> print (("column " ^ Int.toString col) ^ "\n")

    let rec displaySum = function
      | Sum (m, Mon (n, _) :: monL) -> begin
          print (OrderedField.toString n);
          begin
            print " ? + ";
            displaySum (Sum (m, monL))
          end
        end
      | Sum (m, []) -> begin
          print (OrderedField.toString m);
          print " >= 0\n"
        end

    let rec display () =
      let rec printLabel (_col, (l : label)) =
        begin
          print "\t";
          begin
            begin match l.owner with Var _ -> print "V" | Exp _ -> print "E"
            end;
            begin
              begin if restricted l then print ">" else print "*"
              end;
              begin if dead l then print "#" else print ""
              end
            end
          end
        end
      in
      let rec printRow (row, (l : label)) =
        let rec printCol (_col, (d : number)) =
          begin
            print "\t";
            print (toString d)
          end
        in
        let vec = Array2.row (tableau.coeffs, row, (0, nCols ())) in
        begin
          begin match l.owner with Var _ -> print "V" | Exp _ -> print "E"
          end;
          begin
            begin if restricted l then print ">" else print "*"
            end;
            begin
              begin if dead l then print "#" else print ""
              end;
              begin
                print "\t";
                begin
                  ignore (Vector.mapi printCol vec);
                  begin
                    print "\t";
                    begin
                      print (toString (const row));
                      print "\n"
                    end
                  end
                end
              end
            end
          end
        end
      in
      begin
        print "\t";
        begin
          Array.app printLabel (tableau.clabels, 0, nCols ());
          begin
            print "\n";
            begin
              Array.app printRow (tableau.rlabels, 0, nRows ());
              begin
                print "Columns:\n";
                begin
                  Array.app
                    (function _, (l : label) -> displaySum (ownerSum l.owner))
                    (tableau.clabels, 0, nCols ());
                  begin
                    print "Rows:\n";
                    Array.app
                      (function
                        | _, (l : label) -> displaySum (ownerSum l.owner))
                      (tableau.rlabels, 0, nRows ())
                  end
                end
              end
            end
          end
        end
      end

    let rec findMon mon =
      let exception Found of int in
      let rec find (i, (l : label)) =
        begin match l.owner with
        | Var (_g_, mon') -> begin
            if compatibleMon (mon, mon') then raise (Found i) else ()
          end
        | _ -> ()
        end
      in
      try
        begin
          Array.app find (tableau.clabels, 0, nCols ());
          try
            begin
              Array.app find (tableau.rlabels, 0, nRows ());
              None
            end
          with Found i -> Some (Row i)
        end
      with Found j -> Some (Col j)

    let rec findTag t =
      let exception Found of int in
      let rec find (i, (l : label)) =
        begin if l.tag = t then raise (Found i) else ()
        end
      in
      try
        begin
          Array.app find (tableau.clabels, 0, nCols ());
          try
            begin
              Array.app find (tableau.rlabels, 0, nRows ());
              None
            end
          with Found i -> Some (Row i)
        end
      with Found j -> Some (Col j)

    let rec isConstant row =
      Array.foldl
        (function j, l, rest -> (dead l || coeff (row, j) = zero) && rest)
        true
        (tableau.clabels, 0, nCols ())

    let rec isSubsumed row =
      let constRow = const row in
      let rec isSubsumedByRow () =
        let candidates =
          Array.foldl
            (function
              | i, (l : label), rest -> begin
                  if i <> row && (not (dead l)) && const i = constRow then
                    i :: rest
                  else rest
                end)
            []
            (tableau.rlabels, 0, nRows ())
        in
        let rec filter = function
          | _j, _l, [] -> []
          | j, (l : label), candidates -> begin
              if not (dead l) then
                List.filter
                  (function i -> coeff (i, j) = coeff (row, j))
                  candidates
              else candidates
            end
        in
        begin match
          Array.foldl filter candidates (tableau.clabels, 0, nCols ())
        with
        | [] -> None
        | i :: _ -> Some i
        end
      in
      let rec isSubsumedByCol () =
        begin if constRow = zero then
          let nonNull =
            Array.foldl
              (function
                | j, (l : label), rest -> begin
                    if not (dead l) then
                      let value = coeff (row, j) in
                      begin if value <> zero then (j, value) :: rest else rest
                      end
                    else rest
                  end)
              []
              (tableau.clabels, 0, nCols ())
          in
          begin match nonNull with
          | (j, value) :: [] -> begin if value = one then Some j else None end
          | _ -> None
          end
        else None
        end
      in
      begin match isSubsumedByRow () with
      | Some i -> Some (Row i)
      | None -> begin
          match isSubsumedByCol () with Some j -> Some (Col j) | None -> None
        end
      end

    let rec findPivot row =
      let rec compareScore = function
        | Some d, Some d' -> compare (d, d')
        | Some _d, None -> Less
        | None, Some _d' -> Greater
        | None, None -> Equal
      in
      let rec findPivotCol (j, (l : label), ((score, champs) as result)) =
        let value = coeff (row, j) in
        let rec findPivotRow sgn (i, (l : label), ((score, champs) as result)) =
          let value = coeff (i, j) in
          begin if
            (not (dead l))
            && i <> row && restricted l
            && fromInt sgn * value < zero
          then
            let score' = Some (abs (const i * inverse value)) in
            begin match compareScore (score, score') with
            | Greater -> (score', [ (i, j) ])
            | Equal -> (score, (i, j) :: champs)
            | Less -> result
            end
          else result
          end
        in
        begin if
          (not (dead l))
          && value <> zero
          && ((not (restricted l)) || value > zero)
        then
          let ((score', champs') as result') =
            Array.foldl
              (findPivotRow (sign value))
              (None, [ (row, j) ])
              (tableau.rlabels, 0, nRows ())
          in
          begin match compareScore (score, score') with
          | Greater -> result
          | Equal -> (score, champs @ champs')
          | Less -> result'
          end
        else result
        end
      in
      begin match
        Array.foldl findPivotCol (Some zero, []) (tableau.clabels, 0, nCols ())
      with
      | _, [] -> None
      | _, champs -> Some (List.nth (champs, rand (0, List.length champs)))
      end

    let rec pivot (row, col) =
      let pCoeffInverse = inverse (coeff (row, col)) in
      let pRowVector = Array2.row (tableau.coeffs, row, (0, nCols ())) in
      let rec pRow j = Vector.sub (pRowVector, j) in
      let pColVector = Array2.column (tableau.coeffs, col, (0, nRows ())) in
      let rec pCol i = Vector.sub (pColVector, i) in
      let pConst = const row in
      let pRLabel = rlabel row in
      let pCLabel = clabel col in
      begin
        Array.modify
          (function
            | i, value -> begin
                if i = row then -(value * pCoeffInverse)
                else value - (pConst * pCol i * pCoeffInverse)
              end)
          (tableau.consts, 0, nRows ());
        begin
          Array2.modify Array2.ColMajor
            (function
              | i, j, value -> begin
                  match (i = row, j = col) with
                  | true, true -> pCoeffInverse
                  | true, false -> -(value * pCoeffInverse)
                  | false, true -> value * pCoeffInverse
                  | false, false -> value - (pRow j * pCol i * pCoeffInverse)
                end)
            {
              base = tableau.coeffs;
              row = 0;
              col = 0;
              nrows = nRows ();
              ncols = nCols ();
            };
          begin
            Array.update (tableau.rlabels, row, pCLabel);
            Array.update (tableau.clabels, col, pRLabel)
          end
        end
      end

    type maximizeResult = Positive | Maximized of number | Unbounded of int

    let rec maximizeRow row =
      let value = const row in
      begin if value <= zero then begin
        match findPivot row with
        | Some (i, j) -> begin
            if i <> row then begin
              Trail.log (tableau.trail, Pivot (i, j));
              begin
                pivot (i, j);
                maximizeRow row
              end
            end
            else Unbounded j
          end
        | None -> Maximized value
      end
      else Positive
      end

    let rec delayMon (Mon (_n, usL_), cnstr) =
      List.app (function us_ -> Unify.delay (us_, cnstr)) usL_

    let rec unifyRestr (Restr (g_, proof, _strict), proof') =
      begin if Unify.unifiable (g_, (proof, id), (proof', id)) then ()
      else raise Error
      end

    let rec unifySum (g_, sum, d) =
      begin if Unify.unifiable (g_, (toExp sum, id), (constant d, id)) then ()
      else raise Error
      end

    type nonrec decomp = number * (number * position) list

    let rec unaryMinusDecomp (d, wposL) =
      (-d, List.map (function d, pos -> (-d, pos)) wposL)

    let rec decomposeSum (g_, Sum (m, monL)) =
      let rec monToWPos (Mon (n, usL_) as mon) =
        begin match findMon mon with
        | Some pos -> (n, pos)
        | None ->
            let new_ = incrNCols () in
            let l =
              {
                owner = Var (g_, Mon (one, usL_));
                tag = ref 0;
                restr = ref None;
                dead = ref false;
              }
            in
            begin
              Trail.log (tableau.trail, Insert (Col new_));
              begin
                delayMon (mon, ref (makeCnstr l.tag));
                begin
                  Array.update (tableau.clabels, new_, l);
                  (n, Col new_)
                end
              end
            end
        end
      in
      (m, List.map monToWPos monL)

    and insertDecomp (((d, wposL) as decomp), owner) =
      let new_ = incrNRows () in
      let rec insertWPos (d, pos) =
        begin match pos with
        | Row row -> begin
            incrArray2Row
              ( tableau.coeffs,
                new_,
                (0, nCols ()),
                function j -> d * coeff (row, j) );
            incrArray (tableau.consts, new_, d * const row)
          end
        | Col col -> incrArray2 (tableau.coeffs, new_, col, d)
        end
      in
      begin
        List.app insertWPos wposL;
        begin
          incrArray (tableau.consts, new_, d);
          begin match isSubsumed new_ with
          | Some pos -> begin
              clearArray2Row (tableau.coeffs, new_, (0, nCols ()));
              begin
                Array.update (tableau.consts, new_, zero);
                begin
                  decrNRows ();
                  pos
                end
              end
            end
          | None -> begin
              setOwnership (Row new_, owner, ref 0);
              begin
                (label (Row new_)).dead := isConstant new_;
                begin
                  Trail.log (tableau.trail, Insert (Row new_));
                  Row new_
                end
              end
            end
          end
        end
      end

    and insert (g_, us_) =
      let sum = fromExp us_ in
      insertDecomp (decomposeSum (g_, sum), Exp (g_, sum))

    and minimize row =
      let rec killColumn (j, (l : label)) =
        begin if (not (dead l)) && coeff (row, j) <> zero then begin
          Trail.log (tableau.trail, Kill (Col j));
          begin
            (Array.sub (tableau.clabels, j)).dead := true;
            begin
              begin match restriction l with
              | Some restr -> unifyRestr (restr, geq00 ())
              | None -> ()
              end;
              begin match l.owner with
              | Var _ as owner ->
                  unifySum (ownerContext owner, ownerSum owner, zero)
              | _ -> ()
              end
            end
          end
        end
        else ()
        end
      in
      let rec killRow (i, (l : label)) =
        begin if not (dead l) then begin
          if isConstant i then begin
            Trail.log (tableau.trail, Kill (Row i));
            begin
              (Array.sub (tableau.rlabels, i)).dead := true;
              begin
                begin match restriction l with
                | Some restr -> unifyRestr (restr, geqN0 (const i))
                | None -> ()
                end;
                begin match l.owner with
                | Var _ as owner ->
                    unifySum (ownerContext owner, ownerSum owner, const i)
                | _ -> ()
                end
              end
            end
          end
          else begin
            match isSubsumed i with
            | Some pos' ->
                let l' = label pos' in
                begin
                  Trail.log (tableau.trail, Kill (Row i));
                  begin
                    (Array.sub (tableau.rlabels, i)).dead := true;
                    begin match (restriction l, restriction l') with
                    | Some restr, Some (Restr (_, proof', _)) ->
                        unifyRestr (restr, proof')
                    | Some _, None -> begin
                        Trail.log (tableau.trail, Restrict pos');
                        l'.restr := restriction l
                      end
                    | None, _ -> ()
                    end
                  end
                end
            | None -> ()
          end
        end
        else ()
        end
      in
      begin
        Array.app killColumn (tableau.clabels, 0, nCols ());
        Array.app killRow (tableau.rlabels, 0, nRows ())
      end

    and restrict = function
      | (Col col as pos), restr ->
          let l = label pos in
          begin if dead l then unifyRestr (restr, geq00 ())
          else begin
            match restriction l with
            | Some (Restr (_, proof', _)) -> unifyRestr (restr, proof')
            | None ->
                let nonNull =
                  Array.foldl
                    (function
                      | i, (l : label), rest -> begin
                          if not (dead l) then
                            let value = coeff (i, col) in
                            begin if value <> zero then i :: rest else rest
                            end
                          else rest
                        end)
                    []
                    (tableau.rlabels, 0, nRows ())
                in
                begin match nonNull with
                | row :: _ -> begin
                    Trail.log (tableau.trail, Pivot (row, col));
                    begin
                      pivot (row, col);
                      restrict (Row row, restr)
                    end
                  end
                | [] -> begin
                    Trail.log (tableau.trail, Restrict (Col col));
                    (label (Col col)).restr := Some restr
                  end
                end
          end
          end
      | (Row row as pos), restr ->
          let l = label pos in
          begin if dead l then unifyRestr (restr, geqN0 (const row))
          else begin
            match restriction l with
            | Some (Restr (_, proof', _)) -> unifyRestr (restr, proof')
            | None -> begin
                match maximizeRow row with
                | Unbounded col -> begin
                    Trail.log (tableau.trail, Restrict (Row row));
                    begin
                      (Array.sub (tableau.rlabels, row)).restr := Some restr;
                      begin if const row < zero then begin
                        Trail.log (tableau.trail, Pivot (row, col));
                        pivot (row, col)
                      end
                      else ()
                      end
                    end
                  end
                | Positive -> begin
                    Trail.log (tableau.trail, Restrict (Row row));
                    (Array.sub (tableau.rlabels, row)).restr := Some restr
                  end
                | Maximized value -> begin
                    if value = zero then begin
                      Trail.log (tableau.trail, Restrict (Row row));
                      begin
                        (Array.sub (tableau.rlabels, row)).restr := Some restr;
                        minimize row
                      end
                    end
                    else raise Error
                  end
              end
          end
          end

    and insertEqual (g_, pos, sum) =
      let m, wposL = decomposeSum (g_, sum) in
      let decomp' = (m, (-one, pos) :: wposL) in
      let pos' = insertDecomp (decomp', Exp (g_, Sum (zero, []))) in
      let decomp'' = unaryMinusDecomp decomp' in
      let tag'' =
        (label (insertDecomp (decomp'', Exp (g_, Sum (zero, []))))).tag
      in
      begin
        restrict (pos', Restr (g_, geq00 (), false));
        begin match findTag tag'' with
        | Some pos'' -> restrict (pos'', Restr (g_, geq00 (), false))
        end
      end

    and update (g_, pos, sum) =
      let l = label pos in
      begin
        Trail.log (tableau.trail, UpdateOwner (pos, l.owner, l.tag));
        begin
          setOwnership (pos, Exp (g_, sum), ref 0);
          begin if dead l then begin
            match pos with
            | Row row -> begin
                if isConstant row then unifySum (g_, sum, const row)
                else begin
                  match isSubsumed row with Some pos' -> update (g_, pos', sum)
                end
              end
            | Col _col -> unifySum (g_, sum, zero)
          end
          else
            let rec isVar = function
              | Sum (m, (Mon (n, _) as mon) :: []) -> begin
                  if m = zero && n = one then Some mon else None
                end
              | _sum -> None
            in
            begin match isVar sum with
            | Some mon -> begin
                match findMon mon with
                | Some _ -> insertEqual (g_, pos, sum)
                | None ->
                    let tag = ref 0 in
                    begin
                      Trail.log
                        (tableau.trail, UpdateOwner (pos, l.owner, l.tag));
                      begin
                        setOwnership (pos, Var (g_, mon), tag);
                        delayMon (mon, ref (makeCnstr tag))
                      end
                    end
              end
            | None -> insertEqual (g_, pos, sum)
            end
          end
        end
      end

    and restrictions pos =
      let rec member (x, l) = List.exists (function y -> x = y) l in
      let rec test l = restricted l && not (dead l) in
      let rec reachable = function
        | (Row row as pos) :: candidates, tried, closure -> begin
            if member (pos, tried) then reachable (candidates, tried, closure)
            else
              let new_candidates =
                Array.foldl
                  (function
                    | col, _, candidates -> begin
                        if coeff (row, col) <> zero then Col col :: candidates
                        else candidates
                      end)
                  []
                  (tableau.clabels, 0, nCols ())
              in
              let closure' =
                begin if test (label pos) then pos :: closure else closure
                end
              in
              reachable (new_candidates @ candidates, pos :: tried, closure')
          end
        | (Col col as pos) :: candidates, tried, closure -> begin
            if member (pos, tried) then reachable (candidates, tried, closure)
            else
              let candidates' =
                Array.foldl
                  (function
                    | row, _, candidates -> begin
                        if coeff (row, col) <> zero then Row row :: candidates
                        else candidates
                      end)
                  []
                  (tableau.rlabels, 0, nRows ())
              in
              let closure' =
                begin if test (label pos) then pos :: closure else closure
                end
              in
              reachable (candidates' @ candidates, pos :: tried, closure')
          end
        | [], _, closure -> closure
      in
      let rec restrExp pos =
        let l = label pos in
        let owner = l.owner in
        let g_ = ownerContext owner in
        let u_ = toExp (ownerSum owner) in
        begin match restriction (label pos) with
        | Some (Restr (_, _, true)) -> (g_, gt0 u_)
        | _ -> (g_, geq0 u_)
        end
      in
      List.map restrExp (reachable ([ pos ], [], []))

    and makeCnstr tag = FgnCnstr (!myID, MyFgnCnstrRep tag)

    let rec toInternal tag () =
      begin match findTag tag with None -> [] | Some pos -> restrictions pos
      end

    let rec awake tag () =
      try
        begin match findTag tag with
        | Some pos ->
            let owner = (label pos).owner in
            let g_ = ownerContext owner in
            let sum = normalize (ownerSum owner) in
            begin
              update (g_, pos, sum);
              true
            end
        | None -> true
        end
      with Error -> false

    let rec simplify tag () =
      begin match toInternal tag () with [] -> true | _ :: _ -> false
      end

    let rec undo = function
      | Insert (Row row) -> begin
          (Array.sub (tableau.rlabels, row)).dead := true;
          begin
            clearArray2Row (tableau.coeffs, row, (0, nCols ()));
            begin
              Array.update (tableau.consts, row, zero);
              decrNRows ()
            end
          end
        end
      | Insert (Col col) -> begin
          (Array.sub (tableau.clabels, col)).dead := true;
          begin
            clearArray2Col (tableau.coeffs, col, (0, nRows ()));
            decrNCols ()
          end
        end
      | Pivot (row, col) -> pivot (row, col)
      | Kill pos -> (label pos).dead := false
      | Restrict pos -> (label pos).restr := None
      | UpdateOwner (pos, owner, tag) -> setOwnership (pos, owner, tag)

    let rec reset () =
      let l =
        {
          owner = Exp (Null, Sum (zero, []));
          tag = ref 0;
          restr = ref None;
          dead = ref true;
        }
      in
      begin
        Array.modify (function _ -> l) (tableau.rlabels, 0, nRows ());
        begin
          Array.modify (function _ -> l) (tableau.clabels, 0, nCols ());
          begin
            Array.modify (function _ -> zero) (tableau.consts, 0, nRows ());
            begin
              Array2.modify Array2.RowMajor
                (function _ -> zero)
                {
                  base = tableau.coeffs;
                  row = 0;
                  col = 0;
                  nrows = nRows ();
                  ncols = nCols ();
                };
              begin
                tableau.nrows := 0;
                begin
                  tableau.ncols := 0;
                  Trail.reset tableau.trail
                end
              end
            end
          end
        end
      end

    let rec mark () = Trail.mark tableau.trail
    let rec unwind () = Trail.unwind (tableau.trail, undo)

    let rec fst = function
      | App (u1_, _), s -> (u1_, s)
      | SClo (s_, s'), s -> fst (s_, comp (s', s))

    let rec snd = function
      | App (_u1_, s_), s -> fst (s_, s)
      | SClo (s_, s'), s -> snd (s_, comp (s', s))

    let rec isConstantExp u_ =
      begin match fromExp (u_, id) with Sum (m, []) -> Some m | _ -> None
      end

    let rec isZeroExp u_ =
      begin match isConstantExp u_ with Some d -> d = zero | None -> false
      end

    let rec solveGt = function
      | g_, s_, 0 -> (
          let rec solveGt0 w_ =
            begin match isConstantExp w_ with
            | Some d -> begin if d > zero then gtNExp d else raise Error end
            | None ->
                let proof = newEVar (g_, gt0 w_) in
                let _ =
                  restrict
                    ( insert (g_, (w_, id)),
                      Restr (g_, gtGeq (w_, constant zero, proof), true) )
                in
                proof
            end
          in
          let u1_ =
            let e_, s_' = fst (s_, id) in
            EClo (e_, s_')
          in
          let u2_ =
            let e_, s_' = snd (s_, id) in
            EClo (e_, s_')
          in
          try
            begin if isZeroExp u2_ then Some (solveGt0 u1_)
            else
              let w_ = minus (u1_, u2_) in
              let proof = solveGt0 w_ in
              Some (gtAdd (w_, constant zero, u2_, proof))
            end
          with Error -> None)
      | _g_, _s_, _n -> None

    let rec solveGeq = function
      | g_, s_, 0 -> (
          let rec solveGeq0 w_ =
            begin match isConstantExp w_ with
            | Some d -> begin if d >= zero then geqN0 d else raise Error end
            | None ->
                let proof = newEVar (g_, geq0 w_) in
                let _ =
                  restrict (insert (g_, (w_, id)), Restr (g_, proof, false))
                in
                proof
            end
          in
          let u1_ =
            let e_, s_' = fst (s_, id) in
            EClo (e_, s_')
          in
          let u2_ =
            let e_, s_' = snd (s_, id) in
            EClo (e_, s_')
          in
          try
            begin if isZeroExp u2_ then Some (solveGeq0 u1_)
            else
              let w_ = minus (u1_, u2_) in
              let proof = solveGeq0 w_ in
              Some (geqAdd (w_, constant zero, u2_, proof))
            end
          with Error -> None)
      | _g_, _s_, _n -> None

    let rec pi (name, u_, v_) = Pi ((Dec (Some name, u_), Maybe), v_)
    let rec arrow (u_, v_) = Pi ((Dec (None, u_), No), v_)

    let rec installFgnCnstrOps () =
      let csid = !myID in
      let _ =
        FgnCnstrStd.ToInternal.install
          ( csid,
            function
            | MyFgnCnstrRep tag -> toInternal tag
            | fc -> raise (UnexpectedFgnCnstr fc) )
      in
      let _ =
        FgnCnstrStd.Awake.install
          ( csid,
            function
            | MyFgnCnstrRep tag -> awake tag
            | fc -> raise (UnexpectedFgnCnstr fc) )
      in
      let _ =
        FgnCnstrStd.Simplify.install
          ( csid,
            function
            | MyFgnCnstrRep tag -> simplify tag
            | fc -> raise (UnexpectedFgnCnstr fc) )
      in
      ()

    let rec init (cs, installF) =
      begin
        myID := cs;
        begin
          gtID :=
            installF
              ( ConDec
                  ( ">",
                    None,
                    0,
                    Constraint (!myID, solveGt),
                    arrow_ (number (), arrow_ (number (), Uni Type)),
                    Kind ),
                Some (FX.Infix (FX.minPrec, FX.None)),
                [
                  MS.Mapp
                    ( MS.Marg (MS.Star, None),
                      MS.Mapp (MS.Marg (MS.Star, None), MS.Mnil) );
                ] );
          begin
            geqID :=
              installF
                ( ConDec
                    ( ">=",
                      None,
                      0,
                      Constraint (!myID, solveGeq),
                      arrow_ (number (), arrow_ (number (), Uni Type)),
                      Kind ),
                  Some (FX.Infix (FX.minPrec, FX.None)),
                  [
                    MS.Mapp
                      ( MS.Marg (MS.Star, None),
                        MS.Mapp (MS.Marg (MS.Star, None), MS.Mnil) );
                  ] );
            begin
              gtAddID :=
                installF
                  ( ConDec
                      ( "+>",
                        None,
                        2,
                        Normal,
                        pi
                          ( "X",
                            number (),
                            pi
                              ( "Y",
                                number (),
                                pi
                                  ( "Z",
                                    number (),
                                    arrow_
                                      ( gt
                                          ( Root (BVar 3, Nil),
                                            Root (BVar 2, Nil) ),
                                        gt
                                          ( plus
                                              ( Root (BVar 4, Nil),
                                                Root (BVar 2, Nil) ),
                                            plus
                                              ( Root (BVar 3, Nil),
                                                Root (BVar 2, Nil) ) ) ) ) ) ),
                        Type ),
                    None,
                    [] );
              begin
                geqAddID :=
                  installF
                    ( ConDec
                        ( "+>=",
                          None,
                          2,
                          Normal,
                          pi
                            ( "X",
                              number (),
                              pi
                                ( "Y",
                                  number (),
                                  pi
                                    ( "Z",
                                      number (),
                                      arrow_
                                        ( geq
                                            ( Root (BVar 3, Nil),
                                              Root (BVar 2, Nil) ),
                                          geq
                                            ( plus
                                                ( Root (BVar 4, Nil),
                                                  Root (BVar 2, Nil) ),
                                              plus
                                                ( Root (BVar 3, Nil),
                                                  Root (BVar 2, Nil) ) ) ) ) )
                            ),
                          Type ),
                      None,
                      [] );
                begin
                  gtGeqID :=
                    installF
                      ( ConDec
                          ( ">>=",
                            None,
                            2,
                            Normal,
                            pi
                              ( "X",
                                number (),
                                pi
                                  ( "Y",
                                    number (),
                                    arrow_
                                      ( gt
                                          ( Root (BVar 2, Nil),
                                            Root (BVar 1, Nil) ),
                                        geq
                                          ( Root (BVar 3, Nil),
                                            Root (BVar 2, Nil) ) ) ) ),
                            Type ),
                        None,
                        [] );
                  begin
                    geq00ID :=
                      installF
                        ( ConDec
                            ("0>=0", None, 0, Normal, geq0 (constant zero), Type),
                          None,
                          [] );
                    begin
                      installFgnCnstrOps ();
                      ()
                    end
                  end
                end
              end
            end
          end
        end
      end
  end

  (* Cs_manager.ModeSyn *)
  (* solver ID of this solver *)
  (* constant IDs of the declared type constants *)
  (* constructors for the declared types *)
  (* specialized constructors for the declared types *)
  (* constant IDs of the declared object constants *)
  (* constructors for the declared objects *)
  (* constant declaration for the proof object d>0 *)
  (* foreign constant for the proof object d>0 *)
  (* specialized constructors for the declared objects *)
  (* parsing proof objects d>0 *)
  (* Position of a tableau entry       *)
  (* Owner of an entry:                *)
  (*   - monomial                      *)
  (*   - sum                           *)
  (* Restriction: (proof object)       *)
  (*   Restr (G, U, strict)            *)
  (* owner of the row/column (if any)  *)
  (* tag: used to keep track of the    *)
  (* position of a tableau entry       *)
  (* restriction (if any)              *)
  (* has the row/column already been   *)
  (* solved?                           *)
  (* Undoable operations:              *)
  (* insert a new row/column           *)
  (* pivot on (i, j)                   *)
  (* mark the given position solved    *)
  (* restrict the given position       *)
  (* change the owner                  *)
  (* Tableau:                          *)
  (* row labels                        *)
  (* column labels                     *)
  (* constant terms                    *)
  (* variables coefficients            *)
  (* dimensions                        *)
  (* undo mechanism                    *)
  (* FgnCnstr representation *)
  (* Representational invariants:
         rlabels[i] = vacuous
         clabels[j] = vacuous
         const[i] = zero
         coeff[i,j] = zero
       for i >= !nrows or j > !ncols, where ""vacuous"" is the vacuous label:
          #owner(vacuous) = Exp (Null, Sum (zero, nil))
          #restr(vacuous) = ref NONE
          #dead(vacuous) = ref true
    *)
  (* little random generation routine taken from Paulson '91 *)
  (* create a new (empty) tableau *)
  (* i-th tableau row label *)
  (* j-th tableau column label *)
  (* i-th tableau constant term *)
  (* coefficient in row i, column j *)
  (* number of rows *)
  (* number of columns *)
  (* increase the number of rows, and return the index of the last row *)
  (* increase the number of columns, and return the index of the last column *)
  (* decrease the number of rows *)
  (* decrease the number of columns *)
  (* increase by the given amount the element i of the array *)
  (* increase by the given amount the element (i, j) of the array *)
  (* increase by f(j') all the elements (i, j'), with j <= j' < j+len *)
  (* increase by f(i') all the elements (i', j), with i <= i' < i+len *)
  (* set the given row to zero *)
  (* set the given column to zero *)
  (* return the label at the given position (row or column) *)
  (* return the restriction on the given label *)
  (* is the given label is restricted? *)
  (* return true iff the given label has been solved *)
  (* set the ownership of the given position *)
  (* return the context of a owner *)
  (* return the owner as a sum *)
  (* debugging code - REMOVE *)
  (* debugging code - REMOVE *)
  (* debugging code - REMOVE *)
  (* find the given monomial in the tableau *)
  (* return the a position in the tableau of the tagged expression *)
  (* return true iff the given row is null at all the active columns *)
  (* return the position of the row/column of the tableau (if any) that makes the
       given row redundant *)
  (* the candidates are those (active) rows with the same constant
                       term *)
  (* if j is active, trim the list of candidates to those that have
                       the same coefficient in column j
                    *)
  (* compute the list of non-null coefficients in the row *)
  (* find the coordinates of the pivot which gives the largest increase in const(row) *)
  (* extend Field.compare to deal with NONE (= infinity) *)
  (* find the best pivot candidates for the given row *)
  (* find the best pivot candidates for the given row and column *)
  (* always choose the smallest *)
  (* always choose the largest *)
  (* choose one randomly to ensure fairness *)
  (* pivot the element at the given coordinates *)
  (* same row as the pivot *)
  (* any other row *)
  (* pivot *)
  (* same row as the pivot *)
  (* same column as the pivot *)
  (* any other row/column *)
  (* Result of maximization of a row:             *)
  (* manifestly maximized at some value > 0       *)
  (* manifestly maximized at c <= 0               *)
  (* manifestly unbounded, pivoting on column col *)
  (* maximize the given row by performing pivot operations.
       Return a term of type MaximizeResult.
    *)
  (* delay all terms of a monomial on the given constraint *)
  (* unify two restrictions *)
  (* unify a sum with a number *)
  (* decomposition of an expression as the weighted sum of tableau positions *)
  (* change sign to the given decomposition *)
  (* decompose a sum in whnf into a weighted sum of tableau positions *)
  (* insert the given expression in the tableau, labelling it with owner *)
  (* add the decomposition to the newly created row *)
  (* is this row trivial? *)
  (* log the creation of this row *)
  (* return its position *)
  (* insert the given (unrestricted) expression in the tableau *)
  (* minimize a tableau that has been determined non-minimal (but consistent) as a
       consequence of adding the given row.
    *)
  (* equate the given column to zero if coeff(row, j) <> zero *)
  (* mark the column dead *)
  (* if restricted, instantiate the proof object to 0>=0 *)
  (* if owned by a monomial, unify it with zero *)
  (* find out if the given row has been made trivial by killing some
               columns
            *)
  (* row is now constant and equal to n = const(i) *)
  (* mark the row dead *)
  (* if restricted, instantiate the proof object to n>=0 *)
  (* if owned by a monomial, unify it with n *)
  (* it is safe to restrict without doing all
                                              the checks in this case, since the two rows
                                              are identical *)
  (* restrict the given row/column to be nonnegative *)
  (* compute the list of non-null row entries *)
  (* pivot to a row position; this is sound since
                                   the column is unrestricted (see Nelson '81)
                                *)
  (* the column is zero at all the active row
                                   positions, so we can restrict it right away
                                *)
  (* the tableau is satisfiable and minimal *)
  (* the tableau is satisfiable but not minimal*)
  (* insert the equality Var(pos) = Us as two inequalities:
         Var(pos) - Us >= zero
         Us - Var(pos) >= zero
    *)
  (* the second expression may change position when we
                  restrict the first. We use tags to keep track of it *)
  (* update the tableau upon discovery that Var(pos) = sum *)
  (* if the given position has a owner, delete it, since not doing so
                 may violate the invariant *)
  (* analyze the given position to see exactly how to represent this
                 equality *)
  (* find out why it died *)
  (* row is dead because constant and equal to n *)
  (* row is dead because is subsumed by another *)
  (* column is dead because = 0 *)
  (* the nf is another variable *)
  (* recycle the current label *)
  (* returns the list of unsolved constraints associated with the given position *)
  (* create a foreingn constraint for the given tag *)
  (* returns the list of unsolved constraints associated with the given tag *)
  (* awake function for tableau constraints *)
  (* simplify function for tableau constraints *)
  (* undo function for trailing tableau operations *)
  (* reset the internal status of the tableau *)
  (* trailing functions *)
  (* fst (S, s) = U1, the first argument in S[s] *)
  (* snd (S, s) = U2, the second argument in S[s] *)
  (* checks if the given foreign term can be simplified to a constant *)
  (* checks if the given foreign term can be simplified to zero *)
  (* solveGt (G, S, n) tries to find the n-th solution to G |- '>' @ S : type *)
  (* solveGeq (G, S, n) tries to find the n-th solution to G |- '>=' @ S : type *)
  (* constructors for higher-order types *)
  (* install the signature *)
  let solver =
    ({
       name = ("inequality/" ^ OrderedField.name) ^ "s";
       keywords = "arithmetic,inequality";
       needs = [ "Unify"; Cs_eq_field.solver.name ];
       fgnConst = Some { parse = parseGtN };
       init;
       reset;
       mark;
       unwind;
     }
      : Cs_manager.solver)
end
(* functor Cs_ineq_field *)

(* # 1 "src/solvers/cs_ineq_field.sml.ml" *)
