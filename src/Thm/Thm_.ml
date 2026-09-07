open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Formatter.Formatter_
open! Modes
open! Modes__Modes_
open! Paths.Paths_
open! Tabling

(* # 1 "src/thm/Thm_.sig.ml" *)
open Thmsyn
open Thmprint

(* Theorem Declarations *)
(* Author: Carsten Schuermann *)

include THM
(** Modified: Brigitte Pientka, Frank Pfenning *)

(* signature THM *)

(* # 1 "src/thm/Thm_.fun.ml" *)
open! Basis

(* Theorem and Related Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module Make_Thm
    (Global : GLOBAL)
    (ThmSyn' : THMSYN)
    (TabledSyn : Tabledsyn.TABLEDSYN)
    (ModeTable : Modetable.MODETABLE)
    (Order : ORDER)
    (ThmPrint : Thmprint.THMPRINT) : THM with module ThmSyn = ThmSyn' = struct
  module ThmSyn = ThmSyn'

  (*! structure Paths = Paths' !*)
  module TabledSyn = TabledSyn

  (* -bp *)
  type order = Varg | Lex of order list | Simul of order list
  [@@deriving eq, ord, show]

  exception Error of string

  open! struct
    module L = ThmSyn
    module M = Modesyn.ModeSyn
    module I = IntSyn
    module P = ThmPrint
    module O = Order

    let error r msg = raise (Error (Paths.wrap r msg))

    let unique (((a, p), r), a_) =
      let rec unique' (b, c, a_) = match b, c with
        | I.Uni _, [] -> a_
        | I.Pi (_, v), None :: p -> unique' (v, p, a_)
        | I.Pi (_, v), Some x :: p -> begin
            List.app
              (function
                | x' ->
                    begin if x = x' then
                      error r (("Variable " ^ x) ^ " used more than once")
                    else ()
                    end)
              a_;
            unique' (v, p, x :: a_)
          end
        | I.Uni _, _ ->
            error
              r ("Too many arguments supplied to type family "
                ^ Names.qidToString (Names.constQid a))
        | I.Pi (_, v), [] ->
            error
              r ("Too few arguments supplied to type family "
                ^ Names.qidToString (Names.constQid a))
        | I.Root _, _ ->
            error
              r (("Constant " ^ Names.qidToString (Names.constQid a))
                ^ " is an object, not a type family")
      in
      let rec skip (k, a, p, a_) = match k, a with
        | 0, v -> unique' (v, p, a_)
        | k, I.Pi (_, v) -> skip (k - 1, v, p, a_)
      in
      skip (I.constImp a, I.constType a, p, a_)

    let uniqueCallpats (l, rs) =
      let rec uniqueCallpats' (a, a_) = match a with
        | ([], []) -> ()
        | (aP :: l, r :: rs) ->
            uniqueCallpats' ((l, rs), unique ((aP, r), a_))
      in
      uniqueCallpats' ((l, rs), [])

    let wfCallpats (l0, c0, r) =
      let rec makestring = function
        | [] -> ""
        | s :: [] -> s
        | s :: l -> (s ^ " ") ^ makestring l
      in
      let rec exists' (x, a, b) = match a, b with
        | [], _ -> false
        | None :: l, M.Mapp (_, mS) -> exists' (x, l, mS)
        | Some y :: l, M.Mapp (M.Marg (mode, _), mS) ->
            begin if x = y then
              begin match mode with
              | M.Plus -> true
              | _ ->
                  error
                    r (((("Expected " ^ x) ^ " to have ") ^ M.modeToString M.Plus)
                      ^ " mode")
              end
            else exists' (x, l, mS)
            end
      in
      let rec skip (k, x, p, a) = match k, a with
        | 0, mS -> exists' (x, p, mS)
        | k, M.Mapp (_, mS) -> skip (k - 1, x, p, mS)
      in
      let rec delete (x, b) = match b with
        | ((a, p) as aP) :: c ->
            begin if skip (I.constImp a, x, p, valOf (ModeTable.modeLookup a))
            then c
            else aP :: delete (x, c)
            end
        | [] -> error r (("Variable " ^ x) ^ " does not occur as argument")
      in
      let rec wfCallpats' = function
        | [], [] -> ()
        | x :: l, c -> wfCallpats' (l, delete (x, c))
        | _ ->
            error
              r (("Mutual argument (" ^ makestring l0)
                ^ ") does not cover all call patterns")
      in
      wfCallpats' (l0, c0)

    let wf ((o, L.Callpats c), (r, rs)) =
      let rec wfOrder = function
        | L.Varg l -> wfCallpats (l, c, r)
        | L.Lex l -> wfOrders l
        | L.Simul l -> wfOrders l
      and wfOrders = function
        | [] -> ()
        | o :: l -> begin
            wfOrder o;
            wfOrders l
          end
      in
      let rec allModed = function
        | [] -> ()
        | (a, p) :: cs -> begin
            begin match ModeTable.modeLookup a with
            | None ->
                error
                  r (("Expected " ^ Names.qidToString (Names.constQid a))
                    ^ " to be moded")
            | Some mS -> ()
            end;
            allModed cs
          end
      in
      allModed c;
      begin
        uniqueCallpats (c, rs);
        wfOrder o
      end

    let rec argPos (x, a, n) = match a with
      | [] -> None
      | None :: l -> argPos (x, l, n + 1)
      | Some x' :: l ->
          begin if x = x' then Some n else argPos (x, l, n + 1)
          end

    let rec locate (x :: vars, params, imp) =
      begin match argPos (x, params, imp + 1) with
      | None -> locate (vars, params, imp)
      | Some n -> n
      end

    let rec argOrder (a, p, n) = match a with
      | L.Varg l -> O.Arg (locate (l, p, n))
      | L.Simul l -> O.Simul (argOrderL (l, p, n))
      | L.Lex l -> O.Lex (argOrderL (l, p, n))

    and argOrderL (a, p, n) = match a with
      | [] -> []
      | o :: l -> argOrder (o, p, n) :: argOrderL (l, p, n)

    let rec argOrderMutual (a, k, a_) = match a with
      | [] -> a_
      | p :: l -> argOrderMutual (l, k, k (p, a_))

    let rec installOrder (o, b, thmsLT) = match b with
      | [] -> ()
      | ((a, p) as aP) :: thmsLE ->
          let m' =
            argOrderMutual
              ( thmsLE,
                (function (a, _), l -> O.Le (a, l)),
                argOrderMutual
                  ( aP :: thmsLT,
                    (function (a, _), l -> O.Lt (a, l)),
                    O.Empty ) )
          in
          let o' = argOrder (o, p, I.constImp a) in
          let s' = O.install a (O.TDec (o', m')) in
          installOrder (o, thmsLE, aP :: thmsLT)

    let installDecl (o, L.Callpats l) =
      begin
        installOrder (o, l, []);
        map (function a, _ -> a) l
      end

    let installTerminates (L.TDecl (o, cp)) rrs =
      begin
        wf ((o, cp), rrs);
        installDecl (o, cp)
      end

    let uninstallTerminates cid = O.uninstall cid

    let installTotal (L.TDecl (o, cp)) rrs =
      begin
        wf ((o, cp), rrs);
        installDecl (o, cp)
      end

    let uninstallTotal cid = O.uninstall cid

    let rec argROrder (a, p, n) = match a with
      | L.Varg l -> O.Arg (locate (l, p, n))
      | L.Simul l -> O.Simul (argROrderL (l, p, n))
      | L.Lex l -> O.Lex (argROrderL (l, p, n))

    and argROrderL (a, p, n) = match a with
      | [] -> []
      | o :: l -> argROrder (o, p, n) :: argROrderL (l, p, n)

    let argPredicate (a, o, o') = match a with
      | L.Less -> O.Less (o, o')
      | L.Leq -> O.Leq (o, o')
      | L.Eq -> O.Eq (o, o')

    let rec installPredicate (b, c, thmsLT) = match b, c with
      | _, [] -> ()
      | L.RedOrder (pred, o1, o2), ((a, p) as aP) :: thmsLE ->
          let m' =
            argOrderMutual
              ( thmsLE,
                (function (a, _), l -> O.Le (a, l)),
                argOrderMutual
                  ( aP :: thmsLT,
                    (function (a, _), l -> O.Lt (a, l)),
                    O.Empty ) )
          in
          let o1' = argROrder (o1, p, I.constImp a) in
          let o2' = argROrder (o2, p, I.constImp a) in
          let pr = argPredicate (pred, o1', o2') in
          let s'' = O.installROrder a (O.RDec (pr, m')) in
          installPredicate (L.RedOrder (pred, o1, o2), thmsLE, aP :: thmsLT)

    let installRDecl (r, L.Callpats l) =
      begin
        installPredicate (r, l, []);
        map (function a, _ -> a) l
      end

    let wfRCallpats (l0, c0, r) =
      let rec makestring = function
        | [] -> ""
        | s :: [] -> s
        | s :: l -> (s ^ " ") ^ makestring l
      in
      let rec exists' (x, a) = match a with
        | [] -> false
        | None :: l -> exists' (x, l)
        | Some y :: l -> x = y || exists' (x, l)
      in
      let rec delete (x, b) = match b with
        | ((a, p) as aP) :: c ->
            begin if exists' (x, p) then c else aP :: delete (x, c)
            end
        | [] -> error r (("Variable " ^ x) ^ " does not occur as argument")
      in
      let rec wfCallpats' = function
        | [], [] -> ()
        | x :: l, c -> wfCallpats' (l, delete (x, c))
        | _ ->
            error
              r (("Mutual argument (" ^ makestring l0)
                ^ ") does not cover all call patterns")
      in
      wfCallpats' (l0, c0)

    let wfred ((L.RedOrder (pred, o, o'), L.Callpats c), (r, rs)) =
      let rec wfOrder = function
        | L.Varg l -> begin
            wfRCallpats (l, c, r);
            Varg
          end
        | L.Lex l -> Lex (wfOrders l)
        | L.Simul l -> Simul (wfOrders l)
      and wfOrders = function
        | [] -> []
        | o :: l -> wfOrder o :: wfOrders l
      in
      uniqueCallpats (c, rs);
      begin if wfOrder o = wfOrder o' then ()
      else
        error
          r (("Reduction Order ("
            ^ P.rOrderToString
                (Obj.magic (L.RedOrder (pred, o, o')) : P.ThmSyn.redOrder)
            )
            ^ ") requires both orders to be of the same type.")
      end

    let installReduces (L.RDecl (r, c)) rrs =
      begin
        wfred ((r, c), rrs);
        installRDecl (r, c)
      end

    let uninstallReduces cid = O.uninstallROrder cid
    let installTabled (L.TabledDecl cid) = TabledSyn.installTabled cid
    let installKeepTable (L.KeepTableDecl cid) = TabledSyn.installKeepTable cid
  end

  (* L.ModeSyn *)
  (* To check validity of a termination declaration  O C
       we enforce that all variable names which occur in C must be distinct
       and if C = C1 .. Cm then we ensure that for all Varg (X1 .. Xn) in O,

           1) n = m
       and 2) each Ci contains an occurrence of Xi
    *)
  (* unique (((a, P), r), A) = A'

       Invariant:
       If   A is a list of variables already collected in a call pattern
       and  P does not contain any variables in A
       then A' = A, Var (P)
       else exception Error is raised.
       (r is region information for error message)
    *)
  (* uniqueCallpats (L, rs) = ()

       Invariant:
       If   L is a callpattern
       and  each variable in L is unique
       then uniqueCallpats returns ()
       else exception Error is raised.

       (rs is a list of region information for error message,
       each region corresponds to one type in the call pattern,
       in order)
    *)
  (* wfCallpats (L, C, r) = ()

       Invariant:
       If   L is a list of variable names of a virtual argument
       and  C is a call pattern, the predicate in C has a mode
       then wfCallpats terminates with () if
            1) there are as many call patterns as variable names
            2) each variable name occurs in a different call pattern
       else exception Error is raised
       (r region information, needed for error messages)
    *)
  (* skip (i, x, P, mS)  ignores first i argument in modeSpine mS,
             then returns true iff x occurs in argument list P
             Effect: raises Error if position of x is not input (+).
          *)
  (* exists by invariant *)
  (* wf ((O, C), (r, rs)) = ()

       Invariant:
       If   O is an order
       and  C is a call pattern
       then wf terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
  (* argPos (x, L, n) = nOpt

       Invariant:
       If   x is a variable name
       and  L is a list of argument for a call pattern
       and  n is the position of the first argument name in L
            in the call pattern
       then nOpt describes the optional  position of the occurrence
    *)
  (* locate (L, P, n) = n'

       Invariant:
       If   L is a list of variable names (as part of a virtual argument)
       and  P is an argument list (from a call pattern)
       and  n is the position of the first argument name in P
            in the call pattern
       then n' describes the position of the virtual argument in P
    *)
  (* locate nil cannot occur by invariant *)
  (* argOrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)
  (*  argOrderMutual (C, k, A) = A'

        Invariant:

        If   C is a list of call patterns
        and  k is a function, mapping a call patterns to 'a
        and  A is an acculmulator for objects of type 'a
        then A' is an accumulator extending A containing all
             images of C under k.
    *)
  (* installorder (O, LE, LT) = ()

       Invariant:
       If   O is an order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument order with type families.
    *)
  (* installDecl (O, C) = L'

       Invariant:
       If   O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: All orders are stored
    *)
  (* installTerminates (T, (r,rs)) = L'

       Invariant:
       If   T is a termination declaration of (O, C)
       and  O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (O, C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
  (* installTotal (T, (r, rs)) = L'
       Invariant as in installTerminates
    *)
  (* -bp *)
  (* argROrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)
  (* installPredicate (name, R, LE, LT) = ()

       Invariant:
       If   R is a reduction order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument reduction order with
               type families.

    *)
  (* install termination order *)
  (* bug: %reduces should not entail %terminates *)
  (* fixed: Sun Mar 13 09:41:18 2005 -fp *)
  (* val S'  = O.install (a, O.TDec (O2', M')) *)
  (* install reduction order   *)
  (* installRDecl (R, C) = L'

       Invariant:
       If   R is a reduction order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: reduction order is stored
    *)
  (* wfRCallpats
       well-formed call pattern in a reduction declaration
       pattern does not need to be moded
       Tue Apr 30 10:32:31 2002 -bp
     *)
  (* wfred ((Red(Pred,O.O'), C), (r, rs)) = ()

       Invariant:
       If   O,O' is an order and Pred is some predicate
       and  C is a call pattern
       then wfred terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
  (* installRedOrder (R, (r,rs)) = L'

       Invariant:
       If   R is a reduction declaration of (pred(O,O'), C)
       and  O,O' is an order
       and pred is a predicate
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (pred(O,O'), C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
  let installTotal = installTotal
  let uninstallTotal = uninstallTotal
  let installTerminates = installTerminates
  let uninstallTerminates = uninstallTerminates
  let installReduces = installReduces
  let uninstallReduces = uninstallReduces
  let installTabled = installTabled
  let installKeepTable = installKeepTable
end

(*! structure Paths' : PATHS !*)
(* local *)
(* functor Thm *)

(* # 1 "src/thm/Thm_.sml.ml" *)

module ThmSyn = ThmSyn (struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure ModeSyn' = ModeSyn !*)
  module Abstract = Abstract
  module Whnf = Whnf
  module Paths' = Paths
  module Names' = Names
end)

module ThmPrint = ThmPrint (struct
  module ThmSyn' = ThmSyn
  module Formatter = Formatter
end)

module Thm =
  Make_Thm (Global) (ThmSyn) (Tabled.TabledSyn) (ModeTable) (Order) (ThmPrint)
