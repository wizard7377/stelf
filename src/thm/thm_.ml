(* # 1 "src/thm/thm_.sig.ml" *)
open! Basis
open Thmsyn
open Thmprint

(* Theorem Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka, Frank Pfenning *)
module type THM = sig
  module ThmSyn : THMSYN

  (*! structure Paths : PATHS !*)
  exception Error of string

  val installTotal :
    ThmSyn.tDecl_ * (Paths.region * Paths.region list) -> IntSyn.cid list

  val uninstallTotal : IntSyn.cid -> bool

  val installTerminates :
    ThmSyn.tDecl_ * (Paths.region * Paths.region list) -> IntSyn.cid list

  val uninstallTerminates : IntSyn.cid -> bool

  (* true: was declared, false not *)
  val installReduces :
    ThmSyn.rDecl_ * (Paths.region * Paths.region list) -> IntSyn.cid list

  val uninstallReduces : IntSyn.cid -> bool
  val installTabled : ThmSyn.tabledDecl_ -> unit
  val installKeepTable : ThmSyn.keepTableDecl_ -> unit
end
(* signature THM *)

(* # 1 "src/thm/thm_.fun.ml" *)
open! Basis

(* Theorem and Related Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)
module Make_Thm (Thm__0 : sig
  module Global : GLOBAL
  module ThmSyn' : THMSYN
  module TabledSyn : Tabledsyn.TABLEDSYN
  module ModeTable : Modetable.MODETABLE
  module Order : ORDER

  (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*)
  module ThmPrint : Thmprint.THMPRINT
end) : THM with module ThmSyn = Thm__0.ThmSyn' = struct
  open Thm__0
  module ThmSyn = ThmSyn'

  (*! structure Paths = Paths' !*)
  module TabledSyn = TabledSyn

  (* -bp *)
  type order_ = Varg | Lex of order_ list | Simul of order_ list

  exception Error of string

  open! struct
    module L = ThmSyn
    module M = ModeSyn
    module I = IntSyn
    module P = ThmPrint
    module O = Order

    let rec error (r, msg) = raise (Error (Paths.wrap (r, msg)))

    let rec unique (((a, p_), r), a_) =
      let rec unique' = function
        | I.Uni _, [], a_ -> a_
        | I.Pi (_, v_), None :: p_, a_ -> unique' (v_, p_, a_)
        | I.Pi (_, v_), Some x :: p_, a_ -> begin
            List.app
              (function
                | x' -> begin
                    if x = x' then
                      error (r, ("Variable " ^ x) ^ " used more than once")
                    else ()
                  end)
              a_;
            unique' (v_, p_, x :: a_)
          end
        | I.Uni _, _, _ ->
            error
              ( r,
                "Too many arguments supplied to type family "
                ^ Names.qidToString (Names.constQid a) )
        | I.Pi (_, v_), [], _ ->
            error
              ( r,
                "Too few arguments supplied to type family "
                ^ Names.qidToString (Names.constQid a) )
        | I.Root _, _, _ ->
            error
              ( r,
                ("Constant " ^ Names.qidToString (Names.constQid a))
                ^ " is an object, not a type family" )
      in
      let rec skip = function
        | 0, v_, p_, a_ -> unique' (v_, p_, a_)
        | k, I.Pi (_, v_), p_, a_ -> skip (k - 1, v_, p_, a_)
      in
      skip (I.constImp a, I.constType a, p_, a_)

    let rec uniqueCallpats (l_, rs) =
      let rec uniqueCallpats' = function
        | ([], []), a_ -> ()
        | (aP :: l_, r :: rs), a_ ->
            uniqueCallpats' ((l_, rs), unique ((aP, r), a_))
      in
      uniqueCallpats' ((l_, rs), [])

    let rec wfCallpats (l0_, c0_, r) =
      let rec makestring = function
        | [] -> ""
        | s :: [] -> s
        | s :: l_ -> (s ^ " ") ^ makestring l_
      in
      let rec exists' = function
        | x, [], _ -> false
        | x, None :: l_, M.Mapp (_, mS) -> exists' (x, l_, mS)
        | x, Some y :: l_, M.Mapp (M.Marg (mode, _), mS) -> begin
            if x = y then begin
              match mode with
              | M.Plus -> true
              | _ ->
                  error
                    ( r,
                      ((("Expected " ^ x) ^ " to have ") ^ M.modeToString M.Plus)
                      ^ " mode" )
            end
            else exists' (x, l_, mS)
          end
      in
      let rec skip = function
        | 0, x, p_, mS -> exists' (x, p_, mS)
        | k, x, p_, M.Mapp (_, mS) -> skip (k - 1, x, p_, mS)
      in
      let rec delete = function
        | x, ((a, p_) as aP) :: c_ -> begin
            if skip (I.constImp a, x, p_, valOf (ModeTable.modeLookup a)) then
              c_
            else aP :: delete (x, c_)
          end
        | x, [] -> error (r, ("Variable " ^ x) ^ " does not occur as argument")
      in
      let rec wfCallpats' = function
        | [], [] -> ()
        | x :: l_, c_ -> wfCallpats' (l_, delete (x, c_))
        | _ ->
            error
              ( r,
                ("Mutual argument (" ^ makestring l0_)
                ^ ") does not cover all call patterns" )
      in
      wfCallpats' (l0_, c0_)

    let rec wf ((o_, L.Callpats c_), (r, rs)) =
      let rec wfOrder = function
        | L.Varg l_ -> wfCallpats (l_, c_, r)
        | L.Lex l_ -> wfOrders l_
        | L.Simul l_ -> wfOrders l_
      and wfOrders = function
        | [] -> ()
        | o_ :: l_ -> begin
            wfOrder o_;
            wfOrders l_
          end
      in
      let rec allModed = function
        | [] -> ()
        | (a, p_) :: cs_ -> begin
            begin match ModeTable.modeLookup a with
            | None ->
                error
                  ( r,
                    ("Expected " ^ Names.qidToString (Names.constQid a))
                    ^ " to be moded" )
            | Some mS -> ()
            end;
            allModed cs_
          end
      in
      begin
        allModed c_;
        begin
          uniqueCallpats (c_, rs);
          wfOrder o_
        end
      end

    let rec argPos = function
      | x, [], n -> None
      | x, None :: l_, n -> argPos (x, l_, n + 1)
      | x, Some x' :: l_, n -> begin
          if x = x' then Some n else argPos (x, l_, n + 1)
        end

    let rec locate (x :: vars, params, imp) =
      begin match argPos (x, params, imp + 1) with
      | None -> locate (vars, params, imp)
      | Some n -> n
      end

    let rec argOrder = function
      | L.Varg l_, p_, n -> O.Arg (locate (l_, p_, n))
      | L.Simul l_, p_, n -> O.Simul (argOrderL (l_, p_, n))
      | L.Lex l_, p_, n -> O.Lex (argOrderL (l_, p_, n))

    and argOrderL = function
      | [], p_, n -> []
      | o_ :: l_, p_, n -> argOrder (o_, p_, n) :: argOrderL (l_, p_, n)

    let rec argOrderMutual = function
      | [], k, a_ -> a_
      | p_ :: l_, k, a_ -> argOrderMutual (l_, k, k (p_, a_))

    let rec installOrder = function
      | _, [], _ -> ()
      | o_, ((a, p_) as aP) :: thmsLE, thmsLT ->
          let m'_ =
            argOrderMutual
              ( thmsLE,
                (function (a, _), l_ -> O.Le (a, l_)),
                argOrderMutual
                  ( aP :: thmsLT,
                    (function (a, _), l_ -> O.Lt (a, l_)),
                    O.Empty ) )
          in
          let o'_ = argOrder (o_, p_, I.constImp a) in
          let s'_ = O.install (a, O.TDec (o'_, m'_)) in
          installOrder (o_, thmsLE, aP :: thmsLT)

    let rec installDecl (o_, L.Callpats l_) =
      begin
        installOrder (o_, l_, []);
        map (function a, _ -> a) l_
      end

    let rec installTerminates (L.TDecl (o_, cp_), rrs) =
      begin
        wf ((o_, cp_), rrs);
        installDecl (o_, cp_)
      end

    let rec uninstallTerminates cid = O.uninstall cid

    let rec installTotal (L.TDecl (o_, cp_), rrs) =
      begin
        wf ((o_, cp_), rrs);
        installDecl (o_, cp_)
      end

    let rec uninstallTotal cid = O.uninstall cid

    let rec argROrder = function
      | L.Varg l_, p_, n -> O.Arg (locate (l_, p_, n))
      | L.Simul l_, p_, n -> O.Simul (argROrderL (l_, p_, n))
      | L.Lex l_, p_, n -> O.Lex (argROrderL (l_, p_, n))

    and argROrderL = function
      | [], p_, n -> []
      | o_ :: l_, p_, n -> argROrder (o_, p_, n) :: argROrderL (l_, p_, n)

    let rec argPredicate = function
      | less_, o_, o'_ -> O.Less (o_, o'_)
      | leq_, o_, o'_ -> O.Leq (o_, o'_)
      | eq_, o_, o'_ -> O.Eq (o_, o'_)

    let rec installPredicate = function
      | _, [], _ -> ()
      | L.RedOrder (pred_, o1_, o2_), ((a, p_) as aP) :: thmsLE, thmsLT ->
          let m'_ =
            argOrderMutual
              ( thmsLE,
                (function (a, _), l_ -> O.Le (a, l_)),
                argOrderMutual
                  ( aP :: thmsLT,
                    (function (a, _), l_ -> O.Lt (a, l_)),
                    O.Empty ) )
          in
          let o1'_ = argROrder (o1_, p_, I.constImp a) in
          let o2'_ = argROrder (o2_, p_, I.constImp a) in
          let pr = argPredicate (pred_, o1'_, o2'_) in
          let s''_ = O.installROrder (a, O.RDec (pr, m'_)) in
          installPredicate (L.RedOrder (pred_, o1_, o2_), thmsLE, aP :: thmsLT)

    let rec installRDecl (r_, L.Callpats l_) =
      begin
        installPredicate (r_, l_, []);
        map (function a, _ -> a) l_
      end

    let rec wfRCallpats (l0_, c0_, r) =
      let rec makestring = function
        | [] -> ""
        | s :: [] -> s
        | s :: l_ -> (s ^ " ") ^ makestring l_
      in
      let rec exists' = function
        | x, [] -> false
        | x, None :: l_ -> exists' (x, l_)
        | x, Some y :: l_ -> begin if x = y then true else exists' (x, l_) end
      in
      let rec delete = function
        | x, ((a, p_) as aP) :: c_ -> begin
            if exists' (x, p_) then c_ else aP :: delete (x, c_)
          end
        | x, [] -> error (r, ("Variable " ^ x) ^ " does not occur as argument")
      in
      let rec wfCallpats' = function
        | [], [] -> ()
        | x :: l_, c_ -> wfCallpats' (l_, delete (x, c_))
        | _ ->
            error
              ( r,
                ("Mutual argument (" ^ makestring l0_)
                ^ ") does not cover all call patterns" )
      in
      wfCallpats' (l0_, c0_)

    let rec wfred ((L.RedOrder (pred_, o_, o'_), L.Callpats c_), (r, rs)) =
      let rec wfOrder = function
        | L.Varg l_ -> begin
            wfRCallpats (l_, c_, r);
            Varg
          end
        | L.Lex l_ -> Lex (wfOrders l_)
        | L.Simul l_ -> Simul (wfOrders l_)
      and wfOrders = function
        | [] -> []
        | o_ :: l_ -> wfOrder o_ :: wfOrders l_
      in
      begin
        uniqueCallpats (c_, rs);
        begin if wfOrder o_ = wfOrder o'_ then ()
        else
          error
            ( r,
              ("Reduction Order ("
              ^ P.rOrderToString
                  (Obj.magic (L.RedOrder (pred_, o_, o'_)) : P.ThmSyn.redOrder_)
              )
              ^ ") requires both orders to be of the same type." )
        end
      end

    let rec installReduces (L.RDecl (r_, c_), rrs) =
      begin
        wfred ((r_, c_), rrs);
        installRDecl (r_, c_)
      end

    let rec uninstallReduces cid = O.uninstallROrder cid
    let rec installTabled (L.TabledDecl cid) = TabledSyn.installTabled cid

    let rec installKeepTable (L.KeepTableDecl cid) =
      TabledSyn.installKeepTable cid
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

(* # 1 "src/thm/thm_.sml.ml" *)
open! Basis

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

module Thm = Make_Thm (struct
  module Global = Global
  module ThmSyn' = ThmSyn
  module TabledSyn = Tabled.TabledSyn

  (*       structure RedOrder = RedOrder *)
  (* -bp *)
  module Order = Order
  module ModeTable = ModeTable
  module ThmPrint = ThmPrint
  module Paths' = Paths
end)
