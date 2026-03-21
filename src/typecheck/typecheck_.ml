(* # 1 "src/typecheck/typecheck_.sig.ml" *)
open! Basis

(* Type Checking *)

(** Author: Carsten Schuermann *)
module type TYPECHECK = sig
  (*! structure IntSyn : INTSYN !*)
  exception Error of string

  val check : IntSyn.exp * IntSyn.exp -> unit
  val checkDec : IntSyn.dctx * (IntSyn.dec * IntSyn.sub) -> unit
  val checkConv : IntSyn.exp * IntSyn.exp -> unit
  val infer : IntSyn.exp -> IntSyn.exp
  val infer' : IntSyn.dctx * IntSyn.exp -> IntSyn.exp
  val typeCheck : IntSyn.dctx * (IntSyn.exp * IntSyn.exp) -> unit
  val typeCheckCtx : IntSyn.dctx -> unit

  val typeCheckSub : IntSyn.dctx * IntSyn.sub * IntSyn.dctx -> unit
  (** val typeCheckSpine : IntSyn.dctx * IntSyn.Spine -> unit *)
end
(* signature TYPECHECK *)

(* # 1 "src/typecheck/typecheck_.fun.ml" *)
open! Basis

(* Type Checking *)
(* Author: Carsten Schuermann *)
module MakeTypeCheck (TypeCheck__0 : sig
  (*! structure IntSyn' : INTSYN !*)
  module Conv : CONV

  (*! sharing Conv.IntSyn = IntSyn' !*)
  module Whnf : WHNF

  (*! sharing Whnf.IntSyn = IntSyn'  !*)
  module Names : NAMES

  (*! sharing Names.IntSyn = IntSyn' !*)
  module Print : PRINT
end) : TYPECHECK = struct
  (*! structure IntSyn = IntSyn' !*)
  exception Error of string

  open! struct
    module I = IntSyn

    let rec subToString = function
      | g_, I.Dot (I.Idx n, s) -> (Int.toString n ^ ".") ^ subToString (g_, s)
      | g_, I.Dot (I.Exp u_, s) ->
          (("(" ^ Print.expToString (g_, u_)) ^ ").") ^ subToString (g_, s)
      | g_, I.Dot (I.Block (I.LVar _ as l_), s) ->
          (lVarToString (g_, l_) ^ ".") ^ subToString (g_, s)
      | g_, I.Shift n -> "^" ^ Int.toString n

    and lVarToString = function
      | g_, I.LVar ({ contents = Some b_ }, sk, (l, t)) ->
          lVarToString (g_, I.blockSub (b_, sk))
      | g_, I.LVar ({ contents = None }, sk, (cid, t)) ->
          ((("#" ^ I.conDecName (I.sgnLookup cid)) ^ "[") ^ subToString (g_, t))
          ^ "]"

    let rec checkExp (g_, us_, vs_) =
      let us'_ = inferExp (g_, us_) in
      begin if Conv.conv (us'_, vs_) then () else raise (Error "Type mismatch")
      end

    and inferUni I.Type = I.Kind

    and inferExpW = function
      | g_, (I.Uni l_, _) -> (I.Uni (inferUni l_), I.id)
      | g_, (I.Pi ((d_, _), v_), s) -> begin
          checkDec (g_, (d_, s));
          inferExp (I.Decl (g_, I.decSub (d_, s)), (v_, I.dot1 s))
        end
      | g_, (I.Root (c_, s_), s) ->
          inferSpine (g_, (s_, s), Whnf.whnf (inferCon (g_, c_), I.id))
      | g_, (I.Lam (d_, u_), s) -> begin
          checkDec (g_, (d_, s));
          ( I.Pi
              ( (I.decSub (d_, s), I.Maybe),
                let v_ie_, s_ie_ =
                  inferExp (I.Decl (g_, I.decSub (d_, s)), (u_, I.dot1 s))
                in
                I.EClo (v_ie_, s_ie_) ),
            I.id )
        end
      | g_, (I.FgnExp (cs_csfe, fe_csfe), s) ->
          inferExp (g_, (I.FgnExpStd.ToInternal.apply (cs_csfe, fe_csfe) (), s))

    and inferExp (g_, us_) = inferExpW (g_, Whnf.whnf us_)

    and inferSpine = function
      | g_, (I.Nil, _), vs_ -> vs_
      | g_, (I.SClo (s_, s'), s), vs_ ->
          inferSpine (g_, (s_, I.comp (s', s)), vs_)
      | g_, (I.App (u_, s_), s1), (I.Pi ((I.Dec (_, v1_), _), v2_), s2) -> begin
          checkExp (g_, (u_, s1), (v1_, s2));
          inferSpine
            (g_, (s_, s1), Whnf.whnf (v2_, I.Dot (I.Exp (I.EClo (u_, s1)), s2)))
        end
      | g_, ((I.App _, _) as ss_), ((I.Root (I.Def _, _), _) as vs_) ->
          inferSpine (g_, ss_, Whnf.expandDef vs_)
      | g_, (I.App (u_, s_), _), (v_, s) ->
          raise (Error "Expression is applied, but not a function")

    and inferCon = function
      | g_, I.BVar k' ->
          let (I.Dec (_, v_)) = I.ctxDec (g_, k') in
          v_
      | g_, I.Proj (b_, i) ->
          let (I.Dec (_, v_)) = I.blockDec (g_, b_, i) in
          v_
      | g_, I.Const c -> I.constType c
      | g_, I.Def d -> I.constType d
      | g_, I.Skonst c -> I.constType c
      | g_, I.FgnConst (cs, conDec) -> I.conDecType conDec

    and typeCheck (g_, (u_, v_)) =
      begin
        checkCtx g_;
        checkExp (g_, (u_, I.id), (v_, I.id))
      end

    and checkSub = function
      | IntSyn.Null, I.Shift 0, IntSyn.Null -> ()
      | I.Decl (g_, d_), I.Shift k, IntSyn.Null -> begin
          if k > 0 then checkSub (g_, I.Shift (k - 1), I.Null)
          else raise (Error "Substitution not well-typed")
        end
      | g'_, I.Shift k, g_ ->
          checkSub (g'_, I.Dot (I.Idx (k + 1), I.Shift (k + 1)), g_)
      | g'_, I.Dot (I.Idx k, s'), I.Decl (g_, I.Dec (_, v2_)) ->
          let _ = checkSub (g'_, s', g_) in
          let (I.Dec (_, v1_)) = I.ctxDec (g'_, k) in
          begin if Conv.conv ((v1_, I.id), (v2_, s')) then ()
          else
            raise
              (Error
                 ((("Substitution not well-typed \n  found: "
                   ^ Print.expToString (g'_, v1_))
                  ^ "\n  expected: ")
                 ^ Print.expToString (g'_, I.EClo (v2_, s'))))
          end
      | g'_, I.Dot (I.Exp u_, s'), I.Decl (g_, I.Dec (_, v2_)) ->
          let _ = checkSub (g'_, s', g_) in
          let _ = typeCheck (g'_, (u_, I.EClo (v2_, s'))) in
          ()
      | g'_, I.Dot (I.Idx w, t), I.Decl (g_, I.BDec (_, (l, s))) ->
          let _ = checkSub (g'_, t, g_) in
          let (I.BDec (_, (l', s'))) = I.ctxDec (g'_, w) in
          begin if l <> l' then raise (Error "Incompatible block labels found")
          else begin
            if Conv.convSub (I.comp (s, t), s') then ()
            else
              raise (Error "Substitution in block declaration not well-typed")
          end
          end
      | g'_, I.Dot (I.Block (I.Inst i_), t), I.Decl (g_, I.BDec (_, (l, s))) ->
          let _ = checkSub (g'_, t, g_) in
          let g_, l_ = I.constBlock l in
          let _ = checkBlock (g'_, i_, (I.comp (s, t), l_)) in
          ()
      | g'_, (I.Dot (_, _) as s), IntSyn.Null ->
          raise (Error (("Long substitution" ^ "\n") ^ subToString (g'_, s)))

    and checkBlock = function
      | g_, [], (_, []) -> ()
      | g_, u_ :: i_, (t, I.Dec (_, v_) :: l_) -> begin
          checkExp (g_, (u_, I.id), (v_, t));
          checkBlock (g_, i_, (I.Dot (I.Exp u_, t), l_))
        end

    and checkDec = function
      | g_, (I.Dec (_, v_), s) -> checkExp (g_, (v_, s), (I.Uni I.Type, I.id))
      | g_, (I.BDec (_, (c, t)), s) ->
          let gsome_, piDecs = I.constBlock c in
          checkSub (g_, I.comp (t, s), gsome_)
      | g_, (NDec _, _) -> ()

    and checkCtx = function
      | IntSyn.Null -> ()
      | I.Decl (g_, d_) -> begin
          checkCtx g_;
          checkDec (g_, (d_, I.id))
        end

    let rec check (u_, v_) = checkExp (I.Null, (u_, I.id), (v_, I.id))

    let rec infer u_ =
      let v_ie_, s_ie_ = inferExp (I.Null, (u_, I.id)) in
      I.EClo (v_ie_, s_ie_)

    let rec infer' (g_, u_) =
      let v_ie_, s_ie_ = inferExp (g_, (u_, I.id)) in
      I.EClo (v_ie_, s_ie_)

    let rec checkConv (u1_, u2_) =
      begin if Conv.conv ((u1_, I.id), (u2_, I.id)) then ()
      else
        raise
          (Error
             ((("Terms not equal\n  left: " ^ Print.expToString (I.Null, u1_))
              ^ "\n  right:")
             ^ Print.expToString (I.Null, u2_)))
      end
  end

  (* for debugging purposes *)
  (* whnf for Blocks ? Sun Dec  1 11:38:17 2002 -cs *)
  (* some well-formedness conditions are assumed for input expressions *)
  (* e.g. don't contain ""Kind"", Evar's are consistently instantiated, ... *)
  (* checkExp (G, (U, s1), (V2, s2)) = ()

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2    G2 |- V2 : L
       returns () if there is a V1 s.t.
            G1 |- U : V1
       and  G  |- V1 [s1] = V2 [s2] : L
       otherwise exception Error is raised
    *)
  (* impossible: Kind *)
  (* inferExp (G, (U, s)) = (V', s')

       Invariant:
       If   G  |- s : G1
       then if G1 |- U : V   (U doesn't contain EVAR's, FVAR's)
            then  G  |- s' : G'     G' |- V' : L
            and   G  |- V [s] = V'[s'] : L
            else exception Error is raised.
     *)
  (* no cases for Redex, EVars and EClo's *)
  (* AK: typecheck a representative -- presumably if one rep checks, they all do *)
  (* inferExp (G, Us) = (V', s')

       Invariant: same as inferExp, argument is not in whnf
    *)
  (* inferSpine (G, (S, s1), (V, s2)) = (V', s')

       Invariant:
       If   G |- s1 : G1
       and  G |- s2 : G2  and  G2 |- V : L ,   (V, s2) in whnf
       and  (S,V  don't contain EVAR's, FVAR's)
       then if   there ex V1, V1'  G1 |- S : V1 > V1'
            then G |- s' : G'    and  G' |- V' : L
            and  G |- V1 [s1]   = V [s2] : L
            and  G |- V1'[s1]   = V' [s'] : L
    *)
  (* G |- Pi (x:V1, V2) [s2] = Pi (x: V1 [s2], V2 [1.s2 o ^1] : L
             G |- U [s1] : V1 [s2]
             Hence
             G |- S [s1] : V2 [1. s2 o ^1] [U [s1], id] > V' [s']
             which is equal to
             G |- S [s1] : V2 [U[s1], s2] > V' [s']

             Note that G |- U[s1] : V1 [s2]
             and hence V2 must be under the substitution    U[s1]: V1, s2
          *)
  (* V <> (Pi x:V1. V2, s) *)
  (* inferCon (G, C) = V'

       Invariant:
       If    G |- C : V
       and  (C  doesn't contain FVars)
       then  G' |- V' : L      (for some level L)
       and   G |- V = V' : L
       else exception Error is raised.
    *)
  (* this is just a hack. --cs
                                                       must be extended to handle arbitrary
                                                       Skolem constants in the right way *)
  (* no case for FVar *)
  (* checkSub (G1, s, G2) = ()

       Invariant:
       The function terminates
       iff  G1 |- s : G2
    *)
  (* changed order of subgoals here Sun Dec  2 12:14:27 2001 -fp *)
  (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
  (* Front of the substitution cannot be a I.Bidx or LVar *)
  (* changed order of subgoals here Sun Dec  2 12:15:53 2001 -fp *)
  (* G' |- s' : GSOME *)
  (* G  |- s  : GSOME *)
  (* G' |- t  : G       (verified below) *)
  (*
      | checkSub (G', I.Dot (I.Block (I.Bidx _), t), G) =
        raise Error ""Unexpected block index in substitution""
      | checkSub (G', I.Dot (I.Block (I.LVar _), t), G) =
        raise Error ""Unexpected LVar in substitution after abstraction""
      *)
  (* checkDec (G, (x:V, s)) = B

       Invariant:
       If G |- s : G1
       then B iff G |- V[s] : type
    *)
  (* G1 |- t : GSOME *)
  (* G  |- s : G1 *)
  let check = check
  let checkDec = checkDec
  let checkConv = checkConv
  let infer = infer
  let infer' = infer'
  let typeCheck = typeCheck
  let typeCheckCtx = checkCtx
  let typeCheckSub = checkSub
end

(*! sharing Print.IntSyn = IntSyn' !*)
(* local ... *)
(* functor TypeCheck *)

(* # 1 "src/typecheck/typecheck_.sml.ml" *)
open! Basis

module type STRICT = Strict.STRICT

module TypeCheck = MakeTypeCheck (struct
  (*! structure IntSyn' = IntSyn !*)
  module Conv = Conv
  module Whnf = Whnf
  module Names = Names
  module Print = Print
end)

module Strict = Strict.Strict (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf
end)
