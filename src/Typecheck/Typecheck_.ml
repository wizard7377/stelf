open! Intsyn.Lambda_
open! Print.Print_
open! Names.Names_

(* # 1 "src/typecheck/Typecheck_.sig.ml" *)

(* Type Checking *)

include TYPECHECK
(** Author: Carsten Schuermann *)

(* signature TYPECHECK *)

(* # 1 "src/typecheck/Typecheck_.fun.ml" *)
open! Basis

(* Type Checking *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeTypeCheck
    (Conv : CONV)
    (Whnf : WHNF)
    (Names : NAMES)
    (Print : PRINT) : TYPECHECK = struct
  (*
  (*! structure IntSyn' : INTSYN !*)
  (*! sharing Conv.IntSyn = IntSyn' !*)
  (*! sharing Whnf.IntSyn = IntSyn'  !*)
  (*! sharing Names.IntSyn = IntSyn' !*)
*)
  (*! structure IntSyn = IntSyn' !*)
  exception Error = Error

  open! struct
    module I = IntSyn

    let rec subToString (g, a) = match a with
      | I.Dot (I.Idx n, s) -> (Int.toString n ^ ".") ^ subToString (g, s)
      | I.Dot (I.Exp u, s) ->
          (("(" ^ Print.expToString g u) ^ ").") ^ subToString (g, s)
      | I.Dot (I.Block (I.LVar _ as l), s) ->
          (lVarToString (g, l) ^ ".") ^ subToString (g, s)
      | I.Shift n -> "^" ^ Int.toString n

    and lVarToString (g, a) = match a with
      | I.LVar ({ contents = Some b }, sk, (l, t)) ->
          lVarToString (g, I.blockSub b sk)
      | I.LVar ({ contents = None }, sk, (cid, t)) ->
          ((("#" ^ I.conDecName (I.sgnLookup cid)) ^ "[") ^ subToString (g, t))
          ^ "]"

    let rec checkExp (g, us, vs) =
      let us' = inferExp (g, us) in
      begin if Conv.conv us' vs then ()
      else begin
        let ie, is = us' in
        let ee, es = vs in
        let inferred_s =
          try Print.expToString g (I.EClo (ie, is))
          with _ -> "<print-error>"
        in
        let expected_s =
          try Print.expToString g (I.EClo (ee, es))
          with _ -> "<print-error>"
        in
        let rec show_exp_raw = function
          | I.Root (h, sp) ->
              let hs =
                match h with
                | I.BVar k -> Printf.sprintf "BVar(%d)" k
                | I.Const c ->
                    Printf.sprintf "Const(%d=%s)" c
                      (I.conDecName (I.sgnLookup c))
                | I.Def d ->
                    Printf.sprintf "Def(%d=%s)" d (I.conDecName (I.sgnLookup d))
                | _ -> "OtherHead"
              in
              Printf.sprintf "Root(%s, %s)" hs (show_spine_raw sp)
          | I.Pi _ -> "Pi(...)"
          | I.Lam _ -> "Lam(...)"
          | I.EClo (e, s) -> Printf.sprintf "EClo(%s, ...)" (show_exp_raw e)
          | I.Uni _ -> "Uni"
          | I.Redex _ -> "Redex"
          | I.EVar _ -> "EVar"
          | _ -> "Other"
        and show_spine_raw = function
          | I.Nil -> "Nil"
          | I.App (u, sp) ->
              Printf.sprintf "App(%s, %s)" (show_exp_raw u) (show_spine_raw sp)
          | I.SClo (sp, _) -> Printf.sprintf "SClo(%s, ...)" (show_spine_raw sp)
        in
        Printf.eprintf "RAW inferred: %s\nRAW expected: %s\n%!"
          (show_exp_raw (I.EClo (ie, is)))
          (show_exp_raw (I.EClo (ee, es)));
        let msg =
          Printf.sprintf "Type mismatch\n  inferred: %s\n  expected: %s"
            inferred_s expected_s
        in
        raise (Error msg)
      end
      end

    and inferUni I.Type = I.Kind

    and inferExpW (g, a) = match a with
      | (I.Uni l, _) -> (I.Uni (inferUni l), I.id)
      | (I.Pi ((d, _), v), s) -> begin
          checkDec g (d, s);
          inferExp (I.Decl (g, I.decSub d s), (v, I.dot1 s))
        end
      | (I.Root (c, s_), s) ->
          inferSpine (g, (s_, s), Whnf.whnf (inferCon (g, c), I.id))
      | (I.Lam (d, u), s) -> begin
          checkDec g (d, s);
          ( I.Pi
              ( (I.decSub d s, I.Maybe),
                let v_ie, s_ie =
                  inferExp (I.Decl (g, I.decSub d s), (u, I.dot1 s))
                in
                I.EClo (v_ie, s_ie) ),
            I.id )
        end
      | (I.FgnExp (cs_csfe, fe_csfe), s) ->
          inferExp (g, (I.FgnExpStd.ToInternal.apply cs_csfe fe_csfe (), s))

    and inferExp (g, us) = inferExpW (g, Whnf.whnf us)

    and inferSpine (g, b, c) = match b, c with
      | (I.Nil, _), vs -> vs
      | (I.SClo (s_, s'), s), vs ->
          inferSpine (g, (s_, I.comp s' s), vs)
      | (I.App (u, s), s1), (I.Pi ((I.Dec (_, v1), _), v2), s2) -> begin
          checkExp (g, (u, s1), (v1, s2));
          inferSpine
            (g, (s, s1), Whnf.whnf (v2, I.Dot (I.Exp (I.EClo (u, s1)), s2)))
        end
      | ((I.App _, _) as ss), ((I.Root (I.Def _, _), _) as vs) ->
          inferSpine (g, ss, Whnf.expandDef vs)
      | (I.App (u, s_), _), (v, s) ->
          raise (Error "Expression is applied, but not a function")

    and inferCon (g, a) = match a with
      | I.BVar k' ->
          let (I.Dec (_, v)) = I.ctxDec g k' in
          v
      | I.Proj (b, i) ->
          let (I.Dec (_, v)) = I.blockDec g b i in
          v
      | I.Const c -> I.constType c
      | I.Def d -> I.constType d
      | I.Skonst c -> I.constType c
      | I.FgnConst (cs, conDec) -> I.conDecType conDec

    and typeCheck g (u, v) =
      begin
        checkCtx g;
        checkExp (g, (u, I.id), (v, I.id))
      end

    and checkSub a1 b1 c1 = match a1, b1, c1 with
      | IntSyn.Null, I.Shift 0, IntSyn.Null -> ()
      | I.Decl (g, d), I.Shift k, IntSyn.Null ->
          begin if k > 0 then checkSub g (I.Shift (k - 1)) I.Null
          else raise (Error "Substitution not well-typed")
          end
      | g', I.Shift k, g ->
          checkSub g' (I.Dot (I.Idx (k + 1), I.Shift (k + 1))) g
      | g', I.Dot (I.Idx k, s'), I.Decl (g, I.Dec (_, v2)) ->
          ignore (checkSub g' s' g);
          let (I.Dec (_, v1)) = I.ctxDec g' k in
          begin if Conv.conv (v1, I.id) (v2, s') then ()
          else
            raise
              (Error
                 ((("Substitution not well-typed \n  found: "
                   ^ Print.expToString g' v1)
                  ^ "\n  expected: ")
                 ^ Print.expToString g' (I.EClo (v2, s'))))
          end
      | g', I.Dot (I.Exp u, s'), I.Decl (g, I.Dec (_, v2)) ->
          ignore (checkSub g' s' g);
          ignore (typeCheck g' (u, I.EClo (v2, s')));
          ()
      | g', I.Dot (I.Idx w, t), I.Decl (g, I.BDec (_, (l, s))) ->
          ignore (checkSub g' t g);
          let (I.BDec (_, (l', s'))) = I.ctxDec g' w in
          begin if l <> l' then raise (Error "Incompatible block labels found")
          else
            begin if Conv.convSub (I.comp s t) s' then ()
            else
              raise (Error "Substitution in block declaration not well-typed")
            end
          end
      | g', I.Dot (I.Block (I.Inst i), t), I.Decl (g, I.BDec (_, (l, s))) ->
          ignore (checkSub g' t g);
          let g, l_ = I.constBlock l in
          ignore (checkBlock (g', i, (I.comp s t, l_)));
          ()
      | g', (I.Dot (_, _) as s), IntSyn.Null ->
          raise (Error (("Long substitution" ^ "\n") ^ subToString (g', s)))

    and checkBlock (g, a, b) = match a, b with
      | [], (_, []) -> ()
      | u :: i, (t, I.Dec (_, v) :: l) -> begin
          checkExp (g, (u, I.id), (v, t));
          checkBlock (g, i, (I.Dot (I.Exp u, t), l))
        end

    and checkDec a1 b1 = match a1, b1 with
      | g, (I.Dec (_, v), s) -> checkExp (g, (v, s), (I.Uni I.Type, I.id))
      | g, (I.BDec (_, (c, t)), s) ->
          let gsome, piDecs = I.constBlock c in
          checkSub g (I.comp t s) gsome
      | g, (NDec _, _) -> ()

    and checkCtx = function
      | IntSyn.Null -> ()
      | I.Decl (g, d) -> begin
          checkCtx g;
          checkDec g (d, I.id)
        end

    let check (u, v) = checkExp (I.Null, (u, I.id), (v, I.id))

    let infer u =
      let v_ie, s_ie = inferExp (I.Null, (u, I.id)) in
      I.EClo (v_ie, s_ie)

    let infer' g u =
      let v_ie, s_ie = inferExp (g, (u, I.id)) in
      I.EClo (v_ie, s_ie)

    let checkConv u1 u2 =
      begin if Conv.conv (u1, I.id) (u2, I.id) then ()
      else
        raise
          (Error
             ((("Terms not equal\n  left: " ^ Print.expToString I.Null u1)
              ^ "\n  right:")
             ^ Print.expToString I.Null u2))
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

(* # 1 "src/typecheck/Typecheck_.sml.ml" *)

module type STRICT = Strict.STRICT

module TypeCheck = MakeTypeCheck (Conv) (Whnf) (Names) (Print)

module Strict = Strict.Strict (struct
  (*! structure IntSyn' = IntSyn !*) module Whnf = Whnf
end)
