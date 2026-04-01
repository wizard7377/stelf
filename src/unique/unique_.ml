(* # 1 "src/unique/unique_.sig.ml" *)
open! Basis

(* Uniqueness Checking *)

(** Author: Frank Pfenning *)
include Unique_intf
(* raises Error(msg) *)
(* signature UNIQUE *)

(* # 1 "src/unique/unique_.fun.ml" *)
open! Basis

(* Uniqueness Checking *)
(* Author: Frank Pfenning *)
module MakeUnique (Unique__0 : sig
  module Global : GLOBAL
  module Whnf : WHNF
  module Abstract : ABSTRACT
  module Unify : UNIFY

  (* must be trailing! *)
  module Constraints : CONSTRAINTS
  module UniqueTable : Modetable.MODETABLE
  module UniqueCheck : Modecheck.MODECHECK
  module Index : INDEX
  module Subordinate : Subordinate_.SUBORDINATE
  module WorldSyn : Worldcheck_.WORLDSYN
  module Names : NAMES
  module Print : PRINT
  module TypeCheck : TYPECHECK
  module Timers : Timers.TIMERS
end) : UNIQUE = struct
  exception Error of string

  module Subordinate = Unique__0.Subordinate
  module Unify = Unique__0.Unify
  module UniqueCheck = Unique__0.UniqueCheck

  open! struct
    module I = IntSyn
    module M = Modes.Modesyn.ModeSyn
    module W = Unique__0.WorldSyn
    module P = Paths
    module F = Print.Formatter
    module N = Names
    module T = Tomega

    let rec chatter chlev f =
      begin if !Global.chatter >= chlev then print (f ()) else ()
      end

    let rec cName cid = N.qidToString (N.constQid cid)

    let rec pName = function
      | cid, Some x -> (("#" ^ cName cid) ^ "_") ^ x
      | cid, None -> ("#" ^ cName cid) ^ "_?"

    let rec instEVars = function
      | g_, (I.Pi ((I.Dec (_, v1_), _), v2_), s) ->
          let x1_ = I.newEVar (g_, I.EClo (v1_, s)) in
          instEVars (g_, (v2_, I.Dot (I.Exp x1_, s)))
      | g_, ((I.Root _, _) as vs_) -> vs_

    let rec createEVarSub = function
      | g_, I.Null -> I.Shift (I.ctxLength g_)
      | g_, I.Decl (g'_, (I.Dec (_, v_) as d_)) ->
          let s = createEVarSub (g_, g'_) in
          let v'_ = I.EClo (v_, s) in
          let x_ = I.newEVar (g_, v'_) in
          I.Dot (I.Exp x_, s)

    let rec unifiable (g_, (u_, s), (u'_, s')) =
      Unify.unifiable (g_, (u_, s), (u'_, s'))

    let rec unifiableSpines = function
      | g_, (I.Nil, s), (I.Nil, s'), M.Mnil -> true
      | ( g_,
          (I.App (u1_, s2_), s),
          (I.App (u1'_, s2'_), s'),
          M.Mapp (M.Marg (M.Plus, _), ms2) ) ->
          unifiable (g_, (u1_, s), (u1'_, s'))
          && unifiableSpines (g_, (s2_, s), (s2'_, s'), ms2)
      | ( g_,
          (I.App (u1_, s2_), s),
          (I.App (u1'_, s2'_), s'),
          M.Mapp (M.Marg (mode, _), ms2) ) ->
          unifiableSpines (g_, (s2_, s), (s2'_, s'), ms2)

    let rec unifiableRoots
        (g_, (I.Root (I.Const a, s_), s), (I.Root (I.Const a', s'_), s'), ms) =
      a = a' && unifiableSpines (g_, (s_, s), (s'_, s'), ms)

    let rec checkNotUnifiableTypes (g_, vs_, vs'_, ms, (bx, by)) =
      begin
        chatter 6 (function () ->
            ((("?- " ^ pName bx) ^ " ~ ") ^ pName by) ^ "\n");
        Cs_manager.trail (function () ->
            begin if unifiableRoots (g_, vs_, vs'_, ms) then
              raise
                (Error
                   (((("Blocks " ^ pName bx) ^ " and ") ^ pName by) ^ " overlap"))
            else ()
            end)
      end

    let rec checkDiffConstConst (I.Const cid, I.Const cid', ms) =
      let _ =
        chatter 6 (function () ->
            ((("?- " ^ cName cid) ^ " ~ ") ^ cName cid') ^ "\n")
      in
      let vs_ = instEVars (I.Null, (I.constType cid, I.id)) in
      let vs'_ = instEVars (I.Null, (I.constType cid', I.id)) in
      let _ =
        Cs_manager.trail (function () ->
            begin if unifiableRoots (I.Null, vs_, vs'_, ms) then
              raise
                (Error
                   (((("Constants " ^ cName cid) ^ " and ") ^ cName cid')
                   ^ " overlap\n"))
            else ()
            end)
      in
      ()

    let rec checkUniqueConstConsts = function
      | c, [], ms -> ()
      | c, c' :: cs', ms -> begin
          checkDiffConstConst (c, c', ms);
          checkUniqueConstConsts (c, cs', ms)
        end

    let rec checkUniqueConsts = function
      | [], ms -> ()
      | c :: cs, ms -> begin
          checkUniqueConstConsts (c, cs, ms);
          checkUniqueConsts (cs, ms)
        end

    let rec checkDiffBlocksInternal = function
      | g_, vs_, (t, []), (a, ms), bx -> ()
      | g_, (v_, s), (t, (I.Dec (yOpt, v'_) as d_) :: piDecs), (a, ms), (b, xOpt)
        ->
          let a' = I.targetFam v'_ in
          let _ =
            begin if a = a' then
              checkNotUnifiableTypes
                ( g_,
                  (v_, s),
                  instEVars (g_, (v'_, t)),
                  ms,
                  ((b, xOpt), (b, yOpt)) )
            else ()
            end
          in
          checkDiffBlocksInternal
            ( I.Decl (g_, d_),
              (v_, I.comp (s, I.shift)),
              (I.dot1 t, piDecs),
              (a, ms),
              (b, xOpt) )

    let rec checkUniqueBlockInternal' = function
      | g_, (t, []), (a, ms), b -> ()
      | g_, (t, (I.Dec (xOpt, v_) as d_) :: piDecs), (a, ms), b ->
          let a' = I.targetFam v_ in
          let _ =
            begin if a = a' then
              let v'_, s = instEVars (g_, (v_, t)) in
              checkDiffBlocksInternal
                ( I.Decl (g_, d_),
                  (v'_, I.comp (s, I.shift)),
                  (I.dot1 t, piDecs),
                  (a, ms),
                  (b, xOpt) )
            else ()
            end
          in
          checkUniqueBlockInternal'
            (I.Decl (g_, d_), (I.dot1 t, piDecs), (a, ms), b)

    let rec checkUniqueBlockInternal ((gsome_, piDecs), (a, ms), b) =
      let t = createEVarSub (I.Null, gsome_) in
      checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b)

    let rec checkUniqueBlockConsts = function
      | g_, vs_, [], ms, bx -> ()
      | g_, vs_, I.Const cid :: cs, ms, bx ->
          let _ =
            chatter 6 (function () ->
                ((("?- " ^ pName bx) ^ " ~ ") ^ cName cid) ^ "\n")
          in
          let vs'_ = instEVars (g_, (I.constType cid, I.id)) in
          let _ =
            Cs_manager.trail (function () ->
                begin if unifiableRoots (g_, vs_, vs'_, ms) then
                  raise
                    (Error
                       (((("Block " ^ pName bx) ^ " and constant ") ^ cName cid)
                       ^ " overlap"))
                else ()
                end)
          in
          checkUniqueBlockConsts (g_, vs_, cs, ms, bx)
      | g_, vs_, I.Def cid :: cs, ms, bx ->
          let _ =
            chatter 6 (function () ->
                ((("?- " ^ pName bx) ^ " ~ ") ^ cName cid) ^ "\n")
          in
          let vs'_ = instEVars (g_, (I.constType cid, I.id)) in
          let _ =
            Cs_manager.trail (function () ->
                begin if unifiableRoots (g_, vs_, vs'_, ms) then
                  raise
                    (Error
                       (((("Block " ^ pName bx) ^ " and constant ") ^ cName cid)
                       ^ " overlap"))
                else ()
                end)
          in
          checkUniqueBlockConsts (g_, vs_, cs, ms, bx)
      | g_, vs_, _ :: cs, ms, bx ->
          (* Skip other head types *)
          checkUniqueBlockConsts (g_, vs_, cs, ms, bx)

    let rec checkUniqueBlockBlock = function
      | g_, vs_, (t, []), (a, ms), (bx, b') -> ()
      | g_, (v_, s), (t, (I.Dec (yOpt, v'_) as d_) :: piDecs), (a, ms), (bx, b')
        ->
          let a' = I.targetFam v'_ in
          let _ =
            begin if a = a' then
              checkNotUnifiableTypes
                (g_, (v_, s), instEVars (g_, (v'_, t)), ms, (bx, (b', yOpt)))
            else ()
            end
          in
          checkUniqueBlockBlock
            ( I.Decl (g_, d_),
              (v_, I.comp (s, I.shift)),
              (I.dot1 t, piDecs),
              (a, ms),
              (bx, b') )

    let rec checkUniqueBlockBlocks = function
      | g_, vs_, [], (a, ms), bx -> ()
      | g_, vs_, b :: bs, (a, ms), bx ->
          let gsome_, piDecs = I.constBlock b in
          let t = createEVarSub (g_, gsome_) in
          let _ =
            checkUniqueBlockBlock (g_, vs_, (t, piDecs), (a, ms), (bx, b))
          in
          checkUniqueBlockBlocks (g_, vs_, bs, (a, ms), bx)

    let rec checkUniqueBlock' = function
      | g_, (t, []), bs, cs, (a, ms), b -> ()
      | g_, (t, (I.Dec (xOpt, v_) as d_) :: piDecs), bs, cs, (a, ms), b ->
          let a' = I.targetFam v_ in
          let _ =
            begin if a = a' then
              let v'_, s = instEVars (g_, (v_, t)) in
              let _ =
                checkUniqueBlockBlocks (g_, (v'_, s), bs, (a, ms), (b, xOpt))
              in
              let _ =
                checkUniqueBlockConsts (g_, (v'_, s), cs, ms, (b, xOpt))
              in
              ()
            else ()
            end
          in
          checkUniqueBlock'
            (I.Decl (g_, d_), (I.dot1 t, piDecs), bs, cs, (a, ms), b)

    let rec checkUniqueBlock ((gsome_, piDecs), bs, cs, (a, ms), b) =
      let t = createEVarSub (I.Null, gsome_) in
      checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)

    let rec checkUniqueWorlds = function
      | [], cs, (a, ms) -> ()
      | b :: bs, cs, (a, ms) -> begin
          checkUniqueBlockInternal (I.constBlock b, (a, ms), b);
          begin
            checkUniqueBlock (I.constBlock b, b :: bs, cs, (a, ms), b);
            checkUniqueWorlds (bs, cs, (a, ms))
          end
        end
  end

  (*---------------------*)
  (* Auxiliary Functions *)
  (*---------------------*)
  (* instEVars (G, ({x1:V1}...{xn:Vn}a@S, id)) = (a @ S, s)
       where G |- s : {x1:V1}...{xn:Vn}
       substitutes new EVars for x1,...,xn

       Invariants: {x1:V1}...{xn:Vn}a@S NF
    *)
  (* generalized from ../cover/cover.fun *)
  (* createEVarSub (G, G') = s

       Invariant:
       If   G |- G' ctx
       then G |- s : G' and s instantiates each x:A with an EVar G |- X : A
    *)
  (* unifiable (G, (U, s), (U', s')) = true
       iff G |- U[s] = U'[s'] : V  (for some V)
       Effect: may instantiate EVars in all inputs
    *)
  (* unifiableSpines (G, (S, s), (S', s'), ms) = true
       iff G |- S[s] == S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
  (* skip output ( - ) or ignore ( * ) arguments *)
  (* unifiableRoots (G, (a @ S, s), (a' @ S', s'), ms) = true
       iff G |- a@S[s] == a'@S'[s'] on input ( + ) arguments according to ms
       Effect: may instantiate EVars in all inputs
    *)
  (*----------------------------*)
  (* Constant/Constant overlaps *)
  (*----------------------------*)
  (* checkNotUnifable (c, c', ms) = ()
       check if c:A overlaps with c':A' on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
  (* checkUniqueConstConsts (c, cs, ms) = ()
       checks if c:A overlaps with any c':A' in cs on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
  (* checkUniqueConsts (cs, ms) = ()
       checks if no two pairs of constant types in cs overlap on input arguments ( + )
       according to mode spine ms
       Effect: raises Error(msg) otherwise
    *)
  (*-----------------------------------------*)
  (* Block/Block and Block/Constant overlaps *)
  (*-----------------------------------------*)
  (* checkDiffBlocksInternal (G, (V, s), (t, piDecs), (a, ms), bx) = ()
       checks that V[s] does not overlap with any declaration in piDecs
       on input arguments ( + ) according to mode spine ms.
       bx = (b, xOpt) is the block identifier and parameter name in which V[s] occur
       Invariant: V[s] = a @ S and ms is mode spine for a
    *)
  (* checkUniqueBlockInternal' (G, (t, piDecs), (a, ms), b) = ()
       checks that no two declarations for family a in piDecs[t] overlap
       on input arguments ( + ) according to mode spine ms
       b is the block identifier and parameter name is which piDecs
       Effect: raises Error(msg) otherwise
    *)
  (* checkUniqueBlockInternal ((Gsome, piDecs), (a, ms))
       see checkUniqueBlockInternal'
    *)
  (* . |- t : Gsome *)
  (* checkUniqueBlockConstants (G, (V, s), cs, ms, bx) = ()
       checks that V[s] = a@S[s] does not overlap with any constant in cs
       according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       Effect: raises Error(msg) otherwise
    *)
  (* checkUniqueBlockBlock (G, (V, s), (t, piDecs), (a, ms), (bx, b')) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for a in piDecs[t] according to mode spine ms for family a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
       b' is the block indentifier in which piDecs occurs
       Effect: raises Error(msg) otherwise
    *)
  (* checkUniqueBlockBlocks (G, (V, s), bs, (a, ms), bx) = ()
       checks that V[s] = a @ S[s] does not overlap with any declaration
       for family a in any block in bs = [b1,...,bn] according to mode spine ms for a
       bx = (b, xOpt) is the block identifier and parameter name is which V[s] occur
    *)
  (* checkUniqueBlock' (G, (t, piDecs), bs, cs, (a, ms), b) = ()
       check that no declaration for family a in piDecs[t]
       overlaps with any declaration for a in bs or any constant in cs
       according to mode spine ms for a
       b is the block identifier in which piDecs occur for error messages
    *)
  (* checkUniqueBlock ((Gsome, piDecs), bs, cs, (a, ms), b) = ()
       see checkUniqueBlock'
    *)
  (* checkUniqueWorlds (bs, cs, (a, ms)) = ()
       checks if no declarations for a in bs overlap with other declarations
       for a in bs or any constant in cs according to mode spine ms
       Effect: raise Error(msg) otherwise
    *)
  (* checkNoDef (a) = ()
       Effect: raises Error if a is a defined type family
    *)
  let rec checkNoDef a =
    begin match I.sgnLookup a with
    | I.ConDef _ ->
        raise
          (Error
             (("Uniqueness checking " ^ cName a)
             ^ ":\ntype family must not be defined."))
    | _ -> ()
    end

  (* checkUnique (a, ms) = ()
       checks uniqueness of applicable cases with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
  let rec checkUnique (a, ms) =
    let _ =
      chatter 4 (function () ->
          ("Uniqueness checking family " ^ cName a) ^ "\n")
    in
    let _ = checkNoDef a in
    let _ =
      try Subordinate.checkNoDef a
      with Subordinate.Error msg ->
        raise (Error ((("Coverage checking " ^ cName a) ^ ":\n") ^ msg))
    in
    let cs = Index.lookup a in
    let (T.Worlds bs) =
      try W.lookup a
      with W.Error msg ->
        raise
          (Error
             ((("Uniqueness checking " ^ cName a)
              ^ ":\nMissing world declaration for ")
             ^ cName a))
      (* worlds declarations for a *)
    in
    let _ =
      try checkUniqueConsts (cs, ms)
      with Error msg ->
        raise (Error ((("Uniqueness checking " ^ cName a) ^ ":\n") ^ msg))
    in
    let _ =
      try checkUniqueWorlds (bs, cs, (a, ms))
      with Error msg ->
        raise (Error ((("Uniqueness checking " ^ cName a) ^ ":\n") ^ msg))
    in
    let _ =
      chatter 5 (function () ->
          ("Checking uniqueness modes for family " ^ cName a) ^ "\n")
    in
    let _ =
      try UniqueCheck.checkMode (a, ms)
      with UniqueCheck.Error msg ->
        raise (Error ((("Uniqueness mode checking " ^ cName a) ^ ":\n") ^ msg))
    in
    ()
  (* lookup constants defining a *)
end
(* functor Unique *)

(* # 1 "src/unique/unique_.sml.ml" *)
open! Basis

module UniqueTable = Modetable.MakeModeTable (struct
  module Table = Table_instances.IntRedBlackTree
end)

module UniqueCheck = Modecheck.MakeModeCheck (struct
  module ModeTable = UniqueTable
  module Whnf = Whnf
  module Index = Index
  module Origins = Origins
end)

module Unique = MakeUnique (struct
  module Global = Global
  module Whnf = Whnf
  module Abstract = Abstract
  module Unify = UnifyTrail
  module Constraints = Constraints
  module UniqueTable = UniqueTable
  module UniqueCheck = UniqueCheck
  module Index = Index
  module Subordinate = Subordinate_.Subordinate
  module WorldSyn = Worldcheck_.WorldSyn
  module Names = Names
  module Print = Print
  module TypeCheck = TypeCheck
  module Timers = Timers.Timers
end)
