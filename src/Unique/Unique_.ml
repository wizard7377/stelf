open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Table
open! Print.Print_
open! Subordinate
open! Modes
open! Typecheck.Typecheck_
open! Index.Index_
open! Solvers.Solvers_
open! Worldcheck
open! Timing

(* # 1 "src/unique/Unique_.sig.ml" *)

(* Uniqueness Checking *)

include UNIQUE
(** Author: Frank Pfenning *)

(* raises Error(msg) *)
(* signature UNIQUE *)

(* # 1 "src/unique/Unique_.fun.ml" *)
open! Basis

(* Uniqueness Checking *)
(* Author: Frank Pfenning *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeUnique
    (Global : GLOBAL)
    (Whnf : WHNF)
    (Abstract : ABSTRACT)
    (Unify : UNIFY)
    (Constraints : CONSTRAINTS)
    (UniqueTable : Modetable.MODETABLE)
    (UniqueCheck : Modecheck.MODECHECK)
    (Index : INDEX)
    (Subordinate : Subordinate_.SUBORDINATE)
    (WorldSyn : Worldcheck_.WORLDSYN)
    (Names : NAMES)
    (Print : PRINT)
    (TypeCheck : TYPECHECK)
    (Timers : Timers.TIMERS) : UNIQUE = struct
  exception Error = Error

  module Subordinate = Subordinate
  module Unify = Unify
  module UniqueCheck = UniqueCheck

  open! struct
    module I = IntSyn
    module M = Modes.Modesyn.ModeSyn
    module W = WorldSyn
    module P = Paths
    module F = Print.Formatter
    module N = Names
    module T = Tomega

    let chatter chlev f = Display.chatter_s chlev (f ())
    let cName cid = N.qidToString (N.constQid cid)

    let pName (cid, a) = match a with
      | Some x -> (("#" ^ cName cid) ^ "_") ^ x
      | None -> ("#" ^ cName cid) ^ "_?"

    let rec instEVars (g, a) = match a with
      | (I.Pi ((I.Dec (_, v1), _), v2), s) ->
          let x1 = I.newEVar g (I.EClo (v1, s)) in
          instEVars (g, (v2, I.Dot (I.Exp x1, s)))
      | ((I.Root _, _) as vs) -> vs

    let rec createEVarSub (g, a) = match a with
      | I.Null -> I.Shift (I.ctxLength g)
      | I.Decl (g', (I.Dec (_, v) as d)) ->
          let s = createEVarSub (g, g') in
          let v' = I.EClo (v, s) in
          let x = I.newEVar g v' in
          I.Dot (I.Exp x, s)

    let unifiable g (u, s) (u', s') =
      Unify.unifiable g (u, s) (u', s')

    let rec unifiableSpines (g, a, b, c) = match a, b, c with
      | (I.Nil, s), (I.Nil, s'), M.Mnil -> true
      | (I.App (u1, s2), s), (I.App (u1', s2'), s'), M.Mapp (M.Marg (M.Plus, _), ms2) ->
          unifiable g (u1, s) (u1', s')
          && unifiableSpines (g, (s2, s), (s2', s'), ms2)
      | (I.App (u1, s2), s), (I.App (u1', s2'), s'), M.Mapp (M.Marg (mode, _), ms2) ->
          unifiableSpines (g, (s2, s), (s2', s'), ms2)

    let unifiableRoots
        (g, (I.Root (I.Const a, s_), s), (I.Root (I.Const a', s'_), s'), ms) =
      a = a' && unifiableSpines (g, (s_, s), (s'_, s'), ms)

    let checkNotUnifiableTypes (g, vs, vs', ms, (bx, by)) =
      begin
        chatter 6 (function () ->
            ((("?- " ^ pName bx) ^ " ~ ") ^ pName by) ^ "\n");
        CsManager.trail (function () ->
            begin if unifiableRoots (g, vs, vs', ms) then
              raise
                (Error
                   (((("Blocks " ^ pName bx) ^ " and ") ^ pName by) ^ " overlap"))
            else ()
            end)
      end

    let checkDiffConstConst (I.Const cid, I.Const cid', ms) =
      ignore (chatter 6 (function () ->
            ((("?- " ^ cName cid) ^ " ~ ") ^ cName cid') ^ "\n"));
      let vs = instEVars (I.Null, (I.constType cid, I.id)) in
      let vs' = instEVars (I.Null, (I.constType cid', I.id)) in
      ignore (CsManager.trail (function () ->
            begin if unifiableRoots (I.Null, vs, vs', ms) then
              raise
                (Error
                   (((("Constants " ^ cName cid) ^ " and ") ^ cName cid')
                   ^ " overlap\n"))
            else ()
            end));
      ()

    let rec checkUniqueConstConsts (c, a, ms) = match a with
      | [] -> ()
      | c' :: cs' -> begin
          checkDiffConstConst (c, c', ms);
          checkUniqueConstConsts (c, cs', ms)
        end

    let rec checkUniqueConsts (a, ms) = match a with
      | [] -> ()
      | c :: cs -> begin
          checkUniqueConstConsts (c, cs, ms);
          checkUniqueConsts (cs, ms)
        end

    let rec checkDiffBlocksInternal (g, vs, c, d, bx) = match vs, c, d, bx with
      | vs, (t, []), (a, ms), bx -> ()
      | (v, s), (t, (I.Dec (yOpt, v') as d) :: piDecs), (a, ms), (b, xOpt)
        ->
          let a' = I.targetFam v' in
          ignore begin if a = a' then
              checkNotUnifiableTypes
                ( g,
                  (v, s),
                  instEVars (g, (v', t)),
                  ms,
                  ((b, xOpt), (b, yOpt)) )
            else ()
            end;
          checkDiffBlocksInternal
            ( I.Decl (g, d),
              (v, I.comp s I.shift),
              (I.dot1 t, piDecs),
              (a, ms),
              (b, xOpt) )

    let rec checkUniqueBlockInternal' (g, c, d, b) = match c, d with
      | (t, []), (a, ms) -> ()
      | (t, (I.Dec (xOpt, v) as d) :: piDecs), (a, ms) ->
          let a' = I.targetFam v in
          ignore begin if a = a' then
              let v', s = instEVars (g, (v, t)) in
              checkDiffBlocksInternal
                ( I.Decl (g, d),
                  (v', I.comp s I.shift),
                  (I.dot1 t, piDecs),
                  (a, ms),
                  (b, xOpt) )
            else ()
            end;
          checkUniqueBlockInternal'
            (I.Decl (g, d), (I.dot1 t, piDecs), (a, ms), b)

    let checkUniqueBlockInternal ((gsome, piDecs), (a, ms), b) =
      let t = createEVarSub (I.Null, gsome) in
      checkUniqueBlockInternal' (I.Null, (t, piDecs), (a, ms), b)

    let rec checkUniqueBlockConsts (g, vs, a, ms, bx) = match a with
      | [] -> ()
      | I.Const cid :: cs ->
          ignore (chatter 6 (function () ->
                ((("?- " ^ pName bx) ^ " ~ ") ^ cName cid) ^ "\n"));
          let vs' = instEVars (g, (I.constType cid, I.id)) in
          ignore (CsManager.trail (function () ->
                begin if unifiableRoots (g, vs, vs', ms) then
                  raise
                    (Error
                       (((("Block " ^ pName bx) ^ " and constant ") ^ cName cid)
                       ^ " overlap"))
                else ()
                end));
          checkUniqueBlockConsts (g, vs, cs, ms, bx)
      | I.Def cid :: cs ->
          ignore (chatter 6 (function () ->
                ((("?- " ^ pName bx) ^ " ~ ") ^ cName cid) ^ "\n"));
          let vs' = instEVars (g, (I.constType cid, I.id)) in
          ignore (CsManager.trail (function () ->
                begin if unifiableRoots (g, vs, vs', ms) then
                  raise
                    (Error
                       (((("Block " ^ pName bx) ^ " and constant ") ^ cName cid)
                       ^ " overlap"))
                else ()
                end));
          checkUniqueBlockConsts (g, vs, cs, ms, bx)
      | _ :: cs ->
          (* Skip other head types *)
          checkUniqueBlockConsts (g, vs, cs, ms, bx)

    let rec checkUniqueBlockBlock (g, vs, b, c, d) = match vs, b, c, d with
      | vs, (t, []), (a, ms), (bx, b') -> ()
      | (v, s), (t, (I.Dec (yOpt, v') as d) :: piDecs), (a, ms), (bx, b')
        ->
          let a' = I.targetFam v' in
          ignore begin if a = a' then
              checkNotUnifiableTypes
                (g, (v, s), instEVars (g, (v', t)), ms, (bx, (b', yOpt)))
            else ()
            end;
          checkUniqueBlockBlock
            ( I.Decl (g, d),
              (v, I.comp s I.shift),
              (I.dot1 t, piDecs),
              (a, ms),
              (bx, b') )

    let rec checkUniqueBlockBlocks (g, vs, c, d, bx) = match c, d with
      | [], (a, ms) -> ()
      | b :: bs, (a, ms) ->
          let gsome, piDecs = I.constBlock b in
          let t = createEVarSub (g, gsome) in
          ignore (checkUniqueBlockBlock (g, vs, (t, piDecs), (a, ms), (bx, b)));
          checkUniqueBlockBlocks (g, vs, bs, (a, ms), bx)

    let rec checkUniqueBlock' (g, c, bs, cs, d, b) = match c, d with
      | (t, []), (a, ms) -> ()
      | (t, (I.Dec (xOpt, v) as d) :: piDecs), (a, ms) ->
          let a' = I.targetFam v in
          ignore begin if a = a' then
              let v', s = instEVars (g, (v, t)) in
              ignore (checkUniqueBlockBlocks (g, (v', s), bs, (a, ms), (b, xOpt)));
              ignore (checkUniqueBlockConsts (g, (v', s), cs, ms, (b, xOpt)));
              ()
            else ()
            end;
          checkUniqueBlock'
            (I.Decl (g, d), (I.dot1 t, piDecs), bs, cs, (a, ms), b)

    let checkUniqueBlock ((gsome, piDecs), bs, cs, (a, ms), b) =
      let t = createEVarSub (I.Null, gsome) in
      checkUniqueBlock' (I.Null, (t, piDecs), bs, cs, (a, ms), b)

    let rec checkUniqueWorlds (c, cs, d) = match c, d with
      | [], (a, ms) -> ()
      | b :: bs, (a, ms) -> begin
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
  (* generalized from ../cover/Cover.fun *)
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
  let checkNoDef a =
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
  let checkUnique a ms =
    ignore (chatter 4 (function () ->
          ("Uniqueness checking family " ^ cName a) ^ "\n"));
    ignore (checkNoDef a);
    ignore (try Subordinate.checkNoDef a
      with Subordinate.Error msg ->
        raise (Error ((("Coverage checking " ^ cName a) ^ ":\n") ^ msg)));
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
    ignore (try checkUniqueConsts (cs, ms)
      with Error msg ->
        raise (Error ((("Uniqueness checking " ^ cName a) ^ ":\n") ^ msg)));
    ignore (try checkUniqueWorlds (bs, cs, (a, ms))
      with Error msg ->
        raise (Error ((("Uniqueness checking " ^ cName a) ^ ":\n") ^ msg)));
    ignore (chatter 5 (function () ->
          ("Checking uniqueness modes for family " ^ cName a) ^ "\n"));
    ignore (try UniqueCheck.checkMode a ms
      with UniqueCheck.Error msg ->
        raise (Error ((("Uniqueness mode checking " ^ cName a) ^ ":\n") ^ msg)));
    ()
  (* lookup constants defining a *)
end
(* functor Unique *)

(* # 1 "src/unique/Unique_.sml.ml" *)
module UniqueTable = Modetable.MakeModeTable (TableInstances.IntRedBlackTree)

module UniqueCheck =
  Modecheck.MakeModeCheck (UniqueTable) (Whnf) (Index) (Origins)

module Unique =
  MakeUnique (Global) (Whnf) (Abstract) (UnifyTrail) (Constraints) (UniqueTable)
    (UniqueCheck)
    (Index)
    (Subordinate_.Subordinate)
    (Worldcheck_.WorldSyn)
    (Names)
    (Print)
    (TypeCheck)
    (Timers.Timers)
