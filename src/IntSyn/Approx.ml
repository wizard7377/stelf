
(* # 1 "src/lambda/Approx.sig.ml" *)
open Intsyn_

(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
include APPROX

(* # 1 "src/lambda/Approx.fun.ml" *)
open! Whnf
open! Basis

(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
exception Ambiguous

let () =
  Printexc.register_printer (function
    | Ambiguous -> Some "Ambiguous term"
    | _ -> None)

exception Unify of string

let () =
  Printexc.register_printer (function Unify msg -> Some msg | _ -> None)

module MakeApprox (Whnf : WHNF) : APPROX = struct
  (*! structure IntSyn = IntSyn' !*)
  module I = IntSyn

  let headConDec = function
    | I.Const c -> I.sgnLookup c
    | I.Skonst c -> I.sgnLookup c
    | I.Def d -> I.sgnLookup d
    | I.NSDef d -> I.sgnLookup d
    | I.FgnConst (_, cd) -> cd

  (* others impossible by invariant *)
  (* The approximate language is based on the idea of erasure.  The
     erasure of a term is defined as follows:

       c- = c
       d- = d
       type- = type
       kind- = kind
       ({x:A} B)- = A- -> B-
       ([x:A] M)- = M-    
       (M N)- = M-

       x- undefined
       X- undefined

     Note that erasure is always defined on well-typed terms at type
     family or kind level.  Also, if G |- U1 = U2 : V and U1,U2 are at
     type family or kind level, then U1- and U2- are defined and
     equal.  We can define the approximate typing judgment
             
       G |- U ~:~ V
                  
     by replacing appeals to equality in the usual presentation of the
     LF type theory with appeals to

       G |- U1 = U2 ~:~ V,

     which is defined to mean
           G |- U1 ~:~ V  and  G |- U2 ~:~ V  and  U1- = U2-
                                                         
     This is a mutual recursion between the two judgments, just as for
     the standard LF type theory.

     There is also a typing judgment on approximate terms

       |- u : v

     defined in the obvious way.  If |- u : v : l then for any
     well-formed G there are most general U, V such that G |- U : V
     and U- = u and V- = v.  *)
  (* The approximate language *)
  type uni = Level of int | Next of uni | LVar of uni option ref
  [@@deriving eq, show]
  (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)

  type exp =
    | Uni of uni
    | Arrow of exp * exp
    | Const of I.head
    | CVar of exp option ref
    | Undefined
  [@@deriving eq, show]
  (* Const/Def/NSDef *)

  (* Because approximate type reconstruction uses the pattern G |- U
     ~:~ V ~:~ L and universe unification on L, if U is to be an
     arbitrary input expression, there must be an internal universe
     Hyperkind such that |- Type ~:~ Kind ~:~ Hyperkind.  The
     Hyperkind universe is used only during the approximate phase of
     reconstruction.  The invariants established by
     ReconTerm.filterLevel ensure that Hyperkind will never appear
     elsewhere. *)
  let type_ = Level 1
  let kind = Level 2
  let hyperkind = Level 3
  let newLVar () = LVar (ref None)
  let newCVar () = CVar (ref None)

  (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)
  let rec whnfUni = function
    | Next l ->
        begin match whnfUni l with Level i -> Level (i + 1) | l' -> Next l'
        end
    | LVar { contents = Some l } -> whnfUni l
    | l -> l

  (* whnf (u) = u'
       where u = u' and u' is in whnf *)
  let rec whnf = function CVar { contents = Some v } -> whnf v | v -> v

  open! struct
    type nonrec varEntry = (exp * exp * uni) * string

    let varList : varEntry list ref = ref []
  end

  (* just a little list since these are only for printing errors *)
  let varReset () = varList := []

  let varLookupRef r =
    List.find (function (CVar r', _, _), _ -> r == r') !varList

  let varLookupName name =
    List.find (function _, name' -> name = name') !varList

  let varInsert ((u, v, l), name) =
    varList := ((u, v, l), name) :: !varList

  exception Ambiguous = Ambiguous

  (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)
  let getReplacementName ((CVar r as u), v, l, allowed) =
    begin match varLookupRef r with
    | Some (_, name) -> name
    | None ->
        ignore begin if allowed then () else raise Ambiguous
          end;
        let pref =
          begin match whnfUni l with Level 2 -> "A" | Level 3 -> "K"
          end
        in
        let rec try_ i =
          let name = (("%" ^ pref) ^ Int.toString i) ^ "%" in
          begin match varLookupName name with
          | None -> begin
              varInsert ((u, v, l), name);
              name
            end
          | Some _ -> try_ (i + 1)
          end
        in
        try_ 1 (* others impossible by invariant *)
    end

  (* findByReplacementName (name) = (u, v, l)
         if getReplacementName (u, v, l, allowed) = name was already called
         then u : v : l *)
  let findByReplacementName name =
    begin match varLookupName name with
    | Some (uvl, _) -> uvl
    | None ->
        Debug.msg ~src:Debug.Group.approx ~level:Debug.Level.Debug
          (Debug.Fmt.exact "Failed to find name");
        raise (Fail "Name not found")
    end
  (* must be in list by invariant *)

  (* converting exact terms to approximate terms *)
  (* uniToApx (L) = L- *)
  let uniToApx = function I.Type -> type_ | I.Kind -> kind

  (* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U "":"" V = ""hyperkind"" *)
  let rec expToApx = function
    | I.Uni l ->
        let l' = uniToApx l in
        (Uni l', Uni (whnfUni (Next l')))
    | I.Pi ((I.Dec (_, v1), _), v2) ->
        let v1', _ (* Type *) = expToApx v1 in
        let v2', l' = expToApx v2 in
        (Arrow (v1', v2'), l')
    | I.Root (I.FVar (name, _, _), _) ->
        let u, v, l = findByReplacementName name in
        (u, v)
    | I.Root (h, _ (* Const/Def/NSDef *)) -> (Const h, Uni type_)
    | I.Redex (u, _) -> expToApx u
    | I.Lam (_, u) -> expToApx u
    | I.EClo (u, _) -> expToApx u

  (* are we sure Skonst/FgnConst are never types or kinds? *)
  (* must have been created to represent a CVar *)

  (* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V "":"" L = ""hyperkind"" *)
  let classToApx v =
    let v', l' = expToApx v in
    let (Uni l'') = whnf l' in
    (v', l'')

  (* exactToApx (U, V) = (U-, V-)
     if G |- U : V *)
  let exactToApx u v =
    let v', l' = classToApx v in
    begin match whnfUni l' with
    | Level 1 -> (Undefined, v', l')
    | _ ->
        let u', _ (* V' *) = expToApx u in
        (u', v', l')
    end

  (* Type *)
  (* Kind/Hyperkind *)

  (* constDefApx (d) = V-
     if |- d = V : type *)
  let constDefApx d =
    begin match I.sgnLookup d with
    | I.ConDef (_, _, _, u, _, _, _) ->
        let v', _ (* Uni Type *) = expToApx u in
        v'
    | I.AbbrevDef (_, _, _, u, _, _) ->
        let v', _ (* Uni Type *) = expToApx u in
        v'
    end

  (* converting approximate terms to exact terms *)
  (* apxToUni (L-) = L *)
  let apxToUniW = function Level 1 -> I.Type | Level 2 -> I.Kind

  (* others impossible by invariant *)
  let apxToUni l = apxToUniW (whnfUni l)

  (* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)
  let rec apxToClassW g a b allowed = match a, b with
    | Uni l, _ (* Next L *) -> I.Uni (apxToUni l)
    | Arrow (v1, v2), l ->
        let v1' = apxToClass g v1 type_ allowed in
        let d = I.Dec (None, v1') in
        let v2' = apxToClass (I.Decl (g, d)) v2 l allowed in
        I.Pi ((d, I.Maybe), v2')
    | (CVar r as v), l (* Type or Kind *) ->
        let name = getReplacementName (v, Uni l, Next l, allowed) in
        let s = I.Shift (I.ctxLength g) in
        I.Root (I.FVar (name, I.Uni (apxToUni l), s), I.Nil)
    | Const h, l (* Type *) ->
        I.Root (h, Whnf.newSpineVar g (I.conDecType (headConDec h), I.id))
  (* convert undetermined CVars to FVars *)
  (* also, does the name of the bound variable here matter? *)
  (* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)

  and apxToClass g v l allowed = apxToClassW g (whnf v) l allowed

  (* Undefined case impossible *)
  (* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)
  let rec apxToExactW g u b allowed = match b with
    | (I.Pi ((d, _), v), s) ->
        let d' = I.decSub d s in
        I.Lam (d', apxToExact (I.Decl (g, d')) u (v, I.dot1 s) allowed)
    | (I.Uni l, s) -> apxToClass g u (uniToApx l) allowed
    | ((I.Root (I.FVar (name, _, _), _), s) as vs) ->
        let v, l, _ (* Next L *) = findByReplacementName name in
        let (Uni l) = whnf l in
        begin match whnfUni l with
        | Level 1 ->
            let vs_e, vs_s = vs in
            I.newEVar g (I.EClo (vs_e, vs_s))
        | Level 2 ->
            let name' = getReplacementName (whnf u, v, Level 2, allowed) in
            let v' = apxToClass Null v (Level 2) allowed in
            let s' = I.Shift (I.ctxLength g) in
            I.Root (I.FVar (name', v', s'), I.Nil)
        (* NOTE: V' differs from Vs by a Shift *)
        (* probably could avoid the following call by removing the
                  substitutions in Vs instead *)
        end
        (* U must be a CVar *)
    | vs (* an atomic type, not Def *) ->
        let vs_e, vs_s = vs in
        I.newEVar g (I.EClo (vs_e, vs_s))

  and apxToExact g u vs allowed =
    apxToExactW g u (Whnf.whnfExpandDef vs) allowed

  (* matching for the approximate language *)
  exception Unify = Unify

  (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)
  let rec occurUniW (r, a) = match a with
    | Next l -> occurUniW (r, l)
    | LVar r' ->
        begin if r == r' then raise (Unify "Level circularity") else ()
        end
    | _ -> ()

  let occurUni (r, l) = occurUniW (r, whnfUni l)

  (* matchUni (l1, l2) = ()
       iff l1<I> = l2<I> for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
  let rec matchUniW = function
    | Level i1, Level i2 ->
        begin if i1 = i2 then () else raise (Unify "Level clash")
        end
    | Level i1, Next l2 ->
        begin if i1 > 1 then matchUniW (Level (i1 - 1), l2)
        else raise (Unify "Level clash")
        end
    | Next l1, Level i2 ->
        begin if i2 > 1 then matchUniW (l1, Level (i2 - 1))
        else raise (Unify "Level clash")
        end
    | Next l1, Next l2 -> matchUniW (l1, l2)
    | LVar r1, (LVar r2 as l2) ->
        begin if r1 == r2 then () else r1 := Some l2
        end
    | LVar r1, l2 -> begin
        occurUniW (r1, l2);
        r1 := Some l2
      end
    | l1, LVar r2 -> begin
        occurUniW (r2, l1);
        r2 := Some l1
      end

  let matchUni l1 l2 = matchUniW (whnfUni l1, whnfUni l2)

  (* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)
  let rec occurW (r, a) = match a with
    | _ when !r == None -> false
    | Arrow (v1, v2) -> begin occur' (r, v1) || occur' (r, v2) end
    | CVar r' ->
        begin if r == r' then raise (Unify "Type/kind variable occurrence")
        else false
        end
    | _ -> false

  and occur' (r, u) = occurW (r, whnf u)

  let occur = ignore occur'

  (* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
  let rec matchW = function
    | Uni l1, Uni l2 -> matchUni l1 l2
    | (Const h1 as v1), (Const h2 as v2) ->
        begin match (h1, h2) with
        | I.Const c1, I.Const c2 ->
            begin if c1 = c2 then ()
            else raise (Unify "Type/kind constant clash")
            end
        | I.Def d1, I.Def d2 ->
            begin if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
            end
        | I.Def d1, _ -> match_ (constDefApx d1, v2)
        | _, I.Def d2 -> match_ (v1, constDefApx d2)
        | I.NSDef d1, I.NSDef d2 ->
            begin if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
            end
        | I.NSDef d1, _ -> match_ (constDefApx d1, v2)
        | _, I.NSDef d2 -> match_ (v1, constDefApx d2)
        end
    | Arrow (v1, v2), Arrow (v3, v4) -> begin
        (try match_ (v1, v3)
         with e ->
           begin
             match_ (v2, v4);
             raise e
           end);
        match_ (v2, v4)
      end
    | (Arrow _ as v1), Const (I.Def d2) -> match_ (v1, constDefApx d2)
    | Const (I.Def d1), (Arrow _ as v2) -> match_ (constDefApx d1, v2)
    | (Arrow _ as v1), Const (I.NSDef d2) -> match_ (v1, constDefApx d2)
    | Const (I.NSDef d1), (Arrow _ as v2) -> match_ (constDefApx d1, v2)
    | CVar r1, (CVar r2 as u2) ->
        begin if r1 == r2 then () else r1 := Some u2
        end
    | CVar r1, u2 -> begin
        ignore @@ occurW (r1, u2);
        r1 := Some u2
      end
    | u1, CVar r2 -> begin
        ignore @@ occurW (r2, u1);
        r2 := Some u1
      end
    | u -> begin
        Debug.(
          msg' ~src:Group.approx ~level:Level.Debug
          @@ Fmt.concat
               Fmt.
                 [
                   const string "Failed to match";
                   using fst pp_exp;
                   const string "with";
                   using snd pp_exp;
                 ])
          u;
        raise (Unify "Type/kind expression clash")
      end

  and match_ (u1, u2) = matchW (whnf u1, whnf u2)

  let matchable (u1, u2) =
    try
      begin
        match_ (u1, u2);
        true
      end
    with Unify _ -> false

  let rec makeGroundUni = function
    | Level _ -> false
    | Next l -> makeGroundUni l
    | LVar { contents = Some l } -> makeGroundUni l
    | LVar ({ contents = None } as r) -> begin
        r := Some (Level 1);
        true
      end
end
(*! structure IntSyn' : INTSYN !*)
(*! sharing Whnf.IntSyn = IntSyn' !*)
(* structure Apx *)
(* # 1 "src/lambda/Approx.sml.ml" *)
