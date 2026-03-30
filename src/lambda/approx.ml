(* # 1 "src/lambda/approx.sig.ml" *)
open! Basis
open Intsyn

(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
module type APPROX = sig
  (*! structure IntSyn : INTSYN !*)
  type uni = Level of int | Next of uni | LVar of uni option ref
  [@@deriving eq, show]

  (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)
  type exp =
    | Uni of uni
    | Arrow of exp * exp
    | Const of IntSyn.head
    | CVar of exp option ref
    | Undefined
  [@@deriving eq, show]

  (* Const/Def/NSDef *)
  val type_ : uni
  val kind : uni
  val hyperkind : uni

  (* resets names of undetermined type/kind variables chosen for printing *)
  val varReset : unit -> unit
  val newLVar : unit -> uni
  val newCVar : unit -> exp
  val whnfUni : uni -> uni
  val whnf : exp -> exp
  val uniToApx : IntSyn.uni -> uni
  val classToApx : IntSyn.exp -> exp * uni
  val exactToApx : IntSyn.exp * IntSyn.exp -> exp * exp * uni

  exception Ambiguous

  val apxToUni : uni -> IntSyn.uni
  val apxToClass : IntSyn.dctx * exp * uni * bool -> IntSyn.exp
  val apxToExact : IntSyn.dctx * exp * IntSyn.eclo * bool -> IntSyn.exp

  exception Unify of string

  val matchUni : uni * uni -> unit
  val match_ : exp * exp -> unit
  val makeGroundUni : uni -> bool
end

(* # 1 "src/lambda/approx.fun.ml" *)
open! Whnf
open! Basis

(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)
module MakeApprox (Approx__0 : sig
  module Whnf : WHNF
end) : APPROX = struct
  (*! structure IntSyn = IntSyn' !*)
  module Whnf = Approx__0.Whnf
  module I = IntSyn

  let rec headConDec = function
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
  let rec newLVar () = LVar (ref None)
  let rec newCVar () = CVar (ref None)

  (* whnfUni (l) = l'
       where l = l' and l' is in whnf *)
  let rec whnfUni = function
    | Next l_ -> begin
        match whnfUni l_ with Level i -> Level (i + 1) | l'_ -> Next l'_
      end
    | LVar { contents = Some l_ } -> whnfUni l_
    | l_ -> l_

  (* whnf (u) = u'
       where u = u' and u' is in whnf *)
  let rec whnf = function CVar { contents = Some v_ } -> whnf v_ | v_ -> v_

  open! struct
    type nonrec varEntry = (exp * exp * uni) * string

    let varList : varEntry list ref = ref []
  end

  (* just a little list since these are only for printing errors *)
  let rec varReset () = varList := []

  let rec varLookupRef r =
    List.find (function (CVar r', _, _), _ -> r == r') !varList

  let rec varLookupName name =
    List.find (function _, name' -> name = name') !varList

  let rec varInsert ((u_, v_, l_), name) =
    varList := ((u_, v_, l_), name) :: !varList

  exception Ambiguous

  (* getReplacementName (u, v, l, allowed) = name
         if u : v : l
         and u is a CVar at type family or kind level *)
  let rec getReplacementName ((CVar r as u_), v_, l_, allowed) =
    begin match varLookupRef r with
    | Some (_, name) -> name
    | None ->
        let _ =
          begin if allowed then () else raise Ambiguous
          end
        in
        let pref =
          begin match whnfUni l_ with Level 2 -> "A" | Level 3 -> "K"
          end
        in
        let rec try_ i =
          let name = (("%" ^ pref) ^ Int.toString i) ^ "%" in
          begin match varLookupName name with
          | None -> begin
              varInsert ((u_, v_, l_), name);
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
  let rec findByReplacementName name =
    begin match varLookupName name with
    | Some (uvl_, _) -> uvl_
    | None ->
        Logs.debug (fun m -> m "Failed to find name");
        raise (Fail "Name not found")
    end
  (* must be in list by invariant *)

  (* converting exact terms to approximate terms *)
  (* uniToApx (L) = L- *)
  let rec uniToApx = function I.Type -> type_ | I.Kind -> kind

  (* expToApx (U) = (U-, V-)
     if G |- U : V
     or G |- U "":"" V = ""hyperkind"" *)
  let rec expToApx = function
    | I.Uni l_ ->
        let l'_ = uniToApx l_ in
        (Uni l'_, Uni (whnfUni (Next l'_)))
    | I.Pi ((I.Dec (_, v1_), _), v2_) ->
        let v1'_, _ (* Type *) = expToApx v1_ in
        let v2'_, l'_ = expToApx v2_ in
        (Arrow (v1'_, v2'_), l'_)
    | I.Root (I.FVar (name, _, _), _) ->
        let u_, v_, l_ = findByReplacementName name in
        (u_, v_)
    | I.Root (h_, _ (* Const/Def/NSDef *)) -> (Const h_, Uni type_)
    | I.Redex (u_, _) -> expToApx u_
    | I.Lam (_, u_) -> expToApx u_
    | I.EClo (u_, _) -> expToApx u_

  (* are we sure Skonst/FgnConst are never types or kinds? *)
  (* must have been created to represent a CVar *)

  (* classToApx (V) = (V-, L-)
     if G |- V : L
     or G |- V "":"" L = ""hyperkind"" *)
  let rec classToApx v_ =
    let v'_, l'_ = expToApx v_ in
    let (Uni l''_) = whnf l'_ in
    (v'_, l''_)

  (* exactToApx (U, V) = (U-, V-)
     if G |- U : V *)
  let rec exactToApx (u_, v_) =
    let v'_, l'_ = classToApx v_ in
    begin match whnfUni l'_ with
    | Level 1 -> (Undefined, v'_, l'_)
    | _ ->
        let u'_, _ (* V' *) = expToApx u_ in
        (u'_, v'_, l'_)
    end

  (* Type *)
  (* Kind/Hyperkind *)

  (* constDefApx (d) = V-
     if |- d = V : type *)
  let rec constDefApx d =
    begin match I.sgnLookup d with
    | I.ConDef (_, _, _, u_, _, _, _) ->
        let v'_, _ (* Uni Type *) = expToApx u_ in
        v'_
    | I.AbbrevDef (_, _, _, u_, _, _) ->
        let v'_, _ (* Uni Type *) = expToApx u_ in
        v'_
    end

  (* converting approximate terms to exact terms *)
  (* apxToUni (L-) = L *)
  let rec apxToUniW = function Level 1 -> I.Type | Level 2 -> I.Kind

  (* others impossible by invariant *)
  let rec apxToUni l_ = apxToUniW (whnfUni l_)

  (* apxToClass (G, v, L-, allowed) = V
     pre: L is ground and <= Hyperkind,
          and if L is Hyperkind then the target classifier
          of v is ground
          v : L-
     post: V is most general such that V- = v and G |- V : L *)
  let rec apxToClassW = function
    | g_, Uni l_, _, allowed (* Next L *) -> I.Uni (apxToUni l_)
    | g_, Arrow (v1_, v2_), l_, allowed ->
        let v1'_ = apxToClass (g_, v1_, type_, allowed) in
        let d_ = I.Dec (None, v1'_) in
        let v2'_ = apxToClass (I.Decl (g_, d_), v2_, l_, allowed) in
        I.Pi ((d_, I.Maybe), v2'_)
    | g_, (CVar r as v_), l_, allowed (* Type or Kind *) ->
        let name = getReplacementName (v_, Uni l_, Next l_, allowed) in
        let s = I.Shift (I.ctxLength g_) in
        I.Root (I.FVar (name, I.Uni (apxToUni l_), s), I.Nil)
    | g_, Const h_, l_, allowed (* Type *) ->
        I.Root (h_, Whnf.newSpineVar (g_, (I.conDecType (headConDec h_), I.id)))
  (* convert undetermined CVars to FVars *)
  (* also, does the name of the bound variable here matter? *)
  (* this is probably very bad -- it should be possible to infer
         more accurately which pis can be dependent *)

  and apxToClass (g_, v_, l_, allowed) = apxToClassW (g_, whnf v_, l_, allowed)

  (* Undefined case impossible *)
  (* apxToExact (G, u, (V, s), allowed) = U
     if u : V-
     and G' |- V : L and G |- s : G'
     then U- = u and G |- U : V[s] and U is the most general such *)
  let rec apxToExactW = function
    | g_, u_, (I.Pi ((d_, _), v_), s), allowed ->
        let d'_ = I.decSub (d_, s) in
        I.Lam (d'_, apxToExact (I.Decl (g_, d'_), u_, (v_, I.dot1 s), allowed))
    | g_, u_, (I.Uni l_, s), allowed -> apxToClass (g_, u_, uniToApx l_, allowed)
    | g_, u_, ((I.Root (I.FVar (name, _, _), _), s) as vs_), allowed ->
        let v_, l_, _ (* Next L *) = findByReplacementName name in
        let (Uni l_) = whnf l_ in
        begin match whnfUni l_ with
        | Level 1 ->
            let vs_e, vs_s = vs_ in
            I.newEVar (g_, I.EClo (vs_e, vs_s))
        | Level 2 ->
            let name' = getReplacementName (whnf u_, v_, Level 2, allowed) in
            let v'_ = apxToClass (Null, v_, Level 2, allowed) in
            let s' = I.Shift (I.ctxLength g_) in
            I.Root (I.FVar (name', v'_, s'), I.Nil)
        (* NOTE: V' differs from Vs by a Shift *)
        (* probably could avoid the following call by removing the
                  substitutions in Vs instead *)
        end
        (* U must be a CVar *)
    | g_, u_, vs_, allowed (* an atomic type, not Def *) ->
        let vs_e, vs_s = vs_ in
        I.newEVar (g_, I.EClo (vs_e, vs_s))

  and apxToExact (g_, u_, vs_, allowed) =
    apxToExactW (g_, u_, Whnf.whnfExpandDef vs_, allowed)

  (* matching for the approximate language *)
  exception Unify of string

  (* occurUni (r, l) = ()
       iff r does not occur in l,
       otherwise raises Unify *)
  let rec occurUniW = function
    | r, Next l_ -> occurUniW (r, l_)
    | r, LVar r' -> begin
        if r == r' then raise (Unify "Level circularity") else ()
      end
    | r, _ -> ()

  let rec occurUni (r, l_) = occurUniW (r, whnfUni l_)

  (* matchUni (l1, l2) = ()
       iff l1<I> = l2<I> for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
  let rec matchUniW = function
    | Level i1, Level i2 -> begin
        if i1 = i2 then () else raise (Unify "Level clash")
      end
    | Level i1, Next l2_ -> begin
        if i1 > 1 then matchUniW (Level (i1 - 1), l2_)
        else raise (Unify "Level clash")
      end
    | Next l1_, Level i2 -> begin
        if i2 > 1 then matchUniW (l1_, Level (i2 - 1))
        else raise (Unify "Level clash")
      end
    | Next l1_, Next l2_ -> matchUniW (l1_, l2_)
    | LVar r1, (LVar r2 as l2_) -> begin
        if r1 == r2 then () else r1 := Some l2_
      end
    | LVar r1, l2_ -> begin
        occurUniW (r1, l2_);
        r1 := Some l2_
      end
    | l1_, LVar r2 -> begin
        occurUniW (r2, l1_);
        r2 := Some l1_
      end

  let rec matchUni (l1_, l2_) = matchUniW (whnfUni l1_, whnfUni l2_)

  (* occur (r, u) = ()
       iff r does not occur in u,
       otherwise raises Unify *)
  let rec occurW = function
    | r, _ when !r == None -> false
    | r, Arrow (v1_, v2_) -> begin occur' (r, v1_) || occur' (r, v2_) end
    | r, CVar r' -> begin
        if r == r' then raise (Unify "Type/kind variable occurrence") else false
      end
    | r, _ -> false

  and occur' (r, u_) = occurW (r, whnf u_)

  let occur = ignore occur'

  (* match (u1, u2) = ()
       iff u1<I> = u2<I> : v for some most general instantiation I
       effect: applies I
       otherwise raises Unify *)
  let rec matchW = function
    | Uni l1_, Uni l2_ -> matchUni (l1_, l2_)
    | (Const h1_ as v1_), (Const h2_ as v2_) -> begin
        match (h1_, h2_) with
        | I.Const c1, I.Const c2 -> begin
            if c1 = c2 then () else raise (Unify "Type/kind constant clash")
          end
        | I.Def d1, I.Def d2 -> begin
            if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
          end
        | I.Def d1, _ -> match_ (constDefApx d1, v2_)
        | _, I.Def d2 -> match_ (v1_, constDefApx d2)
        | I.NSDef d1, I.NSDef d2 -> begin
            if d1 = d2 then () else match_ (constDefApx d1, constDefApx d2)
          end
        | I.NSDef d1, _ -> match_ (constDefApx d1, v2_)
        | _, I.NSDef d2 -> match_ (v1_, constDefApx d2)
      end
    | Arrow (v1_, v2_), Arrow (v3_, v4_) -> begin
        (try match_ (v1_, v3_)
         with e ->
           begin
             match_ (v2_, v4_);
             raise e
           end);
        match_ (v2_, v4_)
      end
    | (Arrow _ as v1_), Const (I.Def d2) -> match_ (v1_, constDefApx d2)
    | Const (I.Def d1), (Arrow _ as v2_) -> match_ (constDefApx d1, v2_)
    | (Arrow _ as v1_), Const (I.NSDef d2) -> match_ (v1_, constDefApx d2)
    | Const (I.NSDef d1), (Arrow _ as v2_) -> match_ (constDefApx d1, v2_)
    | CVar r1, (CVar r2 as u2_) -> begin
        if r1 == r2 then () else r1 := Some u2_
      end
    | CVar r1, u2_ -> begin
        ignore @@ occurW (r1, u2_);
        r1 := Some u2_
      end
    | u1_, CVar r2 -> begin
        ignore @@ occurW (r2, u1_);
        r2 := Some u1_
      end
    | u -> begin
        Debug.(
          msg Group.approx Level.Debug
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

  and match_ (u1_, u2_) = matchW (whnf u1_, whnf u2_)

  let rec matchable (u1_, u2_) =
    try
      begin
        match_ (u1_, u2_);
        true
      end
    with Unify _ -> false

  let rec makeGroundUni = function
    | Level _ -> false
    | Next l_ -> makeGroundUni l_
    | LVar { contents = Some l_ } -> makeGroundUni l_
    | LVar ({ contents = None } as r) -> begin
        r := Some (Level 1);
        true
      end
end
(*! structure IntSyn' : INTSYN !*)
(*! sharing Whnf.IntSyn = IntSyn' !*)
(* structure Apx *)
(* # 1 "src/lambda/approx.sml.ml" *)
