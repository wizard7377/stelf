open! Global.Global_
open! Intsyn.Lambda_
open! Names.Names_
open! Paths
open! Paths.Paths_
open! Index.Index_

(* # 1 "src/style/Style_.sig.ml" *)

(* Style Checking *)

include STYLE
(** Author: Carsten Schuermann *)

(* signature STYLECHECK *)

(* # 1 "src/style/Style_.fun.ml" *)
open! Basis
open Origins

exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module MakeStyleCheck (Whnf : WHNF) (Index : INDEX) (Origins : ORIGINS) :
  STYLECHECK = struct
  exception Error = Error

  open! struct
    module I = IntSyn
    module P = Paths

    type polarity = Plus | Minus [@@deriving eq, ord, show]

    type info = Correct | Incorrect of string list * string
    [@@deriving eq, ord, show]

    let toggle = function Plus -> Minus | Minus -> Plus

    let wrapMsg (c, occ, msg) err =
      begin match Origins.originLookup c with
      | fileName, None -> (fileName ^ ":") ^ msg
      | fileName, Some occDec ->
          P.wrapLoc'
            (P.Loc (fileName, err occDec occ)) (Origins.linesInfoLookup fileName) msg
      end

    let rec denumber = function
      | [] -> []
      | c :: l ->
          let x = ord c in
          let l' = denumber l in
          begin if (x >= 65 && x <= 90) || (x >= 97 && x <= 122) then c :: l'
          else l'
          end

    let rec options = function n :: [] -> n | n :: l -> (n ^ ", ") ^ options l

    let error c (prefNames, n, occ) err =
      [
        wrapMsg
          ( c,
            occ,
            ((("Variable naming: expected " ^ options prefNames) ^ " found ")
            ^ n)
            ^ "\n" )
          err;
      ]

    let checkVariablename (n, prefNames) =
      begin if
        List.exists
          (function n' -> denumber (explode n) = denumber (explode n'))
          prefNames
      then Correct
      else Incorrect (prefNames, n)
      end

    let checkVar (a, pol) = match a with
      | I.Dec (Some n, v) ->
          begin match Names.getNamePref (I.targetFam v) with
          | None -> Correct
          | Some (prefENames, prefUNames) ->
              begin match pol with
              | Plus -> checkVariablename (n, prefENames)
              | Minus -> checkVariablename (n, prefUNames)
              end
          end
      | I.Dec (None, v) -> Correct

    let implicitHead = function
      | I.BVar k -> 0
      | I.Const c -> I.constImp c
      | I.Skonst k -> 0
      | I.Def d -> I.constImp d
      | I.NSDef d -> I.constImp d
      | I.FgnConst _ -> 0

    let rec checkExp arg__1 arg__2 arg__3 =
      begin match (arg__1, arg__2, arg__3) with
      | c, ((g, p), I.Uni _, occ), err -> []
      | c, ((g, p), I.Lam (d, u), occ), err ->
          checkDec c
            ((g, p), d, Minus, occ)
            err
            (function
              | (g', p'), l' ->
              l' @ checkExp c ((g', p'), u, P.body occ) err)
      | c, ((g, p), I.Root (h, s), occ), err ->
          checkHead c ((g, p), h, P.head occ) err
          @ checkSpine c ((g, p), 1, implicitHead h, s, P.body occ) err
      | c, ((g, p), I.FgnExp (_, _), occ), err -> []
      end

    and checkType arg__4 arg__5 arg__6 =
      begin match (arg__4, arg__5, arg__6) with
      | c, ((g, p), I.Uni _, pol, occ), err -> []
      | c, ((g, p), I.Pi ((d, Maybe), v), pol, occ), err ->
          checkDec c
            ((g, p), d, pol, occ)
            err
            (function
              | (g', p'), l' ->
              l' @ checkType c ((g', p'), v, pol, P.body occ) err)
      | c, ((g, p), I.Pi ((d, No), v), pol, occ), err ->
          checkDec c
            ((g, p), d, pol, occ)
            err
            (function
              | (g', p'), l' ->
              l' @ checkType c ((g', p'), v, pol, P.body occ) err)
      | c, ((g, p), I.Root (h, s), pol, occ), err ->
          checkHead c ((g, p), h, P.head occ) err
          @ checkSpine c ((g, p), 1, implicitHead h, s, P.body occ) err
      | c, ((g, p), I.FgnExp (_, _), pol, occ), err -> []
      end

    and checkDecImp ((g, p), (I.Dec (_, v) as d), pol) k =
      let i = checkVar (d, pol) in
      k ((I.Decl (g, d), I.Decl (p, i)), [])

    and checkDec c ((g, p), (I.Dec (_, v) as d), pol, occ) err k =
      let i = checkVar (d, pol) in
      let e1 =
        begin match i with
        | Correct -> []
        | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err
        end
      in
      let e2 = checkType c ((g, p), v, toggle pol, P.label occ) err in
      k ((I.Decl (g, d), I.Decl (p, i)), e1 @ e2)

    and checkHead arg__7 arg__8 arg__9 =
      begin match (arg__7, arg__8, arg__9) with
      | c, ((g, p), I.BVar k, occ), err ->
          begin match I.ctxLookup p k with
          | Correct -> []
          | Incorrect (prefNames, n) -> error c (prefNames, n, occ) err
          end
      | c, ((g, p), I.Const _, occ), err -> []
      | c, ((g, p), I.Skonst k, occ), err -> []
      | c, ((g, p), I.Def d, occ), err -> []
      | c, ((g, p), I.NSDef d, occ), err -> []
      | c, ((g, p), I.FgnConst _, occ), err -> []
      end

    and checkSpine arg__10 arg__11 arg__12 =
      begin match (arg__10, arg__11, arg__12) with
      | c, ((g, p), n, 0, I.Nil, occ), err -> []
      | c, ((g, p), n, 0, I.App (u, s), occ), err ->
          checkExp c ((g, p), u, P.arg n occ) err
          @ checkSpine c ((g, p), n + 1, 0, s, occ) err
      | c, ((g, p), n, i, I.App (u, s), occ), err ->
          checkSpine c ((g, p), n + 1, i - 1, s, occ) err
      end

    let rec checkType' arg__13 arg__14 arg__15 =
      begin match (arg__13, arg__14, arg__15) with
      | c, ((g, p), 0, v, occ), err ->
          checkType c ((g, p), v, Plus, occ) err
      | c, ((g, p), n, I.Pi ((d, Maybe), v), occ), err ->
          checkDecImp
            ((g, p), d, Plus)
            (function
              | (g', p'), l' ->
              l' @ checkType' c ((g', p'), n - 1, v, P.body occ) err)
      end

    let rec checkExp' arg__16 arg__17 arg__18 =
      begin match (arg__16, arg__17, arg__18) with
      | c, ((g, p), I.Lam (d, u), occ), err ->
          checkDec c
            ((g, p), d, Plus, occ)
            err
            (function
              | (g', p'), l' ->
              l' @ checkExp' c ((g', p'), u, P.body occ) err)
      | c, ((g, p), u, occ), err -> checkExp c ((g, p), u, occ) err
      end

    let rec checkDef arg__19 arg__20 arg__21 =
      begin match (arg__19, arg__20, arg__21) with
      | c, ((g, p), 0, u, occ), err -> checkExp' c ((g, p), u, occ) err
      | c, ((g, p), n, I.Lam (d, u), occ), err ->
          checkDecImp
            ((g, p), d, Plus)
            (function
              | (g', p'), l' ->
              l' @ checkDef c ((g', p'), n - 1, u, P.body occ) err)
      end

    let checkConDec arg__22 arg__23 =
      begin match (arg__22, arg__23) with
      | c, I.ConDec (_, _, implicit, _, u, _) -> begin
          begin if !Global.chatter > 3 then
            print (Names.qidToString (Names.constQid c) ^ " ")
          else ()
          end;
          checkType' c ((I.Null, I.Null), implicit, u, P.top) P.occToRegionDec
        end
      | c, I.ConDef (_, _, implicit, u, v, I.Type, _) -> begin
          begin if !Global.chatter > 3 then
            print (Names.qidToString (Names.constQid c) ^ " ")
          else ()
          end;
          checkType' c ((I.Null, I.Null), implicit, v, P.top) P.occToRegionDef2
          @ checkDef c ((I.Null, I.Null), implicit, u, P.top) P.occToRegionDef1
        end
      | c, I.AbbrevDef (_, _, implicit, u, v, I.Type) -> begin
          begin if !Global.chatter > 3 then
            print (Names.qidToString (Names.constQid c) ^ " ")
          else ()
          end;
          begin
            ignore
            @@ checkType' c
                 ((I.Null, I.Null), implicit, v, P.top)
                 P.occToRegionDef2;
            checkDef c ((I.Null, I.Null), implicit, u, P.top) P.occToRegionDef1
          end
        end
      | c, _ -> []
      end

    let rec checkAll (c, n) =
      begin if c <= n then checkConDec c (I.sgnLookup c) @ checkAll (c + 1, n)
      else []
      end

    let check () =
      let n, _ = I.sgnSize () in
      ignore @@ map print (checkAll (0, n));
      ()
  end

  (* indicates positivity *)
  (* distinguishes style correct
                                           from - incorrect declarations *)
  (* wrapMsg (c, occ, msg) err = s

       Invariant:
       Let c be a cid
       occ by an occurrence,
       msg an error message,
       and err a function that computes adequate region information for c
       then s is msg wrapped with location information
    *)
  (* denumber L = L'

       Invariant:
       L' = L without digits
    *)
  (* checkVariblename (n, prefNames) = I

       Invariant:
       If n occurs in prefNames then I = Correct otherwise Incorrect
    *)
  (* checkVar (D, pol) = I

       Invariant:
       If  D's name corresponds to the name choice for pol,
       then I is Correct else Incorrect
    *)
  (* implicitHead H = k

       Invariant:
       k = # implicit arguments associated with H
    *)
  (* checkExp c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from U
    *)
  (* checkType c ((G, P), V, pol, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  V : type
       and   occ an occurrence to the current location
       and   err an function mapping occ to regions
       then  L is a list of strings (error messages) computed from V
    *)
  (* checkDecImp c ((G, P), D, pol) k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed D
       ( checkDecImp does not generate any error messages for D since omitted)
    *)
  (* checkDec c ((G, P), D, pol, occ) err k = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-pol  D declation
       and   occ occurrence, err wrapper function
       and   k a continuation, that expects the extended context (G', P')
             and a list of already computed error messages L' as argument.
       then  L is a list of strings (error messages) computed from D
    *)
  (* checkHead c ((G, P), H, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |-  H head
       and   occ occurrence, err wrapper function
       then  L is a list of at most one string (error message) computed from H
    *)
  (* checkSpine c ((G, P), S, n, i, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- S : V1 >> V2  for V1 V2, valid types
       and   n a running number of arguments considered
       and   i the number of remaining implicit arguments
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from S
    *)
  (* checkType' c ((G, P), n, V, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- V : type
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from V
       (omitted arguments generate error message where they are used not declared)
    *)
  (* checkExp' c ((G, P), U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of  strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
  (* checkDef c ((G, P), n, U, occ) err = L

       Invariant:
       Let   c be a cid
       and   |- G ctx
       and   |- P info for G
       and   n a decreasing number of implicit arguments
       and   G |- U : V for some type V, body of a definition
       and   occ occurrence, err wrapper function
       then  L is a list of strings (error messages) computed from U
       (top level negative occurrences exception.  Treated as pos occurrences)
    *)
  (* checkConDec c C = L

       Invariant:
       Let   c be a cid
       and   . |- C : V for some type V, constant declaration
       then  L is a list of  strings (error messages) computed from C
    *)
  (* type level definitions ? *)
  (* type level abbreviations ? *)
  (* in all other cases *)
  (* checkAll (c, n) = L

       Invariant:
       Let   c be a cid
       and   n the max. number of cids
       then  L is a list of  strings (error messages) computed from the signature c<=n
    *)
  (* checkAll () = L

       Invariant:
       L is a list of  strings (error messages) computed from the entire Stelf signature
    *)
  let checkConDec = function
    | c -> begin
        ignore @@ map print (checkConDec c (I.sgnLookup c));
        ()
      end

  let check = check
end

(* # 1 "src/style/Style_.sml.ml" *)
module StyleCheck = MakeStyleCheck (Whnf) (Index) (Origins)
