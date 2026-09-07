open! Intsyn.Lambda_
open! Paths.Paths_

(* # 1 "src/typecheck/Strict.sig.ml" *)

(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)
include STRICT
(* signature STRICT *)

(* # 1 "src/typecheck/Strict.fun.ml" *)
open! Basis

(* Checking Definitions for Strict *)
(* Author: Carsten Schuermann *)
exception Error of string

let () =
  Printexc.register_printer (function Error msg -> Some msg | _ -> None)

module Strict (Strict__0 : sig
  module Whnf : WHNF
end) : STRICT = struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  exception Error = Error

  open! struct
    module I = IntSyn

    let rec patSpine = function
      | _, I.Nil -> true
      | k, I.App (I.Root (I.BVar k', I.Nil), s_) ->
          let rec indexDistinct = function
            | I.Nil -> true
            | I.App (I.Root (I.BVar k'', I.Nil), s_) ->
                k' <> k'' && indexDistinct s_
            | _ -> false
          in
          k' <= k && patSpine (k, s_) && indexDistinct s_
      | _ -> false

    let rec strictExp (k, p, a) = match a with
      | I.Uni _ -> false
      | I.Lam (d_, u_) ->
          strictDec (k, p, d_) || strictExp (k + 1, p + 1, u_)
      | I.Pi ((d_, _), u_) ->
          strictDec (k, p, d_) || strictExp (k + 1, p + 1, u_)
      | I.Root (h_, s_) ->
          begin match h_ with
          | I.BVar k' ->
              begin if k' = p then patSpine (k, s_)
              else k' <= k && strictSpine (k, p, s_)
              end
          | I.Const c -> strictSpine (k, p, s_)
          | I.Def d -> strictSpine (k, p, s_)
          | I.FgnConst (cs, conDec) -> strictSpine (k, p, s_)
          end
      | I.FgnExp (cs, ops) -> false

    and strictSpine (k, p, a) = match a with
      | I.Nil -> false
      | I.App (u_, s_) -> strictExp (k, p, u_) || strictSpine (k, p, s_)

    and strictDec (k, p, I.Dec (_, v_)) = strictExp (k, p, v_)

    let rec strictArgParm (p, a) = match a with
      | (I.Root _ as u_) -> strictExp (0, p, u_)
      | (I.Pi _ as u_) -> strictExp (0, p, u_)
      | (I.FgnExp _ as u_) -> strictExp (0, p, u_)
      | I.Lam (d_, u_) -> strictArgParm (p + 1, u_)

    let occToString (a, occ) = match a with
      | Some ocd -> Paths.wrap (Paths.occToRegionDef1 ocd occ) ("")
      | None -> "Error: "

    let decToVarName = function
      | I.Dec (None, _) -> "implicit variable"
      | I.Dec (Some x, _) -> "variable " ^ x

    let strictTop ((u_, v_), ocdOpt) =
      let rec strictArgParms (a, b, occ) = match a, b with
        | I.Root (I.BVar _, _), _ ->
            raise
              (Error (occToString (ocdOpt, occ) ^ "Head not rigid, use %abbrev"))
        | I.Root _, _ -> ()
        | I.Pi _, _ -> ()
        | I.FgnExp _, _ -> ()
        | I.Lam (d_, u'_), I.Pi (_, v'_) ->
            begin if strictArgParm (1, u'_) then
              strictArgParms (u'_, v'_, Paths.body occ)
            else
              raise
                (Error
                   (((occToString (ocdOpt, occ) ^ "No strict occurrence of ")
                    ^ decToVarName d_)
                   ^ ", use %abbrev"))
            end
        | (I.Lam _ as u_), (I.Root (I.Def _, _) as v_) ->
            strictArgParms (u_, Whnf.normalize (Whnf.expandDef (v_, I.id)), occ)
      in
      strictArgParms (u_, v_, Paths.top)

    let occursInType ((i, v_), ocdOpt) =
      let rec oit = function
        | (0, v_), occ -> ()
        | (i, I.Pi ((d_, p_), v_)), occ ->
            begin match Abstract.piDepend d_ p_ v_ with
            | I.Pi ((d'_, Maybe), v_) -> oit ((i - 1, v_), Paths.body occ)
            | _ ->
                raise
                  (Error
                     (((occToString (ocdOpt, occ) ^ "No occurrence of ")
                      ^ decToVarName d_)
                     ^ " in type, use %abbrev"))
            end
        | _ -> ()
      in
      oit ((i, v_), Paths.top)
  end

  (* Definition of normal form (nf) --- see lambda/Whnf.fun *)
  (* patSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > V', S in nf
       and |D| = k
       then B iff S = (k1 ; k2 ;...; kn ; NIL), kn <= k, all ki pairwise distinct
    *)
  (* possibly eta-contract? -fp *)
  (* strictExp (k, p, U) = B

       Invariant:
       If  G, D |- U : V
       and U is in nf (normal form)
       and |D| = k
       then B iff U is strict in p
    *)
  (* checking D in this case might be redundant -fp *)
  (* no other cases possible *)
  (* this is a hack - until we investigate this further   -rv *)
  (* no other cases possible *)
  (* strictSpine (k, S) = B

       Invariant:
       If  G, D |- S : V > W
       and S is in nf (normal form)
       and |D| = k
       then B iff S is strict in k
    *)
  (* strictArgParm (p, U) = B

       Traverses the flexible abstractions in U.

       Invariant:
       If   G |- U : V
       and  G |- p : V'
       and  U is in nf
       then B iff argument parameter p occurs in strict position in U
                  which starts with argument parameters
    *)
  (* strictTop ((U, V), ocdOpt) = ()

       Invariant:
       condec has form c = U : V where . |- U : V
       and U is in nf (normal form)
       then function returns () if U every argument parameter of U
            has at least one strict and rigid occurrence in U
       raises Error otherwise

       ocdOpt is an optional occurrence tree for condec for error messages
    *)
  (* may not be sound in general *)
  (* Wed Aug 25 16:39:57 2004 -fp *)
  let check = strictTop
  let checkType k u_ occ = occursInType ((k, u_), occ)
end
(*! structure IntSyn' : INTSYN !*)
(*! sharing Whnf.IntSyn = IntSyn' !*)
(*! structure Paths' : PATHS !*)
(* functor Strict *)

(* # 1 "src/typecheck/Strict.sml.ml" *)
