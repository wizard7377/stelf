
(* # 1 "src/compress/Strict.sig.ml" *)

(* # 1 "src/compress/Strict.fun.ml" *)

(* # 1 "src/compress/Strict.sml.ml" *)
open! Basis

module Strict = struct
  open Syntax
  open Syntax

  exception EtaContract

  (* val eta_contract_var : spineelt -> int
      if the spine element given is an ordinary spine element (i.e. an Elt)
      that is an eta-expansion of the deBruijn index n,
      then returns n. Otherwise raises EtaContract.
    *)
  let rec eta_contract_var = function
    | Elt t -> eta_contract_var' 0 t
    | _ -> raise EtaContract

  and eta_contract_var' arg__2 arg__3 =
    begin match (arg__2, arg__3) with
    | n, ATerm (ARoot (Var n', s)) ->
        let s' = map eta_contract_var s in
        let rec decreasing_list arg__0 arg__1 =
          begin match (arg__0, arg__1) with
          | 0, [] -> true
          | n, h :: tl -> n - 1 = h && decreasing_list (n - 1) tl
          | _, _ -> false
          end
        in
        begin if decreasing_list n s' then n' - n else raise EtaContract
        end
    | n, NTerm (Lam t) -> eta_contract_var' (n + 1) t
    | _, _ -> raise EtaContract
    end

  let rec pattern_spine' (d, a) = match a with
    | [] -> true
    | n :: s ->
        let isn x = x = n in
        let hasn s = List.exists isn s in
        hasn d && (not (hasn s)) && pattern_spine' (d, s)

  let pattern_spine (d, s) =
    try pattern_spine' (d, map eta_contract_var s) with EtaContract -> false

  let rec spine_occ arg__4 arg__5 =
    begin match (arg__4, arg__5) with
    | n, (d, []) -> false
    | n, (d, Elt t :: s) -> term_occ n (d, t) || spine_occ n (d, s)
    | n, (d, AElt t :: s) -> aterm_occ n (d, t) || spine_occ n (d, s)
    | n, (d, Ascribe (t, a) :: s) ->
        nterm_occ n (d, t) || type_occ n (d, a) || spine_occ n (d, s)
    | n, (d, Omit :: s) -> false
    end

  and term_occ arg__6 arg__7 =
    begin match (arg__6, arg__7) with
    | n, (d, NTerm t) -> nterm_occ n (d, t)
    | n, (d, ATerm t) -> aterm_occ n (d, t)
    end

  and nterm_occ arg__8 arg__9 =
    begin match (arg__8, arg__9) with
    | n, (d, Lam t) -> term_occ (n + 1) (0 :: map (function x -> x + 1) d, t)
    | n, (d, NRoot (h, s)) -> root_occ n (d, h, s)
    end

  and aterm_occ arg__10 arg__11 =
    begin match (arg__10, arg__11) with
    | n, (d, ARoot (h, s)) -> root_occ n (d, h, s)
    | n, (d, ERoot _) -> false
    end

  and root_occ arg__12 arg__13 =
    begin match (arg__12, arg__13) with
    | n, (d, Var n', s) ->
        begin if n = n' then pattern_spine (d, s)
        else List.exists (function x -> x = n') d && spine_occ n (d, s)
        end
    | n, (d, Const n', s) -> spine_occ n (d, s)
    end

  and type_occ arg__14 arg__15 =
    begin match (arg__14, arg__15) with
    | n, (d, TRoot (_, s)) -> spine_occ n (d, s)
    | n, (d, TPi (_, a, b)) ->
        type_occ n (d, a)
        || type_occ (n + 1) (0 :: map (function x -> x + 1) d, b)
    (* PERF: suspend these context shifts, do them at the end *)
    end

  (* Omit invalidates all strict
					    occurrences to the right *)
  (* PERF: suspend these context shifts, do them at the end *)
  (* toplevel strictness judgments *)
  let rec check_strict_type' arg__16 arg__17 arg__18 =
    begin match (arg__16, arg__17, arg__18) with
    | n, p, TRoot (n', s) ->
        begin if p then false else spine_occ n ([], s)
        end
    | n, p, TPi (Plus, a, b) ->
        type_occ n ([], a) || check_strict_type' (n + 1) p b
    | n, p, TPi (_, a, b) -> check_strict_type' (n + 1) p b
    end

  let rec check_strict_kind' arg__19 arg__20 =
    begin match (arg__19, arg__20) with
    | n, Type -> false
    | n, KPi (Plus, a, k) -> type_occ n ([], a) || check_strict_kind' (n + 1) k
    | n, KPi (_, a, k) -> check_strict_kind' (n + 1) k
    end

  (* p is whether we should imagine we are checking a c+ (rather than c-) constant *)
  let check_strict_type p b = check_strict_type' 0 p b
  let check_strict_kind k = check_strict_kind' 0 k
end

include Strict

let () =
  Printexc.register_printer (function
    | EtaContract -> Some "EtaContract"
    | _ -> None)
