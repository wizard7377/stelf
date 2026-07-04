open Intsyn.IntSyn
open Intsyn.Lambda_.Abstract
open IntSynHelpers

(* closedExp checks: "does this expression contain any uninstantiated EVar
   or FVar?" — not whether de Bruijn indices are in bounds. *)

let test_closed_uni_type () =
  Alcotest.(check bool) "Uni Type is closed (no EVars)" true
    (closedExp (null_ctx, (Uni Type, id_sub)))

let test_closed_uni_kind () =
  Alcotest.(check bool) "Uni Kind is closed (no EVars)" true
    (closedExp (null_ctx, (Uni Kind, id_sub)))

let test_closed_lam () =
  let lam = lam_ (Uni Type) (bvar 1) in
  Alcotest.(check bool) "Lam with no EVars is closed" true
    (closedExp (null_ctx, (lam, id_sub)))

let test_closed_pi () =
  let pi = Pi ((Dec (None, Uni Type), No), Uni Type) in
  Alcotest.(check bool) "Pi with no EVars is closed" true
    (closedExp (null_ctx, (pi, id_sub)))

let test_not_closed_evar () =
  let evar = EVar (ref None, null_ctx, Uni Type, ref []) in
  Alcotest.(check bool) "Uninstantiated EVar is not closed" false
    (closedExp (null_ctx, (evar, id_sub)))

let test_closed_instantiated_evar () =
  (* An instantiated EVar is transparent — closedExp follows the instantiation *)
  let evar_ref = ref (Some (Uni Type)) in
  let evar = EVar (evar_ref, null_ctx, Uni Type, ref []) in
  Alcotest.(check bool) "Instantiated EVar (= Uni Type) is closed" true
    (closedExp (null_ctx, (evar, id_sub)))

(* closedCtx: all declarations in the context must also be closed *)

let test_closed_ctx_null () =
  Alcotest.(check bool) "Null context is closed" true (closedCtx null_ctx)

let test_closed_ctx_with_type () =
  let ctx = Decl (null_ctx, Dec (None, Uni Type)) in
  Alcotest.(check bool) "Context with Uni Type decl is closed" true (closedCtx ctx)

let test_not_closed_ctx_with_evar () =
  let evar = EVar (ref None, null_ctx, Uni Type, ref []) in
  let ctx = Decl (null_ctx, Dec (None, evar)) in
  Alcotest.(check bool) "Context with EVar decl is not closed" false (closedCtx ctx)

(* collectEVars: gather all uninstantiated EVars in a term *)

let test_collect_no_evars () =
  let evars = collectEVars (null_ctx, (Uni Type, id_sub), []) in
  Alcotest.(check int) "Uni Type has no EVars" 0 (List.length evars)

let test_collect_one_evar () =
  let evar = EVar (ref None, null_ctx, Uni Type, ref []) in
  let evars = collectEVars (null_ctx, (evar, id_sub), []) in
  Alcotest.(check int) "one EVar collected" 1 (List.length evars)

let test_collect_dedup_evar () =
  (* The SAME EVar appearing twice should be collected only once *)
  let evar_ref = ref None in
  let evar = EVar (evar_ref, null_ctx, Uni Type, ref []) in
  let pi_with_dup = Pi ((Dec (None, evar), No), evar) in
  let evars = collectEVars (null_ctx, (pi_with_dup, id_sub), []) in
  Alcotest.(check int) "same EVar deduplicated" 1 (List.length evars)

let suites =
  [ ( "Abstract.closedExp"
    , [ Alcotest.test_case "Uni Type is closed" `Quick test_closed_uni_type
      ; Alcotest.test_case "Uni Kind is closed" `Quick test_closed_uni_kind
      ; Alcotest.test_case "Lam is closed" `Quick test_closed_lam
      ; Alcotest.test_case "Pi is closed" `Quick test_closed_pi
      ; Alcotest.test_case "EVar is not closed" `Quick test_not_closed_evar
      ; Alcotest.test_case "instantiated EVar is closed"
          `Quick test_closed_instantiated_evar
      ] )
  ; ( "Abstract.closedCtx"
    , [ Alcotest.test_case "Null ctx is closed" `Quick test_closed_ctx_null
      ; Alcotest.test_case "ctx with type decl is closed"
          `Quick test_closed_ctx_with_type
      ; Alcotest.test_case "ctx with EVar decl is not closed"
          `Quick test_not_closed_ctx_with_evar
      ] )
  ; ( "Abstract.collectEVars"
    , [ Alcotest.test_case "no EVars in Uni Type" `Quick test_collect_no_evars
      ; Alcotest.test_case "one EVar collected" `Quick test_collect_one_evar
      ; Alcotest.test_case "same EVar deduplicated" `Quick test_collect_dedup_evar
      ] )
  ]
