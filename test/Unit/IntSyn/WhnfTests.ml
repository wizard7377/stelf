open Intsyn.IntSyn
open Intsyn.Lambda_.Whnf
open IntSynHelpers

(* ── isId ─────────────────────────────────────────── *)

let test_isId_shift0 () =
  Alcotest.(check bool) "Shift 0 is identity" true (isId (Shift 0))

let test_isId_shift1 () =
  Alcotest.(check bool) "Shift 1 is not identity (weakening)" false (isId (Shift 1))

let test_isId_shift_n () =
  Alcotest.(check bool) "Shift 5 is not identity" false (isId (Shift 5))

(* ── isPatSub ─────────────────────────────────────── *)

let test_isPatSub_shift () =
  Alcotest.(check bool) "Shift k is always a pattern substitution" true
    (isPatSub (Shift 3))

let test_isPatSub_idx () =
  (* Dot(Idx 1, Shift 1): variable 1 maps to 1, rest shift by 1 *)
  Alcotest.(check bool) "Dot(Idx n, Shift k) is pattern sub (n ≤ k)" true
    (isPatSub (Dot (Idx 1, Shift 1)))

let test_isPatSub_exp_front () =
  (* Exp front makes it non-pattern *)
  Alcotest.(check bool) "Dot(Exp _, _) is not a pattern substitution" false
    (isPatSub (Dot (Exp (bvar 1), Shift 0)))

let test_isPatSub_undef () =
  (* Undef front is allowed in pattern subs *)
  Alcotest.(check bool) "Dot(Undef, Shift 0) is a pattern substitution" true
    (isPatSub (Dot (Undef, Shift 0)))

(* ── whnf on values ───────────────────────────────── *)

(* Universes, Pi, and Lam are values — whnf returns them unchanged *)

let test_whnf_uni_type () =
  let result = whnf (Uni Type, id_sub) in
  Alcotest.(check bool) "whnf(Uni Type) returns Uni Type" true
    (fst result = Uni Type)

let test_whnf_uni_kind () =
  let result = whnf (Uni Kind, id_sub) in
  Alcotest.(check bool) "whnf(Uni Kind) returns Uni Kind" true
    (fst result = Uni Kind)

let test_whnf_lam_is_value () =
  let body = bvar 1 in
  let lam = lam_ (Uni Type) body in
  let (u', _) = whnf (lam, id_sub) in
  Alcotest.(check bool) "whnf(Lam) is a value (not reduced)" true
    (match u' with Lam _ -> true | _ -> false)

(* ── normalize ────────────────────────────────────── *)

let test_normalize_uni () =
  let result = normalize (Uni Type, id_sub) in
  Alcotest.(check exp_testable) "normalize(Uni Type) = Uni Type" (Uni Type) result

let test_normalize_lam () =
  let lam = lam_ (Uni Type) (bvar 1) in
  let result = normalize (lam, id_sub) in
  Alcotest.(check bool) "normalize(Lam) preserves Lam structure" true
    (match result with Lam _ -> true | _ -> false)

let test_normalize_pi () =
  let pi_t = Pi ((Dec (None, Uni Type), No), Uni Type) in
  let result = normalize (pi_t, id_sub) in
  Alcotest.(check bool) "normalize(Pi) preserves Pi structure" true
    (match result with Pi _ -> true | _ -> false)

let suites =
  [ ( "Whnf.isId"
    , [ Alcotest.test_case "Shift 0 is identity" `Quick test_isId_shift0
      ; Alcotest.test_case "Shift 1 not identity" `Quick test_isId_shift1
      ; Alcotest.test_case "Shift n not identity" `Quick test_isId_shift_n
      ] )
  ; ( "Whnf.isPatSub"
    , [ Alcotest.test_case "Shift k is pattern" `Quick test_isPatSub_shift
      ; Alcotest.test_case "Dot(Idx, Shift) is pattern" `Quick test_isPatSub_idx
      ; Alcotest.test_case "Dot(Exp, _) not pattern" `Quick test_isPatSub_exp_front
      ; Alcotest.test_case "Dot(Undef, _) is pattern" `Quick test_isPatSub_undef
      ] )
  ; ( "Whnf.whnf"
    , [ Alcotest.test_case "Uni Type is value" `Quick test_whnf_uni_type
      ; Alcotest.test_case "Uni Kind is value" `Quick test_whnf_uni_kind
      ; Alcotest.test_case "Lam is value" `Quick test_whnf_lam_is_value
      ] )
  ; ( "Whnf.normalize"
    , [ Alcotest.test_case "normalize Uni Type" `Quick test_normalize_uni
      ; Alcotest.test_case "normalize Lam" `Quick test_normalize_lam
      ; Alcotest.test_case "normalize Pi" `Quick test_normalize_pi
      ] )
  ]
