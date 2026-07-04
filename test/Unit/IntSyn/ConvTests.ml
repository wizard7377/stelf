open Intsyn.IntSyn
open Intsyn.Lambda_.Conv
open IntSynHelpers

(* Conv checks definitional equality (β/η) via whnf internally.
   Tests use only closed terms with no defined constants so no
   global signature is needed. *)

(* ── Universe equality ────────────────────────────── *)

let test_conv_type_refl () =
  let t = (Uni Type, id_sub) in
  Alcotest.(check bool) "Type ≡ Type" true (conv (t, t))

let test_conv_kind_refl () =
  let k = (Uni Kind, id_sub) in
  Alcotest.(check bool) "Kind ≡ Kind" true (conv (k, k))

let test_conv_type_ne_kind () =
  Alcotest.(check bool) "Type ≢ Kind" false
    (conv ((Uni Type, id_sub), (Uni Kind, id_sub)))

(* ── Lambda equality ──────────────────────────────── *)

let test_conv_lam_refl () =
  let lam = (lam_ (Uni Type) (bvar 1), id_sub) in
  Alcotest.(check bool) "λx:type.x ≡ λx:type.x (reflexive)" true (conv (lam, lam))

let test_conv_lam_body_matters () =
  (* λx:type.x vs λx:type.type — bodies differ *)
  let lam1 = (lam_ (Uni Type) (bvar 1), id_sub) in
  let lam2 = (lam_ (Uni Type) (Uni Type), id_sub) in
  Alcotest.(check bool) "λx.x ≢ λx.type" false (conv (lam1, lam2))

(* ── Pi equality ──────────────────────────────────── *)

let test_conv_pi_refl () =
  let pi = (Pi ((Dec (None, Uni Type), No), Uni Type), id_sub) in
  Alcotest.(check bool) "Pi(type, type) ≡ itself" true (conv (pi, pi))

let test_conv_pi_domain_matters () =
  let pi1 = (Pi ((Dec (None, Uni Type), No), Uni Type), id_sub) in
  let pi2 = (Pi ((Dec (None, Uni Kind), No), Uni Type), id_sub) in
  Alcotest.(check bool) "Pi domains differ" false (conv (pi1, pi2))

(* ── Substitution equality ────────────────────────── *)

let test_conv_sub_id () =
  (* identity substitution in two syntactic forms should be equal modulo comp *)
  Alcotest.(check bool) "id ≡ id" true (convSub (Shift 0, Shift 0))

let test_conv_sub_different_idx () =
  (* Dot fronts with different Idx values are not equal *)
  Alcotest.(check bool) "Dot(Idx 1, ..) ≢ Dot(Idx 2, ..)" false
    (convSub (Dot (Idx 1, Shift 0), Dot (Idx 2, Shift 0)))

let suites =
  [ ( "Conv.conv (universes)"
    , [ Alcotest.test_case "Type ≡ Type" `Quick test_conv_type_refl
      ; Alcotest.test_case "Kind ≡ Kind" `Quick test_conv_kind_refl
      ; Alcotest.test_case "Type ≢ Kind" `Quick test_conv_type_ne_kind
      ] )
  ; ( "Conv.conv (lambdas)"
    , [ Alcotest.test_case "Lam reflexive" `Quick test_conv_lam_refl
      ; Alcotest.test_case "Lam body matters" `Quick test_conv_lam_body_matters
      ] )
  ; ( "Conv.conv (pi types)"
    , [ Alcotest.test_case "Pi reflexive" `Quick test_conv_pi_refl
      ; Alcotest.test_case "Pi domain matters" `Quick test_conv_pi_domain_matters
      ] )
  ; ( "Conv.convSub"
    , [ Alcotest.test_case "id ≡ id" `Quick test_conv_sub_id
      ; Alcotest.test_case "Dot(Idx 1) ≢ Dot(Idx 2)" `Quick test_conv_sub_different_idx
      ] )
  ]
