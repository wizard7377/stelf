open Intsyn.IntSyn
open IntSynHelpers

(* Use the trailed version of Unify so backtracking tests work. *)
module U = Intsyn.Lambda_.UnifyTrail

(* Helper: assert that unify raises Unify exception *)
let check_unify_fails lbl ctx lhs rhs =
  match U.unify (ctx, lhs, rhs) with
  | exception U.Unify _ -> ()
  | () -> Alcotest.failf "%s: expected Unify exception but unify succeeded" lbl

(* Helper: fresh EVar of type `Uni Type` in empty context *)
let fresh_evar () =
  let r = ref None in
  (r, EVar (r, null_ctx, Uni Type, ref []))

(* ── Ground term unification ──────────────────────── *)

let test_unify_uni_refl () =
  U.reset ();
  U.unify (null_ctx, (Uni Type, id_sub), (Uni Type, id_sub))

let test_unify_kind_refl () =
  U.reset ();
  U.unify (null_ctx, (Uni Kind, id_sub), (Uni Kind, id_sub))

let test_unify_bvar_clash () =
  (* BVar indices that don't match cause a "Bound variable clash" *)
  U.reset ();
  check_unify_fails "BVar 1 ≢ BVar 2" null_ctx
    (Root (BVar 1, Nil), id_sub)
    (Root (BVar 2, Nil), id_sub)

let test_unify_lam_refl () =
  U.reset ();
  let lam = lam_ (Uni Type) (bvar 1) in
  U.unify (null_ctx, (lam, id_sub), (lam, id_sub))

(* ── EVar instantiation ───────────────────────────── *)

let test_unify_evar_assigns () =
  U.reset ();
  let r, x = fresh_evar () in
  U.unify (null_ctx, (x, id_sub), (Uni Type, id_sub));
  Alcotest.(check bool) "EVar is instantiated after unify" true (!r <> None)

let test_unify_evar_value () =
  U.reset ();
  let r, x = fresh_evar () in
  U.unify (null_ctx, (x, id_sub), (Uni Type, id_sub));
  match !r with
  | None -> Alcotest.fail "EVar not instantiated"
  | Some v ->
      Alcotest.(check bool) "EVar assigned to Uni Type" true (v = Uni Type)

let test_unify_two_evars () =
  U.reset ();
  let r1, x1 = fresh_evar () in
  let r2, x2 = fresh_evar () in
  U.unify (null_ctx, (x1, id_sub), (x2, id_sub));
  (* at least one of them must be assigned (or they're unified via sharing) *)
  Alcotest.(check bool)
    "at least one EVar is assigned" true
    (!r1 <> None || !r2 <> None)

(* ── Backtracking ─────────────────────────────────── *)

let test_unify_backtrack_evar () =
  U.reset ();
  let r, x = fresh_evar () in
  U.mark ();
  U.unify (null_ctx, (x, id_sub), (Uni Type, id_sub));
  let () =
    Alcotest.(check bool) "EVar assigned before unwind" true (!r <> None)
  in
  U.unwind ();
  Alcotest.(check bool) "EVar reset after unwind" true (!r = None)

let test_unify_backtrack_two_evars () =
  U.reset ();
  let r1, x1 = fresh_evar () in
  let r2, x2 = fresh_evar () in
  U.mark ();
  U.unify (null_ctx, (x1, id_sub), (Uni Type, id_sub));
  U.unify (null_ctx, (x2, id_sub), (Uni Kind, id_sub));
  U.unwind ();
  Alcotest.(check bool)
    "both EVars reset after unwind" true
    (!r1 = None && !r2 = None)

let test_unify_backtrack_preserves_earlier () =
  (* Assignments BEFORE mark survive unwind; those AFTER do not. *)
  U.reset ();
  let r1, x1 = fresh_evar () in
  let r2, x2 = fresh_evar () in
  U.unify (null_ctx, (x1, id_sub), (Uni Type, id_sub));
  U.mark ();
  U.unify (null_ctx, (x2, id_sub), (Uni Kind, id_sub));
  U.unwind ();
  Alcotest.(check bool) "x1 (before mark) still assigned" true (!r1 <> None);
  Alcotest.(check bool) "x2 (after mark) reset" true (!r2 = None)

(* ── unifiable predicate ──────────────────────────── *)

let test_unifiable_true () =
  U.reset ();
  let _, x = fresh_evar () in
  Alcotest.(check bool)
    "EVar unifiable with Uni Type" true
    (U.unifiable (null_ctx, (x, id_sub), (Uni Type, id_sub)))

let test_unifiable_false () =
  (* BVar with different indices are not unifiable *)
  U.reset ();
  Alcotest.(check bool)
    "BVar 1 not unifiable with BVar 2" false
    (U.unifiable
       (null_ctx, (Root (BVar 1, Nil), id_sub), (Root (BVar 2, Nil), id_sub)))

let suites =
  [
    ( "Unify (ground)",
      [
        Alcotest.test_case "Uni Type ≡ Uni Type" `Quick test_unify_uni_refl;
        Alcotest.test_case "Uni Kind ≡ Uni Kind" `Quick test_unify_kind_refl;
        Alcotest.test_case "BVar 1 ≢ BVar 2 raises" `Quick test_unify_bvar_clash;
        Alcotest.test_case "Lam ≡ Lam" `Quick test_unify_lam_refl;
      ] );
    ( "Unify (EVar instantiation)",
      [
        Alcotest.test_case "EVar is assigned" `Quick test_unify_evar_assigns;
        Alcotest.test_case "EVar assigned correct value" `Quick
          test_unify_evar_value;
        Alcotest.test_case "two EVars unified" `Quick test_unify_two_evars;
      ] );
    ( "Unify (backtracking)",
      [
        Alcotest.test_case "unwind resets one EVar" `Quick
          test_unify_backtrack_evar;
        Alcotest.test_case "unwind resets two EVars" `Quick
          test_unify_backtrack_two_evars;
        Alcotest.test_case "pre-mark assignments survive unwind" `Quick
          test_unify_backtrack_preserves_earlier;
      ] );
    ( "Unify.unifiable",
      [
        Alcotest.test_case "EVar unifiable with type" `Quick test_unifiable_true;
        Alcotest.test_case "BVar 1 and BVar 2 not unifiable" `Quick
          test_unifiable_false;
      ] );
  ]
