open! Basis

(** Unit tests targeting root causes of failing integration tests.

    The integration test failures fall into three categories:

    1. ctxLookup crash (Test 010 - cut_elim): Pattern match failure in
    IntSyn.ctxLookup when de Bruijn index exceeds context depth. Triggered
    during coverage checker's abstract + doubleCheck path.

    2. Approximate type matching (Test 008 - debruijn1): Apx.match_ raises
    "Type/kind expression clash" when approximate types have incompatible shapes
    during higher-order variable application reconstruction.

    3. Coverage missing cases (Tests 016, 021-024, 029-031): Coverage checker
    reports spurious "missing cases" involving parameter variables (#ovar). The
    splitting logic in cover_.ml (paramCases/constCases) may not enumerate all
    parameter variable instantiations correctly.

    These unit tests isolate each subsystem to pinpoint the exact failure
    conditions without needing full .elf file loading. *)

module I = Lambda.Lambda_.IntSyn
module Whnf = Lambda.Lambda_.Whnf
module Approx = Lambda.Lambda_.Approx
module Abstract = Lambda.Lambda_.Abstract
module ModernSyntax = Syntax.IntSyn (Global.Global_.Global)
module TestLexer = Lexer.Lexer
module TestParser = Parser.Make_Parser (struct
  type t = string
end) (TestLexer)

module Modern = Grammar__Modern.Make_Modern (ModernSyntax) (TestLexer) (TestParser)

(* ──────────────────────────────────────────────────────────────────── *)
(* Test helpers                                                        *)
(* ──────────────────────────────────────────────────────────────────── *)

(** Build a context of depth n with dummy Dec entries *)
let rec make_ctx n =
  if n <= 0 then I.Null
  else
    I.Decl (make_ctx (n - 1), I.Dec (Some ("x" ^ string_of_int n), I.Uni I.Type))

let modern_state () : Modern.state = { fixities = Hashtbl.create 8 }

let parse_modern parser input =
  let lexbuf = Modern.Lexer.of_string input in
  match Modern.Parser.run parser lexbuf (modern_state ()) with
  | Modern.Parser.Success (value, _, _), final_lexbuf
    when Modern.Lexer.get_offset final_lexbuf = String.size input -> value
  | Modern.Parser.Success (_, _, _), final_lexbuf ->
      Alcotest.fail
        (Printf.sprintf
           "parser left trailing input at offset %d in %S"
           (Modern.Lexer.get_offset final_lexbuf) input)
  | Modern.Parser.ParseError errors, _ ->
      let error_text =
        String.concatWith "; "
          (List.map (fun (msg, _pos) -> msg) errors)
      in
      Alcotest.fail ("parse failed for " ^ input ^ ": " ^ error_text)

let test_modern_name () =
  let result = parse_modern Modern.name "foo" in
  Alcotest.(check string) "name parses" "foo" result

let test_modern_name_rejects_wildcard () =
  let lexbuf = Modern.Lexer.of_string "_" in
  match Modern.Parser.run Modern.name lexbuf (modern_state ()) with
  | Modern.Parser.ParseError _, _ -> Alcotest.(check bool) "wildcard rejected" true true
  | Modern.Parser.Success (_, _, _), _ ->
      Alcotest.fail "underscore should not parse as a name"

let modern_parser_cases =
  [ Alcotest.test_case "name parser" `Quick test_modern_name
  ; Alcotest.test_case "wildcard rejection" `Quick test_modern_name_rejects_wildcard
  ]

(* ──────────────────────────────────────────────────────────────────── *)
(* 1. ctxLookup tests                                                  *)
(* ──────────────────────────────────────────────────────────────────── *)

let test_ctx_lookup_valid () =
  let ctx = make_ctx 3 in
  (* lookup index 1 = rightmost declaration *)
  let d = I.ctxLookup (ctx, 1) in
  (match d with
  | I.Dec (Some name, _) -> Alcotest.(check string) "rightmost decl" "x3" name
  | _ -> Alcotest.fail "unexpected declaration form");
  (* lookup index 3 = leftmost declaration *)
  let d = I.ctxLookup (ctx, 3) in
  match d with
  | I.Dec (Some name, _) -> Alcotest.(check string) "leftmost decl" "x1" name
  | _ -> Alcotest.fail "unexpected declaration form"

let test_ctx_lookup_out_of_bounds () =
  (* This is the exact crash from Test 010: ctxLookup reaches Null
     and raises Invalid_argument when the index exceeds the context depth.
     The coverage checker's abstract function can produce terms where
     de Bruijn indices exceed the context depth. *)
  let ctx = make_ctx 2 in
  let raised =
    try
      ignore (I.ctxLookup (ctx, 5));
      false
    with Invalid_argument _ -> true
  in
  Alcotest.(check bool) "out-of-bounds raises Invalid_argument" true raised

let test_ctx_lookup_null () =
  (* Looking up anything in Null context should fail.
     This happens when abstract produces a term with BVar(k)
     but the surrounding context is empty. *)
  let raised =
    try
      ignore (I.ctxLookup (I.Null, 1));
      false
    with Invalid_argument _ -> true
  in
  Alcotest.(check bool) "Null context raises Invalid_argument" true raised

let test_ctx_lookup_zero_index () =
  (* Index 0 is invalid (indices are 1-based). This should not
     silently succeed. *)
  let ctx = make_ctx 2 in
  let raised =
    try
      ignore (I.ctxLookup (ctx, 0));
      false
    with _ -> true
  in
  Alcotest.(check bool) "zero index is invalid" true raised

let test_ctx_length () =
  Alcotest.(check int) "empty ctx" 0 (I.ctxLength I.Null);
  Alcotest.(check int) "depth 1" 1 (I.ctxLength (make_ctx 1));
  Alcotest.(check int) "depth 5" 5 (I.ctxLength (make_ctx 5))

let ctx_lookup_cases =
  [
    Alcotest.test_case "valid lookups" `Quick test_ctx_lookup_valid;
    Alcotest.test_case "out-of-bounds crash" `Quick
      test_ctx_lookup_out_of_bounds;
    Alcotest.test_case "null context crash" `Quick test_ctx_lookup_null;
    Alcotest.test_case "zero index invalid" `Quick test_ctx_lookup_zero_index;
    Alcotest.test_case "ctxLength consistency" `Quick test_ctx_length;
  ]

(* ──────────────────────────────────────────────────────────────────── *)
(* 2. Approximate type matching tests                                  *)
(* ──────────────────────────────────────────────────────────────────── *)

let test_apx_match_same_const () =
  (* Matching identical constants should succeed *)
  let h = I.Const 42 in
  try
    Approx.match_ (Approx.Const h, Approx.Const h);
    Alcotest.(check pass) "same const matches" () ()
  with Approx.Unify msg ->
    Alcotest.fail ("should match identical consts: " ^ msg)

let test_apx_match_different_const () =
  (* Matching different non-Def constants should fail *)
  let raised =
    try
      Approx.match_ (Approx.Const (I.Const 1), Approx.Const (I.Const 2));
      false
    with Approx.Unify _ -> true
  in
  Alcotest.(check bool) "different consts clash" true raised

let test_apx_match_arrow_vs_const () =
  (* Arrow vs non-Def Const: this is the "Type/kind expression clash"
     from Test 008. When a higher-order variable is applied,
     its approximate type may be Arrow while the expected type is Const. *)
  let arrow = Approx.Arrow (Approx.Uni Approx.type_, Approx.Uni Approx.type_) in
  let konst = Approx.Const (I.Const 1) in
  let raised =
    try
      Approx.match_ (arrow, konst);
      false
    with Approx.Unify msg ->
      Alcotest.(check string) "clash message" "Type/kind expression clash" msg;
      true
  in
  Alcotest.(check bool) "arrow vs const clashes" true raised

let test_apx_match_cvar_unifies () =
  (* CVar should unify with any concrete type *)
  let r = ref None in
  let target = Approx.Uni Approx.type_ in
  Approx.match_ (Approx.CVar r, target);
  match !r with
  | Some v ->
      Alcotest.(check bool) "CVar bound" true (Approx.equal_exp v target)
  | None -> Alcotest.fail "CVar should be instantiated"

let test_apx_match_arrow_structural () =
  (* Arrow matching should unify both domain and codomain *)
  let r1 = ref None in
  let r2 = ref None in
  let lhs = Approx.Arrow (Approx.CVar r1, Approx.CVar r2) in
  let rhs = Approx.Arrow (Approx.Uni Approx.type_, Approx.Uni Approx.kind) in
  Approx.match_ (lhs, rhs);
  Alcotest.(check bool) "domain bound" true (Option.isSome !r1);
  Alcotest.(check bool) "codomain bound" true (Option.isSome !r2)

let test_apx_match_undefined_clash () =
  (* Undefined is used for variables whose type can't be approximated.
     Matching Undefined against a concrete type should fail. *)
  let raised =
    try
      Approx.match_ (Approx.Undefined, Approx.Uni Approx.type_);
      false
    with Approx.Unify _ -> true
  in
  Alcotest.(check bool) "Undefined vs Uni clashes" true raised

let apx_match_cases =
  [
    Alcotest.test_case "same constant" `Quick test_apx_match_same_const;
    Alcotest.test_case "different constants" `Quick
      test_apx_match_different_const;
    Alcotest.test_case "arrow vs const clash" `Quick
      test_apx_match_arrow_vs_const;
    Alcotest.test_case "CVar unification" `Quick test_apx_match_cvar_unifies;
    Alcotest.test_case "arrow structural" `Quick test_apx_match_arrow_structural;
    Alcotest.test_case "Undefined clash" `Quick test_apx_match_undefined_clash;
  ]

(* ──────────────────────────────────────────────────────────────────── *)
(* 3. Whnf normalization of EClo/EVar                                  *)
(* ──────────────────────────────────────────────────────────────────── *)

let test_whnf_eclo_bvar () =
  (* EClo(BVar(1), Shift(2)) should reduce to BVar(3) under whnf.
     Whnf returns (exp, sub) pair — the result may carry a substitution. *)
  let term = I.Root (I.BVar 1, I.Nil) in
  (* Apply substitution via normalize which fully reduces *)
  let result = Whnf.normalize (term, I.Shift 2) in
  match result with
  | I.Root (I.BVar 3, I.Nil) -> Alcotest.(check pass) "shifted correctly" () ()
  | I.Root (I.BVar k, _) ->
      Alcotest.fail (Printf.sprintf "wrong index: expected 3, got %d" k)
  | other ->
      Alcotest.fail (Printf.sprintf "unexpected form: %s" (I.show_exp other))

let test_whnf_evar_uninstantiated () =
  (* An uninstantiated EVar under EClo should remain as EVar in whnf *)
  let r = ref None in
  let constraints = ref [] in
  let evar = I.EVar (r, I.Null, I.Uni I.Type, constraints) in
  let eclo = I.EClo (evar, I.Shift 0) in
  let result, _ = Whnf.whnf (eclo, I.Shift 0) in
  match result with
  | I.EVar ({ contents = None }, _, _, _) ->
      Alcotest.(check pass) "EVar stays uninstantiated" () ()
  | _ -> Alcotest.fail "expected uninstantiated EVar after whnf"

let test_whnf_evar_instantiated () =
  (* An instantiated EVar should reduce to its value under whnf *)
  let inner = I.Root (I.BVar 1, I.Nil) in
  let r = ref (Some inner) in
  let constraints = ref [] in
  let evar = I.EVar (r, I.Null, I.Uni I.Type, constraints) in
  let result, _ = Whnf.whnf (evar, I.Shift 0) in
  match result with
  | I.Root (I.BVar 1, _) -> Alcotest.(check pass) "EVar reduced" () ()
  | _ -> Alcotest.fail "instantiated EVar should reduce to its value"

let test_normalize_identity () =
  (* normalize (U, id) where U is already normal should return U *)
  let term = I.Uni I.Type in
  let result = Whnf.normalize (term, I.id) in
  Alcotest.(check bool)
    "Uni Type normalizes to itself" true
    (I.equal_exp result (I.Uni I.Type))

let whnf_cases =
  [
    Alcotest.test_case "EClo BVar shift" `Quick test_whnf_eclo_bvar;
    Alcotest.test_case "uninstantiated EVar" `Quick
      test_whnf_evar_uninstantiated;
    Alcotest.test_case "instantiated EVar" `Quick test_whnf_evar_instantiated;
    Alcotest.test_case "normalize identity" `Quick test_normalize_identity;
  ]

(* ──────────────────────────────────────────────────────────────────── *)
(* 4. Abstract (coverage checker path)                                 *)
(* ──────────────────────────────────────────────────────────────────── *)

let test_abstract_simple_type () =
  (* Abstract a simple closed type: should succeed with i=0 (no free vars) *)
  let term = I.Uni I.Type in
  let i, result = Abstract.abstractDecImp term in
  Alcotest.(check int) "no implicit vars" 0 i;
  Alcotest.(check bool)
    "result is Uni Type" true
    (I.equal_exp result (I.Uni I.Type))

let test_abstract_with_evar () =
  (* Abstract a type containing an uninstantiated EVar.
     The EVar should be abstracted into a Pi binding.
     This exercises the same path that crashes in Test 010. *)
  let r = ref None in
  let constraints = ref [] in
  let evar_type = I.Uni I.Type in
  let evar = I.EVar (r, I.Null, evar_type, constraints) in
  (* Create a type: EVar -> type *)
  let term = I.Root (I.BVar 1, I.App (evar, I.Nil)) in
  (* This may raise; we want to observe whether it does *)
  let result =
    try
      let i, v = Abstract.abstractDecImp term in
      `Ok (i, v)
    with
    | Match_failure _ -> `MatchFailure
    | exn -> `Exn (Printexc.to_string exn)
  in
  match result with
  | `Ok (i, _) -> Alcotest.(check bool) "abstracted some vars" true (i >= 0)
  | `MatchFailure ->
      (* This is the bug: abstract produced a term with invalid indices *)
      Alcotest.fail
        "abstractDecImp raised Match_failure — likely invalid de Bruijn index"
  | `Exn msg -> Alcotest.fail ("abstractDecImp raised: " ^ msg)

let abstract_cases =
  [
    Alcotest.test_case "simple closed type" `Quick test_abstract_simple_type;
    Alcotest.test_case "type with EVar" `Quick test_abstract_with_evar;
  ]

(* ──────────────────────────────────────────────────────────────────── *)
(* 5. Coverage checker integration (mini end-to-end)                   *)
(* ──────────────────────────────────────────────────────────────────── *)

(** These tests load minimal .cfg/.elf files through the Stelf frontend,
    isolating the specific phases that fail. *)

let () = Printexc.record_backtrace true
let _ = Frontend.Frontend_.Stelf.chatter := 0

(** Run Stelf.make on a file and return whether it succeeded *)
let twelf_make ?(unsafe = false) file =
  let prev_unsafe = !Frontend.Frontend_.Stelf.unsafe in
  Frontend.Frontend_.Stelf.unsafe := unsafe;
  let result =
    try
      match Frontend.Frontend_.Stelf.make file with
      | Frontend.Frontend_.Stelf.Ok -> `Ok
      | Frontend.Frontend_.Stelf.Abort -> `Abort
    with exn -> `Exn exn
  in
  Frontend.Frontend_.Stelf.unsafe := prev_unsafe;
  result

let test_debruijn1_no_doublecheck () =
  (* After fixing trans.elf (removing explicit {E : exp -> exp} quantification),
     debruijn1/test.cfg now passes without doubleCheck. *)
  Frontend.Frontend_.Stelf.doubleCheck := false;
  let result = twelf_make "examples/compile/debruijn1/test.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "debruijn1 passes without doubleCheck" () ()
  | `Abort -> Alcotest.fail "debruijn1 should pass without doubleCheck"
  | `Exn exn ->
      Alcotest.fail
        ("unexpected exception: " ^ Printexc.to_string exn ^ "\n"
       ^ Printexc.get_backtrace ())

let test_cut_elim_no_doublecheck () =
  (* Test 010 passes without doubleCheck but fails with it.
     This confirms the bug is in the doubleCheck validation path,
     not in the core coverage algorithm. *)
  Frontend.Frontend_.Stelf.doubleCheck := false;
  let result = twelf_make "examples/cut_elim/test.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "cut_elim passes without doubleCheck" () ()
  | `Abort -> Alcotest.fail "cut_elim should pass without doubleCheck"
  | `Exn exn ->
      Alcotest.fail
        ("unexpected exception: " ^ Printexc.to_string exn ^ "\n"
       ^ Printexc.get_backtrace ())

let test_cut_elim_with_doublecheck () =
  (* cut_elim now passes with doubleCheck — the abstract function
     gracefully handles type-check failures from coverage splitting. *)
  Frontend.Frontend_.Stelf.doubleCheck := true;
  let result = twelf_make "examples/cut_elim/test.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "cut_elim passes with doubleCheck" () ()
  | `Abort -> Alcotest.fail "cut_elim should pass with doubleCheck"
  | `Exn exn -> Alcotest.fail ("unexpected exception: " ^ Printexc.to_string exn)

let test_lp_coverage_no_doublecheck () =
  (* Test 016 (lp with unsafe) passes without doubleCheck.
     This confirms the core logic works. *)
  Frontend.Frontend_.Stelf.doubleCheck := false;
  let result = twelf_make ~unsafe:true "examples/lp/test.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "lp passes without doubleCheck" () ()
  | `Abort -> Alcotest.fail "lp should pass without doubleCheck"
  | `Exn exn ->
      Alcotest.fail
        ("unexpected exception: " ^ Printexc.to_string exn ^ "\n"
       ^ Printexc.get_backtrace ())

let test_lp_coverage_with_doublecheck () =
  (* lp now passes with doubleCheck — the abstract function
     gracefully handles type-check failures from coverage splitting. *)
  Frontend.Frontend_.Stelf.doubleCheck := true;
  let result = twelf_make ~unsafe:true "examples/lp/test.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "lp passes with doubleCheck" () ()
  | `Abort -> Alcotest.fail "lp should pass with doubleCheck"
  | `Exn exn -> Alcotest.fail ("unexpected exception: " ^ Printexc.to_string exn)

let test_crary_explicit_coverage () =
  (* Tests 021/022 fail with coverage errors in explicit context examples.
     These are the simplest of the coverage failures. *)
  Frontend.Frontend_.Stelf.doubleCheck := false;
  let result = twelf_make "examples/crary/explicit/excon.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "crary/explicit passes coverage" () ()
  | `Abort -> Alcotest.fail "crary/explicit should pass coverage"
  | `Exn exn ->
      Alcotest.fail
        ("unexpected exception: " ^ Printexc.to_string exn ^ "\n"
       ^ Printexc.get_backtrace ())

(* ──────────────────────────────────────────────────────────────────── *)
(* 5b. map-eval.elf type mismatch isolation                            *)
(* ──────────────────────────────────────────────────────────────────── *)

(** These tests isolate the two type mismatch errors in map-eval.elf:
    - Line 8 (mp_1): tr_lam C2 inside tr_1's argument has incompatible type.
      Expected: trans K2 (lam' F2) (lam ([e:exp] E1 e)) Inferred: trans K1 (lam'
      F1) (lam ([e:exp] `C2 e)) → "Type/kind expression clash"
    - Line 9: same tr_lam C2 in the vtr_lam argument triggers the same clash.
      Both errors stem from approximate type matching during reconstruction of
      higher-order pattern variables (C2) in tr_lam applications. *)

let twelf_load_file file =
  try
    match Frontend.Frontend_.Stelf.loadFile file with
    | Frontend.Frontend_.Stelf.Ok -> `Ok
    | Frontend.Frontend_.Stelf.Abort -> `Abort
  with exn -> `Exn exn

let test_debruijn1_prereqs_ok () =
  (* The prerequisite files (mini-ml, debruijn, trans, feval, eval)
     should all load successfully. This isolates the failure to map-eval.elf. *)
  Frontend.Frontend_.Stelf.doubleCheck := false;
  let result = twelf_make "examples/compile/debruijn1/prereqs.cfg" in
  match result with
  | `Ok -> Alcotest.(check pass) "prereqs load OK" () ()
  | `Abort -> Alcotest.fail "prerequisite files should load without error"
  | `Exn exn ->
      Alcotest.fail
        ("unexpected exception: " ^ Printexc.to_string exn ^ "\n"
       ^ Printexc.get_backtrace ())

let test_map_eval_type_mismatch () =
  (* After fixing trans.elf (removing explicit {E : exp -> exp} quantification
     from tr_lam), map-eval.elf now loads successfully.
     Load prerequisites, then load map-eval.elf separately. *)
  Frontend.Frontend_.Stelf.doubleCheck := false;
  (* First load prerequisites via make (which resets) *)
  let prereq_result = twelf_make "examples/compile/debruijn1/prereqs.cfg" in
  (match prereq_result with
  | `Ok -> ()
  | _ -> Alcotest.fail "prereqs must load before testing map-eval.elf");
  (* Now load map-eval.elf on top of the existing signature *)
  let result = twelf_load_file "examples/compile/debruijn1/map-eval.elf" in
  match result with
  | `Ok -> Alcotest.(check pass) "map-eval.elf loads successfully" () ()
  | `Abort ->
      Alcotest.fail "map-eval.elf should load successfully after trans.elf fix"
  | `Exn exn ->
      Alcotest.fail
        ("unexpected exception: " ^ Printexc.to_string exn ^ "\n"
       ^ Printexc.get_backtrace ())

let test_map_eval_mp1_type_clash () =
  (* The mp_1 declaration uses tr_lam C2 in two places:
       (tr_1 (vtr_lam (tr_lam C2)))  -- argument to tr_1
       (vtr_lam (tr_lam C2))         -- result vtrans
     The reconstruction of C2 via Approx.match_ encounters:
       Arrow (from tr_lam's Pi-type) vs Const (expected simple type)
     This is the "Type/kind expression clash" error.
     Test that the approximate type system correctly rejects this. *)
  let arrow = Approx.Arrow (Approx.Uni Approx.type_, Approx.Uni Approx.type_) in
  let konst = Approx.Const (I.Const 1) in
  (* Arrow vs non-Def Const must raise Unify with the specific message *)
  let raised_msg =
    try
      Approx.match_ (arrow, konst);
      None
    with Approx.Unify msg -> Some msg
  in
  match raised_msg with
  | Some msg ->
      Alcotest.(check string)
        "clash message matches error from mp_1" "Type/kind expression clash" msg
  | None ->
      Alcotest.fail
        "Arrow vs Const should raise Unify (this is the mp_1 root cause)"

let test_map_eval_nested_tr_lam_clash () =
  (* Simulate the nested tr_lam scenario: tr_lam expects its argument C
     to have type ({w:val}{x:exp} vtrans w x -> trans (K;w) F (E x)),
     which is approximated as Arrow(..., Arrow(..., Arrow(..., Const(trans)))).
     But when C2 is shared between tr_1 and vtr_lam contexts, the
     inferred approximate type (Arrow) clashes with the expected type
     (Const) in the second occurrence. *)
  let r = ref None in
  let cvar = Approx.CVar r in
  let uni_t = Approx.Uni Approx.type_ in
  (* First match: CVar against an Arrow (simulating tr_lam's Pi-type) *)
  let arrow = Approx.Arrow (uni_t, Approx.Arrow (uni_t, uni_t)) in
  Approx.match_ (cvar, arrow);
  (* CVar is now bound to Arrow *)
  Alcotest.(check bool) "CVar bound after first match" true (Option.isSome !r);
  (* Second match: the bound CVar (Arrow) against a Const —
     this is what happens when the same C2 is used in vtr_lam context *)
  let konst = Approx.Const (I.Const 1) in
  let raised =
    try
      Approx.match_ (Approx.CVar r, konst);
      false
    with Approx.Unify _ -> true
  in
  Alcotest.(check bool)
    "bound CVar (Arrow) vs Const clashes (mp_1 second occurrence)" true raised

let map_eval_cases =
  [
    Alcotest.test_case "debruijn1 prereqs load OK" `Quick
      test_debruijn1_prereqs_ok;
    Alcotest.test_case "map-eval.elf loads after trans.elf fix" `Quick
      test_map_eval_type_mismatch;
    Alcotest.test_case "mp_1 Arrow vs Const clash" `Quick
      test_map_eval_mp1_type_clash;
    Alcotest.test_case "mp_1 nested tr_lam shared CVar clash" `Quick
      test_map_eval_nested_tr_lam_clash;
  ]

let coverage_cases =
  [
    Alcotest.test_case "debruijn1 passes (no doubleCheck)" `Quick
      test_debruijn1_no_doublecheck;
    Alcotest.test_case "cut_elim without doubleCheck" `Quick
      test_cut_elim_no_doublecheck;
    Alcotest.test_case "cut_elim with doubleCheck (ctxLookup crash)" `Quick
      test_cut_elim_with_doublecheck;
    Alcotest.test_case "lp without doubleCheck (unsafe)" `Quick
      test_lp_coverage_no_doublecheck;
    Alcotest.test_case "lp with doubleCheck (unsafe)" `Quick
      test_lp_coverage_with_doublecheck;
    Alcotest.test_case "crary explicit coverage" `Quick
      test_crary_explicit_coverage;
  ]

(* ──────────────────────────────────────────────────────────────────── *)
(* Exported test suite                                                 *)
(* ──────────────────────────────────────────────────────────────────── *)

let unit_cases =
  [
    ("modern parser", modern_parser_cases);
    ("ctxLookup", ctx_lookup_cases);
    ("approx matching", apx_match_cases);
    ("whnf normalization", whnf_cases);
    ("abstract", abstract_cases);
    ("map-eval type mismatch", map_eval_cases);
    ("coverage integration", coverage_cases);
  ]
