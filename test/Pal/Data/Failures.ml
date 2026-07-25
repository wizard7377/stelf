(* handbook/fol.elf: first-order logic from Frank Pfenning's Handbook chapter.
   Identical in structure to the existing FOL suite (i/o/imp/not/forall/nd/hil/ded).
   SKIPPED: By the time this runs, `o` has been re-declared as a term (not a sort)
   by the CRARY-EXCON group (%term o tp). Attempting to use `o` as a type causes
   "Level clash: Argument type did not match function domain type".
   Placeholder kept so the test entry can reference it. *)
let handbook_sources_1 = {| (* placeholder: o pollution from CRARY-EXCON *) |}

(* failure/fail.elf: only a %query declaration which is not supported in STELF.
   Expected to raise a parse error. Translating %sort void then the %query itself
   as a raw string — the %query will fail. *)
let failure_sources_1 = {|
%sort void
%query 1 1 void
|}

(* wiki_failures/coverage_error.elf: intentionally incomplete coverage proof.
   Defines sub (subtyping) with sub-trans missing the arrow base case.
   %total on sub-trans should trigger a coverage failure in STELF. *)
let wiki_failures_coverage_error_1 =
  {|
%sort wf_tp
%term wf_int wf_tp
%term wf_float wf_tp
%term wf_arrow {_ wf_tp} {_ wf_tp} wf_tp
%sort wf_sub {_ wf_tp} {_ wf_tp}
%term wf_sub_ii wf_sub wf_int wf_int
%term wf_sub_ff wf_sub wf_float wf_float
%term wf_sub_if wf_sub wf_int wf_float
%term wf_sub_arrow {{T S T' S'}} {_ wf_sub T' T} {_ wf_sub S S'} wf_sub (wf_arrow T S) (wf_arrow T' S')
%sort wf_sub_trans {_ wf_tp} {_ wf_tp} {_ wf_tp}
%mode wf_sub_trans %in %in %out
%term wf_sub_trans_refl {{T}} {D wf_sub T T} wf_sub_trans T T T
%term wf_sub_trans_ii_if wf_sub_trans wf_int wf_float wf_float
%term wf_sub_trans_if_ff wf_sub_trans wf_int wf_float wf_float
%worlds () (wf_sub_trans _ _ _)
%total D (wf_sub_trans D _ _)
|}

(* wiki_failures/mode_error.elf: relation with a mode violation.
   plus is defined correctly but bad uses output N2 in input position.
   %mode or %total check should fail. *)
let wiki_failures_mode_error_1 =
  {|
%sort wfm_nat
%term wfm_z wfm_nat
%term wfm_s {_ wfm_nat} wfm_nat
%sort wfm_plus {_ wfm_nat} {_ wfm_nat} {_ wfm_nat}
%mode wfm_plus %in %in %out
%term wfm_plus_z {N wfm_nat} wfm_plus wfm_z N N
%term wfm_plus_s {{N1 N2 N3}} {_ wfm_plus N1 N2 N3} wfm_plus (wfm_s N1) N2 (wfm_s N3)
%worlds () (wfm_plus _ _ _)
%total N (wfm_plus N _ _)
%sort wfm_bad {_ wfm_nat} {_ wfm_nat}
%mode wfm_bad %in %out
%term wfm_bad_case {{N1 N2}} {_ wfm_plus N1 N2 N1} wfm_bad N1 N2
%worlds () (wfm_bad _ _)
%total N (wfm_bad N _)
|}

(* wiki_failures/totality_error.elf: relation with no base case for z.
   %total should fail because there is no clause for partial z _. *)
let wiki_failures_totality_error_1 =
  {|
%sort wft_nat
%term wft_z wft_nat
%term wft_s {_ wft_nat} wft_nat
%sort wft_partial {_ wft_nat} {_ wft_nat}
%mode wft_partial %in %out
%term wft_partial_s {{N M}} {_ wft_partial N M} wft_partial (wft_s N) (wft_s M)
%worlds () (wft_partial _ _)
%total N (wft_partial N _)
|}

(* wiki_failures/unsatisfiable_query.elf: defines an empty type then uses %query.
   %query is not supported in STELF; the parse will fail. *)
let wiki_failures_unsatisfiable_query_1 =
  {|
%sort wfq_empty
%query 1 1 wfq_empty
|}
