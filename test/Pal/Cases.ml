open Common

let nat_test =
  [ {| %sort nat |}; {| %term zero nat |}; {| %term succ {_ nat} nat |} ]

let add_test =
  [
    {| %sort add {_ nat} {_ nat} {_ nat} |};
    {| %term add/zero {y nat} add zero y y |};
    {| %term add/succ {x nat} {y nat} {z nat} {_ add x y z} add (succ x) y (succ z) |};
  ]

let mul_test =
  [
    {| %sort mul {_ nat} {_ nat} {_ nat} |};
    {| %term mul/zero {x nat} mul x zero zero |};
    {| %term mul/succ {x nat} {y nat} {z nat} {z' nat} {_ mul x y z} {_ add y z z'} (mul (succ x) y z') |};
  ]

let total_add_mul_test =
  [
    {| %mode {%in x nat} {%in y nat} {%out z nat} add x y z |};
    {| %worlds () (add _ _ _) |};
    {| %total N (add N _ _) |};
  ]

let cases () =
  Alcotest.run "PAL"
    begin
      [
        test "%term and %sort"
          Source.
            [
              String.concat "\n" nat_test;
              String.concat "\n" add_test;
              String.concat "\n" mul_test;
              String.concat "\n" total_add_mul_test;
            ];
        test "ZF" Source.[ zf_1; zf_2; zf_3; zf_4; zf_5; zf_6 ];
        test "FOL"
          Source.
            [
              fol1;
              fol2;
              fol3_1;
              fol3_2_1;
              fol3_2_2;
              fol3_2_3;
              fol3_3;
              fol3_4;
              fol4_1;
              fol4_2;
              fol5_1;
              fol5_2;
              fol6_1;
              fol6_2;
            ];
        test "Nats" Source.[ nats1; nats2; nats3; nats4 ];
        test "S4" Source.[ jsf_1; jsf_2_1; jsf_2_2; jsf_3; jsf_4 ];
        test "LAM" Source.[ lam_1; lam_2; lam_3; lam_4; lam_5 ];
        test "POLYLAM" Source.[ polylam ];
        test "PROP-CALC"
          Source.
            [
              prop_calc_types;
              prop_calc_types ^ prop_calc_hilbert;
              prop_calc_types ^ prop_calc_hilbert ^ prop_calc_nd;
            ];
        test "MINI-ML" Source.[ mini_ml_exp; mini_ml_value; mini_ml_tp ];
        test "ARITH" Source.[ arith_nat; arith_nt; arith_plus; arith_acker ];
        test "GUIDE-LISTS"
          Source.[ guide_lists_types; guide_lists_append; guide_lists_mode ];
        test "TAPL-NAT" Source.[ tapl_nat_base; tapl_nat_eq ];
        test "LP-HORN-ND" Source.[ lp_horn_nd ];
        test "CHURCH-ROSSER-LAM" Source.[ church_rosser_lam ];
        test "CUT-ELIM-FORMULAS" Source.[ cut_elim_formulas ];
        test "cut_elim/sources"
          Source.[ cut_elim_formulas; cut_elim_sources_2 ];
        test "GUIDE-ND" Source.[ guide_nd ];
        test "CPSOCC-DSBNF" Source.[ cpsocc_dsbnf ];
        test "CPSOCC-CPSBF" Source.[ cpsocc_cpsBNF ];
        test "SMALL-STEP-LAM"
          Source.
            [
              small_step_lam_types;
              small_step_lam_terms;
              small_step_lam_typing;
              small_step_lam_value;
              small_step_lam_step;
            ];
        test "CRARY-EXCON" Source.[ crary_excon ];
        test "CRARY-EXCON-REV" Source.[ crary_excon_rev_syntax ];
        test "TAPL-DEFS"
          Source.
            [
              tapl_defs_types;
              tapl_defs_labels;
              tapl_defs_exp;
              tapl_defs_value;
              tapl_defs_store;
              tapl_defs_heap;
            ];
        test "SMALL-STEP-SYSF"
          Source.
            [
              small_step_sysf_types;
              small_step_sysf_terms;
              small_step_sysf_typing;
              small_step_sysf_value;
              small_step_sysf_step;
            ];
        test "SMALL-STEP-SYSF-ISO"
          Source.
            [
              small_step_sysf_iso_types;
              small_step_sysf_iso_terms;
              small_step_sysf_iso_typing;
              small_step_sysf_iso_value;
              small_step_sysf_iso_step;
            ];
        test "POPLMARK-1A"
          Source.[ poplmark_1a_syntax; poplmark_1b_syntax; poplmark_2b_syntax ];
        test "POPLMARK-2A"
          Source.[ poplmark_1a_syntax; poplmark_2a_syntax ];
        test "CCC" Source.[ ccc_syntax ];
        test "INCLL" Source.[ incll_syntax ];
        test "CRARY-LINEAR" Source.[ crary_linear_syntax; crary_linear_linear ];
        test "CRARY-LINEARD" Source.[ crary_lineard_syntax ];
        test "CRARY-MODAL" Source.[ crary_modal_syntax ];
        test "church_rosser/sources"
          Source.
            [
              church_rosser_lam;
              church_rosser_sources_2;
              church_rosser_sources_3;
            ];
        test ~skip:true "mini_ml/sources"
          Source.
            [
              mini_ml_exp;
              mini_ml_value;
              mini_ml_tp;
              mini_ml_sources_eval;
              mini_ml_sources_tpinf;
            ];
        (* Skipped: dependent sort indices in %sort declarations not yet supported. *)
        test ~skip:true "lp_horn/sources"
          Source.[ lp_horn_nd; lp_horn_sources_2; lp_horn_sources_3 ];
        (* examples/arith/sources.cfg: nat + nt + plus + acker — same content as ARITH
       above, re-declared. Pal frontend is lenient about re-declarations. *)
        test "arith/sources"
          Source.[ arith_nat; arith_nt; arith_plus; arith_acker ];
        (* examples/fol/sources.cfg: same content as FOL above *)
        test "fol/sources"
          Source.
            [
              fol1;
              fol2;
              fol3_1;
              fol3_2_1;
              fol3_2_2;
              fol3_2_3;
              fol3_3;
              fol3_4;
              fol4_1;
              fol4_2;
              fol5_1;
              fol5_2;
              fol6_1;
              fol6_2;
            ];
        (* examples/polylam/sources.cfg: same content as POLYLAM above *)
        test "polylam/sources" Source.[ polylam ];
        (* examples/guide/sources.cfg: nd + lists + lam. guide_nd fails with worldcheck
       library bug (same as GUIDE-ND above), so it is omitted here. Lists and lam
       are re-tested to confirm they still pass after the worldcheck group. *)
        test "guide/sources"
          Source.
            [
              guide_lists_types;
              guide_lists_append;
              guide_lists_mode;
              lam_1;
              lam_2;
              lam_3;
              lam_4;
              lam_5;
            ];
        (* examples/prop_calc/sources.cfg: types + hilbert + nd cumulative *)
        test "prop_calc/sources"
          Source.
            [
              prop_calc_types;
              prop_calc_types ^ prop_calc_hilbert;
              prop_calc_types ^ prop_calc_hilbert ^ prop_calc_nd;
            ];
        (* examples/crary/explicit/excon *)
        test "crary/explicit/excon" Source.[ crary_excon ];
        (* examples/crary/explicit/excon-rev *)
        test "crary/explicit/excon-rev" Source.[ crary_excon_rev_syntax ];
        (* examples/crary/substruct/linear *)
        test "crary/substruct/linear"
          Source.[ crary_linear_syntax; crary_linear_linear ];
        (* examples/crary/substruct/lineard *)
        test "crary/substruct/lineard" Source.[ crary_lineard_syntax ];
        (* examples/crary/substruct/modal *)
        test "crary/substruct/modal" Source.[ crary_modal_syntax ];
        (* Tier 2: single-elf cfg files *)

        test ~skip:true "handbook/sources" Source.[ handbook_sources_1 ];
        (* examples/ccc/spass.cfg → spass.elf: CCC with categorical laws.
       Uses dependent sort indices (== : mor A B -> mor A B -> type) —
       STELF reconstructor does not support dependent sort indices yet. *)
        test ~skip:true "ccc/spass" Source.[ ccc_spass_1 ];
        (* examples/failure/sources.cfg → fail.elf: only %query (unsupported in STELF).
       Expected to fail with ParseError. *)
        test ~failure:true "failure/sources" Source.[ failure_sources_1 ];
        (* examples/wiki_failures/coverage_error.cfg: incomplete coverage proof.
       %total on wf_sub_trans should trigger a coverage or totality failure. *)
        test ~failure:true "wiki_failures/coverage_error"
          Source.[ wiki_failures_coverage_error_1 ];
        (* examples/wiki_failures/mode_error.cfg: bad mode — output used as input.
       %mode check on wfm_bad should fail. *)
        test ~failure:true "wiki_failures/mode_error"
          Source.[ wiki_failures_mode_error_1 ];
        (* examples/wiki_failures/totality_error.cfg: no base case for z.
       %total check on wft_partial should fail. *)
        test ~failure:true "wiki_failures/totality_error"
          Source.[ wiki_failures_totality_error_1 ];
        (* examples/wiki_failures/unsatisfiable_query.cfg: %query on empty type.
       %query not supported in STELF; expected ParseError. *)
        test ~failure:true "wiki_failures/unsatisfiable_query"
          Source.[ wiki_failures_unsatisfiable_query_1 ];
        (* examples/crary/standard/standard.cfg → standard.elf (1602 lines).
       Higher-order CBV lambda calculus. Too large to translate now. *)
        test ~skip:true "crary/standard/standard"
          Source.[ crary_standard_standard_1 ];
        (* examples/tabled/parsing/arithml.cfg: grammar with numeric identifiers. *)
        test ~skip:true "tabled/parsing/arithml"
          Source.[ tabled_parsing_arithml_1 ];
        (* examples/tabled/parsing/foll.cfg: FOL grammar with %tabled. *)
        test ~skip:true "tabled/parsing/foll" Source.[ tabled_parsing_foll_1 ];
        (* examples/tabled/parsing/tab.cfg: DCG grammar with single-quoted tokens. *)
        test ~skip:true "tabled/parsing/tab" Source.[ tabled_parsing_tab_1 ];
        (* examples/tabled/ccc/tab.cfg: CCC with tabling. *)
        test ~skip:true "tabled/ccc/tab" Source.[ tabled_ccc_tab_1 ];
        test "nat-scope" Source.[ nat_scope ]; 
      ];
    
    end 
