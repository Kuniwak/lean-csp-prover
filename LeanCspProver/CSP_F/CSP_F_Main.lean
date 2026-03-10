           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |               February 2005  (modified)   |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_tactic
import LeanCspProver.CSP_F.CSP_F_surj
import LeanCspProver.CSP_T.CSP_T_Main
import LeanCspProver.CSP_F.CSP_F_T_domain
import LeanCspProver.CSP_F.CSP_F_MF_MT

open Function
open SumType

noncomputable section

/-
(*--------------------------------------------*
 |                                            |
 |    decomposition considering refinement    |
 |                                            |
 *--------------------------------------------*)
-/

/- The Isabelle theorem bundle `cspF_mono_ref` is represented by
   `cspF_free_mono`, `cspF_Act_prefix_mono`, `cspF_Ext_pre_choice_mono`,
   `cspF_IF_mono`, and `cspF_decompo_subset`. -/

/- The Isabelle theorem bundle `cspF_decompo_ref` is represented by
   `cspF_mono_ref` and `cspF_cong`. -/

/-
(*-------------------------------------------------------*
 |                                                       |
 |  The folloing def have already added in CSP_T         |
 |                                                       |
 |   Procfun_def                                         |
 |   ProcX_def                                           |
 |   gSKIPX_def                                          |
 |   gProcX_def                                          |
 |   nohideX_def                                         |
 |                                                       |
 *-------------------------------------------------------*)
-/

/-
(*----------------------------------------------------------------------*
 |                                                                      |
 |  To unfold (resp. fold) syntactic-sugar for Ext_ and Int_pre_choices |
 |  choices, use "unfold csp_prefix_ss_def"                             |
 |                                                                      |
 *----------------------------------------------------------------------*)
-/

/-
(*------------------------------------*
 |                                    |
 |    laws automatically applied      |
 |                                    |
 *------------------------------------*)
-/

/- intro! intro? are automatically applied by "rule".     -/
/- intro! is automatically applied by "rules" and "auto". -/

/- Lean note:
   Isabelle's theorem bundles and `declare ... [simp]/[intro!]` commands do
   not have a direct Lean counterpart. The imported files already expose the
   corresponding individual theorems, and this theory records the same bundle
   structure for later local registration when needed. -/

/- CSP_F_law_basic -/

/- The Isabelle theorem bundle `cspF_commut` is represented by
   `cspF_Ext_choice_commut`, `cspF_Int_choice_commut`, and
   `cspF_Parallel_commut`. -/

/- CSP_F_law_ref -/

/- The Isabelle `[intro!]` declaration for `cspF_Int_choice_right` has no
   direct Lean analogue. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_right` is represented by
   the theorems documented in `CSP_F_law_ref`. -/

/- CSP_F_law_SKIP -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_resolve` is represented by the
   theorem bundles documented in `CSP_F_law_aux`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_resolve_sym` is represented by
   the `cspF_sym` images of theorems in `cspF_SKIP_DIV_resolve`. -/

/- CSP_F_law_decompo -/

/- The Isabelle theorem bundle `cspF_rm_head` is represented by
   `cspF_rm_head_mono` and `cspF_rm_head_cong`. -/

/- The Isabelle theorem bundle `cspF_decompo` is represented by
   `cspF_mono` and `cspF_cong`. -/

/- CSP_F_law_dist -/

/- The Isabelle theorem bundle `cspF_all_dist` is represented by the theorem
   bundles documented in `CSP_F_tactic`. -/

/- The Isabelle theorem bundle `cspF_all_dist_sym` is represented by the
   `cspF_sym` images of theorems in `cspF_all_dist`. -/

/-
declare cspF_unwind                                  [simp]
lemmas  cspF_unwind_sym                              [simp]
      = cspF_unwind[THEN cspF_sym]
-/

/- CSP_F_law_step -/

/-
declare cspF_step                                    [simp]
lemmas  cspF_step_sym                                [simp]
      = cspF_step[THEN cspF_sym]
-/

/- The Isabelle theorem bundle `cspF_step_rw` is represented by the theorem
   bundle documented in `CSP_F_law_step`. -/

/- The Isabelle theorem bundle `cspF_step_rw_sym` is represented by the
   `cspF_sym` images of theorems in `cspF_step_rw`. -/

/- CSP_F_law_etc -/

/- The Isabelle theorem bundle `cspF_choice_IF` is represented by the theorem
   bundles documented in `CSP_F_tactic`. -/

/- CSP_F_DIV_top -/

/- The Isabelle theorem bundle `cspF_DIV_top` is represented by
   `cspF_DIV_top`. -/

/- Alpha_Parallel -/

/- The Isabelle theorem bundle `cspF_decompo_Alpha_parallel` is represented by
   `cspF_Alpha_parallel_mono` and `cspF_Alpha_parallel_cong`. -/

/-
(* ------------------------------------------------------------------- *

      The lemma "cspF_Rep_int_simp" is not automatically applied by
      tactics. If you want to simplify indexes in replicated internal
      choice, then the following command will be useful.

         apply (cspF_simp cspF_Rep_int_simp)

 * ------------------------------------------------------------------- *)
-/

/- The Isabelle theorem bundle `cspF_Rep_int_simp` is represented by
   `cspF_choice_delay`, `cspF_Rep_int_choice_sepa`, and
   `cspF_Rep_int_choice_f_map`. -/

/-
(* -------------------------------------------------- *
        The following lemma is added to "simp"
        This is applied for simplifying compostions
        of functions in internal choices.
        (See the bottom of CSP_F_law_basic.thy)
 * -------------------------------------------------- *)
-/

theorem compo_inj_is_inj {f : β → γ} {g : α → β}
    (hf : Injective f) (hg : Injective g) :
    Injective (f ∘ g) :=
  hf.comp hg

/-
(* -------------------------------------------------- *
           convenient lemmas for event-sets
 * -------------------------------------------------- *)
-/

/-
declare simp_event_set [simp]
-/

end
