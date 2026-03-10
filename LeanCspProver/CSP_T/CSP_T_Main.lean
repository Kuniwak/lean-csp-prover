           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |               February 2005  (modified)   |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_tactic
import LeanCspProver.CSP_T.CSP_T_surj

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

/- The Isabelle theorem bundle `cspT_mono_ref` is represented by
   `cspT_free_mono`, `cspT_Act_prefix_mono`, `cspT_Ext_pre_choice_mono`,
   `cspT_IF_mono`, and `cspT_decompo_subset`. -/

/- The Isabelle theorem bundle `cspT_decompo_ref` is represented by
   `cspT_mono_ref` and `cspT_cong`. -/

/-
(*-------------------------------------------------------*
 |                                                       |
 |      adding ... to automatically check Procfun        |
 |                                                       |
 *-------------------------------------------------------*)
-/

/-
(*-------------------------------------------------------------*
 |                                                             |
 |  Users may be sometimes required to apply "Int_prefix_def"  |
 |  for unfoling "! x:X -> P". Do you like the following ?     |
 |                                                             |
 |  declare Int_pre_choice_def                     [simp]      |
 |                                                             |
 |  Users may be sometimes required to apply "Send_prefix_def" |
 |  for unfoling "a ! x: -> P". Do you like the following ?    |
 |                                                             |
 |  declare Send_prefix_def                        [simp]      |
 |                                                             |
 |  Users may be sometimes required to apply "Rec_prefix_def"  |
 |  for unfoling "a ? x:X -> P". Do you like the following ?   |
 |                                                             |
 |  declare Rec_prefix_def                         [simp]      |
 |                                                             |
 *-------------------------------------------------------------*)
-/

/-                           NO                                -/

/-
(*----------------------------------------------------------------------*
 |                                                                      |
 |  To unfold (resp. fold) syntactic-sugar for Ext_ and Int_pre_choices |
 |  choices, use "unfold csp_prefix_ss_def"                             |
 |                                                                      |
 *----------------------------------------------------------------------*)
-/

/-
(*---------------------------------------------------------------------*
 | Nondet_send_prefix_def : non-deterministic sending                  |
 | Rep_int_choice_fun_def : Replicated internal choice with a function |
 *---------------------------------------------------------------------*)
-/

/-   "inj_on_def" is needed for resolving (inv f) in R_Prefix_def -/
/-  declare inj_on_def                                 [simp]     -/

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

/- CSP_T_law_basic -/

/- The Isabelle theorem bundle `cspT_commut` is represented by
   `cspT_Ext_choice_commut`, `cspT_Int_choice_commut`, and
   `cspT_Parallel_commut`. -/

/- CSP_T_law_ref -/

/- The Isabelle `[intro!]` declaration for `cspT_Int_choice_right` has no
   direct Lean analogue. -/

/- The Isabelle theorem bundle `cspT_Rep_int_choice_right` is represented by
   the theorems documented in `CSP_T_law_ref`. -/

/- CSP_T_law_SKIP -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_resolve` is represented by the
   theorem bundles documented in `CSP_T_law_aux`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_resolve_sym` is represented by
   the `cspT_sym` images of theorems in `cspT_SKIP_DIV_resolve`. -/

/- CSP_T_law_decompo -/

/- The Isabelle theorem bundle `cspT_rm_head` is represented by
   `cspT_rm_head_mono` and `cspT_rm_head_cong`. -/

/- The Isabelle theorem bundle `cspT_decompo` is represented by
   `cspT_mono` and `cspT_cong`. -/

/- CSP_T_law_dist -/

/- The Isabelle theorem bundle `cspT_all_dist` is represented by the theorem
   bundles documented in `CSP_T_tactic`. -/

/- The Isabelle theorem bundle `cspT_all_dist_sym` is represented by the
   `cspT_sym` images of theorems in `cspT_all_dist`. -/

/-
declare cspT_unwind                                  [simp]
lemmas  cspT_unwind_sym                              [simp]
      = cspT_unwind[THEN cspT_sym]
-/

/- CSP_T_law_step -/

/-
declare cspT_step                                    [simp]
lemmas  cspT_step_sym                                [simp]
      = cspT_step[THEN cspT_sym]
-/

/- The Isabelle theorem bundle `cspT_step_rw` is represented by the theorem
   bundle documented in `CSP_T_law_step`. -/

/- The Isabelle theorem bundle `cspT_step_rw_sym` is represented by the
   `cspT_sym` images of theorems in `cspT_step_rw`. -/

/- CSP_T_law_etc -/

/- The Isabelle theorem bundle `cspT_choice_IF` is represented by the theorem
   bundles documented in `CSP_T_tactic`. -/

/- top -/

/- The Isabelle theorem bundle `cspT_top` is represented by
   `cspT_STOP_top` and `cspT_DIV_top`. -/

/- The Isabelle theorem bundle `cspT_Ent_choice_left_ref` is represented by
   `cspT_Ent_choice_left1_ref` and `cspT_Ent_choice_left2_ref`. -/

/- The Isabelle theorem bundle `cspT_decompo_Alpha_parallel` is represented by
   `cspT_Alpha_parallel_mono` and `cspT_Alpha_parallel_cong`. -/

/-
(*-------------------[test of CSP_T]------------------------*

datatype Event = eva | evb

datatype PNSpec = AB
datatype PNImpl = A

consts
  PNfunSpec :: "PNSpec => (PNSpec, Event) proc"
  PNfunImpl :: "PNImpl => (PNImpl, Event) proc"

primrec
  "PNfunSpec   AB = eva -> $AB |~| evb -> $AB"

primrec
  "PNfunImpl   A = eva -> $A"

defs (overloaded)
Set_PNfunSpec_def : "PNfun == PNfunSpec"
Set_PNfunImpl_def : "PNfun == PNfunImpl"
FPmode_def        : "FPmode == CMSmode"

declare Set_PNfunSpec_def [simp]
declare Set_PNfunImpl_def [simp]
declare FPmode_def        [simp]

lemma example_test_01: "PNfun AB = eva -> $AB |~| evb -> $AB"
by (simp)

lemma example_test_02: "PNfun A = eva -> $A"
by (simp)

consts
  Spec_Impl :: "PNSpec => (PNImpl, Event) proc"

primrec
  "Spec_Impl  AB = $A"

consts
  Spec :: "(PNSpec, Event) proc"
  Impl :: "(PNImpl, Event) proc"

defs
  Spec_def : "Spec == $AB"
  Impl_def : "Impl == $A"

lemma guardedfun_ex[simp]:
  "guardedfun PNfunSpec"
  "guardedfun PNfunImpl"
by (simp add: guardedfun_def, rule allI, induct_tac p, simp)+

lemma example_test_fp: "Spec <=T Impl"
apply (simp add: Spec_def Impl_def)
apply (rule cspT_fp_induct_left[of _ "Spec_Impl"])
apply (simp_all)
apply (simp)

apply (induct_tac p)
apply (simp)

apply (rule cspT_rw_right)
apply (rule cspT_unwind)
apply (simp_all)
apply (simp)

apply (rule cspT_Int_choice_left1)
apply (simp)
done

-- you have to note that you cannot prove "$AB <=T $A"
-- because $AB has a wider type "(PNSpec,'s) proc" than
-- "(PNSpec,Event) proc".

 *-------------------[test of CSP_T]------------------------*)
-/

end
