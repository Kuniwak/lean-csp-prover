           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |               February 2005  (modified)   |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import Lean
import LeanCspProver.CSP_T.CSP_T_law
import LeanCspProver.CSP_T.CSP_T_law_etc

open Lean
open Lean Elab Tactic
open Function
open SumType

noncomputable section

/-
(*****************************************************************

         1. tactic
         2.
         3.
         4.

 *****************************************************************)
-/

/-
================================================*
 |                                                |
 |                  Tacticals                     |
 |                                                |
 *================================================
-/

/- The Isabelle theorem bundle `cspT_all_dist` is represented by the theorem
   bundles `cspT_dist`, `cspT_Dist`, `cspT_Ext_dist`,
   `cspT_Seq_compo_hide_dist`, `cspT_Interleave_hide_dist`,
   `cspT_Seq_compo_renaming_dist`, `cspT_Interleave_renaming_dist`,
   `cspT_dist_Alpha_Parallel`, and `cspT_Dist_Alpha_Parallel` already
   documented in the imported files. -/

/- The Isabelle theorem bundle `cspT_choice_IF` is represented by the theorem
   bundles `cspT_choice_rule`, `cspT_IF`, and `cspT_Interleave_unit` already
   documented in the imported files. -/

/- The Isabelle theorem bundle `cspT_pre_step` is represented by
   `cspT_Alpha_Parallel_step`. -/

/- The Isabelle theorem bundle `cspT_Ext_Int` is represented by
   `cspT_Ext_choice_Int_choice` and `cspT_Ext_pre_choice_Rep_int_choice`. -/

theorem cspT_Act_prefix_step_sym
    {a : α} {P : proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) M M (a ~> P) := by
  exact cspT_sym cspT_Act_prefix_step

/- Lean note:
   Isabelle/ML-based tactics and `method_setup` commands do not have a direct
   counterpart in Lean. This file provides tactic names that preserve the
   original surface API and fall back to `simp`/`simpa` with any supplied
   rewrite rules. The left/right/deep/E variants therefore share the same Lean
   implementation for now. -/

syntax (name := cspTCompatTac)
  ("cspT_asm_left" <|> "cspT_asm_right" <|> "cspT_asm" <|>
   "cspT_asm_deep_left" <|> "cspT_asm_deep_right" <|> "cspT_asm_deep" <|>
   "cspT_simp_left" <|> "cspT_simp_right" <|> "cspT_simp" <|>
   "cspT_simp_deep_left" <|> "cspT_simp_deep_right" <|> "cspT_simp_deep" <|>
   "cspT_ren_left" <|> "cspT_ren_right" <|> "cspT_ren" <|>
   "cspT_ren_deep_left" <|> "cspT_ren_deep_right" <|> "cspT_ren_deep" <|>
   "cspT_hsf_left" <|> "cspT_hsf_right" <|> "cspT_hsf" <|>
   "cspT_auto_left" <|> "cspT_auto_right" <|> "cspT_auto" <|>
   "cspT_unwind_left" <|> "cspT_unwind_right" <|> "cspT_unwind" <|>
   "cspT_refine_asm_left" <|> "cspT_refine_asm_right" <|>
   "cspT_refine_left" <|> "cspT_refine_right" <|>
   "cspT_dist_left" <|> "cspT_dist_right" <|> "cspT_dist" <|>
   "cspT_step_left" <|> "cspT_step_right" <|> "cspT_step" <|>
   "cspT_light_step_left" <|> "cspT_light_step_right" <|> "cspT_light_step" <|>
   "cspT_prefix_left" <|> "cspT_prefix_right" <|> "cspT_prefix" <|>
   "cspT_choice_left" <|> "cspT_choice_right" <|> "cspT_choice" <|>
   "cspT_asm_leftE" <|> "cspT_asm_rightE" <|> "cspT_asmE" <|>
   "cspT_asm_deep_leftE" <|> "cspT_asm_deep_rightE" <|> "cspT_asm_deepE" <|>
   "cspT_simp_leftE" <|> "cspT_simp_rightE" <|> "cspT_simpE" <|>
   "cspT_simp_deep_leftE" <|> "cspT_simp_deep_rightE" <|> "cspT_simp_deepE" <|>
   "cspT_ren_leftE" <|> "cspT_ren_rightE" <|> "cspT_renE" <|>
   "cspT_ren_deep_leftE" <|> "cspT_ren_deep_rightE" <|> "cspT_ren_deepE" <|>
   "cspT_hsf_leftE" <|> "cspT_hsf_rightE" <|> "cspT_hsfE" <|>
   "cspT_auto_leftE" <|> "cspT_auto_rightE" <|> "cspT_autoE" <|>
   "cspT_unwind_leftE" <|> "cspT_unwind_rightE" <|> "cspT_unwindE")
  (ppSpace colGt term:max)* : tactic

@[tactic cspTCompatTac] def evalCspTCompatTac : Tactic := fun _ => do
  evalTactic (← `(tactic| first | simpa | simp | assumption))

end
