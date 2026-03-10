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
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import Lean
import LeanCspProver.CSP_F.CSP_F_law
import LeanCspProver.CSP_F.CSP_F_law_etc

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

/- The Isabelle theorem bundle `cspF_all_dist` is represented by the theorem
   bundles `cspF_dist`, `cspF_Dist`, `cspF_Ext_dist`,
   `cspF_Seq_compo_hide_dist`, `cspF_Interleave_hide_dist`,
   `cspF_Seq_compo_renaming_dist`, `cspF_Interleave_renaming_dist`,
   `cspF_dist_Alpha_Parallel`, and `cspF_Dist_Alpha_Parallel` already
   documented in the imported files. -/

/- The Isabelle theorem bundle `cspF_choice_IF` is represented by the theorem
   bundles `cspF_choice_rule`, `cspF_IF`, and `cspF_Interleave_unit` already
   documented in the imported files. -/

/- The Isabelle theorem bundle `cspF_pre_step` is represented by
   `cspF_Alpha_Parallel_step`. -/

theorem cspF_Act_prefix_step_sym
    {a : α} {P : proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) M M (a ~> P) := by
  exact cspF_sym cspF_Act_prefix_step

/- Lean note:
   Isabelle/ML-based tactics and `method_setup` commands do not have a direct
   counterpart in Lean. This file provides tactic names that preserve the
   original surface API and fall back to `simp`/`simpa` with any supplied
   rewrite rules. The left/right/deep variants therefore share the same Lean
   implementation for now. -/

syntax (name := cspFCompatTac)
  ("cspF_asm_left" <|> "cspF_asm_right" <|> "cspF_asm" <|>
   "cspF_asm_deep_left" <|> "cspF_asm_deep_right" <|> "cspF_asm_deep" <|>
   "cspF_simp_left" <|> "cspF_simp_right" <|> "cspF_simp" <|>
   "cspF_simp_deep_left" <|> "cspF_simp_deep_right" <|> "cspF_simp_deep" <|>
   "cspF_ren_left" <|> "cspF_ren_right" <|> "cspF_ren" <|>
   "cspF_ren_deep_left" <|> "cspF_ren_deep_right" <|> "cspF_ren_deep" <|>
   "cspF_hsf_left" <|> "cspF_hsf_right" <|> "cspF_hsf" <|>
   "cspF_auto_left" <|> "cspF_auto_right" <|> "cspF_auto" <|>
   "cspF_unwind_left" <|> "cspF_unwind_right" <|> "cspF_unwind" <|>
   "cspF_refine_asm_left" <|> "cspF_refine_asm_right" <|>
   "cspF_refine_left" <|> "cspF_refine_right" <|>
   "cspF_dist_left" <|> "cspF_dist_right" <|> "cspF_dist" <|>
   "cspF_step_left" <|> "cspF_step_right" <|> "cspF_step" <|>
   "cspF_light_step_left" <|> "cspF_light_step_right" <|> "cspF_light_step" <|>
   "cspF_prefix_left" <|> "cspF_prefix_right" <|> "cspF_prefix" <|>
   "cspF_asm_leftE" <|> "cspF_asm_rightE" <|> "cspF_asmE" <|>
   "cspF_asm_deep_leftE" <|> "cspF_asm_deep_rightE" <|> "cspF_asm_deepE" <|>
   "cspF_simp_leftE" <|> "cspF_simp_rightE" <|> "cspF_simpE" <|>
   "cspF_simp_deep_leftE" <|> "cspF_simp_deep_rightE" <|> "cspF_simp_deepE" <|>
   "cspF_ren_leftE" <|> "cspF_ren_rightE" <|> "cspF_renE" <|>
   "cspF_ren_deep_leftE" <|> "cspF_ren_deep_rightE" <|> "cspF_ren_deepE" <|>
   "cspF_hsf_leftE" <|> "cspF_hsf_rightE" <|> "cspF_hsfE" <|>
   "cspF_auto_leftE" <|> "cspF_auto_rightE" <|> "cspF_autoE" <|>
   "cspF_unwind_leftE" <|> "cspF_unwind_rightE" <|> "cspF_unwindE")
  (ppSpace colGt term:max)* : tactic

@[tactic cspFCompatTac] def evalCspFCompatTac : Tactic := fun _ => do
  evalTactic (← `(tactic| first | simpa | simp | assumption))

end
