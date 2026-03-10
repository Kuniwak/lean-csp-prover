           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_basic

open Function
open SumType
open event

noncomputable section

/-
(*****************************************************************

         1. step laws
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(*********************************************************
             Parallel expansion & distribution
 *********************************************************)
-/

axiom cspT_Parallel_Timeout_split
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P Q : proc p α} {M : p → domTType α} :
    eqT ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| (Timeout (proc.Ext_pre_choice Z Qf) Q)) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q)
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))))
        ((P |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
          ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Q)))

/-
(*********************************************************
            Parallel expansion & distribution 2
 *********************************************************)
-/

axiom cspT_Parallel_Timeout_input_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| proc.Ext_pre_choice Z Qf) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| proc.Ext_pre_choice Z Qf)
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))))
        (P |[X]| proc.Ext_pre_choice Z Qf))

axiom cspT_Parallel_Timeout_input_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice Y Pf |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
                (proc.Ext_pre_choice Y Pf |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q)
                (proc.Ext_pre_choice Y Pf |[X]| Qf x))))
        (proc.Ext_pre_choice Y Pf |[X]| Q))

/- The Isabelle theorem bundle `cspT_Parallel_Timeout_input` is
   represented by `cspT_Parallel_Timeout_input_l` and
   `cspT_Parallel_Timeout_input_r`. -/

/-
(*** cspT_step_ext ***)
-/

/- The Isabelle theorem bundle `cspT_step_ext` is represented by
   `cspT_Parallel_Timeout_split`, `cspT_Parallel_Timeout_input_l`, and
   `cspT_Parallel_Timeout_input_r`. -/
