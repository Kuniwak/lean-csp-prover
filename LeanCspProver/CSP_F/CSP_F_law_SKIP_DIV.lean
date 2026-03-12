           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_SKIP
import LeanCspProver.CSP_F.CSP_F_law_DIV
import LeanCspProver.CSP_T.CSP_T_law_SKIP_DIV

open Function
open SumType
open event

noncomputable section

/-
(*********************************************************
                   (SKIP [+] DIV)
 *********************************************************)
-/

axiom cspF_SKIP_DIV_Ext_choice1
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) [+] proc.DIV)) M1 M2 (proc.SKIP : proc q α)

theorem cspF_SKIP_DIV_Ext_choice2
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.DIV : proc p α) [+] proc.SKIP)) M1 M2 (proc.SKIP : proc q α) := by
  have h₁ :
      eqF (((proc.DIV : proc p α) [+] proc.SKIP)) M1 M1
        (((proc.SKIP : proc p α) [+] proc.DIV)) :=
    cspF_Ext_choice_commut
  have h₂ :
      eqF (((proc.SKIP : proc p α) [+] proc.DIV)) M1 M2 (proc.SKIP : proc q α) :=
    cspF_SKIP_DIV_Ext_choice1
  exact cspF_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Ext_choice` is represented by
   `cspF_SKIP_DIV_Ext_choice1` and `cspF_SKIP_DIV_Ext_choice2`. -/

/-
(*********************************************************
                    SKIP |[X]| DIV
 *********************************************************)
-/

axiom cspF_SKIP_DIV_Parallel1
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| proc.DIV)) M1 M2 (proc.DIV : proc q α)

theorem cspF_SKIP_DIV_Parallel2
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.DIV : proc p α) |[X]| proc.SKIP)) M1 M2 (proc.DIV : proc q α) := by
  have h₁ :
      eqF (((proc.DIV : proc p α) |[X]| proc.SKIP)) M1 M1
        (((proc.SKIP : proc p α) |[X]| proc.DIV)) :=
    cspF_Parallel_commut
  have h₂ :
      eqF (((proc.SKIP : proc p α) |[X]| proc.DIV)) M1 M2 (proc.DIV : proc q α) :=
    cspF_SKIP_DIV_Parallel1
  exact cspF_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Parallel` is represented by
   `cspF_SKIP_DIV_Parallel1`, `cspF_SKIP_DIV_Parallel2`,
   `cspF_Parallel_term`, and `cspF_DIV_Parallel`. -/

/-
(*********************************************************
                 DIV and Parallel-SKIP
 *********************************************************)
-/

/- (*** SKIP and DIV ***) -/

axiom cspF_DIV_Parallel_Ext_choice_SKIP_l
    {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF ((((P [+] proc.SKIP) |[X]| (proc.DIV : proc p α)))) M M (P |[X]| (proc.DIV : proc p α))

theorem cspF_DIV_Parallel_Ext_choice_SKIP_r
    {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (((proc.DIV : proc p α) |[X]| (P [+] proc.SKIP))) M M ((proc.DIV : proc p α) |[X]| P) := by
  have h₁ :
      eqF (((proc.DIV : proc p α) |[X]| (P [+] proc.SKIP))) M M
        ((((P [+] proc.SKIP) |[X]| (proc.DIV : proc p α)))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF ((((P [+] proc.SKIP) |[X]| (proc.DIV : proc p α)))) M M (P |[X]| (proc.DIV : proc p α)) :=
    cspF_DIV_Parallel_Ext_choice_SKIP_l
  have h₃ :
      eqF (P |[X]| (proc.DIV : proc p α)) M M ((proc.DIV : proc p α) |[X]| P) :=
    cspF_Parallel_commut
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_DIV_Parallel_Ext_choice_SKIP` is
   represented by `cspF_DIV_Parallel_Ext_choice_SKIP_l` and
   `cspF_DIV_Parallel_Ext_choice_SKIP_r`. -/

/- The Isabelle theorem bundle `cspF_DIV_Parallel_Ext_choice` is
   represented by `cspF_DIV_Parallel_Ext_choice_SKIP_l`,
   `cspF_DIV_Parallel_Ext_choice_SKIP_r`,
   `cspF_DIV_Parallel_Ext_choice_DIV_l`, and
   `cspF_DIV_Parallel_Ext_choice_DIV_r`. -/

/-
(*********************************************************
                 SKIP and Parallel-DIV
 *********************************************************)
-/

/- (*** DIV and SKIP ***) -/

axiom cspF_SKIP_Parallel_Ext_choice_DIV_l
    {Y X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]| proc.SKIP)) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+] proc.DIV))

theorem cspF_SKIP_Parallel_Ext_choice_DIV_r
    {Y X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.DIV))) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+]
        proc.DIV)) := by
  have h₁ :
      eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.DIV))) M M
        ((((proc.Ext_pre_choice Y Pf) [+] proc.DIV) |[X]| (proc.SKIP : proc p α))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF ((((proc.Ext_pre_choice Y Pf) [+] proc.DIV) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
          proc.DIV)) :=
    cspF_SKIP_Parallel_Ext_choice_DIV_l
  have h₃₁ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  have h₃ :
      eqF
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
          proc.DIV)) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+]
          proc.DIV)) := by
    exact cspF_Ext_choice_cong h₃₁ cspF_reflex_eq_DIV
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_SKIP_Parallel_Ext_choice_DIV` is
   represented by `cspF_SKIP_Parallel_Ext_choice_DIV_l` and
   `cspF_SKIP_Parallel_Ext_choice_DIV_r`. -/

/- The Isabelle theorem bundle `cspF_SKIP_Parallel_Ext_choice` is
   represented by `cspF_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`,
   `cspF_SKIP_Parallel_Ext_choice_DIV_l`, and
   `cspF_SKIP_Parallel_Ext_choice_DIV_r`. -/

/-
(*---------------------------------------------*
 |                 SKIP , DIV                  |
 *---------------------------------------------*)
-/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Parallel_step` is represented
   by `cspF_Parallel_preterm_l`, `cspF_Parallel_preterm_r`,
   `cspF_DIV_Parallel_step_l`, and `cspF_DIV_Parallel_step_r`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Parallel_Ext_choice` is
   represented by `cspF_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`,
   `cspF_SKIP_Parallel_Ext_choice_DIV_l`,
   `cspF_SKIP_Parallel_Ext_choice_DIV_r`,
   `cspF_DIV_Parallel_Ext_choice_SKIP_l`,
   `cspF_DIV_Parallel_Ext_choice_SKIP_r`,
   `cspF_DIV_Parallel_Ext_choice_DIV_l`, and
   `cspF_DIV_Parallel_Ext_choice_DIV_r`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Hiding_Id` is represented by
   `cspF_SKIP_Hiding_Id` and `cspF_DIV_Hiding_Id`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Hiding_step` is represented by
   `cspF_DIV_Hiding_step` and `cspF_SKIP_Hiding_step`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Renaming_Id` is represented by
   `cspF_SKIP_Renaming_Id` and `cspF_DIV_Renaming_Id`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Seq_compo` is represented by
   `cspF_Seq_compo_unit_l`, `cspF_Seq_compo_unit_r`, and
   `cspF_DIV_Seq_compo`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Seq_compo_step` is represented
   by `cspF_SKIP_Seq_compo_step` and `cspF_DIV_Seq_compo_step`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Depth_rest` is represented by
   `cspF_SKIP_Depth_rest` and `cspF_DIV_Depth_rest`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV` is represented by
   `cspF_Parallel_preterm_l`, `cspF_Parallel_preterm_r`,
   `cspF_SKIP_DIV_Ext_choice1`, `cspF_SKIP_DIV_Ext_choice2`,
   `cspF_SKIP_DIV_Parallel1`, `cspF_SKIP_DIV_Parallel2`,
   `cspF_Parallel_term`, `cspF_DIV_Parallel`,
   `cspF_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`,
   `cspF_SKIP_Parallel_Ext_choice_DIV_l`,
   `cspF_SKIP_Parallel_Ext_choice_DIV_r`,
   `cspF_DIV_Parallel_Ext_choice_SKIP_l`,
   `cspF_DIV_Parallel_Ext_choice_SKIP_r`,
   `cspF_DIV_Parallel_Ext_choice_DIV_l`,
   `cspF_DIV_Parallel_Ext_choice_DIV_r`,
   `cspF_SKIP_Hiding_Id`, `cspF_DIV_Hiding_Id`,
   `cspF_DIV_Hiding_step`, `cspF_SKIP_Hiding_step`,
   `cspF_SKIP_Renaming_Id`, `cspF_DIV_Renaming_Id`,
   `cspF_Seq_compo_unit_l`, `cspF_Seq_compo_unit_r`,
   `cspF_DIV_Seq_compo`, `cspF_SKIP_Seq_compo_step`,
   `cspF_DIV_Seq_compo_step`, `cspF_SKIP_Depth_rest`,
   and `cspF_DIV_Depth_rest`. -/

/- (*** resolve ***) -/

/- The Isabelle theorem bundle `cspF_Ext_choice_SKIP_DIV_resolve` is
   represented by `cspF_Ext_choice_SKIP_resolve` and
   `cspF_Ext_choice_DIV_resolve`. -/

/-
(*----------------------------------------------*
 |                                              |
 |        for convenienve  (SKIP or DIV)        |
 |                                              |
 *----------------------------------------------*)
-/

/-
(*********************************************************
            (SKIP or DIV [+] SKIP or DIV)
 *********************************************************)
-/

open Classical in
theorem cspF_SKIP_or_DIV_Ext_choice
    {P Q : proc p α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : P = (proc.SKIP : proc p α) ∨ P = proc.DIV)
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqF (P [+] Q) M1 M2
      (if P = (proc.SKIP : proc p α) ∨ Q = proc.SKIP then
        (proc.SKIP : proc q α)
      else
        proc.DIV) := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · simpa using cspF_trans_left_eq cspF_Ext_choice_idem cspF_reflex_eq_SKIP
  · simpa using cspF_SKIP_DIV_Ext_choice1
  · simpa using cspF_SKIP_DIV_Ext_choice2
  · simpa using cspF_trans_left_eq cspF_Ext_choice_idem cspF_reflex_eq_DIV

/-
(*********************************************************
            (SKIP or DIV |[X]| SKIP or DIV)
 *********************************************************)
-/

open Classical in
theorem cspF_SKIP_or_DIV_Parallel
    {P Q : proc p α} {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : P = (proc.SKIP : proc p α) ∨ P = proc.DIV)
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqF (P |[X]| Q) M1 M2
      (if P = (proc.SKIP : proc p α) ∧ Q = proc.SKIP then
        (proc.SKIP : proc q α)
      else
        proc.DIV) := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · simpa using cspF_Parallel_term
  · simpa using cspF_SKIP_DIV_Parallel1
  · simpa using cspF_SKIP_DIV_Parallel2
  · simpa using cspF_DIV_Parallel

/-
(*********************************************************
                  (SKIP or DIV) and Hiding
 *********************************************************)
-/

theorem cspF_SKIP_or_DIV_Hiding_step [Inhabited α]
    {Q : proc p α} {Y X : Set α} {Pf : α → proc p α} {M : p → domFType α}
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqF (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] Q) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] Q) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) := by
  rcases hQ with rfl | rfl
  · exact cspF_SKIP_Hiding_step
  · exact cspF_DIV_Hiding_step

/-
(*********************************************************
                  SKIP or DIV |. Suc n
 *********************************************************)
-/

open Classical in
theorem cspF_SKIP_or_DIV_Depth_rest
    {Q : proc p α} {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α}
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqF (Q |. Nat.succ n) M1 M2
      (if Q = (proc.SKIP : proc p α) then (proc.SKIP : proc q α) else proc.DIV) := by
  rcases hQ with rfl | rfl
  · simpa using (cspF_SKIP_Depth_rest (n := n) (M1 := M1) (M2 := M2))
  · simpa using (cspF_DIV_Depth_rest (n := Nat.succ n) (M1 := M1) (M2 := M2))

/-
(*********************************************************
                    P [+] (SKIP or DIV)
 *********************************************************)
-/

theorem cspF_Ext_choice_SKIP_or_DIV_resolve
    {P Q : proc p α} {M : p → domFType α}
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqF (P [+] Q) M M (P [> Q) := by
  rcases hQ with rfl | rfl
  · exact cspF_Ext_choice_SKIP_resolve
  · exact cspF_Ext_choice_DIV_resolve

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV` is represented by
   `cspF_SKIP_or_DIV_Ext_choice`, `cspF_SKIP_or_DIV_Parallel`,
   `cspF_SKIP_or_DIV_Hiding_step`, and `cspF_SKIP_or_DIV_Depth_rest`.

   The resolve theorem is represented separately by
   `cspF_Ext_choice_SKIP_or_DIV_resolve`. -/

end
