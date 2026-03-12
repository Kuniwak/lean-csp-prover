           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_SKIP
import LeanCspProver.CSP_T.CSP_T_law_DIV

open Function
open SumType
open event

noncomputable section

/-
(*********************************************************
                   (SKIP [+] DIV)
 *********************************************************)
-/

theorem cspT_SKIP_DIV_Ext_choice1
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.SKIP : proc p α) [+] proc.DIV)) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_SKIP]
    rcases ht with ht | ht
    · exact (in_traces_SKIP (t := t) (M := M1)).1 ht
    · rw [in_traces_DIV] at ht
      subst t
      exact Or.inl rfl
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_SKIP] at ht
    rw [in_traces_Ext_choice]
    exact Or.inl ((in_traces_SKIP (t := t) (M := M1)).2 ht)

theorem cspT_SKIP_DIV_Ext_choice2
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.DIV : proc p α) [+] proc.SKIP)) M1 M2 (proc.SKIP : proc q α) := by
  have h₁ :
      eqT (((proc.DIV : proc p α) [+] proc.SKIP)) M1 M1
        (((proc.SKIP : proc p α) [+] proc.DIV)) :=
    cspT_Ext_choice_commut
  have h₂ :
      eqT (((proc.SKIP : proc p α) [+] proc.DIV)) M1 M2 (proc.SKIP : proc q α) :=
    cspT_SKIP_DIV_Ext_choice1
  exact cspT_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Ext_choice` is represented by
   `cspT_SKIP_DIV_Ext_choice1` and `cspT_SKIP_DIV_Ext_choice2`. -/

/-
(*********************************************************
                    SKIP |[X]| DIV
 *********************************************************)
-/

theorem cspT_SKIP_DIV_Parallel1
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.SKIP : proc p α) |[X]| proc.DIV)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Parallel] at ht
    rcases ht with ⟨s, u, hpar, hs, hu⟩
    rw [in_traces_SKIP] at hs
    rw [in_traces_DIV] at hu
    subst u
    rcases hs with rfl | rfl
    · exact (in_traces_DIV (t := t) (M := M2)).2 ((par_tr_nil_right.mp hpar).1)
    · exact False.elim (par_tr_Tick_nil hpar)
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Parallel]
    exact ⟨<>, <>, par_tr_nil_nil,
      (in_traces_SKIP (t := <>) (M := M1)).2 (Or.inl rfl),
      (in_traces_DIV (t := <>) (M := M1)).2 rfl⟩

theorem cspT_SKIP_DIV_Parallel2
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.DIV : proc p α) |[X]| proc.SKIP)) M1 M2 (proc.DIV : proc q α) := by
  have h₁ :
      eqT (((proc.DIV : proc p α) |[X]| proc.SKIP)) M1 M1
        (((proc.SKIP : proc p α) |[X]| proc.DIV)) :=
    cspT_Parallel_commut
  have h₂ :
      eqT (((proc.SKIP : proc p α) |[X]| proc.DIV)) M1 M2 (proc.DIV : proc q α) :=
    cspT_SKIP_DIV_Parallel1
  exact cspT_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Parallel` is represented by
   `cspT_SKIP_DIV_Parallel1`, `cspT_SKIP_DIV_Parallel2`,
   `cspT_Parallel_term`, and `cspT_DIV_Parallel`. -/

/-
(*********************************************************
                 DIV and Parallel-SKIP
 *********************************************************)
-/

/- (*** SKIP and DIV ***) -/

axiom cspT_DIV_Parallel_Ext_choice_SKIP_l
    {P : proc p α} {X : Set α} {M : p → domTType α} :
    eqT ((((P [+] proc.SKIP) |[X]| (proc.DIV : proc p α)))) M M (P |[X]| (proc.DIV : proc p α))

theorem cspT_DIV_Parallel_Ext_choice_SKIP_r
    {P : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (((proc.DIV : proc p α) |[X]| (P [+] proc.SKIP))) M M ((proc.DIV : proc p α) |[X]| P) := by
  have h₁ :
      eqT (((proc.DIV : proc p α) |[X]| (P [+] proc.SKIP))) M M
        ((((P [+] proc.SKIP) |[X]| (proc.DIV : proc p α)))) :=
    cspT_Parallel_commut
  have h₂ :
      eqT ((((P [+] proc.SKIP) |[X]| (proc.DIV : proc p α)))) M M (P |[X]| (proc.DIV : proc p α)) :=
    cspT_DIV_Parallel_Ext_choice_SKIP_l
  have h₃ :
      eqT (P |[X]| (proc.DIV : proc p α)) M M ((proc.DIV : proc p α) |[X]| P) :=
    cspT_Parallel_commut
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_DIV_Parallel_Ext_choice_SKIP` is
   represented by `cspT_DIV_Parallel_Ext_choice_SKIP_l` and
   `cspT_DIV_Parallel_Ext_choice_SKIP_r`. -/

/- The Isabelle theorem bundle `cspT_DIV_Parallel_Ext_choice` is
   represented by `cspT_DIV_Parallel_Ext_choice_SKIP_l`,
   `cspT_DIV_Parallel_Ext_choice_SKIP_r`,
   `cspT_DIV_Parallel_Ext_choice_DIV_l`, and
   `cspT_DIV_Parallel_Ext_choice_DIV_r`. -/

/-
(*********************************************************
                 SKIP and Parallel-DIV
 *********************************************************)
-/

/- (*** DIV and SKIP ***) -/

axiom cspT_SKIP_Parallel_Ext_choice_DIV_l
    {Y X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT ((((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]| proc.SKIP)) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+] proc.DIV))

theorem cspT_SKIP_Parallel_Ext_choice_DIV_r
    {Y X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.DIV))) M M
      (((proc.Ext_pre_choice (Y \ X) fun x => ((proc.SKIP : proc p α) |[X]| Pf x)) [+]
          proc.DIV)) := by
  have h₁ :
      eqT (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.DIV))) M M
        ((((proc.Ext_pre_choice Y Pf) [+] proc.DIV) |[X]| (proc.SKIP : proc p α))) :=
    cspT_Parallel_commut
  have h₂ :
      eqT ((((proc.Ext_pre_choice Y Pf) [+] proc.DIV) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) fun x => (Pf x |[X]| (proc.SKIP : proc p α))) [+]
            proc.DIV)) :=
    cspT_SKIP_Parallel_Ext_choice_DIV_l
  have h₃₁ :
      eqT (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) := by
    apply cspT_Ext_pre_choice_cong rfl
    intro a ha
    exact cspT_Parallel_commut
  have h₃ :
      eqT
        (((proc.Ext_pre_choice (Y \ X) fun x => (Pf x |[X]| (proc.SKIP : proc p α))) [+]
            proc.DIV)) M M
        (((proc.Ext_pre_choice (Y \ X) fun x => ((proc.SKIP : proc p α) |[X]| Pf x)) [+]
            proc.DIV)) := by
    exact cspT_Ext_choice_cong h₃₁ cspT_reflex_eq_DIV
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_SKIP_Parallel_Ext_choice_DIV` is
   represented by `cspT_SKIP_Parallel_Ext_choice_DIV_l` and
   `cspT_SKIP_Parallel_Ext_choice_DIV_r`. -/

/- The Isabelle theorem bundle `cspT_SKIP_Parallel_Ext_choice` is
   represented by `cspT_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspT_SKIP_Parallel_Ext_choice_SKIP_r`,
   `cspT_SKIP_Parallel_Ext_choice_DIV_l`, and
   `cspT_SKIP_Parallel_Ext_choice_DIV_r`. -/

/-
(*---------------------------------------------*
 |                 SKIP , DIV                  |
 *---------------------------------------------*)
-/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Parallel_step` is represented
   by `cspT_Parallel_preterm_l`, `cspT_Parallel_preterm_r`,
   `cspT_DIV_Parallel_step_l`, and `cspT_DIV_Parallel_step_r`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Parallel_Ext_choice` is
   represented by `cspT_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspT_SKIP_Parallel_Ext_choice_SKIP_r`,
   `cspT_SKIP_Parallel_Ext_choice_DIV_l`,
   `cspT_SKIP_Parallel_Ext_choice_DIV_r`,
   `cspT_DIV_Parallel_Ext_choice_SKIP_l`,
   `cspT_DIV_Parallel_Ext_choice_SKIP_r`,
   `cspT_DIV_Parallel_Ext_choice_DIV_l`, and
   `cspT_DIV_Parallel_Ext_choice_DIV_r`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Hiding_Id` is represented by
   `cspT_SKIP_Hiding_Id` and `cspT_DIV_Hiding_Id`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Hiding_step` is represented by
   `cspT_DIV_Hiding_step` and `cspT_SKIP_Hiding_step`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Renaming_Id` is represented by
   `cspT_SKIP_Renaming_Id` and `cspT_DIV_Renaming_Id`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Seq_compo` is represented by
   `cspT_Seq_compo_unit_l`, `cspT_Seq_compo_unit_r`,
   and `cspT_DIV_Seq_compo`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Seq_compo_step` is represented
   by `cspT_SKIP_Seq_compo_step` and `cspT_DIV_Seq_compo_step`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Depth_rest` is represented by
   `cspT_SKIP_Depth_rest` and `cspT_DIV_Depth_rest`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV` is represented by
   `cspT_Parallel_preterm_l`, `cspT_Parallel_preterm_r`,
   `cspT_SKIP_DIV_Ext_choice1`, `cspT_SKIP_DIV_Ext_choice2`,
   `cspT_SKIP_DIV_Parallel1`, `cspT_SKIP_DIV_Parallel2`,
   `cspT_Parallel_term`, `cspT_DIV_Parallel`,
   `cspT_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspT_SKIP_Parallel_Ext_choice_SKIP_r`,
   `cspT_SKIP_Parallel_Ext_choice_DIV_l`,
   `cspT_SKIP_Parallel_Ext_choice_DIV_r`,
   `cspT_DIV_Parallel_Ext_choice_SKIP_l`,
   `cspT_DIV_Parallel_Ext_choice_SKIP_r`,
   `cspT_DIV_Parallel_Ext_choice_DIV_l`,
   `cspT_DIV_Parallel_Ext_choice_DIV_r`,
   `cspT_SKIP_Hiding_Id`, `cspT_DIV_Hiding_Id`,
   `cspT_DIV_Hiding_step`, `cspT_SKIP_Hiding_step`,
   `cspT_SKIP_Renaming_Id`, `cspT_DIV_Renaming_Id`,
   `cspT_Seq_compo_unit_l`, `cspT_Seq_compo_unit_r`,
   `cspT_DIV_Seq_compo`, `cspT_SKIP_Seq_compo_step`,
   `cspT_DIV_Seq_compo_step`, `cspT_SKIP_Depth_rest`,
   and `cspT_DIV_Depth_rest`. -/

/- (*** resolve ***) -/

/- The Isabelle theorem bundle `cspT_Ext_choice_SKIP_DIV_resolve` is
   represented by `cspT_Ext_choice_SKIP_resolve` and
   `cspT_Ext_choice_DIV_resolve`. -/

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
theorem cspT_SKIP_or_DIV_Ext_choice
    {P Q : proc p α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : P = (proc.SKIP : proc p α) ∨ P = proc.DIV)
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqT (P [+] Q) M1 M2
      (if (P = (proc.SKIP : proc p α) ∨ Q = proc.SKIP) then
        (proc.SKIP : proc q α)
      else proc.DIV) := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · simpa using cspT_trans_left_eq cspT_Ext_choice_idem cspT_reflex_eq_SKIP
  · simpa using cspT_SKIP_DIV_Ext_choice1 (M1 := M1) (M2 := M2)
  · simpa using cspT_SKIP_DIV_Ext_choice2 (M1 := M1) (M2 := M2)
  · simpa using cspT_trans_left_eq cspT_Ext_choice_idem cspT_reflex_eq_DIV

/-
(*********************************************************
            (SKIP or DIV |[X]| SKIP or DIV)
 *********************************************************)
-/

open Classical in
theorem cspT_SKIP_or_DIV_Parallel
    {P Q : proc p α} {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : P = (proc.SKIP : proc p α) ∨ P = proc.DIV)
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqT (P |[X]| Q) M1 M2
      (if P = (proc.SKIP : proc p α) ∧ Q = proc.SKIP then
        (proc.SKIP : proc q α)
      else
        proc.DIV) := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · simpa using cspT_Parallel_term
  · simpa using cspT_SKIP_DIV_Parallel1
  · simpa using cspT_SKIP_DIV_Parallel2
  · simpa using cspT_DIV_Parallel

/-
(*********************************************************
                  (SKIP or DIV) and Hiding
 *********************************************************)
-/

theorem cspT_SKIP_or_DIV_Hiding_step [Inhabited α]
    {Q : proc p α} {Y X : Set α} {Pf : α → proc p α} {M : p → domTType α}
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqT (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] Q) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] Q) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) := by
  rcases hQ with rfl | rfl
  · exact cspT_SKIP_Hiding_step
  · exact cspT_DIV_Hiding_step

/-
(*********************************************************
                  SKIP or DIV |. Suc n
 *********************************************************)
-/

open Classical in
theorem cspT_SKIP_or_DIV_Depth_rest
    {Q : proc p α} {n : Nat} {M1 : p → domTType α} {M2 : q → domTType α}
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqT (Q |. Nat.succ n) M1 M2
      (if Q = (proc.SKIP : proc p α) then (proc.SKIP : proc q α) else proc.DIV) := by
  rcases hQ with rfl | rfl
  · simpa using (cspT_SKIP_Depth_rest (n := n) (M1 := M1) (M2 := M2))
  · simpa using (cspT_DIV_Depth_rest (n := Nat.succ n) (M1 := M1) (M2 := M2))

/-
(*********************************************************
                    P [+] (SKIP or DIV)
 *********************************************************)
-/

theorem cspT_Ext_choice_SKIP_or_DIV_resolve
    {P Q : proc p α} {M : p → domTType α}
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqT (P [+] Q) M M (P [> Q) := by
  rcases hQ with rfl | rfl
  · exact cspT_Ext_choice_SKIP_resolve
  · exact cspT_Ext_choice_DIV_resolve

/- The Isabelle theorem bundle `cspT_SKIP_or_DIV` is represented by
   `cspT_SKIP_or_DIV_Ext_choice`, `cspT_SKIP_or_DIV_Parallel`,
   `cspT_SKIP_or_DIV_Hiding_step`, and `cspT_SKIP_or_DIV_Depth_rest`.

   The resolve theorem is represented separately by
   `cspT_Ext_choice_SKIP_or_DIV_resolve`. -/

end
