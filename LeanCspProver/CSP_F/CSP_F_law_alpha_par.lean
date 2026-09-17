           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_op_alpha_par
import LeanCspProver.CSP_F.CSP_F_law_decompo
import LeanCspProver.CSP_F.CSP_F_law_SKIP
import LeanCspProver.CSP_T.CSP_T_law_alpha_par
import LeanCspProver.CSP_F.CSP_F_simp

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `UnionT` and `InterT`.             -/
/-                                                                     -/
/-  Lean has no direct analogue of these Isabelle simp rules, so there -/
/-  is nothing to disable or re-enable here.                           -/

/-
(*****************************************************************

         1. associativity of |[X,Y]|
         2. commutativity of |[X,Y]|
         3. monotonicity of |[X,Y]|
         4.

 *****************************************************************)
-/

/-
(*********************************************************
                        P |[X,Y]| Q
 *********************************************************)
-/

/-
(************************************
 |         SKIP and SKIP            |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_SKIP_Alpha_parallel
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) |[(∅ : Set α), (∅ : Set α)]| (proc.SKIP : proc p α))) M1 M2
      (proc.SKIP : proc q α) := by
  rw [Alpha_parallel_def, Set.compl_empty, Set.empty_inter]
  have h₁ :
      eqF
        (((proc.SKIP : proc p α) |[(Set.univ : Set α)]| (proc.SKIP : proc p α)) |[(∅ : Set α)]|
          ((proc.SKIP : proc p α) |[(Set.univ : Set α)]| (proc.SKIP : proc p α)))
        M1 M2
        (((proc.SKIP : proc q α) |[(∅ : Set α)]| (proc.SKIP : proc q α))) := by
    exact cspF_Parallel_cong rfl cspF_Parallel_term cspF_Parallel_term
  exact cspF_trans_left_eq h₁ cspF_Parallel_term

/-
(************************************
 |          associativity           |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Alpha_parallel_ass_lm1
    {X1 X2 X3 : Set α} {Ya Za Z : Set (event α)} :
    Ya ∩ Set.insert Tick (Ev '' X1) ∪
        (Za ∩ Set.insert Tick (Ev '' X2) ∪ Z ∩ Set.insert Tick (Ev '' X3)) =
      Ya ∩ Set.insert Tick (Ev '' X1) ∪
        (Za ∩ Set.insert Tick (Ev '' X2) ∪ Z ∩ Set.insert Tick (Ev '' X3)) ∩
          Set.insert Tick (Ev '' (X2 ∪ X3)) := by
  ext e
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      rcases h with ⟨_, hX2⟩ | ⟨_, hX3⟩
      · change e = Tick ∨ e ∈ Ev '' (X2 ∪ X3)
        change e = Tick ∨ e ∈ Ev '' X2 at hX2
        rcases hX2 with hTick | ⟨a, haX2, rfl⟩
        · exact Or.inl hTick
        · exact Or.inr ⟨a, Or.inl haX2, rfl⟩
      · change e = Tick ∨ e ∈ Ev '' (X2 ∪ X3)
        change e = Tick ∨ e ∈ Ev '' X3 at hX3
        rcases hX3 with hTick | ⟨a, haX3, rfl⟩
        · exact Or.inl hTick
        · exact Or.inr ⟨a, Or.inr haX3, rfl⟩
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h.1

private theorem ins_image_mono {A B : Set α} (h : A ⊆ B) :
    Set.insert Tick (Ev '' A) ⊆ Set.insert Tick (Ev '' B) := by
  intro e he
  change e = Tick ∨ e ∈ Ev '' A at he
  change e = Tick ∨ e ∈ Ev '' B
  rcases he with rfl | ⟨a, ha, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, h ha, rfl⟩

private theorem inter_ins_union {A B : Set α} {Y Z : Set (event α)} :
    ((Y ∩ Set.insert Tick (Ev '' A)) ∪ (Z ∩ Set.insert Tick (Ev '' B))) ∩
        Set.insert Tick (Ev '' (A ∪ B)) =
      (Y ∩ Set.insert Tick (Ev '' A)) ∪ (Z ∩ Set.insert Tick (Ev '' B)) := by
  refine Set.inter_eq_left.mpr ?_
  rintro e (⟨-, he⟩ | ⟨-, he⟩)
  · exact ins_image_mono Set.subset_union_left he
  · exact ins_image_mono Set.subset_union_right he

theorem cspF_Alpha_parallel_assoc
    {P1 P2 P3 : proc p α} {X1 X2 X3 : Set α} {M : p → domFType α} :
    eqF (((P1 |[X1, X2]| P2) |[X1 ∪ X2, X3]| P3)) M M
      (P1 |[X1, X2 ∪ X3]| (P2 |[X2, X3]| P3)) := by
  refine cspF_eqF_of_eqT cspT_Alpha_parallel_assoc ?_
  intro s X
  have hassoc : X1 ∪ X2 ∪ X3 = X1 ∪ (X2 ∪ X3) := Set.union_assoc X1 X2 X3
  have hr1 : rest_tr (rest_tr s (X1 ∪ X2)) X1 = rest_tr s X1 :=
    (rest_tr_of_rest_tr_subset (u := s) (X := X1) (Y := X1 ∪ X2) Set.subset_union_left).2
  have hr2 : rest_tr (rest_tr s (X1 ∪ X2)) X2 = rest_tr s X2 :=
    (rest_tr_of_rest_tr_subset (u := s) (X := X2) (Y := X1 ∪ X2) Set.subset_union_right).2
  have hr2' : rest_tr (rest_tr s (X2 ∪ X3)) X2 = rest_tr s X2 :=
    (rest_tr_of_rest_tr_subset (u := s) (X := X2) (Y := X2 ∪ X3) Set.subset_union_left).2
  have hr3' : rest_tr (rest_tr s (X2 ∪ X3)) X3 = rest_tr s X3 :=
    (rest_tr_of_rest_tr_subset (u := s) (X := X3) (Y := X2 ∪ X3) Set.subset_union_right).2
  constructor
  · intro h
    rw [in_failures_Alpha_parallel] at h
    obtain ⟨u, X', hEq, Y', Z, hX, h12, h3, hsu⟩ := h
    have hu : u = s := (Prod.mk.inj hEq).1.symm
    have hXX : X' = X := (Prod.mk.inj hEq).2.symm
    rw [hu] at h12 h3 hsu
    rw [hXX] at hX
    rw [in_failures_Alpha_parallel] at h12
    obtain ⟨u2, X2', hEq2, Ya, Za, hX12, h1, h2, -⟩ := h12
    have hu2 : u2 = rest_tr s (X1 ∪ X2) := (Prod.mk.inj hEq2).1.symm
    have hYv : X2' = Y' := (Prod.mk.inj hEq2).2.symm
    rw [hu2, hr1] at h1
    rw [hu2, hr2] at h2
    rw [hYv] at hX12
    rw [in_failures_Alpha_parallel]
    refine ⟨s, X, rfl, Ya,
      (Za ∩ Set.insert Tick (Ev '' X2)) ∪ (Z ∩ Set.insert Tick (Ev '' X3)), ?_, h1, ?_,
      by rw [← hassoc]; exact hsu⟩
    · rw [← hassoc, hX, hX12, Set.union_assoc]
      exact cspF_Alpha_parallel_ass_lm1
    · rw [in_failures_Alpha_parallel]
      exact ⟨rest_tr s (X2 ∪ X3),
        (Za ∩ Set.insert Tick (Ev '' X2)) ∪ (Z ∩ Set.insert Tick (Ev '' X3)), rfl, Za, Z,
        inter_ins_union, by rw [hr2']; exact h2, by rw [hr3']; exact h3,
        rest_tr_subset_event⟩
  · intro h
    rw [in_failures_Alpha_parallel] at h
    obtain ⟨u, X', hEq, Y, Z', hX, h1, h23, hsu⟩ := h
    have hu : u = s := (Prod.mk.inj hEq).1.symm
    have hXX : X' = X := (Prod.mk.inj hEq).2.symm
    rw [hu] at h1 h23 hsu
    rw [hXX] at hX
    rw [in_failures_Alpha_parallel] at h23
    obtain ⟨u2, X2', hEq2, Ya', Za', hX23, h2, h3, -⟩ := h23
    have hu2 : u2 = rest_tr s (X2 ∪ X3) := (Prod.mk.inj hEq2).1.symm
    have hZv : X2' = Z' := (Prod.mk.inj hEq2).2.symm
    rw [hu2, hr2'] at h2
    rw [hu2, hr3'] at h3
    rw [hZv] at hX23
    rw [in_failures_Alpha_parallel]
    refine ⟨s, X, rfl,
      (Y ∩ Set.insert Tick (Ev '' X1)) ∪ (Ya' ∩ Set.insert Tick (Ev '' X2)), Za', ?_, ?_, h3,
      by rw [hassoc]; exact hsu⟩
    · rw [hassoc, hX, hX23, inter_ins_union, Set.union_assoc]
    · rw [in_failures_Alpha_parallel]
      exact ⟨rest_tr s (X1 ∪ X2),
        (Y ∩ Set.insert Tick (Ev '' X1)) ∪ (Ya' ∩ Set.insert Tick (Ev '' X2)), rfl, Y, Ya',
        inter_ins_union, by rw [hr1]; exact h1, by rw [hr2]; exact h2,
        rest_tr_subset_event⟩

theorem cspF_Alpha_parallel_assoc_sym
    {P1 P2 P3 : proc p α} {X1 X2 X3 : Set α} {M : p → domFType α} :
    eqF (P1 |[X1, X2 ∪ X3]| (P2 |[X2, X3]| P3)) M M
      (((P1 |[X1, X2]| P2) |[X1 ∪ X2, X3]| P3)) := by
  exact cspF_sym cspF_Alpha_parallel_assoc

/-
(************************************
 |          commutativity           |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Alpha_parallel_commut
    {P1 P2 : proc p α} {X1 X2 : Set α} {M : p → domFType α} :
    eqF (P1 |[X1, X2]| P2) M M (P2 |[X2, X1]| P1) := by
  rw [Alpha_parallel_def, Alpha_parallel_def]
  have h₁ :
      eqF
        (((P1 |[X1ᶜ]| proc.SKIP) |[X1 ∩ X2]| (P2 |[X2ᶜ]| proc.SKIP)))
        M M
        (((P2 |[X2ᶜ]| proc.SKIP) |[X1 ∩ X2]| (P1 |[X1ᶜ]| proc.SKIP))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF
        (((P2 |[X2ᶜ]| proc.SKIP) |[X1 ∩ X2]| (P1 |[X1ᶜ]| proc.SKIP)))
        M M
        (((P2 |[X2ᶜ]| proc.SKIP) |[X2 ∩ X1]| (P1 |[X1ᶜ]| proc.SKIP))) := by
    exact cspF_Parallel_cong (Set.inter_comm X1 X2) cspF_reflex_eq_P cspF_reflex_eq_P
  exact cspF_trans_left_eq h₁ h₂

/-
(************************************
 |          monotonicity            |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Alpha_parallel_mono
    {X1 X2 Y1 Y2 : Set α}
    {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : X1 = X2) (hY : Y1 = Y2)
    (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (P1 |[X1, Y1]| P2) M1 M2 (Q1 |[X2, Y2]| Q2) := by
  subst X2
  subst Y2
  rw [Alpha_parallel_def]
  exact
    cspF_Parallel_mono rfl
      (cspF_Parallel_mono rfl hP cspF_reflex_ref_SKIP)
      (cspF_Parallel_mono rfl hQ cspF_reflex_ref_SKIP)

theorem cspF_Alpha_parallel_cong
    {X1 X2 Y1 Y2 : Set α}
    {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : X1 = X2) (hY : Y1 = Y2)
    (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (P1 |[X1, Y1]| P2) M1 M2 (Q1 |[X2, Y2]| Q2) := by
  rw [cspF_eq_ref_iff] at hP hQ ⊢
  exact
    ⟨cspF_Alpha_parallel_mono hX hY hP.1 hQ.1,
      cspF_Alpha_parallel_mono hX.symm hY.symm hP.2 hQ.2⟩

/- The Isabelle theorem bundle `cspF_decompo_Alpha_parallel` is
   represented by `cspF_Alpha_parallel_mono` and
   `cspF_Alpha_parallel_cong`. -/

end
