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
  simp [Alpha_parallel_def]
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

axiom cspF_Alpha_parallel_assoc
    {P1 P2 P3 : proc p α} {X1 X2 X3 : Set α} {M : p → domFType α} :
    eqF (((P1 |[X1, X2]| P2) |[X1 ∪ X2, X3]| P3)) M M
      (P1 |[X1, X2 ∪ X3]| (P2 |[X2, X3]| P3))

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
