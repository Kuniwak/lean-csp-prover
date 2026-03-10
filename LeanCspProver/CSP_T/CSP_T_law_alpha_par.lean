           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_op_alpha_par
import LeanCspProver.CSP_T.CSP_T_law_decompo

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Union` / `Inter` image   -/
/-  simp rules, so there is nothing to disable or re-enable here.       -/

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

theorem cspT_SKIP_Alpha_parallel
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.SKIP : proc p α) |[(∅ : Set α), (∅ : Set α)]| (proc.SKIP : proc p α))) M1 M2
      (proc.SKIP : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Alpha_parallel] at hu
    rcases hu with ⟨_, _, huTick⟩
    have huTick' : sett u ⊆ ({event.Tick} : Set (event α)) := by
      intro e he
      have hem : e ∈ Set.insert event.Tick (∅ : Set (event α)) := by
        simpa using huTick he
      change e = event.Tick ∨ e ∈ (∅ : Set (event α)) at hem
      rcases hem with he' | he'
      · exact he'
      · simpa using he'
    rw [in_traces_SKIP]
    exact sett_subset_Tick.mp huTick'
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_SKIP] at hu
    rw [in_traces_Alpha_parallel]
    refine ⟨?_, ?_, ?_⟩
    · rw [in_traces_SKIP]
      rcases hu with rfl | rfl <;> simp
    · rw [in_traces_SKIP]
      rcases hu with rfl | rfl <;> simp
    · have huTick : sett u ⊆ ({event.Tick} : Set (event α)) := sett_subset_Tick.mpr hu
      intro e he
      have hem : e ∈ ({event.Tick} : Set (event α)) := huTick he
      have heq : e = event.Tick := by
        simpa using hem
      have hem' : e ∈ Set.insert event.Tick (∅ : Set (event α)) := by
        change e = event.Tick ∨ e ∈ (∅ : Set (event α))
        exact Or.inl heq
      simpa using hem'

/-
(************************************
 |          associativity           |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Alpha_parallel_assoc
    {P1 P2 P3 : proc p α} {X1 X2 X3 : Set α} {M : p → domTType α} :
    eqT (((P1 |[X1, X2]| P2) |[X1 ∪ X2, X3]| P3)) M M
      (P1 |[X1, X2 ∪ X3]| (P2 |[X2, X3]| P3)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Alpha_parallel] at hu
    rcases hu with ⟨h12, h3, huXYZ⟩
    rw [in_traces_Alpha_parallel] at h12
    rcases h12 with ⟨h1, h2, _hu12⟩
    have hrest1 :
        rest_tr (rest_tr u (X1 ∪ X2)) X1 = rest_tr u X1 :=
      (rest_tr_of_rest_tr_subset (u := u) (X := X1) (Y := X1 ∪ X2) (by
        intro a ha
        exact Or.inl ha)).2
    have hrest2 :
        rest_tr (rest_tr u (X1 ∪ X2)) X2 = rest_tr u X2 :=
      (rest_tr_of_rest_tr_subset (u := u) (X := X2) (Y := X1 ∪ X2) (by
        intro a ha
        exact Or.inr ha)).2
    have h23 :
        (rest_tr u (X2 ∪ X3)) :t traces (P2 |[X2, X3]| P3) M := by
      rw [in_traces_Alpha_parallel]
      refine ⟨?_, ?_, rest_tr_subset_event⟩
      · have hrest2' :
            rest_tr (rest_tr u (X2 ∪ X3)) X2 = rest_tr u X2 :=
          (rest_tr_of_rest_tr_subset (u := u) (X := X2) (Y := X2 ∪ X3) (by
            intro a ha
            exact Or.inl ha)).2
        simpa [hrest2, hrest2'] using h2
      · have hrest3 :
            rest_tr (rest_tr u (X2 ∪ X3)) X3 = rest_tr u X3 :=
          (rest_tr_of_rest_tr_subset (u := u) (X := X3) (Y := X2 ∪ X3) (by
            intro a ha
            exact Or.inr ha)).2
        simpa [hrest3] using h3
    rw [in_traces_Alpha_parallel]
    refine ⟨?_, h23, ?_⟩
    · simpa [hrest1] using h1
    · simpa [Set.union_assoc] using huXYZ
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Alpha_parallel] at hu
    rcases hu with ⟨h1, h23, huXYZ⟩
    rw [in_traces_Alpha_parallel] at h23
    rcases h23 with ⟨h2, h3, _hu23⟩
    have hrest1 :
        rest_tr (rest_tr u (X1 ∪ (X2 ∪ X3))) X1 = rest_tr u X1 :=
      (rest_tr_of_rest_tr_subset (u := u) (X := X1) (Y := X1 ∪ (X2 ∪ X3)) (by
        intro a ha
        exact Or.inl ha)).2
    have h12 :
        (rest_tr u (X1 ∪ X2)) :t traces (P1 |[X1, X2]| P2) M := by
      rw [in_traces_Alpha_parallel]
      refine ⟨?_, ?_, rest_tr_subset_event⟩
      · have hrest1' :
            rest_tr (rest_tr u (X1 ∪ X2)) X1 = rest_tr u X1 :=
          (rest_tr_of_rest_tr_subset (u := u) (X := X1) (Y := X1 ∪ X2) (by
            intro a ha
            exact Or.inl ha)).2
        simpa [hrest1, hrest1'] using h1
      · have hrest2 :
            rest_tr (rest_tr u (X1 ∪ X2)) X2 = rest_tr u X2 :=
          (rest_tr_of_rest_tr_subset (u := u) (X := X2) (Y := X1 ∪ X2) (by
            intro a ha
            exact Or.inr ha)).2
        have hrest2' :
            rest_tr (rest_tr u (X2 ∪ X3)) X2 = rest_tr u X2 :=
          (rest_tr_of_rest_tr_subset (u := u) (X := X2) (Y := X2 ∪ X3) (by
            intro a ha
            exact Or.inl ha)).2
        simpa [hrest2, hrest2'] using h2
    rw [in_traces_Alpha_parallel]
    refine ⟨h12, ?_, ?_⟩
    · have hrest3 :
          rest_tr (rest_tr u (X1 ∪ (X2 ∪ X3))) X3 = rest_tr u X3 :=
        (rest_tr_of_rest_tr_subset (u := u) (X := X3) (Y := X1 ∪ (X2 ∪ X3)) (by
          intro a ha
          exact Or.inr (Or.inr ha))).2
      have hrest3' :
          rest_tr (rest_tr u (X2 ∪ X3)) X3 = rest_tr u X3 :=
        (rest_tr_of_rest_tr_subset (u := u) (X := X3) (Y := X2 ∪ X3) (by
          intro a ha
          exact Or.inr ha)).2
      simpa [hrest3, hrest3'] using h3
    · simpa [Set.union_assoc] using huXYZ

theorem cspT_Alpha_parallel_assoc_sym
    {P1 P2 P3 : proc p α} {X1 X2 X3 : Set α} {M : p → domTType α} :
    eqT (P1 |[X1, X2 ∪ X3]| (P2 |[X2, X3]| P3)) M M
      (((P1 |[X1, X2]| P2) |[X1 ∪ X2, X3]| P3)) := by
  exact cspT_sym cspT_Alpha_parallel_assoc

/-
(************************************
 |          commutativity           |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Alpha_parallel_commut
    {P1 : proc p α} {P2 : proc p α} {X1 X2 : Set α} {M : p → domTType α} :
    eqT (P1 |[X1, X2]| P2) M M (P2 |[X2, X1]| P1) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Alpha_parallel] at hu ⊢
    rcases hu with ⟨h1, h2, huXY⟩
    exact ⟨h2, h1, by simpa [Set.union_comm] using huXY⟩
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Alpha_parallel] at hu ⊢
    rcases hu with ⟨h2, h1, huYX⟩
    exact ⟨h1, h2, by simpa [Set.union_comm] using huYX⟩

/-
(************************************
 |          monotonicity            |
 ************************************)
-/

/- (*------------------*
 |      csp law M   |
 *------------------*) -/

theorem cspT_Alpha_parallel_mono
    {X1 X2 Y1 Y2 : Set α}
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : X1 = X2) (hY : Y1 = Y2) (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (P1 |[X1, Y1]| P2) M1 M2 (Q1 |[X2, Y2]| Q2) := by
  subst X2
  subst Y2
  rw [Alpha_parallel_def]
  exact
    cspT_Parallel_mono rfl
      (cspT_Parallel_mono rfl hP cspT_reflex_ref_SKIP)
      (cspT_Parallel_mono rfl hQ cspT_reflex_ref_SKIP)

theorem cspT_Alpha_parallel_cong
    {X1 X2 Y1 Y2 : Set α}
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : X1 = X2) (hY : Y1 = Y2) (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (P1 |[X1, Y1]| P2) M1 M2 (Q1 |[X2, Y2]| Q2) := by
  rw [cspT_eq_ref_iff] at hP hQ ⊢
  exact
    ⟨cspT_Alpha_parallel_mono hX hY hP.1 hQ.1,
      cspT_Alpha_parallel_mono hX.symm hY.symm hP.2 hQ.2⟩

/- The Isabelle theorem bundle `cspT_decompo_Alpha_parallel` is
   represented by `cspT_Alpha_parallel_mono` and
   `cspT_Alpha_parallel_cong`. -/

end
