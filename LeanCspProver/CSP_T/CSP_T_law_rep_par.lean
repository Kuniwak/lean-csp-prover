           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_alpha_par
import LeanCspProver.CSP_T.CSP_T_op_rep_par
import LeanCspProver.CSP_T.CSP_T_simp

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq` or         -/
/-  `Inf_image_eq`, so there is nothing to disable or re-enable here.   -/

/-
(*****************************************************************

         1. associativity of [||]:I
         2. commutativity of [||]:I
         3.
         4.

 *****************************************************************)
-/

/-
(*****************************************************
   replace an index set with another equal index set
 *****************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

private theorem set_map3 {β γ : Type _} (g : β → γ) (l : List β) :
    _root_.set (l.map g) = g '' _root_.set l := by
  ext x
  simp [_root_.set]

private theorem snd_subset_sUnion {I : Set ι} {PXf : ι → proc p α × Set α} {i : ι} (hi : i ∈ I) :
    Prod.snd (PXf i) ⊆ Set.sUnion (Prod.snd '' (PXf '' I)) :=
  fun _ ha => ⟨Prod.snd (PXf i), ⟨PXf i, ⟨i, hi, rfl⟩, rfl⟩, ha⟩

theorem cspT_Rep_parallel_index_eq
    {I1 : Set ι} {I2 : Set κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {M : p → domTType α} :
    I1.Finite →
      (∃ f : ι → κ, I2 = f '' I1 ∧ Set.InjOn f I1 ∧
        (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i)) →
        eqT (Rep_parallel I1 PXf1) M M (Rep_parallel I2 PXf2) := by
  rintro hfin ⟨f, rfl, -, hPX⟩
  by_cases hI1 : I1 = ∅
  · subst hI1
    rw [Set.image_empty, Rep_parallel_empty, Rep_parallel_empty]
    rfl
  · have hI2 : f '' I1 ≠ ∅ := by
      intro hEmpty
      apply hI1
      rw [Set.eq_empty_iff_forall_notMem]
      intro i hi
      have : f i ∈ f '' I1 := ⟨i, hi, rfl⟩
      rw [hEmpty] at this
      exact this
    have hfin2 : (f '' I1).Finite := hfin.image f
    have hUnion :
        Set.sUnion (Prod.snd '' (PXf2 '' (f '' I1))) =
          Set.sUnion (Prod.snd '' (PXf1 '' I1)) := Union_index_fun hPX
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro u hu
      rw [in_traces_Rep_parallel hI1 hfin] at hu
      rw [in_traces_Rep_parallel hI2 hfin2]
      refine ⟨by rw [hUnion]; exact hu.1, ?_⟩
      rintro j ⟨i, hi, rfl⟩
      rw [hPX i hi]
      exact hu.2 i hi
    · rw [subdomT_iff]
      intro u hu
      rw [in_traces_Rep_parallel hI2 hfin2] at hu
      rw [in_traces_Rep_parallel hI1 hfin]
      refine ⟨by rw [← hUnion]; exact hu.1, ?_⟩
      intro i hi
      have hval := hu.2 (f i) ⟨i, hi, rfl⟩
      rwa [hPX i hi] at hval

/-
(*********************************************************
                [||]:I PXf ==> [||] PXs
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Index_to_Inductive_parallel
    {I : Set ι} {Is : List ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I.Finite → isListOf Is I →
      eqT (Rep_parallel I PXf) M M (Inductive_parallel (List.map PXf Is)) := by
  intro hfin hIs
  by_cases hI : I = ∅
  · subst hI
    have hnil : Is = [] := isListOf_emptyset_to_nil.mp hIs
    subst hnil
    rw [Rep_parallel_empty]
    rfl
  · have hne : Is ≠ [] := isListOf_nonemptyset hI hIs
    have hmapne : List.map PXf Is ≠ [] := by simpa using hne
    have hset : _root_.set (List.map PXf Is) = PXf '' I := by
      rw [set_map3, isListOf_set_eq hIs]
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro u hu
      rw [in_traces_Rep_parallel hI hfin] at hu
      rw [in_traces_Inductive_parallel hmapne, hset, to_index_style_T]
      exact hu
    · rw [subdomT_iff]
      intro u hu
      rw [in_traces_Inductive_parallel hmapne, hset, to_index_style_T] at hu
      rw [in_traces_Rep_parallel hI hfin]
      exact hu

/-
(************************************
 |       [||]:I PXf and SKIP        |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_SKIP_Rep_parallel_right
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I.Finite →
      eqT
        ((Rep_parallel I PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' I)),
          (∅ : Set α)]| (proc.SKIP : proc p α))
        M M
        (Rep_parallel I PXf) := by
  intro hfin
  by_cases hI : I = ∅
  · subst hI
    rw [Rep_parallel_empty, Set.image_empty, Set.image_empty, Set.sUnion_empty]
    exact cspT_SKIP_Alpha_parallel
  · rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro u hu
      rw [in_traces_Alpha_parallel] at hu
      obtain ⟨h1, -, h3⟩ := hu
      rw [in_traces_Rep_parallel hI hfin] at h1
      rw [in_traces_Rep_parallel hI hfin]
      refine ⟨by simpa using h3, ?_⟩
      intro i hi
      have hval := h1.2 i hi
      rwa [(rest_tr_of_rest_tr_subset (snd_subset_sUnion hi)).2] at hval
    · rw [subdomT_iff]
      intro u hu
      rw [in_traces_Rep_parallel hI hfin] at hu
      rw [in_traces_Alpha_parallel]
      refine ⟨?_, ?_, by simpa using hu.1⟩
      · rw [in_traces_Rep_parallel hI hfin]
        refine ⟨rest_tr_subset_event, ?_⟩
        intro i hi
        rw [(rest_tr_of_rest_tr_subset (snd_subset_sUnion hi)).2]
        exact hu.2 i hi
      · rcases rest_tr_empty (u := u) with h | h <;> rw [h] <;>
          exact in_traces_SKIP.mpr (by simp)

/-
(************************************
 |        SKIP and [||]:I PXf       |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_SKIP_Rep_parallel_left
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I.Finite →
      eqT
        (((proc.SKIP : proc p α) |[
          (∅ : Set α),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))
        M M
        (Rep_parallel I PXf) := by
  intro hI
  exact
    cspT_trans_left_eq
      (cspT_Alpha_parallel_commut
        (P1 := (proc.SKIP : proc p α))
        (P2 := Rep_parallel I PXf)
        (X1 := (∅ : Set α))
        (X2 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (M := M))
      (cspT_SKIP_Rep_parallel_right (I := I) (PXf := PXf) (M := M) hI)

/- The Isabelle theorem bundle `cspT_SKIP_Rep_parallel` is represented by
   `cspT_SKIP_Rep_parallel_left` and `cspT_SKIP_Rep_parallel_right`. -/

/-
(************************************
 |          associativity           |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Rep_parallel_assoc
    {I1 I2 : Set ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I1 ∩ I2 = ∅ → I1.Finite → I2.Finite →
      eqT
        (Rep_parallel (I1 ∪ I2) PXf) M M
        ((Rep_parallel I1 PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' I1)),
          Set.sUnion (Prod.snd '' (PXf '' I2))]| Rep_parallel I2 PXf) := by
  intro _ hfin1 hfin2
  by_cases hI1 : I1 = ∅
  · subst hI1
    rw [Set.empty_union, Rep_parallel_empty, Set.image_empty, Set.image_empty,
      Set.sUnion_empty]
    exact cspT_sym (cspT_SKIP_Rep_parallel_left hfin2)
  · by_cases hI2 : I2 = ∅
    · subst hI2
      rw [Set.union_empty, Rep_parallel_empty, Set.image_empty, Set.image_empty,
        Set.sUnion_empty]
      exact cspT_sym (cspT_SKIP_Rep_parallel_right hfin1)
    · have hIU : I1 ∪ I2 ≠ ∅ := by
        intro hEmpty
        exact hI1 (Set.eq_empty_iff_forall_notMem.mpr
          fun i hi => by
            have : i ∈ I1 ∪ I2 := Or.inl hi
            rw [hEmpty] at this
            exact this)
      rw [cspT_eqT_semantics]
      apply le_antisymm
      · rw [subdomT_iff]
        intro u hu
        rw [in_traces_Rep_parallel hIU (hfin1.union hfin2), Union_snd_Un] at hu
        rw [in_traces_Alpha_parallel]
        refine ⟨?_, ?_, hu.1⟩
        · rw [in_traces_Rep_parallel hI1 hfin1]
          refine ⟨rest_tr_subset_event, ?_⟩
          intro i hi
          rw [(rest_tr_of_rest_tr_subset (snd_subset_sUnion hi)).2]
          exact hu.2 i (Or.inl hi)
        · rw [in_traces_Rep_parallel hI2 hfin2]
          refine ⟨rest_tr_subset_event, ?_⟩
          intro i hi
          rw [(rest_tr_of_rest_tr_subset (snd_subset_sUnion hi)).2]
          exact hu.2 i (Or.inr hi)
      · rw [subdomT_iff]
        intro u hu
        rw [in_traces_Alpha_parallel] at hu
        obtain ⟨h1, h2, h3⟩ := hu
        rw [in_traces_Rep_parallel hI1 hfin1] at h1
        rw [in_traces_Rep_parallel hI2 hfin2] at h2
        rw [in_traces_Rep_parallel hIU (hfin1.union hfin2), Union_snd_Un]
        refine ⟨h3, ?_⟩
        rintro i (hi | hi)
        · have hval := h1.2 i hi
          rwa [(rest_tr_of_rest_tr_subset (snd_subset_sUnion hi)).2] at hval
        · have hval := h2.2 i hi
          rwa [(rest_tr_of_rest_tr_subset (snd_subset_sUnion hi)).2] at hval

/-
(************************************
 |             induct               |
 ************************************)
-/

/- (*------------------*
 |     csp law      |
 |   (derivable)    |
 *------------------*) -/

theorem cspT_Rep_parallel_induct
    {I : Set ι} {i : ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I.Finite → i ∉ I →
      eqT
        (Rep_parallel (Set.insert i I) PXf) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
  intro hI hiI
  have hDisj : ({i} : Set ι) ∩ I = ∅ := by
    ext x
    simp [hiI]
  have hAssoc :
      eqT
        (Rep_parallel (({i} : Set ι) ∪ I) PXf) M M
        ((Rep_parallel ({i} : Set ι) PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' ({i} : Set ι))),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
    exact cspT_Rep_parallel_assoc (I1 := ({i} : Set ι)) (I2 := I) (PXf := PXf) (M := M)
      hDisj (Set.toFinite {i}) hI
  have hAssoc' :
      eqT
        ((Rep_parallel ({i} : Set ι) PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' ({i} : Set ι))),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]|
          (((proc.SKIP : proc p α) |[
            (∅ : Set α),
            Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))) := by
    simpa [Rep_parallel_one, Set.union_comm, Set.union_left_comm, Set.union_assoc]
      using
        (cspT_Alpha_parallel_assoc
          (P1 := Prod.fst (PXf i))
          (P2 := (proc.SKIP : proc p α))
          (P3 := Rep_parallel I PXf)
          (X1 := Prod.snd (PXf i))
          (X2 := (∅ : Set α))
          (X3 := Set.sUnion (Prod.snd '' (PXf '' I)))
          (M := M))
  have hCong :
      eqT
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]|
          (((proc.SKIP : proc p α) |[
            (∅ : Set α),
            Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
    exact
      cspT_Alpha_parallel_cong
        (X1 := Prod.snd (PXf i))
        (X2 := Prod.snd (PXf i))
        (Y1 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (Y2 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (P1 := Prod.fst (PXf i))
        (Q1 := Prod.fst (PXf i))
        (P2 := ((proc.SKIP : proc p α) |[
          (∅ : Set α),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))
        (Q2 := Rep_parallel I PXf)
        (M1 := M)
        (M2 := M)
        rfl
        rfl
        cspT_reflex_eq_P
        (cspT_SKIP_Rep_parallel_left (I := I) (PXf := PXf) (M := M) hI)
  exact
    cspT_trans_left_eq
      (by simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using hAssoc)
      (cspT_trans_left_eq hAssoc' hCong)

end
