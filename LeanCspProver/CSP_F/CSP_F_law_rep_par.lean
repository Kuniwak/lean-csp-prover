           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_alpha_par
import LeanCspProver.CSP_F.CSP_F_op_rep_par
import LeanCspProver.CSP_T.CSP_T_law_rep_par
import LeanCspProver.CSP_F.CSP_F_simp

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `UnionT` and `InterT`.             -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq` or        -/
/-  `Inf_image_eq`, so there is nothing to disable or re-enable here.  -/

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

private theorem ins_mono {A B : Set α} (h : A ⊆ B) :
    Set.insert Tick (Ev '' A) ⊆ Set.insert Tick (Ev '' B) := by
  intro e he
  rcases he with hT | ⟨a, ha, rfl⟩
  · exact Or.inl hT
  · exact Or.inr ⟨a, h ha, rfl⟩

private theorem snd_subset_sUnion' {I : Set ι} {PXf : ι → proc p α × Set α} {i : ι} (hi : i ∈ I) :
    Prod.snd (PXf i) ⊆ Set.sUnion (Prod.snd '' (PXf '' I)) :=
  fun _ ha => ⟨Prod.snd (PXf i), ⟨PXf i, ⟨i, hi, rfl⟩, rfl⟩, ha⟩

private theorem in_failures_SKIP_iff2 {s : traceType α} {W : Set (event α)}
    {M : p → domFType α} :
    ((s, W) :f failures (proc.SKIP : proc p α) M) ↔
      ((s = <> ∧ W ⊆ Evset) ∨ s = (Abs_trace [event.Tick] : traceType α)) := by
  rw [in_failures_SKIP]
  constructor
  · rintro (⟨V, hEq, hV⟩ | ⟨V, hEq⟩)
    · exact Or.inl ⟨(Prod.mk.inj hEq).1, by rw [(Prod.mk.inj hEq).2]; exact hV⟩
    · exact Or.inr (Prod.mk.inj hEq).1
  · rintro (⟨rfl, hW⟩ | rfl)
    · exact Or.inl ⟨W, rfl, hW⟩
    · exact Or.inr ⟨W, rfl⟩

theorem cspF_Rep_parallel_index_eq_lm1
    [Inhabited ι]
    {I1 : Set ι} {f : ι → κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {Yf : ι → Set (event α)} :
    Set.InjOn f I1 →
      (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i) →
        Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
          S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf1 i))))} =
        Set.sUnion {S | ∃ i : κ, i ∈ f '' I1 ∧
          S =
            Set.inter
              (Yf (inv_on I1 f i))
              (Set.insert Tick (Ev '' (Prod.snd (PXf2 i))))} := by
  intro hinj hPX
  ext e
  constructor
  · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
    refine ⟨Set.inter (Yf (inv_on I1 f (f i)))
        (Set.insert Tick (Ev '' (Prod.snd (PXf2 (f i))))), ⟨f i, ⟨i, hi, rfl⟩, rfl⟩, ?_⟩
    rw [inv_f_f_on hinj hi, hPX i hi]
    exact he
  · rintro ⟨S, ⟨j, ⟨i, hi, rfl⟩, rfl⟩, he⟩
    refine ⟨Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf1 i)))),
      ⟨i, hi, rfl⟩, ?_⟩
    rw [inv_f_f_on hinj hi, hPX i hi] at he
    exact he

theorem cspF_Rep_parallel_index_eq_lm2
    {I1 : Set ι} {f : ι → κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {Yf : κ → Set (event α)} :
    (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i) →
      Set.sUnion {S | ∃ i : κ, i ∈ f '' I1 ∧
        S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf2 i))))} =
      Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
        S = Set.inter (Yf (f i)) (Set.insert Tick (Ev '' (Prod.snd (PXf1 i))))} := by
  cspF_auto

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Rep_parallel_index_eq
    {I1 : Set ι} {I2 : Set κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {M : p → domFType α} :
    I1.Finite →
      (∃ f : ι → κ, I2 = f '' I1 ∧ Set.InjOn f I1 ∧
        (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i)) →
        eqF (Rep_parallel I1 PXf1) M M (Rep_parallel I2 PXf2) := by
  rintro hfin ⟨f, hI2, hinj, hPX⟩
  subst hI2
  by_cases hI1 : I1 = ∅
  · subst hI1
    rw [Set.image_empty, Rep_parallel_empty, Rep_parallel_empty]
    rfl
  · refine cspF_eqF_of_eqT (cspT_Rep_parallel_index_eq hfin ⟨f, rfl, hinj, hPX⟩) ?_
    obtain ⟨i0, -⟩ := Set.nonempty_iff_ne_empty.2 hI1
    haveI : Inhabited ι := ⟨i0⟩
    have hI2ne : f '' I1 ≠ ∅ := by
      intro hEmpty
      apply hI1
      rw [Set.eq_empty_iff_forall_notMem]
      intro i hi
      have hmem : f i ∈ f '' I1 := ⟨i, hi, rfl⟩
      rw [hEmpty] at hmem
      exact hmem
    have hfin2 : (f '' I1).Finite := hfin.image f
    have hUnion :
        Set.sUnion (Prod.snd '' (PXf2 '' (f '' I1))) =
          Set.sUnion (Prod.snd '' (PXf1 '' I1)) := Union_index_fun hPX
    intro s W
    rw [in_failures_Rep_parallel hI1 hfin, in_failures_Rep_parallel hI2ne hfin2, hUnion]
    constructor
    · rintro ⟨u, hsu, Z, hEq, Yf, hZ, hall⟩
      refine ⟨u, hsu, Z, hEq, fun j => Yf (inv_on I1 f j), ?_, ?_⟩
      · rw [hZ]
        exact cspF_Rep_parallel_index_eq_lm1 hinj hPX
      · rintro j ⟨i, hi, rfl⟩
        dsimp only
        rw [inv_f_f_on hinj hi, hPX i hi]
        exact hall i hi
    · rintro ⟨u, hsu, Z, hEq, Yf, hZ, hall⟩
      refine ⟨u, hsu, Z, hEq, fun i => Yf (f i), ?_, ?_⟩
      · rw [hZ]
        exact cspF_Rep_parallel_index_eq_lm2 hPX
      · intro i hi
        have hval := hall (f i) ⟨i, hi, rfl⟩
        dsimp only
        rwa [hPX i hi] at hval

/-
(*********************************************************
                [||]:I PXf ==> [||] PXs
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Index_to_Inductive_parallel
    {I : Set ι} {Is : List ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite → isListOf Is I →
      eqF (Rep_parallel I PXf) M M (Inductive_parallel (List.map PXf Is)) := by
  intro hfin hIs
  by_cases hI : I = ∅
  · subst hI
    have hnil : Is = [] := isListOf_emptyset_to_nil.mp hIs
    subst hnil
    rw [Rep_parallel_empty]
    rfl
  · refine cspF_eqF_of_eqT (cspT_Index_to_Inductive_parallel hfin hIs) ?_
    obtain ⟨i0, -⟩ := Set.nonempty_iff_ne_empty.2 hI
    haveI : Inhabited ι := ⟨i0⟩
    intro s W
    rw [in_failures_Rep_parallel hI hfin, in_failures_Inductive_parallel_isListOf hI hIs]

/-
(************************************
 |       [||]:I PXf and SKIP        |
 ************************************)
-/

theorem cspF_SKIP_Rep_parallel_right_lm1
    {I : Set ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    I ≠ ∅ →
      Set.insert Tick
        (Set.sUnion {S | ∃ i : ι, i ∈ I ∧
          S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))}) =
      Set.sUnion {S | ∃ i : ι, i ∈ I ∧
        S = Set.insert Tick (Set.inter (Yf i) (Ev '' (Prod.snd (PXf i)))) } := by
  intro hI
  obtain ⟨i0, hi0⟩ := Set.nonempty_iff_ne_empty.2 hI
  ext e
  constructor
  · rintro (rfl | ⟨S, ⟨i, hi, rfl⟩, he⟩)
    · exact ⟨Set.insert Tick (Set.inter (Yf i0) (Ev '' (Prod.snd (PXf i0)))),
        ⟨i0, hi0, rfl⟩, Or.inl rfl⟩
    · refine ⟨Set.insert Tick (Set.inter (Yf i) (Ev '' (Prod.snd (PXf i)))), ⟨i, hi, rfl⟩, ?_⟩
      rcases he.2 with hT | hEv
      · exact Or.inl hT
      · exact Or.inr ⟨he.1, hEv⟩
  · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
    rcases he with hT | hEv
    · exact Or.inl hT
    · exact Or.inr ⟨Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))),
        ⟨i, hi, rfl⟩, ⟨hEv.1, Or.inr hEv.2⟩⟩

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_SKIP_Rep_parallel_right
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite →
      eqF
        ((Rep_parallel I PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' I)),
          (∅ : Set α)]| (proc.SKIP : proc p α))
        M M
        (Rep_parallel I PXf) := by
  intro hfin
  by_cases hI : I = ∅
  · subst hI
    rw [Rep_parallel_empty, Set.image_empty, Set.image_empty, Set.sUnion_empty]
    exact cspF_SKIP_Alpha_parallel
  · refine cspF_eqF_of_eqT (cspT_SKIP_Rep_parallel_right hfin) ?_
    intro s W
    rw [in_failures_Alpha_parallel, Set.union_empty, Set.image_empty,
      in_failures_Rep_parallel hI hfin]
    constructor
    · rintro ⟨u, X, hEq, Y, Z, hX, hP, hS, hsu⟩
      rw [in_failures_Rep_parallel hI hfin] at hP
      obtain ⟨u2, -, Z2, hEq2, Yf, hZ2, hall2⟩ := hP
      have hu2 : u2 = u rest-tr (Set.sUnion (Prod.snd '' (PXf '' I))) :=
        (Prod.mk.inj hEq2).1.symm
      have hZ2' : Z2 = Y := (Prod.mk.inj hEq2).2.symm
      rw [hu2] at hall2
      rw [hZ2'] at hZ2
      rw [in_failures_SKIP_iff2] at hS
      by_cases hT : (Tick : event α) ∈ Z
      · have hTick : (u rest-tr (∅ : Set α)) = (Abs_trace [Tick] : traceType α) := by
          rcases hS with ⟨-, hZE⟩ | hTk
          · exact absurd (hZE hT) (by simp [Evset])
          · exact hTk
        obtain ⟨s', hu, -, hno⟩ := rest_tr_Tick_sett.mp hTick
        refine ⟨u, hsu, X, hEq, fun i => Set.insert Tick (Yf i), ?_, ?_⟩
        · have hZfix : Z ∩ Set.insert Tick (∅ : Set (event α)) = {Tick} := by
            rw [Set.eq_singleton_iff_unique_mem]
            refine ⟨⟨hT, Or.inl rfl⟩, ?_⟩
            rintro e ⟨-, (rfl | hf)⟩
            · rfl
            · exact hf.elim
          rw [hX, hZfix, hZ2]
          dsimp only
          obtain ⟨i0, hi0⟩ := Set.nonempty_iff_ne_empty.2 hI
          ext e
          constructor
          · rintro (⟨S, ⟨i, hi, rfl⟩, heS⟩ | he)
            · exact ⟨Set.inter (Set.insert Tick (Yf i))
                (Set.insert Tick (Ev '' (Prod.snd (PXf i)))), ⟨i, hi, rfl⟩,
                ⟨Or.inr heS.1, heS.2⟩⟩
            · rw [Set.mem_singleton_iff] at he
              subst he
              exact ⟨Set.inter (Set.insert Tick (Yf i0))
                (Set.insert Tick (Ev '' (Prod.snd (PXf i0)))), ⟨i0, hi0, rfl⟩,
                ⟨Or.inl rfl, Or.inl rfl⟩⟩
          · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
            rcases he.1 with rfl | hY
            · exact Or.inr rfl
            · exact Or.inl ⟨Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))),
                ⟨i, hi, rfl⟩, ⟨hY, he.2⟩⟩
        · intro i hi
          have hsub := snd_subset_sUnion' (PXf := PXf) hi
          have hval := hall2 i hi
          rw [(rest_tr_of_rest_tr_subset hsub).2] at hval
          rw [hu] at hval ⊢
          rw [rest_tr_appt (Or.inl hno), rest_tr_Tick] at hval ⊢
          exact proc_T2_T3 hval (rest_tr_noTick.mpr hno)
      · refine ⟨u, hsu, X, hEq, Yf, ?_, ?_⟩
        · have hZfix : Z ∩ Set.insert Tick (∅ : Set (event α)) = ∅ := by
            rw [Set.eq_empty_iff_forall_notMem]
            rintro e ⟨he, (rfl | hf)⟩
            · exact hT he
            · exact hf
          rw [hX, hZfix, Set.union_empty, hZ2]
        · intro i hi
          have hval := hall2 i hi
          rwa [(rest_tr_of_rest_tr_subset (snd_subset_sUnion' (PXf := PXf) hi)).2] at hval
    · rintro ⟨u, hsu, Z, hEq, Yf, hZ, hall⟩
      refine ⟨u, Z, hEq, Z, ∅, ?_, ?_, ?_, hsu⟩
      · rw [Set.empty_inter, Set.union_empty]
      · rw [in_failures_Rep_parallel hI hfin]
        refine ⟨u rest-tr (Set.sUnion (Prod.snd '' (PXf '' I))), rest_tr_subset_event,
          Z, rfl, Yf, hZ, ?_⟩
        intro i hi
        rw [(rest_tr_of_rest_tr_subset (snd_subset_sUnion' (PXf := PXf) hi)).2]
        exact hall i hi
      · rw [in_failures_SKIP_iff2]
        rcases rest_tr_empty (u := u) with h | h
        · exact Or.inl ⟨h, Set.empty_subset _⟩
        · exact Or.inr h

/-
(************************************
 |        SKIP and [||]:I PXf       |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_SKIP_Rep_parallel_left
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite →
      eqF
        (((proc.SKIP : proc p α) |[
          (∅ : Set α),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))
        M M
        (Rep_parallel I PXf) := by
  intro hI
  exact
    cspF_trans_left_eq
      (cspF_Alpha_parallel_commut
        (P1 := (proc.SKIP : proc p α))
        (P2 := Rep_parallel I PXf)
        (X1 := (∅ : Set α))
        (X2 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (M := M))
      (cspF_SKIP_Rep_parallel_right (I := I) (PXf := PXf) (M := M) hI)

/- The Isabelle theorem bundle `cspF_SKIP_Rep_parallel` is represented by
   `cspF_SKIP_Rep_parallel_left` and `cspF_SKIP_Rep_parallel_right`. -/

/-
(************************************
 |          associativity           |
 ************************************)
-/

theorem cspF_Rep_parallel_ass_lm1
    {I : Set ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    Set.inter
      (Set.sUnion {S | ∃ i : ι, i ∈ I ∧
        S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))})
      (Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I))))) =
    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} := by
  refine Set.inter_eq_left.mpr ?_
  rintro e ⟨S, ⟨i, hi, rfl⟩, he⟩
  exact ins_mono (snd_subset_sUnion' hi) he.2

theorem cspF_Rep_parallel_ass_lm2
    {I1 I2 : Set ι} {PXf : ι → proc p α × Set α}
    {Yf1 Yf2 : ι → Set (event α)} :
    I1 ∩ I2 = ∅ →
      Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
        S = Set.inter (Yf1 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∪
        Set.sUnion {S | ∃ i : ι, i ∈ I2 ∧
          S = Set.inter (Yf2 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} =
      Set.sUnion {S | (∃ i : ι, i ∈ I1 ∧
        S = Set.inter (Yf1 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))) ∨
        ∃ i : ι, i ∈ I2 ∧
          S = Set.inter (Yf2 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} := by
  intro _
  ext e
  constructor
  · rintro (⟨S, hS, he⟩ | ⟨S, hS, he⟩)
    · exact ⟨S, Or.inl hS, he⟩
    · exact ⟨S, Or.inr hS, he⟩
  · rintro ⟨S, (hS | hS), he⟩
    · exact Or.inl ⟨S, hS, he⟩
    · exact Or.inr ⟨S, hS, he⟩

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/-- `cspF_Rep_parallel_ass_lm1` with `∩` instead of `Set.inter` at the head. -/
private theorem ass_lm1' {I : Set ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    (Set.sUnion {S | ∃ i : ι, i ∈ I ∧
        S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))}) ∩
      Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) =
    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} :=
  cspF_Rep_parallel_ass_lm1

theorem cspF_Rep_parallel_assoc
    {I1 I2 : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I1 ∩ I2 = ∅ → I1.Finite → I2.Finite →
      eqF
        (Rep_parallel (I1 ∪ I2) PXf) M M
        ((Rep_parallel I1 PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' I1)),
          Set.sUnion (Prod.snd '' (PXf '' I2))]| Rep_parallel I2 PXf) := by
  classical
  intro hdisj hfin1 hfin2
  by_cases hI1 : I1 = ∅
  · subst hI1
    rw [Set.empty_union, Rep_parallel_empty, Set.image_empty, Set.image_empty,
      Set.sUnion_empty]
    exact cspF_sym (cspF_SKIP_Rep_parallel_left hfin2)
  · by_cases hI2 : I2 = ∅
    · subst hI2
      rw [Set.union_empty, Rep_parallel_empty, Set.image_empty, Set.image_empty,
        Set.sUnion_empty]
      exact cspF_sym (cspF_SKIP_Rep_parallel_right hfin1)
    · have hIU : I1 ∪ I2 ≠ ∅ := by
        intro hEmpty
        apply hI1
        rw [Set.eq_empty_iff_forall_notMem]
        intro i hi
        have hmem : i ∈ I1 ∪ I2 := Or.inl hi
        rw [hEmpty] at hmem
        exact hmem
      have hnotI1 : ∀ i : ι, i ∈ I2 → i ∉ I1 := by
        intro i hi2 hi1
        have hmem : i ∈ I1 ∩ I2 := ⟨hi1, hi2⟩
        rw [hdisj] at hmem
        exact hmem
      refine cspF_eqF_of_eqT (cspT_Rep_parallel_assoc hdisj hfin1 hfin2) ?_
      intro s W
      rw [in_failures_Rep_parallel hIU (hfin1.union hfin2), in_failures_Alpha_parallel,
        Union_snd_Un]
      constructor
      · rintro ⟨u, hsu, Z, hEq, Yf, hZ, hall⟩
        refine ⟨u, Z, hEq,
          Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
            S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))},
          Set.sUnion {S | ∃ i : ι, i ∈ I2 ∧
            S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))}, ?_, ?_, ?_, hsu⟩
        · rw [hZ, ass_lm1', ass_lm1', cspF_Rep_parallel_ass_lm2 hdisj]
          congr 1
          ext S
          constructor
          · rintro ⟨i, (hi | hi), rfl⟩
            · exact Or.inl ⟨i, hi, rfl⟩
            · exact Or.inr ⟨i, hi, rfl⟩
          · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
            · exact ⟨i, Or.inl hi, rfl⟩
            · exact ⟨i, Or.inr hi, rfl⟩
        · rw [in_failures_Rep_parallel hI1 hfin1]
          refine ⟨u rest-tr (Set.sUnion (Prod.snd '' (PXf '' I1))), rest_tr_subset_event,
            _, rfl, Yf, ass_lm1', ?_⟩
          intro i hi
          rw [(rest_tr_of_rest_tr_subset (snd_subset_sUnion' (PXf := PXf) hi)).2]
          exact hall i (Or.inl hi)
        · rw [in_failures_Rep_parallel hI2 hfin2]
          refine ⟨u rest-tr (Set.sUnion (Prod.snd '' (PXf '' I2))), rest_tr_subset_event,
            _, rfl, Yf, ass_lm1', ?_⟩
          intro i hi
          rw [(rest_tr_of_rest_tr_subset (snd_subset_sUnion' (PXf := PXf) hi)).2]
          exact hall i (Or.inr hi)
      · rintro ⟨u, X, hEq, Y1, Y2, hX, hP1, hP2, hsu⟩
        rw [in_failures_Rep_parallel hI1 hfin1] at hP1
        rw [in_failures_Rep_parallel hI2 hfin2] at hP2
        obtain ⟨u1, -, Z1, hEq1, Yf1, hZ1, hall1⟩ := hP1
        obtain ⟨u2, -, Z2, hEq2, Yf2, hZ2, hall2⟩ := hP2
        rw [(Prod.mk.inj hEq1).1.symm] at hall1
        rw [(Prod.mk.inj hEq1).2.symm] at hZ1
        rw [(Prod.mk.inj hEq2).1.symm] at hall2
        rw [(Prod.mk.inj hEq2).2.symm] at hZ2
        refine ⟨u, hsu, X, hEq, fun i => if i ∈ I1 then Yf1 i else Yf2 i, ?_, ?_⟩
        · rw [hX, hZ1, hZ2]
          ext e
          constructor
          · rintro (⟨S, ⟨i, hi, rfl⟩, he⟩ | ⟨S, ⟨i, hi, rfl⟩, he⟩)
            · refine ⟨Set.inter (Yf1 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))),
                ⟨i, Or.inl hi, ?_⟩, he⟩
              dsimp only
              rw [if_pos hi]
            · refine ⟨Set.inter (Yf2 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))),
                ⟨i, Or.inr hi, ?_⟩, he⟩
              dsimp only
              rw [if_neg (hnotI1 i hi)]
          · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
            rcases hi with hi | hi
            · dsimp only at he
              rw [if_pos hi] at he
              exact Or.inl ⟨Set.inter (Yf1 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))),
                ⟨i, hi, rfl⟩, he⟩
            · dsimp only at he
              rw [if_neg (hnotI1 i hi)] at he
              exact Or.inr ⟨Set.inter (Yf2 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))),
                ⟨i, hi, rfl⟩, he⟩
        · rintro i (hi | hi)
          · dsimp only
            rw [if_pos hi]
            have hval := hall1 i hi
            rwa [(rest_tr_of_rest_tr_subset (snd_subset_sUnion' (PXf := PXf) hi)).2] at hval
          · dsimp only
            rw [if_neg (hnotI1 i hi)]
            have hval := hall2 i hi
            rwa [(rest_tr_of_rest_tr_subset (snd_subset_sUnion' (PXf := PXf) hi)).2] at hval

/-
(************************************
 |             induct               |
 ************************************)
-/

/- (*------------------*
 |     csp law      |
 |   (derivable)    |
 *------------------*) -/

theorem cspF_Rep_parallel_induct
    {I : Set ι} {i : ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite → i ∉ I →
      eqF
        (Rep_parallel (Set.insert i I) PXf) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
  intro hI hiI
  have hDisj : ({i} : Set ι) ∩ I = ∅ := by
    ext x
    simp [hiI]
  have hAssoc :
      eqF
        (Rep_parallel (({i} : Set ι) ∪ I) PXf) M M
        ((Rep_parallel ({i} : Set ι) PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' ({i} : Set ι))),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
    exact cspF_Rep_parallel_assoc (I1 := ({i} : Set ι)) (I2 := I) (PXf := PXf) (M := M)
      hDisj (Set.toFinite {i}) hI
  have hAssoc' :
      eqF
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
        (cspF_Alpha_parallel_assoc
          (P1 := Prod.fst (PXf i))
          (P2 := (proc.SKIP : proc p α))
          (P3 := Rep_parallel I PXf)
          (X1 := Prod.snd (PXf i))
          (X2 := (∅ : Set α))
          (X3 := Set.sUnion (Prod.snd '' (PXf '' I)))
          (M := M))
  have hCong :
      eqF
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
      cspF_Alpha_parallel_cong
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
        cspF_reflex_eq_P
        (cspF_SKIP_Rep_parallel_left (I := I) (PXf := PXf) (M := M) hI)
  exact
    cspF_trans_left_eq
      (by simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using hAssoc)
      (cspF_trans_left_eq hAssoc' hCong)

end
