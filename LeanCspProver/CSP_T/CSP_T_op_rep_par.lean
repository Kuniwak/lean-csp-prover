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
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_op_alpha_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq`,           -/
/-  `Inf_image_eq`, or `disj_not1`, so there is nothing to disable.     -/

/-============================================================*
 |                                                            |
 |            replicated alphabetized parallel                |
 |                                                            |
 *============================================================-/

/- (*** traces Inductive_parallel ***) -/

/-- `set_cons` phrased with Mathlib's `insert`, so that the `Set.insert` produced by
    `Compat.set_cons` matches the `insert` used by Mathlib's simp lemmas. -/
private theorem set_cons' {β : Type _} (a : β) (s : List β) :
    _root_.set (a :: s) = insert a (_root_.set s) := by
  rw [set_cons]
  rfl

private theorem sUnion_snd_cons {PX : proc p α × Set α} {PXs : List (proc p α × Set α)} :
    Set.sUnion (Prod.snd '' _root_.set (PX :: PXs)) =
      Prod.snd PX ∪ Set.sUnion (Prod.snd '' _root_.set PXs) := by
  rw [set_cons', Set.image_insert_eq, Set.sUnion_insert]

private theorem set_map {β γ : Type _} (f : β → γ) (l : List β) :
    _root_.set (l.map f) = f '' _root_.set l := by
  ext x
  simp [_root_.set]

theorem in_traces_Inductive_parallel_lm1
    {P : proc p α} {X : Set α} {PXs : List (proc p α × Set α)} :
    (P, X) ∈ _root_.set PXs → X ⊆ Set.sUnion (Prod.snd '' _root_.set PXs) := by
  intro h a ha
  exact ⟨X, ⟨(P, X), h, rfl⟩, ha⟩

/- main -/

theorem in_traces_Inductive_parallel_lm
    {PXs : List (proc p α × Set α)} {M : p → domTType α} :
    PXs ≠ [] →
      ∀ u,
        (u :t traces (Inductive_parallel PXs) M) ↔
          (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∀ P X, (P, X) ∈ _root_.set PXs → memT (u rest-tr X) (traces P M)) := by
  induction PXs with
  | nil => intro h; exact absurd rfl h
  | cons PX PXs ih =>
      intro _ u
      by_cases hPXs : PXs = []
      · subst hPXs
        have h0 : Set.sUnion (Prod.snd '' _root_.set ([] : List (proc p α × Set α))) =
            (∅ : Set α) := by simp
        have hSKIP :
            (u rest-tr (Set.sUnion (Prod.snd '' _root_.set ([] : List (proc p α × Set α)))))
              :t traces (Inductive_parallel ([] : List (proc p α × Set α))) M := by
          simp only [Inductive_parallel, h0]
          rcases rest_tr_empty (u := u) with h | h <;> rw [h] <;>
            exact in_traces_SKIP.mpr (by simp)
        simp only [Inductive_parallel]
        rw [in_traces_Alpha_parallel, sUnion_snd_cons, h0, Set.union_empty]
        constructor
        · rintro ⟨hP, -, hs⟩
          refine ⟨hs, ?_⟩
          intro P X hPX
          rw [set_cons', set_nil] at hPX
          simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at hPX
          subst hPX
          exact hP
        · rintro ⟨hs, hall⟩
          refine ⟨hall PX.1 PX.2 ?_, ?_, hs⟩
          · rw [set_cons']
            simp
          · simp only [Inductive_parallel, h0] at hSKIP ⊢
            exact hSKIP
      · simp only [Inductive_parallel]
        rw [in_traces_Alpha_parallel,
          ih hPXs (u rest-tr (Set.sUnion (Prod.snd '' _root_.set PXs))), sUnion_snd_cons]
        constructor
        · rintro ⟨hP, h2, hs⟩
          refine ⟨hs, ?_⟩
          intro P X hPX
          rw [set_cons', Set.mem_insert_iff] at hPX
          rcases hPX with rfl | hPX
          · exact hP
          · have hsub : X ⊆ Set.sUnion (Prod.snd '' _root_.set PXs) :=
              in_traces_Inductive_parallel_lm1 hPX
            have hmem := h2.2 P X hPX
            rwa [(rest_tr_of_rest_tr_subset hsub).2] at hmem
        · rintro ⟨hs, hall⟩
          refine ⟨hall PX.1 PX.2 (by rw [set_cons']; simp), ⟨rest_tr_subset_event, ?_⟩, hs⟩
          intro P X hPX
          have hsub : X ⊆ Set.sUnion (Prod.snd '' _root_.set PXs) :=
            in_traces_Inductive_parallel_lm1 hPX
          rw [(rest_tr_of_rest_tr_subset hsub).2]
          exact hall P X (by rw [set_cons']; exact Or.inr hPX)

/- (*** remove ALL ***) -/

theorem in_traces_Inductive_parallel
    {PXs : List (proc p α × Set α)} {u : traceType α} {M : p → domTType α} :
    PXs ≠ [] →
      ((u :t traces (Inductive_parallel PXs) M) ↔
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
          ∀ P X, (P, X) ∈ _root_.set PXs → memT (u rest-tr X) (traces P M))) :=
  fun h => in_traces_Inductive_parallel_lm h u

/- (*** Semantics for replicated alphabetized parallel on T ***) -/

theorem traces_Inductive_parallel
    {PXs : List (proc p α × Set α)} {M : p → domTType α} :
    PXs ≠ [] →
      traces (Inductive_parallel PXs) M =
        CollectT (fun u : traceType α =>
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∀ P X, (P, X) ∈ _root_.set PXs → memT (u rest-tr X) (traces P M)) := by
  intro h
  rw [← CollectT_open (T := traces (Inductive_parallel PXs) M)]
  apply CollectT_eq
  intro u
  exact propext (in_traces_Inductive_parallel (u := u) h)

/-************************************
 |              traces              |
 ************************************-/

theorem sett_in_traces_Inductive_parallel
    {PXs : List (proc p α × Set α)} {t : traceType α} {M : p → domTType α} :
    PXs ≠ [] → t :t traces (Inductive_parallel PXs) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) :=
  fun h ht => ((in_traces_Inductive_parallel h).1 ht).1

/- ---------------------------------------------------------*
 |        another expression of Inductive_parallel_eval    |
 *--------------------------------------------------------- -/

private def nth_inductive_parallel_cond
    (PXs : List (proc p α × Set α)) (u : traceType α) (M : p → domTType α) (i : Nat) : Prop :=
  let PX := nth PXs i
  memT (u rest-tr PX.2) (traces PX.1 M)

private def in_traces_Inductive_parallel_nth_stmt
    (PXs : List (proc p α × Set α)) (u : traceType α) (M : p → domTType α) : Prop :=
  PXs ≠ [] →
    ((u :t traces (Inductive_parallel PXs) M) ↔
      And
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))))
        (∀ i : Nat, (i < PXs.length) → nth_inductive_parallel_cond PXs u M i))

theorem in_traces_Inductive_parallel_nth
    {PXs : List (proc p α × Set α)} {u : traceType α} {M : p → domTType α} :
    in_traces_Inductive_parallel_nth_stmt PXs u M := by
  intro h
  rw [in_traces_Inductive_parallel h]
  constructor
  · rintro ⟨hs, hall⟩
    refine ⟨hs, ?_⟩
    intro i hi
    exact hall (nth PXs i).1 (nth PXs i).2 (set_nth.mpr ⟨i, hi, rfl⟩)
  · rintro ⟨hs, hall⟩
    refine ⟨hs, ?_⟩
    intro P X hPX
    obtain ⟨i, hi, hEq⟩ := set_nth.mp hPX
    have hval := hall i hi
    simp only [nth_inductive_parallel_cond] at hval
    rw [← hEq] at hval
    exact hval

/-============================================================*
 |                                                            |
 |              indexed alphabetized parallel                 |
 |                                                            |
 *============================================================-/

/- (*** index_style ***) -/

theorem to_index_style_T
    {I : Set ι} {PXf : ι → proc p α × Set α} {u : traceType α} {M : p → domTType α} :
    (∀ P X, (P, X) ∈ PXf '' I → memT (u rest-tr X) (traces P M)) ↔
      (∀ i : ι, (i ∈ I) → memT (u rest-tr (Prod.snd (PXf i))) (traces (Prod.fst (PXf i)) M)) := by
  constructor
  · intro h i hi
    exact h (PXf i).1 (PXf i).2 ⟨i, hi, rfl⟩
  · rintro h P X ⟨i, hi, hEq⟩
    have hval := h i hi
    rw [hEq] at hval
    exact hval

/- (*** in_traces_Rep_parallel (pre) ***) -/

theorem in_traces_Rep_parallel_pre
    {I : Set ι} {PXf : ι → proc p α × Set α} {u : traceType α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite →
      ((u :t traces (Rep_parallel I PXf) M) ↔
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
          ∀ P X, (P, X) ∈ PXf '' I → memT (u rest-tr X) (traces P M))) := by
  intro hI hfin
  have hIs : isListOf (SOME fun Is : List ι => isListOf Is I) I :=
    chooseOrDefault_spec (isListOf_EX hfin)
  have hne : (SOME fun Is : List ι => isListOf Is I) ≠ [] := isListOf_nonemptyset hI hIs
  have hmapne : List.map PXf (SOME fun Is : List ι => isListOf Is I) ≠ [] := by
    simpa using hne
  have hset : _root_.set (List.map PXf (SOME fun Is : List ι => isListOf Is I)) = PXf '' I := by
    rw [set_map, isListOf_set_eq hIs]
  rw [Rep_parallel_def, in_traces_Inductive_parallel hmapne, hset]

/- (*** in_traces_Rep_parallel ***) -/

theorem in_traces_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {u : traceType α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite →
      ((u :t traces (Rep_parallel I PXf) M) ↔
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
          ∀ i : ι, (i ∈ I) →
            memT (u rest-tr (Prod.snd (PXf i))) (traces (Prod.fst (PXf i)) M))) := by
  intro hI hfin
  rw [in_traces_Rep_parallel_pre hI hfin, to_index_style_T]

/- The Isabelle theorem bundle `in_traces_par` is represented by
   `in_traces_Alpha_parallel`, `in_traces_Inductive_parallel`, and
   `in_traces_Rep_parallel`. -/

/- (*** Semantics for indexed alphabetized parallel on T ***) -/

theorem traces_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite →
      traces (Rep_parallel I PXf) M =
        CollectT (fun u : traceType α =>
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
            ∀ i : ι, (i ∈ I) →
              memT (u rest-tr (Prod.snd (PXf i))) (traces (Prod.fst (PXf i)) M)) := by
  intro hI hfin
  rw [← CollectT_open (T := traces (Rep_parallel I PXf) M)]
  apply CollectT_eq
  intro u
  exact propext (in_traces_Rep_parallel (u := u) hI hfin)

/-************************************
 |              traces              |
 ************************************-/

theorem sett_in_traces_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {t : traceType α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite → t :t traces (Rep_parallel I PXf) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) :=
  fun hI hfin ht => ((in_traces_Rep_parallel hI hfin).1 ht).1
