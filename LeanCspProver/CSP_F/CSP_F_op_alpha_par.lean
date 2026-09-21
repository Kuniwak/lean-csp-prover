           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_op_alpha_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `(notick \/ t = <>)`.          -/
/-                                                                     -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

private theorem ev_mem_insert_image {a : α} {X : Set α} :
    Ev a ∈ Set.insert Tick (Ev '' X) → a ∈ X := by
  intro h
  change Ev a = Tick ∨ Ev a ∈ Ev '' X at h
  rcases h with hTick | hImg
  · cases hTick
  · rcases hImg with ⟨b, hbX, hbEq⟩
    cases hbEq
    exact hbX

/-
(*********************************************************
             Alphabetized Parallel eval
 *********************************************************)
-/

theorem in_failures_Parallel_SKIP_lm1
    {X : Set α} {Y Z : Set (event α)} :
    Y \ Set.insert Tick (Ev '' X) = Z \ Set.insert Tick (Ev '' X) →
      (Tick ∉ Z ∨ Z ⊆ Evset) →
        Z \ Y ⊆ Ev '' X := by
  intro hEq hZ e he
  rcases he with ⟨heZ, heY⟩
  have heInsert : e ∈ Set.insert Tick (Ev '' X) := by
    by_contra heNot
    have heDiffZ : e ∈ Z \ Set.insert Tick (Ev '' X) := ⟨heZ, heNot⟩
    have heDiffY : e ∈ Y \ Set.insert Tick (Ev '' X) := by
      rw [hEq]
      exact heDiffZ
    exact heY heDiffY.1
  have heNeTick : e ≠ Tick := by
    rcases hZ with hTick | hSubset
    · exact fun h => hTick (h ▸ heZ)
    · have hEvset : e ∈ Evset := hSubset heZ
      simpa [Evset] using hEvset
  rcases not_Tick_to_Ev.mp heNeTick with ⟨a, rfl⟩
  exact ⟨a, ev_mem_insert_image (X := X) heInsert, rfl⟩

theorem in_failures_Parallel_SKIP_lm2
    {X : Set α} {Y Z : Set (event α)} :
    Y \ Set.insert Tick (Ev '' X) = Z \ Set.insert Tick (Ev '' X) →
      Z \ Set.insert Tick Y ⊆ Ev '' X := by
  intro hEq e he
  rcases he with ⟨heZ, heNotY⟩
  have hNotMemY : e ∉ Y := by
    intro heY
    exact heNotY (Or.inr heY)
  have heNeTick : e ≠ Tick := by
    intro h
    exact heNotY (Or.inl h)
  have heInsert : e ∈ Set.insert Tick (Ev '' X) := by
    by_contra heNot
    have heDiffZ : e ∈ Z \ Set.insert Tick (Ev '' X) := ⟨heZ, heNot⟩
    have heDiffY : e ∈ Y \ Set.insert Tick (Ev '' X) := by
      rw [hEq]
      exact heDiffZ
    exact hNotMemY heDiffY.1
  rcases not_Tick_to_Ev.mp heNeTick with ⟨a, rfl⟩
  exact ⟨a, ev_mem_insert_image (X := X) heInsert, rfl⟩

/- (*** Para SKIP ***) -/


/- (*** pointwise reasoning about `Set.insert Tick (Ev '' X)` ***) -/

private theorem mem_Set_insert {β : Type _} {a b : β} {s : Set β} :
    a ∈ Set.insert b s ↔ (a = b ∨ a ∈ s) :=
  Iff.rfl

private theorem Ev_mem_insert_image_iff {a : α} {X : Set α} :
    (Ev a ∈ Set.insert Tick (Ev '' X)) ↔ a ∈ X := by
  constructor
  · exact ev_mem_insert_image
  · intro h
    exact Or.inr ⟨a, h, rfl⟩

private theorem Tick_mem_insert_image {X : Set α} :
    (Tick : event α) ∈ Set.insert Tick (Ev '' X) :=
  Or.inl rfl

private theorem Tick_notin_Ev_image {X : Set α} :
    (Tick : event α) ∉ Ev '' X := by
  rintro ⟨a, -, ha⟩
  cases ha

private theorem image_union_Tick {X : Set α} :
    ((Ev '' X : Set (event α)) ∪ {Tick}) = Set.insert Tick (Ev '' X) := by
  ext e
  simp [mem_Set_insert]

private theorem sett_inter_compl_iff {u : traceType α} {X : Set α} :
    (sett u ∩ Ev '' Xᶜ = ∅) ↔ sett u ⊆ Set.insert Tick (Ev '' X) := by
  constructor
  · intro hEmpty e he
    rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
    · simp [mem_Set_insert]
    · by_cases ha : a ∈ X
      · simp [mem_Set_insert, ha]
      · exact absurd (by rw [← hEmpty]; exact ⟨he, ⟨a, by simpa using ha, rfl⟩⟩)
          (by simp : (Ev a : event α) ∉ (∅ : Set (event α)))
  · intro hsub
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he, ⟨a, ha, rfl⟩⟩
    exact (by simpa using ha : a ∉ X) (ev_mem_insert_image (X := X) (hsub he))

private theorem subset_image_compl_iff {Z : Set (event α)} {X : Set α} :
    (Z ⊆ Ev '' Xᶜ) ↔ Z ∩ Set.insert Tick (Ev '' X) = ∅ := by
  constructor
  · intro hsub
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he, hIns⟩
    rcases hsub he with ⟨a, ha, rfl⟩
    exact (by simpa using ha : a ∉ X) (ev_mem_insert_image (X := X) hIns)
  · intro hEmpty e he
    have hnot : e ∉ Set.insert Tick (Ev '' X) := by
      intro hIns
      have : e ∈ Z ∩ Set.insert Tick (Ev '' X) := ⟨he, hIns⟩
      rw [hEmpty] at this
      exact this
    rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
    · exact absurd (by simp [mem_Set_insert]) hnot
    · exact ⟨a, by simpa using fun ha : a ∈ X => hnot (by simp [mem_Set_insert, ha]), rfl⟩

theorem in_failures_Parallel_SKIP
    {f : failure α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    (f :f failures (P |[X]| proc.SKIP) M) ↔
      ∃ u Y Z, f = (u, Y ∪ Z) ∧
        (u, Y) :f failures P M ∧
        sett u ∩ Ev '' X = ∅ ∧
        Z ⊆ Ev '' X := by
  rw [in_failures_Parallel]
  constructor
  · rintro ⟨u, Y, Z, rfl, hYZ, s, t, hpar, hsY, htZ⟩
    rw [image_union_Tick] at hYZ
    rw [in_failures_SKIP] at htZ
    rcases htZ with ⟨W, hEq, hW⟩ | ⟨W, hEq⟩
    · rcases Prod.mk.inj hEq with ⟨ht, hZ⟩
      subst ht
      subst hZ
      rcases par_tr_nil_right.mp hpar with ⟨rfl, -, hEmpty⟩
      exact ⟨u, Y, Z \ Y, by rw [Set.union_diff_self], hsY, hEmpty,
        in_failures_Parallel_SKIP_lm1 hYZ (Or.inr hW)⟩
    · rcases Prod.mk.inj hEq with ⟨ht, hZ⟩
      subst ht
      subst hZ
      rcases par_tr_Tick_right.mp hpar with ⟨rfl, hTick, hEmpty⟩
      by_cases hTZ : Tick ∈ Z
      · rcases Tick_in_sett.mp hTick with ⟨w, rfl, hNo⟩
        refine ⟨w ^^^ Abs_trace [Tick], Set.insert Tick Y, Z \ Set.insert Tick Y, ?_,
          proc_T2_T3 hsY hNo, hEmpty, in_failures_Parallel_SKIP_lm2 hYZ⟩
        congr 1
        ext e
        simp only [Set.mem_union, Set.mem_diff, mem_Set_insert]
        constructor
        · rintro (h | h)
          · exact Or.inl (Or.inr h)
          · by_cases hc : e = Tick ∨ e ∈ Y
            · exact Or.inl hc
            · exact Or.inr ⟨h, hc⟩
        · rintro ((rfl | h) | ⟨h, -⟩)
          · exact Or.inr hTZ
          · exact Or.inl h
          · exact Or.inr h
      · exact ⟨u, Y, Z \ Y, by rw [Set.union_diff_self], hsY, hEmpty,
          in_failures_Parallel_SKIP_lm1 hYZ (Or.inl hTZ)⟩
  · rintro ⟨u, Y, Z, rfl, hsY, hEmpty, hZ⟩
    have hZdiff : (Z \ Set.insert Tick (Ev '' X)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨he, hne⟩
      exact hne (Or.inr (hZ he))
    by_cases hTick : Tick ∈ sett u
    · refine ⟨u, Y, Z ∪ Y, ?_, ?_,
        u, Abs_trace [Tick], par_tr_Tick_right.mpr ⟨rfl, hTick, hEmpty⟩, hsY, ?_⟩
      · congr 1
        ext e
        simp only [Set.mem_union]
        tauto
      · rw [image_union_Tick, Set.union_diff_distrib, hZdiff, Set.empty_union]
      · exact in_failures_SKIP.mpr (Or.inr ⟨Z ∪ Y, rfl⟩)
    · refine ⟨u, Y, Z ∪ (Y \ {Tick}), ?_, ?_,
        u, <>, par_tr_nil_right.mpr ⟨rfl, hTick, hEmpty⟩, hsY, ?_⟩
      · congr 1
        ext e
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        tauto
      · have h2 : ((Y \ {Tick}) \ Set.insert Tick (Ev '' X)) = Y \ Set.insert Tick (Ev '' X) := by
          ext e
          simp only [Set.mem_diff, Set.mem_singleton_iff, mem_Set_insert]
          tauto
        rw [image_union_Tick, Set.union_diff_distrib, hZdiff, h2, Set.empty_union]
      · refine in_failures_SKIP.mpr (Or.inl ⟨Z ∪ (Y \ {Tick}), rfl, ?_⟩)
        rintro e (he | ⟨-, he⟩)
        · rcases hZ he with ⟨a, -, rfl⟩
          simp [Evset]
        · simpa [Evset] using he

/- (*** complement ***) -/

theorem in_failures_Parallel_SKIP_comp
    {f : failure α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    (f :f failures (P |[Xᶜ]| proc.SKIP) M) ↔
      ∃ u Y Z, f = (u, Y ∪ Z) ∧
        (u, Y) :f failures P M ∧
        sett u ⊆ Set.insert Tick (Ev '' X) ∧
        Z ∩ Set.insert Tick (Ev '' X) = ∅ := by
  rw [in_failures_Parallel_SKIP]
  constructor
  · rintro ⟨u, Y, Z, hf, hsY, hEmpty, hZ⟩
    exact ⟨u, Y, Z, hf, hsY, sett_inter_compl_iff.mp hEmpty, subset_image_compl_iff.mp hZ⟩
  · rintro ⟨u, Y, Z, hf, hsY, hsub, hZ⟩
    exact ⟨u, Y, Z, hf, hsY, sett_inter_compl_iff.mpr hsub, subset_image_compl_iff.mpr hZ⟩

/- (*** Alpha_parallel_evalF ***) -/

theorem in_failures_Alpha_parallel_lm1
    {X1 X2 : Set α} {Ya Yb Za Zb : Set (event α)} :
    Tick ∉ Za →
      Za ∩ Ev '' X1 = ∅ →
      Tick ∉ Zb →
      Zb ∩ Ev '' X2 = ∅ →
      (Ya ∪ Za) \ Set.insert Tick (Ev '' (X1 ∩ X2)) =
        (Yb ∪ Zb) \ Set.insert Tick (Ev '' (X1 ∩ X2)) →
        (Ya ∪ Za ∪ (Yb ∪ Zb)) ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) =
          (Ya ∩ Set.insert Tick (Ev '' X1)) ∪
            (Yb ∩ Set.insert Tick (Ev '' X2)) := by
  intro hTa hZa hTb hZb hEq
  have hZa' : ∀ a : α, Ev a ∈ Za → a ∉ X1 := by
    intro a haZ haX
    have hmem : Ev a ∈ Za ∩ Ev '' X1 := ⟨haZ, ⟨a, haX, rfl⟩⟩
    rw [hZa] at hmem
    exact hmem
  have hZb' : ∀ a : α, Ev a ∈ Zb → a ∉ X2 := by
    intro a haZ haX
    have hmem : Ev a ∈ Zb ∩ Ev '' X2 := ⟨haZ, ⟨a, haX, rfl⟩⟩
    rw [hZb] at hmem
    exact hmem
  have hEq' : ∀ e : event α,
      (e ∈ Ya ∪ Za ∧ e ∉ Set.insert Tick (Ev '' (X1 ∩ X2))) ↔
        (e ∈ Yb ∪ Zb ∧ e ∉ Set.insert Tick (Ev '' (X1 ∩ X2))) := by
    intro e
    constructor
    · intro h
      have hmem : e ∈ (Yb ∪ Zb) \ Set.insert Tick (Ev '' (X1 ∩ X2)) := by
        rw [← hEq]
        exact h
      exact hmem
    · intro h
      have hmem : e ∈ (Ya ∪ Za) \ Set.insert Tick (Ev '' (X1 ∩ X2)) := by
        rw [hEq]
        exact h
      exact hmem
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · simp only [Set.mem_inter_iff, Set.mem_union, Tick_mem_insert_image, and_true]
    tauto
  · have h1 := hEq' (Ev a)
    have h2 := hZa' a
    have h3 := hZb' a
    simp only [Set.mem_inter_iff, Set.mem_union, Ev_mem_insert_image_iff] at h1 ⊢
    tauto

theorem in_failures_Alpha_parallel_lm2
    {X : Set (event α)} {Y Z : Set (event α)} {X1 X2 : Set α} :
    X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) ⊆ Y ∪ Z →
      X =
        (X ∩ Ev '' (X1 \ X2)) ∪
          (X ∩ Y ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
            (X \ Set.insert Tick (Ev '' X1)) ∪
              ((X ∩ Ev '' (X2 \ X1)) ∪
                (X ∩ Z ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
                (X \ Set.insert Tick (Ev '' X2))) := by
  intro hsub
  have hT : Tick ∈ X → Tick ∈ Y ∨ Tick ∈ Z := fun h => hsub ⟨h, Tick_mem_insert_image⟩
  have hE : ∀ a : α, Ev a ∈ X → (a ∈ X1 ∨ a ∈ X2) → Ev a ∈ Y ∨ Ev a ∈ Z :=
    fun a h ha => hsub ⟨h, Ev_mem_insert_image_iff.mpr ha⟩
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Tick_mem_insert_image,
      Tick_notin_Ev_image, and_false, false_or, not_true_eq_false, and_true, or_false]
    tauto
  · have h1 := hE a
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Ev_mem_insert_image_iff,
      Ev_mem_Ev_image]
    tauto

theorem in_failures_Alpha_parallel_lm3
    {X : Set (event α)} {Y Z : Set (event α)} {X1 X2 : Set α} :
    ((X ∩ Ev '' (X1 \ X2)) ∪
      (X ∩ Y ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
      (X \ Set.insert Tick (Ev '' X1))) \
        Set.insert Tick (Ev '' (X1 ∩ X2)) =
      ((X ∩ Ev '' (X2 \ X1)) ∪
        (X ∩ Z ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
        (X \ Set.insert Tick (Ev '' X2))) \
          Set.insert Tick (Ev '' (X1 ∩ X2)) := by
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · simp only [Set.mem_diff, Tick_mem_insert_image, not_true_eq_false, and_false]
  · simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff, Ev_mem_insert_image_iff,
      Ev_mem_Ev_image]
    tauto

/- (*** F ***) -/

theorem in_failures_Alpha_parallel
    {f : failure α} {P Q : proc p α} {X1 X2 : Set α} {M : p → domFType α} :
    (f :f failures (P |[X1,X2]| Q) M) ↔
      ∃ u X,
        f = (u, X) ∧
          ∃ Y Z,
            X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) =
              (Y ∩ Set.insert Tick (Ev '' X1)) ∪
                (Z ∩ Set.insert Tick (Ev '' X2)) ∧
            (u rest-tr X1, Y) :f failures P M ∧
            (u rest-tr X2, Z) :f failures Q M ∧
            sett u ⊆ Set.insert Tick (Ev '' (X1 ∪ X2)) := by
  rw [Alpha_parallel_def, in_failures_Parallel]
  constructor
  · rintro ⟨u, Y, Z, rfl, hYZ, s, t, hpar, hsY, htZ⟩
    rw [image_union_Tick] at hYZ
    rw [in_failures_Parallel_SKIP_comp] at hsY htZ
    obtain ⟨ua, Ya, Za, hEqa, hPa, hsa, hZa⟩ := hsY
    obtain ⟨ub, Yb, Zb, hEqb, hQb, hsb, hZb⟩ := htZ
    rw [Prod.mk.injEq] at hEqa hEqb
    obtain ⟨rfl, rfl⟩ := hEqa
    obtain ⟨rfl, rfl⟩ := hEqb
    rcases (par_tr_rest_tr hsa hsb).1 hpar with ⟨hrest1, hrest2, huXY⟩
    have hTa : Tick ∉ Za := by
      intro hmem
      have : Tick ∈ Za ∩ Set.insert Tick (Ev '' X1) := ⟨hmem, Tick_mem_insert_image⟩
      rw [hZa] at this
      exact this
    have hTb : Tick ∉ Zb := by
      intro hmem
      have : Tick ∈ Zb ∩ Set.insert Tick (Ev '' X2) := ⟨hmem, Tick_mem_insert_image⟩
      rw [hZb] at this
      exact this
    have hZa' : Za ∩ Ev '' X1 = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨he, ⟨a, ha, rfl⟩⟩
      have : Ev a ∈ Za ∩ Set.insert Tick (Ev '' X1) := ⟨he, Ev_mem_insert_image_iff.mpr ha⟩
      rw [hZa] at this
      exact this
    have hZb' : Zb ∩ Ev '' X2 = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨he, ⟨a, ha, rfl⟩⟩
      have : Ev a ∈ Zb ∩ Set.insert Tick (Ev '' X2) := ⟨he, Ev_mem_insert_image_iff.mpr ha⟩
      rw [hZb] at this
      exact this
    refine ⟨u, (Ya ∪ Za) ∪ (Yb ∪ Zb), rfl, Ya, Yb,
      in_failures_Alpha_parallel_lm1 hTa hZa' hTb hZb' hYZ, ?_, ?_, huXY⟩
    · rw [← hrest1]
      exact hPa
    · rw [← hrest2]
      exact hQb
  · rintro ⟨u, X, rfl, Y, Z, hX, hP, hQ, hsu⟩
    have hsub : X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) ⊆ Y ∪ Z := by
      rw [hX]
      rintro e (⟨he, -⟩ | ⟨he, -⟩)
      · exact Or.inl he
      · exact Or.inr he
    have hYmem : ∀ a : α, Ev a ∈ X → a ∈ X1 → a ∉ X2 → Ev a ∈ Y := by
      intro a heX ha1 ha2
      have hmem : Ev a ∈ X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) :=
        ⟨heX, Ev_mem_insert_image_iff.mpr (Or.inl ha1)⟩
      rw [hX] at hmem
      rcases hmem with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · exact absurd (Ev_mem_insert_image_iff.mp h) ha2
    have hZmem : ∀ a : α, Ev a ∈ X → a ∈ X2 → a ∉ X1 → Ev a ∈ Z := by
      intro a heX ha2 ha1
      have hmem : Ev a ∈ X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) :=
        ⟨heX, Ev_mem_insert_image_iff.mpr (Or.inr ha2)⟩
      rw [hX] at hmem
      rcases hmem with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd (Ev_mem_insert_image_iff.mp h) ha1
      · exact h
    refine ⟨u,
      (X ∩ Ev '' (X1 \ X2)) ∪ (X ∩ Y ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
        (X \ Set.insert Tick (Ev '' X1)),
      (X ∩ Ev '' (X2 \ X1)) ∪ (X ∩ Z ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
        (X \ Set.insert Tick (Ev '' X2)),
      ?_, ?_, u rest-tr X1, u rest-tr X2, par_tr_rest_tr_if hsu, ?_, ?_⟩
    · congr 1
      exact in_failures_Alpha_parallel_lm2 hsub
    · rw [image_union_Tick]
      exact in_failures_Alpha_parallel_lm3
    · rw [in_failures_Parallel_SKIP_comp]
      refine ⟨u rest-tr X1,
        (X ∩ Ev '' (X1 \ X2)) ∪ (X ∩ Y ∩ Set.insert Tick (Ev '' (X1 ∩ X2))),
        X \ Set.insert Tick (Ev '' X1), rfl, memF_F2 hP ?_, rest_tr_subset_event, ?_⟩
      · rintro e (⟨he, ⟨a, ⟨ha1, ha2⟩, rfl⟩⟩ | ⟨⟨-, hY⟩, -⟩)
        · exact hYmem a he ha1 ha2
        · exact hY
      · rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨-, hne⟩, hIns⟩
        exact hne hIns
    · rw [in_failures_Parallel_SKIP_comp]
      refine ⟨u rest-tr X2,
        (X ∩ Ev '' (X2 \ X1)) ∪ (X ∩ Z ∩ Set.insert Tick (Ev '' (X1 ∩ X2))),
        X \ Set.insert Tick (Ev '' X2), rfl, memF_F2 hQ ?_, rest_tr_subset_event, ?_⟩
      · rintro e (⟨he, ⟨a, ⟨ha2, ha1⟩, rfl⟩⟩ | ⟨⟨-, hZ⟩, -⟩)
        · exact hZmem a he ha2 ha1
        · exact hZ
      · rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨-, hne⟩, hIns⟩
        exact hne hIns

/- (*** Semantics for alphabetized parallel on F ***) -/

theorem failures_Alpha_parallel
    {P Q : proc p α} {X1 X2 : Set α} {M : p → domFType α} :
    failures (P |[X1,X2]| Q) M =
      CollectF (fun f : failure α =>
        ∃ u X,
          f = (u, X) ∧
            ∃ Y Z,
              X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) =
                (Y ∩ Set.insert Tick (Ev '' X1)) ∪
                  (Z ∩ Set.insert Tick (Ev '' X2)) ∧
              (u rest-tr X1, Y) :f failures P M ∧
              (u rest-tr X2, Z) :f failures Q M ∧
              sett u ⊆ Set.insert Tick (Ev '' (X1 ∪ X2))) := by
  rw [← CollectF_open (F := failures (P |[X1,X2]| Q) M)]
  apply CollectF_eq
  intro f
  exact propext
    (in_failures_Alpha_parallel (f := f) (P := P) (Q := Q) (X1 := X1) (X2 := X2) (M := M))

end
