           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_traces
import LeanCspProver.CSP_F.CSP_F_failures

open SumType

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.          -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

/-
(*********************************************************
                        domF
 *********************************************************)
-/

/- (*** unpaired forms of the healthiness conditions (Lean port helpers) ***) -/

theorem HC_T2_pair {T : domTType α} {F : setFType α} :
    HC_T2 (T, F) ↔ ∀ s X, (s, X) :f F → s :t T :=
  Iff.rfl

theorem HC_F3_pair {T : domTType α} {F : setFType α} :
    HC_F3 (T, F) ↔
      ∀ s X Y, (s, X) :f F → noTick s →
        (∀ a, a ∈ Y → ¬ (s ^^^ (Abs_trace [a] : traceType α)) :t T) →
          (s, X ∪ Y) :f F :=
  Iff.rfl

theorem HC_T3_F4_pair {T : domTType α} {F : setFType α} :
    HC_T3_F4 (T, F) ↔
      ∀ s, ((s ^^^ (Abs_trace [event.Tick] : traceType α)) :t T ∧ noTick s) →
        ((s, Evset) :f F ∧
          ∀ X, (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f F) :=
  Iff.rfl

theorem domF_pair {T : domTType α} {F : setFType α} :
    (T, F) ∈ domF (α := α) ↔ (HC_T2 (T, F) ∧ HC_T3 (T, F) ∧ HC_F3 (T, F) ∧ HC_F4 (T, F)) :=
  Iff.rfl

/- --------------------------------*
 |             STOP               |
 *-------------------------------- -/

/- T2 -/

theorem STOP_T2 {M : p → domFType α} :
    HC_T2 (traces proc.STOP (fstF ∘ M), failures proc.STOP M) := by
  rw [HC_T2_pair]
  intro s X h
  obtain ⟨Y, hY⟩ := in_failures_STOP.mp h
  rw [Prod.mk.injEq] at hY
  rw [in_traces_STOP]
  exact hY.1

/- F3 -/

theorem STOP_F3 {M : p → domFType α} :
    HC_F3 (traces proc.STOP (fstF ∘ M), failures proc.STOP M) := by
  rw [HC_F3_pair]
  intro s X Y h _ _
  obtain ⟨Z, hZ⟩ := in_failures_STOP.mp h
  rw [Prod.mk.injEq] at hZ
  refine in_failures_STOP.mpr ⟨X ∪ Y, ?_⟩
  rw [hZ.1]

/- T3_F4 -/

theorem STOP_T3_F4 {M : p → domFType α} :
    HC_T3_F4 (traces proc.STOP (fstF ∘ M), failures proc.STOP M) := by
  rw [HC_T3_F4_pair]
  intro s hs
  rw [in_traces_STOP] at hs
  exact absurd ((appt_nil hs.2).mp hs.1).2 (by simp)

/- (*** STOP_domF ***) -/

theorem STOP_domF {M : p → domFType α} :
    (traces proc.STOP (fstF ∘ M), failures proc.STOP M) ∈ domF (α := α) := by
  exact ⟨STOP_T2, (HC_T3_F4_iff.mp STOP_T3_F4).1, STOP_F3, (HC_T3_F4_iff.mp STOP_T3_F4).2⟩

/- --------------------------------*
 |             SKIP               |
 *-------------------------------- -/

/- T2 -/

theorem SKIP_T2 {M : p → domFType α} :
    HC_T2 (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M) := by
  rw [HC_T2_pair]
  intro s X h
  rw [in_traces_SKIP]
  rcases in_failures_SKIP.mp h with ⟨Z, hEq, _⟩ | ⟨Z, hEq⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · exact Or.inl hEq.1
  · exact Or.inr hEq.1

/- F3 -/

theorem SKIP_F3 {M : p → domFType α} :
    HC_F3 (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M) := by
  rw [HC_F3_pair]
  intro s X Y h hn hY
  rcases in_failures_SKIP.mp h with ⟨Z, hEq, hZ⟩ | ⟨Z, hEq⟩
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    refine in_failures_SKIP.mpr (Or.inl ⟨_, rfl, ?_⟩)
    intro e he
    rcases he with he | he
    · exact hZ he
    · intro hTick
      subst hTick
      exact hY event.Tick he (in_traces_SKIP.mpr (Or.inr (by simp)))
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hs, _⟩ := hEq
    subst hs
    exact absurd hn not_noTick_Tick

/- T3_F4 -/

theorem SKIP_T3_F4 {M : p → domFType α} :
    HC_T3_F4 (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M) := by
  rw [HC_T3_F4_pair]
  intro s hs
  rcases in_traces_SKIP.mp hs.1 with h' | h'
  · exact absurd ((appt_nil hs.2).mp h').2 (by simp)
  · have hsnil : s = <> := by
      rcases (appt_decompo_one (Or.inl hs.2)).mp h' with ⟨_, h2⟩ | ⟨h1, _⟩
      · simp at h2
      · exact h1
    subst hsnil
    constructor
    · exact in_failures_SKIP.mpr (Or.inl ⟨Evset, rfl, Set.Subset.refl _⟩)
    · intro X
      refine in_failures_SKIP.mpr (Or.inr ⟨X, ?_⟩)
      simp

/- (*** SKIP_domF ***) -/

theorem SKIP_domF {M : p → domFType α} :
    (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M) ∈ domF (α := α) := by
  exact ⟨SKIP_T2, (HC_T3_F4_iff.mp SKIP_T3_F4).1, SKIP_F3, (HC_T3_F4_iff.mp SKIP_T3_F4).2⟩

/- --------------------------------*
 |              DIV               |
 *-------------------------------- -/

/- T2 -/

theorem DIV_T2 {M : p → domFType α} :
    HC_T2 (traces proc.DIV (fstF ∘ M), failures proc.DIV M) := by
  rw [HC_T2_pair]
  intro s X h
  exact absurd h in_failures_DIV

/- F3 -/

theorem DIV_F3 {M : p → domFType α} :
    HC_F3 (traces proc.DIV (fstF ∘ M), failures proc.DIV M) := by
  rw [HC_F3_pair]
  intro s X Y h _ _
  exact absurd h in_failures_DIV

/- T3_F4 -/

theorem DIV_T3_F4 {M : p → domFType α} :
    HC_T3_F4 (traces proc.DIV (fstF ∘ M), failures proc.DIV M) := by
  rw [HC_T3_F4_pair]
  intro s hs
  rw [in_traces_DIV] at hs
  exact absurd ((appt_nil hs.2).mp hs.1).2 (by simp)

/- (*** DIV_domF ***) -/

theorem DIV_domF {M : p → domFType α} :
    (traces proc.DIV (fstF ∘ M), failures proc.DIV M) ∈ domF (α := α) := by
  exact ⟨DIV_T2, (HC_T3_F4_iff.mp DIV_T3_F4).1, DIV_F3, (HC_T3_F4_iff.mp DIV_T3_F4).2⟩

theorem union_union_diff {A B C : Set (event α)} :
    (A ∪ B) ∪ (C \ A) = A ∪ (B ∪ C) := by
  ext e
  constructor
  · rintro ((he | he) | ⟨he, _⟩)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  · rintro (he | he | he)
    · exact Or.inl (Or.inl he)
    · exact Or.inl (Or.inr he)
    · by_cases hx : e ∈ A
      · exact Or.inl (Or.inl hx)
      · exact Or.inr ⟨he, hx⟩

theorem union_union_diff' {A B C : Set (event α)} :
    (B ∪ A) ∪ (C \ A) = (B ∪ C) ∪ A := by
  ext e
  constructor
  · rintro ((he | he) | ⟨he, _⟩)
    · exact Or.inl (Or.inl he)
    · exact Or.inr he
    · exact Or.inl (Or.inr he)
  · rintro ((he | he) | he)
    · exact Or.inl (Or.inl he)
    · by_cases hx : e ∈ A
      · exact Or.inl (Or.inr hx)
      · exact Or.inr ⟨he, hx⟩
    · exact Or.inl (Or.inr he)

theorem head_Ev_of_appt_Tick {s t : traceType α} {a : α} :
    noTick s → s ^^^ (Abs_trace [event.Tick] : traceType α) = Abs_trace [event.Ev a] ^^^ t →
      ∃ s', s = Abs_trace [event.Ev a] ^^^ s' ∧
        t = s' ^^^ (Abs_trace [event.Tick] : traceType α) ∧ noTick s' := by
  intro hn heq
  rcases trace_nil_or_Tick_or_Ev s with rfl | rfl | ⟨b, s', rfl⟩
  · rw [appt_nil_left] at heq
    rcases (appt_decompo_one_sym (Or.inl (noTick_Ev a))).mp heq with ⟨_, h2⟩ | ⟨h1, _⟩ <;>
      simp at *
  · exact absurd hn not_noTick_Tick
  · have hn' : noTick s' := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hn).2
    rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hn')] at heq
    obtain ⟨hab, hst⟩ := appt_same_head_only_if heq
    refine ⟨s', ?_, hst.symm, hn'⟩
    rw [hab]

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

/- T2 -/

theorem Act_prefix_T2 {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M) := by
  intro h
  rw [HC_T2_pair]
  intro s X hf
  rw [in_traces_Act_prefix]
  rcases in_failures_Act_prefix.mp hf with ⟨Z, hEq, _⟩ | ⟨t, Z, hEq, ht⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · exact Or.inl hEq.1
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    exact Or.inr ⟨t, rfl, h.1 t _ ht⟩

/- F3 -/

theorem Act_prefix_F3 {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M) := by
  intro h
  rw [HC_F3_pair]
  intro s X Y hf hn hY
  rcases in_failures_Act_prefix.mp hf with ⟨Z, hEq, hZ⟩ | ⟨t, Z, hEq, ht⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    refine in_failures_Act_prefix.mpr (Or.inl ⟨_, rfl, ?_⟩)
    intro hmem
    rcases hmem with hmem | hmem
    · exact hZ hmem
    · refine hY (event.Ev a) hmem ?_
      rw [appt_nil_left, in_traces_Act_prefix]
      exact Or.inr ⟨<>, by simp, nilt_in_T⟩
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    have hn' : noTick t := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hn).2
    refine in_failures_Act_prefix.mpr (Or.inr ⟨t, _, rfl, ?_⟩)
    refine h.2.2.1 t _ Y ht hn' ?_
    intro b hb hmem
    refine hY b hb ?_
    rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hn'), in_traces_Act_prefix]
    exact Or.inr ⟨t ^^^ Abs_trace [b], rfl, hmem⟩

/- T3_F4 -/

theorem Act_prefix_T3_F4 {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M) := by
  intro h
  rw [HC_T3_F4_pair]
  intro s hs
  rcases in_traces_Act_prefix.mp hs.1 with h' | ⟨t, heq, ht⟩
  · exact absurd ((appt_nil hs.2).mp h').2 (by simp)
  · obtain ⟨s', hs', htt, hn'⟩ := head_Ev_of_appt_Tick hs.2 heq
    subst htt
    subst hs'
    obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨h.2.1, h.2.2.2⟩) s' ⟨ht, hn'⟩
    constructor
    · exact in_failures_Act_prefix.mpr (Or.inr ⟨s', Evset, rfl, hF4⟩)
    · intro X
      refine in_failures_Act_prefix.mpr (Or.inr ⟨s' ^^^ Abs_trace [event.Tick], X, ?_, hT3 X⟩)
      rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hn')]

/- (*** Act_prefix_domF ***) -/

theorem Act_prefix_domF {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M) ∈ domF (α := α) := by
  intro h
  exact ⟨Act_prefix_T2 h, (HC_T3_F4_iff.mp (Act_prefix_T3_F4 h)).1, Act_prefix_F3 h,
    (HC_T3_F4_iff.mp (Act_prefix_T3_F4 h)).2⟩

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- T2 -/

theorem Ext_pre_choice_T2 {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      HC_T2
        (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M),
          failures (proc.Ext_pre_choice X Pf) M) := by
  intro h
  rw [HC_T2_pair]
  intro s X0 hf
  rw [in_traces_Ext_pre_choice]
  rcases in_failures_Ext_pre_choice.mp hf with ⟨Z, hEq, _⟩ | ⟨a, t, Z, hEq, ht, haX⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · exact Or.inl hEq.1
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    exact Or.inr ⟨a, t, rfl, (h a).1 t _ ht, haX⟩

/- F3 -/

theorem Ext_pre_choice_F3 {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      HC_F3
        (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M),
          failures (proc.Ext_pre_choice X Pf) M) := by
  intro h
  rw [HC_F3_pair]
  intro s X0 Y0 hf hn hY
  rcases in_failures_Ext_pre_choice.mp hf with ⟨Z, hEq, hZ⟩ | ⟨a, t, Z, hEq, ht, haX⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    refine in_failures_Ext_pre_choice.mpr (Or.inl ⟨_, rfl, ?_⟩)
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨heX, heU⟩
    rcases heU with heU | heU
    · rw [Set.eq_empty_iff_forall_notMem] at hZ
      exact hZ e ⟨heX, heU⟩
    · obtain ⟨b, hbX, rfl⟩ := heX
      refine hY (event.Ev b) heU ?_
      rw [appt_nil_left, in_traces_Ext_pre_choice]
      exact Or.inr ⟨b, <>, by simp, nilt_in_T, hbX⟩
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    have hn' : noTick t := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hn).2
    refine in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, t, _, rfl, ?_, haX⟩)
    refine (h a).2.2.1 t _ Y0 ht hn' ?_
    intro b hb hmem
    refine hY b hb ?_
    rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hn'), in_traces_Ext_pre_choice]
    exact Or.inr ⟨a, t ^^^ Abs_trace [b], rfl, hmem, haX⟩

/- T3_F4 -/

theorem Ext_pre_choice_T3_F4 {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      HC_T3_F4
        (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M),
          failures (proc.Ext_pre_choice X Pf) M) := by
  intro h
  rw [HC_T3_F4_pair]
  intro s hs
  rcases in_traces_Ext_pre_choice.mp hs.1 with h' | ⟨a, t, heq, ht, haX⟩
  · exact absurd ((appt_nil hs.2).mp h').2 (by simp)
  · obtain ⟨s', hs', htt, hn'⟩ := head_Ev_of_appt_Tick hs.2 heq
    subst htt
    subst hs'
    obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨(h a).2.1, (h a).2.2.2⟩) s' ⟨ht, hn'⟩
    constructor
    · exact in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', Evset, rfl, hF4, haX⟩)
    · intro X0
      refine in_failures_Ext_pre_choice.mpr
        (Or.inr ⟨a, s' ^^^ Abs_trace [event.Tick], X0, ?_, hT3 X0, haX⟩)
      rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hn')]

/- (*** Ext_pre_choice_domF ***) -/

theorem Ext_pre_choice_domF {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M), failures (proc.Ext_pre_choice X Pf) M) ∈
        domF (α := α) := by
  intro h
  exact ⟨Ext_pre_choice_T2 h, (HC_T3_F4_iff.mp (Ext_pre_choice_T3_F4 h)).1,
    Ext_pre_choice_F3 h, (HC_T3_F4_iff.mp (Ext_pre_choice_T3_F4 h)).2⟩

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- T2 -/

theorem Ext_choice_T2 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M) := by
  intro h1 h2
  rw [HC_T2_pair]
  intro s X hf
  rcases in_failures_Ext_choice.mp hf with ⟨_, hP, _⟩ | ⟨s', _, hPQ, _⟩ | ⟨Z, hEq, _, _⟩
  · exact in_traces_Ext_choice.mpr (Or.inl (h1.1 s X hP))
  · rcases hPQ with hP | hQ
    · exact in_traces_Ext_choice.mpr (Or.inl (h1.1 s X hP))
    · exact in_traces_Ext_choice.mpr (Or.inr (h2.1 s X hQ))
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hs, _⟩ := hEq
    subst hs
    exact nilt_in_T

/- F3 -/

theorem Ext_choice_F3 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M) := by
  intro h1 h2
  rw [HC_F3_pair]
  intro s X Y hf hn hY
  rcases in_failures_Ext_choice.mp hf with ⟨⟨Z, hEq⟩, hP, hQ⟩ | ⟨s', ⟨Z, hEq⟩, hPQ, hne⟩ |
    ⟨Z, hEq, hTick, hZ⟩ <;> rw [Prod.mk.injEq] at hEq
  · obtain ⟨hs, _⟩ := hEq
    subst hs
    refine in_failures_Ext_choice.mpr (Or.inl ⟨⟨_, rfl⟩, ?_, ?_⟩)
    · refine h1.2.2.1 _ X Y hP hn ?_
      intro a ha hmem
      exact hY a ha (in_traces_Ext_choice.mpr (Or.inl hmem))
    · refine h2.2.2.1 _ X Y hQ hn ?_
      intro a ha hmem
      exact hY a ha (in_traces_Ext_choice.mpr (Or.inr hmem))
  · obtain ⟨hs, _⟩ := hEq
    subst hs
    refine in_failures_Ext_choice.mpr (Or.inr (Or.inl ⟨_, ⟨_, rfl⟩, ?_, hne⟩))
    rcases hPQ with hP | hQ
    · refine Or.inl (h1.2.2.1 _ X Y hP hn ?_)
      intro a ha hmem
      exact hY a ha (in_traces_Ext_choice.mpr (Or.inl hmem))
    · refine Or.inr (h2.2.2.1 _ X Y hQ hn ?_)
      intro a ha hmem
      exact hY a ha (in_traces_Ext_choice.mpr (Or.inr hmem))
  · obtain ⟨hs, hX⟩ := hEq
    subst hs
    subst hX
    refine in_failures_Ext_choice.mpr (Or.inr (Or.inr ⟨_, rfl, hTick, ?_⟩))
    intro e he
    rcases he with he | he
    · exact hZ he
    · intro hTickEq
      subst hTickEq
      refine hY event.Tick he ?_
      rw [appt_nil_left]
      exact in_traces_Ext_choice.mpr hTick

/- T3_F4 -/

theorem Ext_choice_T3_F4 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M) := by
  intro h1 h2
  rw [HC_T3_F4_pair]
  intro s hs
  have hP := HC_T3_F4_iff.mpr ⟨h1.2.1, h1.2.2.2⟩
  have hQ := HC_T3_F4_iff.mpr ⟨h2.2.1, h2.2.2.2⟩
  have hTne : s ^^^ (Abs_trace [event.Tick] : traceType α) ≠ <> := by
    intro h0
    exact absurd ((appt_nil hs.2).mp h0).2 (by simp)
  rcases in_traces_Ext_choice.mp hs.1 with h' | h'
  · obtain ⟨hF4, hT3⟩ := hP s ⟨h', hs.2⟩
    constructor
    · by_cases hs0 : s = <>
      · subst hs0
        refine in_failures_Ext_choice.mpr
          (Or.inr (Or.inr ⟨Evset, rfl, Or.inl ?_, Set.Subset.refl _⟩))
        rwa [appt_nil_left] at h'
      · exact in_failures_Ext_choice.mpr (Or.inr (Or.inl ⟨s, ⟨Evset, rfl⟩, Or.inl hF4, hs0⟩))
    · intro X
      exact in_failures_Ext_choice.mpr
        (Or.inr (Or.inl ⟨_, ⟨X, rfl⟩, Or.inl (hT3 X), hTne⟩))
  · obtain ⟨hF4, hT3⟩ := hQ s ⟨h', hs.2⟩
    constructor
    · by_cases hs0 : s = <>
      · subst hs0
        refine in_failures_Ext_choice.mpr
          (Or.inr (Or.inr ⟨Evset, rfl, Or.inr ?_, Set.Subset.refl _⟩))
        rwa [appt_nil_left] at h'
      · exact in_failures_Ext_choice.mpr (Or.inr (Or.inl ⟨s, ⟨Evset, rfl⟩, Or.inr hF4, hs0⟩))
    · intro X
      exact in_failures_Ext_choice.mpr
        (Or.inr (Or.inl ⟨_, ⟨X, rfl⟩, Or.inr (hT3 X), hTne⟩))

/- (*** Ext_choice_domF ***) -/

theorem Ext_choice_domF {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M) ∈ domF (α := α) := by
  intro h1 h2
  exact ⟨Ext_choice_T2 h1 h2, (HC_T3_F4_iff.mp (Ext_choice_T3_F4 h1 h2)).1,
    Ext_choice_F3 h1 h2, (HC_T3_F4_iff.mp (Ext_choice_T3_F4 h1 h2)).2⟩

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- T2 -/

theorem Int_choice_T2 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M) := by
  intro h1 h2
  rw [HC_T2_pair]
  intro s X h
  rw [in_traces_Int_choice]
  rcases in_failures_Int_choice.mp h with h' | h'
  · exact Or.inl (h1.1 s X h')
  · exact Or.inr (h2.1 s X h')

/- F3 -/

theorem Int_choice_F3 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M) := by
  intro h1 h2
  rw [HC_F3_pair]
  intro s X Y h hn hY
  rw [in_failures_Int_choice]
  rcases in_failures_Int_choice.mp h with h' | h'
  · refine Or.inl (h1.2.2.1 s X Y h' hn ?_)
    intro a ha hmem
    exact hY a ha (in_traces_Int_choice.mpr (Or.inl hmem))
  · refine Or.inr (h2.2.2.1 s X Y h' hn ?_)
    intro a ha hmem
    exact hY a ha (in_traces_Int_choice.mpr (Or.inr hmem))

/- T3_F4 -/

theorem Int_choice_T3_F4 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M) := by
  intro h1 h2
  rw [HC_T3_F4_pair]
  intro s hs
  have hP := HC_T3_F4_iff.mpr ⟨h1.2.1, h1.2.2.2⟩
  have hQ := HC_T3_F4_iff.mpr ⟨h2.2.1, h2.2.2.2⟩
  rcases in_traces_Int_choice.mp hs.1 with h' | h'
  · obtain ⟨hF4, hT3⟩ := hP s ⟨h', hs.2⟩
    exact ⟨in_failures_Int_choice.mpr (Or.inl hF4),
      fun X => in_failures_Int_choice.mpr (Or.inl (hT3 X))⟩
  · obtain ⟨hF4, hT3⟩ := hQ s ⟨h', hs.2⟩
    exact ⟨in_failures_Int_choice.mpr (Or.inr hF4),
      fun X => in_failures_Int_choice.mpr (Or.inr (hT3 X))⟩

/- (*** Int_choice_domF ***) -/

theorem Int_choice_domF {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M) ∈ domF (α := α) := by
  intro h1 h2
  exact ⟨Int_choice_T2 h1 h2, (HC_T3_F4_iff.mp (Int_choice_T3_F4 h1 h2)).1,
    Int_choice_F3 h1 h2, (HC_T3_F4_iff.mp (Int_choice_T3_F4 h1 h2)).2⟩

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- T2 -/

theorem Union_proc_T2 {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      HC_T2
        (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
          CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c)) := by
  intro h
  rw [HC_T2_pair]
  intro s X0 hf
  obtain ⟨c, hc, hsX⟩ := in_failures_Union_proc.mp hf
  exact in_traces_Union_proc.mpr (Or.inr ⟨c, hc, (h c).1 s X0 hsX⟩)

theorem Rep_int_choice_T2 {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      HC_T2
        (traces (proc.Rep_int_choice C Pf) (fstF ∘ M),
          failures (proc.Rep_int_choice C Pf) M) := by
  intro h
  exact Union_proc_T2 (C := sumset C) (Tf := fun c => traces (Pf c) (fstF ∘ M))
    (Ff := fun c => failures (Pf c) M) h

/- F3 -/

theorem Union_proc_F3 {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      HC_F3
        (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
          CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c)) := by
  intro h
  rw [HC_F3_pair]
  intro s X0 Y0 hf hn hY
  obtain ⟨c, hc, hsX⟩ := in_failures_Union_proc.mp hf
  refine in_failures_Union_proc.mpr ⟨c, hc, ?_⟩
  refine (h c).2.2.1 s X0 Y0 hsX hn ?_
  intro a ha hmem
  exact hY a ha (in_traces_Union_proc.mpr (Or.inr ⟨c, hc, hmem⟩))

/- The Isabelle theorem `Rep_int_choice_nat` is named `Rep_int_choice_F3`
   here to avoid clashing with the existing definition `Rep_int_choice_nat`. -/
theorem Rep_int_choice_F3 {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      HC_F3
        (traces (proc.Rep_int_choice C Pf) (fstF ∘ M),
          failures (proc.Rep_int_choice C Pf) M) := by
  intro h
  exact Union_proc_F3 (C := sumset C) (Tf := fun c => traces (Pf c) (fstF ∘ M))
    (Ff := fun c => failures (Pf c) M) h

/- T3_F4 -/

theorem Union_proc_T3_F4 {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      HC_T3_F4
        (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
          CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c)) := by
  intro h
  rw [HC_T3_F4_pair]
  intro s hs
  rcases in_traces_Union_proc.mp hs.1 with h' | ⟨c, hc, h'⟩
  · exact absurd ((appt_nil hs.2).mp h').2 (by simp)
  · obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨(h c).2.1, (h c).2.2.2⟩) s ⟨h', hs.2⟩
    exact ⟨in_failures_Union_proc.mpr ⟨c, hc, hF4⟩,
      fun X0 => in_failures_Union_proc.mpr ⟨c, hc, hT3 X0⟩⟩

theorem Rep_int_choice_T3_F4 {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      HC_T3_F4
        (traces (proc.Rep_int_choice C Pf) (fstF ∘ M), failures (proc.Rep_int_choice C Pf) M) := by
  intro h
  exact Union_proc_T3_F4 (C := sumset C) (Tf := fun c => traces (Pf c) (fstF ∘ M))
    (Ff := fun c => failures (Pf c) M) h

/- (*** F ***) -/

theorem Union_proc_domF {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
        CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c)) ∈ domF (α := α) := by
  intro h
  exact ⟨Union_proc_T2 h, (HC_T3_F4_iff.mp (Union_proc_T3_F4 h)).1, Union_proc_F3 h,
    (HC_T3_F4_iff.mp (Union_proc_T3_F4 h)).2⟩

/- (*** Rep_int_choice_domF ***) -/

theorem Rep_int_choice_domF {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      (traces (proc.Rep_int_choice C Pf) (fstF ∘ M), failures (proc.Rep_int_choice C Pf) M) ∈
        domF (α := α) := by
  intro h
  exact Union_proc_domF (C := sumset C) (Tf := fun c => traces (Pf c) (fstF ∘ M))
    (Ff := fun c => failures (Pf c) M) h

/- --------------------------------*
 |               IF               |
 *-------------------------------- -/

/- T2 -/

theorem IF_T2 {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M) := by
  intro h1 h2
  cases b
  · exact h2.1
  · exact h1.1

/- F3 -/

theorem IF_F3 {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M) := by
  intro h1 h2
  cases b
  · exact h2.2.2.1
  · exact h1.2.2.1

/- T3_F4 -/

theorem IF_T3_F4 {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M) := by
  intro h1 h2
  cases b
  · exact HC_T3_F4_iff.mpr ⟨h2.2.1, h2.2.2.2⟩
  · exact HC_T3_F4_iff.mpr ⟨h1.2.1, h1.2.2.2⟩

/- (*** IF_domF ***) -/

theorem IF_domF {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M) ∈
          domF (α := α) := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** T2 ***) -/

theorem Parallel_T2 {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M) := by
  intro h1 h2
  rw [HC_T2_pair]
  intro u X0 hf
  obtain ⟨u', Y, Z, hEq, _, s, t, hpar, hsY, htZ⟩ := in_failures_Parallel.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hu, _⟩ := hEq
  subst hu
  exact in_traces_Parallel.mpr ⟨s, t, hpar, h1.1 s _ hsY, h2.1 t _ htZ⟩

/- (*** F3 ***) -/

/- Lean note: a faithful transcription of the Isabelle original
     `(X1 Un (X2 Un X3)) - X = ((X1 - X) Un (X2 - X)) Un (X3 - X)`
   needs the explicit parentheses below: `\` binds tighter than `∪` in Lean,
   so the unparenthesised statement would parse as `X1 ∪ ((X2 ∪ X3) \ X)`,
   which is false (take `X1 = X = {a}`, `X2 = X3 = ∅`). -/
theorem Parallel_F3_lm1 {X1 X2 X3 X : Set α} :
    (X1 ∪ (X2 ∪ X3)) \ X = (X1 \ X) ∪ (X2 \ X) ∪ (X3 \ X) := by
  ext e
  constructor
  · rintro ⟨he | he | he, heX⟩
    · exact Or.inl (Or.inl ⟨he, heX⟩)
    · exact Or.inl (Or.inr ⟨he, heX⟩)
    · exact Or.inr ⟨he, heX⟩
  · rintro ((⟨he, heX⟩ | ⟨he, heX⟩) | ⟨he, heX⟩)
    · exact ⟨Or.inl he, heX⟩
    · exact ⟨Or.inr (Or.inl he), heX⟩
    · exact ⟨Or.inr (Or.inr he), heX⟩

theorem Parallel_F3_lm2 {X1 X2 Y1 Y2 : Set α} :
    X1 = X2 → Y1 = Y2 → X1 ∪ Y1 = X2 ∪ Y2 := by
  intro h1 h2
  rw [h1, h2]

theorem Parallel_F3 {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M) := by
  intro h1 h2
  rw [HC_F3_pair]
  intro u X0 Y0 hf hn hY
  obtain ⟨u', Y, Z, hEq, hdiff, s, t, hpar, hsY, htZ⟩ := in_failures_Parallel.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hu, hX⟩ := hEq
  subst hu
  subst hX
  have hns : noTick s := (par_tr_noTick_if hpar hn).1
  have hnt : noTick t := (par_tr_noTick_if hpar hn).2
  have hsT : s :t traces P (fstF ∘ M) := h1.1 s _ hsY
  have htT : t :t traces Q (fstF ∘ M) := h2.1 t _ htZ
  have hnotP : ∀ a, a ∈ Y0 → a ∉ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) →
      ¬ ((s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) := by
    intro a ha haD hmem
    refine hY a ha (in_traces_Parallel.mpr ⟨s ^^^ Abs_trace [a], t, ?_, hmem, htT⟩)
    exact par_tr_last_if hn (Or.inr (Or.inl ⟨fun hc => haD (Or.inl hc),
      fun hc => haD (Or.inr hc), s, hpar, rfl, hns, hnt⟩))
  have hnotQ : ∀ a, a ∈ Y0 → a ∉ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) →
      ¬ ((t ^^^ (Abs_trace [a] : traceType α)) :t traces Q (fstF ∘ M)) := by
    intro a ha haD hmem
    refine hY a ha (in_traces_Parallel.mpr ⟨s, t ^^^ Abs_trace [a], ?_, hsT, hmem⟩)
    exact par_tr_last_if hn (Or.inr (Or.inr ⟨fun hc => haD (Or.inl hc),
      fun hc => haD (Or.inr hc), t, hpar, rfl, hns, hnt⟩))
  have hnotQ2 : ∀ a, a ∈ Y0 → a ∈ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) →
      ((s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) →
      ¬ ((t ^^^ (Abs_trace [a] : traceType α)) :t traces Q (fstF ∘ M)) := by
    intro a ha haD hsP hmem
    refine hY a ha (in_traces_Parallel.mpr
      ⟨s ^^^ Abs_trace [a], t ^^^ Abs_trace [a], ?_, hsP, hmem⟩)
    refine par_tr_last_if hn (Or.inl ⟨?_, s, t, hpar, rfl, rfl, hns, hnt⟩)
    rcases haD with hc | hc
    · exact Or.inl hc
    · exact Or.inr hc
  refine in_failures_Parallel.mpr
    ⟨u,
      Y ∪ ((Y0 \ (event.Ev '' X ∪ ({event.Tick} : Set (event α)))) ∪
        {a | a ∈ Y0 ∧ a ∈ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) ∧
          ¬ ((s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M))}),
      Z ∪ ((Y0 \ (event.Ev '' X ∪ ({event.Tick} : Set (event α)))) ∪
        {a | a ∈ Y0 ∧ a ∈ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) ∧
          ((s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M))}),
      ?_, ?_, s, t, hpar, ?_, ?_⟩
  · rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    ext e
    constructor
    · rintro ((he | he) | he)
      · exact Or.inl (Or.inl he)
      · exact Or.inr (Or.inl he)
      · by_cases hD : e ∈ (event.Ev '' X ∪ ({event.Tick} : Set (event α)))
        · by_cases hP : (s ^^^ (Abs_trace [e] : traceType α)) :t traces P (fstF ∘ M)
          · exact Or.inr (Or.inr (Or.inr ⟨he, hD, hP⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨he, hD, hP⟩))
        · exact Or.inl (Or.inr (Or.inl ⟨he, hD⟩))
    · rintro ((he | (⟨he, _⟩ | ⟨he, _, _⟩)) | (he | (⟨he, _⟩ | ⟨he, _, _⟩)))
      · exact Or.inl (Or.inl he)
      · exact Or.inr he
      · exact Or.inr he
      · exact Or.inl (Or.inr he)
      · exact Or.inr he
      · exact Or.inr he
  · ext e
    constructor
    · rintro ⟨he | (⟨he1, he2⟩ | ⟨_, he2, _⟩), heD⟩
      · refine ⟨Or.inl ?_, heD⟩
        have hmem : e ∈ Y \ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) := ⟨he, heD⟩
        rw [hdiff] at hmem
        exact hmem.1
      · exact ⟨Or.inr (Or.inl ⟨he1, he2⟩), heD⟩
      · exact absurd he2 heD
    · rintro ⟨he | (⟨he1, he2⟩ | ⟨_, he2, _⟩), heD⟩
      · refine ⟨Or.inl ?_, heD⟩
        have hmem : e ∈ Z \ (event.Ev '' X ∪ ({event.Tick} : Set (event α))) := ⟨he, heD⟩
        rw [← hdiff] at hmem
        exact hmem.1
      · exact ⟨Or.inr (Or.inl ⟨he1, he2⟩), heD⟩
      · exact absurd he2 heD
  · refine h1.2.2.1 s Y _ hsY hns ?_
    rintro a (⟨ha, haD⟩ | ⟨ha, haD, hnp⟩)
    · exact hnotP a ha haD
    · exact hnp
  · refine h2.2.2.1 t Z _ htZ hnt ?_
    rintro a (⟨ha, haD⟩ | ⟨ha, haD, hp⟩)
    · exact hnotQ a ha haD
    · exact hnotQ2 a ha haD hp

/- T3_F4 -/

theorem Parallel_T3_F4 {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M) := by
  intro h1 h2
  rw [HC_T3_F4_pair]
  intro u hu
  obtain ⟨s, t, hpar, hsT, htT⟩ := in_traces_Parallel.mp hu.1
  rcases par_tr_last_only_if hpar hu.2 with ⟨_, s', t', hpar', hs, ht, hns', hnt'⟩ |
    ⟨_, hne, _⟩ | ⟨_, hne, _⟩
  · subst hs
    subst ht
    obtain ⟨hF4P, hT3P⟩ := (HC_T3_F4_iff.mpr ⟨h1.2.1, h1.2.2.2⟩) s' ⟨hsT, hns'⟩
    obtain ⟨hF4Q, hT3Q⟩ := (HC_T3_F4_iff.mpr ⟨h2.2.1, h2.2.2.2⟩) t' ⟨htT, hnt'⟩
    constructor
    · exact in_failures_Parallel.mpr
        ⟨u, Evset, Evset, by rw [Set.union_self], rfl, s', t', hpar', hF4P, hF4Q⟩
    · intro W
      exact in_failures_Parallel.mpr
        ⟨(u ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α), W, W,
          by rw [Set.union_self], rfl,
          (s' ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α),
          (t' ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α),
          hpar, hT3P W, hT3Q W⟩
  · exact absurd rfl hne
  · exact absurd rfl hne

/- (*** Parallel_domF ***) -/

theorem Parallel_domF {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M) ∈ domF (α := α) := by
  intro h1 h2
  exact ⟨Parallel_T2 h1 h2, (HC_T3_F4_iff.mp (Parallel_T3_F4 h1 h2)).1,
    Parallel_F3 h1 h2, (HC_T3_F4_iff.mp (Parallel_T3_F4 h1 h2)).2⟩

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- (*** T2 ***) -/

theorem Hiding_T2 {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M) := by
  intro h
  rw [HC_T2_pair]
  intro u X0 hf
  obtain ⟨s, Y, hEq, hsY⟩ := in_failures_Hiding.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hu, hX⟩ := hEq
  subst hu
  subst hX
  exact in_traces_Hiding.mpr ⟨s, rfl, h.1 s _ hsY⟩

/- (*** F3 ***) -/

theorem Hiding_F3 {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M) := by
  intro h
  rw [HC_F3_pair]
  intro u X0 Y0 hf hn hY
  obtain ⟨s, Y, hEq, hsY⟩ := in_failures_Hiding.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hu, hX⟩ := hEq
  subst hu
  subst hX
  have hns : noTick s := hide_tr_noTick.mp hn
  refine in_failures_Hiding.mpr ⟨s, _, rfl, ?_⟩
  rw [← union_union_diff]
  refine h.2.2.1 s _ _ hsY hns ?_
  rintro a ⟨ha, hax⟩ hmem
  refine hY a ha ?_
  have hhide : hide_tr (Abs_trace [a] : traceType α) X = Abs_trace [a] := by
    refine hide_tr_nohiden ?_
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he1, he2⟩
    rw [sett_one, Set.mem_singleton_iff] at he1
    subst he1
    exact hax he2
  rw [← hhide, ← hide_tr_appt (Or.inl hns)]
  exact in_traces_Hiding.mpr ⟨s ^^^ Abs_trace [a], rfl, hmem⟩

/- T3_F4 -/

theorem Hiding_T3_F4 {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M) := by
  intro h
  rw [HC_T3_F4_pair]
  intro u hu
  obtain ⟨s, hEq, hsT⟩ := in_traces_Hiding.mp hu.1
  obtain ⟨s1, s2, hcond, hs, hu1, hu2⟩ :=
    hide_tr_decompo_only_if (Or.inl hu.2) hEq.symm
  obtain ⟨s2', hs2, hsub, hns2'⟩ := hide_tr_Tick_sett_only_if hu2.symm
  have hns1 : noTick s1 := hide_tr_noTick.mp (hu1 ▸ hu.2)
  have hkey : s = (s1 ^^^ s2') ^^^ (Abs_trace [event.Tick] : traceType α) := by
    rw [hs, hs2, appt_assoc (Or.inl hns1) (Or.inl hns2')]
  have hnk : noTick (s1 ^^^ s2') := decompo_appt_noTick_if hns1 hns2'
  rw [hkey] at hsT
  obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨h.2.1, h.2.2.2⟩) (s1 ^^^ s2') ⟨hsT, hnk⟩
  have hhid : hide_tr (s1 ^^^ s2') X = u := by
    rw [hide_tr_appt (Or.inl hns1), hide_tr_nilt_sett_if hsub, appt_nil_right, hu1]
  constructor
  · refine in_failures_Hiding.mpr ⟨s1 ^^^ s2', Evset, ?_, ?_⟩
    · rw [hhid]
    · rw [Un_Evset]
      exact hF4
  · intro X0
    refine in_failures_Hiding.mpr ⟨s, X0, ?_, ?_⟩
    · rw [hEq]
    · rw [hkey]
      exact hT3 _

/- (*** Hiding_domF ***) -/

theorem Hiding_domF {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M) ∈ domF (α := α) := by
  intro h
  exact ⟨Hiding_T2 h, (HC_T3_F4_iff.mp (Hiding_T3_F4 h)).1, Hiding_F3 h,
    (HC_T3_F4_iff.mp (Hiding_T3_F4 h)).2⟩

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** T2 ***) -/

theorem Renaming_T2 {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M) := by
  intro h
  rw [HC_T2_pair]
  intro t X0 hf
  obtain ⟨s, t', X', hEq, hren, hsX⟩ := in_failures_Renaming.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨ht, hX⟩ := hEq
  subst ht
  subst hX
  exact in_traces_Renaming.mpr ⟨s, hren, h.1 s _ hsX⟩

/- (*** F3 ***) -/

theorem Renaming_F3 {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M) := by
  intro h
  rw [HC_F3_pair]
  intro t X0 Y0 hf hn hY
  obtain ⟨s, t', X', hEq, hren, hsX⟩ := in_failures_Renaming.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨ht, hX⟩ := hEq
  subst ht
  subst hX
  have hns : noTick s := ren_tr_noTick_right hren hn
  refine in_failures_Renaming.mpr ⟨s, _, _, rfl, hren, ?_⟩
  rw [ren_inv_Un]
  refine h.2.2.1 s _ (ren_inv r Y0) hsX hns ?_
  rintro a ⟨eb, hebY, hcase⟩ hmem
  have hab : ren_tr (Abs_trace [a] : traceType α) r (Abs_trace [eb] : traceType α) := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨a0, b0, hr, rfl, rfl⟩
    · exact ren_tr_Tick
    · exact ren_tr_one hr
  exact hY eb hebY
    (in_traces_Renaming.mpr ⟨s ^^^ Abs_trace [a], ren_tr_appt hren hab (Or.inl hns), hmem⟩)

/- T3_F4 -/

theorem Renaming_T3_F4 {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M) := by
  intro h
  rw [HC_T3_F4_pair]
  intro t ht
  obtain ⟨s, hren, hsT⟩ := in_traces_Renaming.mp ht.1
  obtain ⟨s1, s2, hseq, hren1, hren2, hcond⟩ :=
    ren_tr_appt_decompo_right_only_if hren (Or.inl ht.2)
  have hs2 : s2 = Abs_trace [event.Tick] := ren_tr_Tick2.mp hren2
  subst hs2
  have hns1 : noTick s1 := by
    rcases hcond with hn | h0
    · exact hn
    · simp at h0
  subst hseq
  obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨h.2.1, h.2.2.2⟩) s1 ⟨hsT, hns1⟩
  constructor
  · exact in_failures_Renaming.mpr ⟨s1, t, Evset, rfl, hren1, memF_F2 hF4 ren_inv_sub_Evset⟩
  · intro X0
    exact in_failures_Renaming.mpr
      ⟨s1 ^^^ Abs_trace [event.Tick], t ^^^ Abs_trace [event.Tick], X0, rfl, hren,
        hT3 (ren_inv r X0)⟩

/- (*** Renaming_domF ***) -/

theorem Renaming_domF {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M) ∈ domF (α := α) := by
  intro h
  exact ⟨Renaming_T2 h, (HC_T3_F4_iff.mp (Renaming_T3_F4 h)).1, Renaming_F3 h,
    (HC_T3_F4_iff.mp (Renaming_T3_F4 h)).2⟩

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** T2 ***) -/

theorem Seq_compo_T2 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M) := by
  intro h1 h2
  rw [HC_T2_pair]
  intro u X0 hf
  rw [in_traces_Seq_compo]
  rcases in_failures_Seq_compo.mp hf with ⟨t, Z, hEq, htZ, hnt⟩ |
    ⟨s, t, Z, hEq, hTick, htZ, hns⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · obtain ⟨hu, hX⟩ := hEq
    subst hu
    subst hX
    exact Or.inl ⟨u, (rmTick_nochange hnt).symm, h1.1 u _ htZ⟩
  · obtain ⟨hu, hX⟩ := hEq
    subst hu
    subst hX
    exact Or.inr ⟨s, t, rfl, hTick, h2.1 t _ htZ, hns⟩

/- (*** F3 ***) -/

theorem Seq_compo_F3 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M) := by
  intro h1 h2
  rw [HC_F3_pair]
  intro u X0 Y0 hf hn hY
  rcases in_failures_Seq_compo.mp hf with ⟨t, Z, hEq, htZ, hnt⟩ |
    ⟨s, t, Z, hEq, hTick, htZ, hns⟩ <;>
    rw [Prod.mk.injEq] at hEq
  · obtain ⟨hu, hX⟩ := hEq
    subst hu
    subst hX
    refine in_failures_Seq_compo.mpr (Or.inl ⟨u, _, rfl, ?_, hnt⟩)
    rw [← union_union_diff']
    refine h1.2.2.1 u _ _ htZ hnt ?_
    rintro a ⟨ha, hax⟩ hmem
    have hna : noTick (Abs_trace [a] : traceType α) := by
      intro hT
      rw [sett_one, Set.mem_singleton_iff] at hT
      exact hax hT.symm
    refine hY a ha ?_
    rw [in_traces_Seq_compo]
    exact Or.inl ⟨(u ^^^ (Abs_trace [a] : traceType α) : traceType α),
      (rmTick_nochange (decompo_appt_noTick_if hnt hna)).symm, hmem⟩
  · obtain ⟨hu, hX⟩ := hEq
    subst hu
    subst hX
    have hnt : noTick t := (decompo_appt_noTick_only_if (Or.inl hns) hn).2
    refine in_failures_Seq_compo.mpr (Or.inr ⟨s, t, _, rfl, hTick, ?_, hns⟩)
    refine h2.2.2.1 t _ Y0 htZ hnt ?_
    intro a ha hmem
    refine hY a ha ?_
    rw [in_traces_Seq_compo]
    refine Or.inr ⟨s, t ^^^ Abs_trace [a], ?_, hTick, hmem, hns⟩
    rw [appt_assoc (Or.inl hns) (Or.inl hnt)]

/- T3_F4 -/

theorem Seq_compo_T3_F4 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M) := by
  intro h1 h2
  rw [HC_T3_F4_pair]
  intro u hu
  rcases in_traces_Seq_compo.mp hu.1 with ⟨s, hEq, hsT⟩ | ⟨s, t, hEq, hTick, htT, hns⟩
  · exfalso
    have hnr : noTick (u ^^^ (Abs_trace [event.Tick] : traceType α)) := by
      rw [hEq]
      exact noTick_rmTick
    exact absurd (decompo_appt_noTick_only_if (Or.inl hu.2) hnr).2 not_noTick_Tick
  · have hw : ∃ w, u = s ^^^ w ∧ t = w ^^^ (Abs_trace [event.Tick] : traceType α) ∧ noTick w := by
      rcases (appt_decompo (Or.inl hu.2) (Or.inl hns)).mp hEq with ⟨w, hw1, hw2, hw3⟩ |
        ⟨w, hw1, hw2, hw3⟩
      · rcases hw3 with hnw | ⟨_, ht0⟩
        · rcases (appt_decompo_one_sym (Or.inl hnw)).mp hw2 with ⟨hw4, _⟩ | ⟨hw4, hw5⟩
          · subst hw4
            exact absurd hnw not_noTick_Tick
          · subst hw4
            rw [appt_nil_right] at hw1
            refine ⟨<>, ?_, ?_, noTick_nil⟩
            · rw [appt_nil_right]
              exact hw1
            · simp [hw5]
        · subst ht0
          rw [appt_nil_right] at hw2
          subst hw2
          rw [← hw1] at hns
          exact absurd (decompo_appt_noTick_only_if (Or.inl hu.2) hns).2 not_noTick_Tick
      · have hnw : noTick w := by
          rcases hw3 with hnw | ⟨_, ht0⟩
          · exact hnw
          · simp at ht0
        exact ⟨w, hw1, hw2.symm, hnw⟩
    obtain ⟨w, huw, htw, hnw⟩ := hw
    subst htw
    obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨h2.2.1, h2.2.2.2⟩) w ⟨htT, hnw⟩
    subst huw
    constructor
    · exact in_failures_Seq_compo.mpr (Or.inr ⟨s, w, Evset, rfl, hTick, hF4, hns⟩)
    · intro X0
      refine in_failures_Seq_compo.mpr
        (Or.inr ⟨s, (w ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α), X0, ?_,
          hTick, hT3 X0, hns⟩)
      rw [appt_assoc (Or.inl hns) (Or.inl hnw)]

/- (*** Seq_compo_domF ***) -/

theorem Seq_compo_domF {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M) ∈ domF (α := α) := by
  intro h1 h2
  exact ⟨Seq_compo_T2 h1 h2, (HC_T3_F4_iff.mp (Seq_compo_T3_F4 h1 h2)).1,
    Seq_compo_F3 h1 h2, (HC_T3_F4_iff.mp (Seq_compo_T3_F4 h1 h2)).2⟩

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** T2 ***) -/

theorem Depth_rest_T2 {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (P |. n) (fstF ∘ M), failures (P |. n) M) := by
  intro h
  rw [HC_T2_pair]
  intro s X0 hf
  obtain ⟨t, Z, hEq, hsX, hcond⟩ := in_failures_Depth_rest.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hs, hX⟩ := hEq
  subst hs
  subst hX
  refine in_traces_Depth_rest.mpr ⟨h.1 s _ hsX, ?_⟩
  rcases hcond with hlt | ⟨heq, _⟩
  · omega
  · omega

/- (*** F3 ***) -/

theorem Depth_rest_F3 {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (P |. n) (fstF ∘ M), failures (P |. n) M) := by
  intro h
  rw [HC_F3_pair]
  intro s X0 Y0 hf hn hY
  obtain ⟨t, Z, hEq, hsX, hcond⟩ := in_failures_Depth_rest.mp hf
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hs, hX⟩ := hEq
  subst hs
  subst hX
  have hlt : LT.lt (lengtht s) n := by
    rcases hcond with hlt | ⟨_, s0, ht, hn0⟩
    · exact hlt
    · subst ht
      exact absurd hn (by simp [hn0, tickTrace])
  refine in_failures_Depth_rest.mpr ⟨s, _, rfl, ?_, Or.inl hlt⟩
  refine h.2.2.1 s _ Y0 hsX hn ?_
  intro a ha hmem
  refine hY a ha (in_traces_Depth_rest.mpr ⟨hmem, ?_⟩)
  rw [lengtht_app_event_Suc_last hn]
  omega

/- T3_F4 -/

theorem Depth_rest_T3_F4 {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (P |. n) (fstF ∘ M), failures (P |. n) M) := by
  intro h
  rw [HC_T3_F4_pair]
  intro s hs
  obtain ⟨hmem, hlen⟩ := in_traces_Depth_rest.mp hs.1
  obtain ⟨hF4, hT3⟩ := (HC_T3_F4_iff.mpr ⟨h.2.1, h.2.2.2⟩) s ⟨hmem, hs.2⟩
  rw [lengtht_app_event_Suc_last hs.2] at hlen
  constructor
  · exact in_failures_Depth_rest.mpr ⟨s, Evset, rfl, hF4, Or.inl (by omega)⟩
  · intro X0
    refine in_failures_Depth_rest.mpr
      ⟨(s ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α), X0, rfl, hT3 X0, ?_⟩
    rw [lengtht_app_event_Suc_last hs.2]
    rcases Nat.lt_or_ge (Nat.succ (lengtht s)) n with hb | hb
    · exact Or.inl hb
    · refine Or.inr ⟨Nat.le_antisymm hlen hb, s, rfl, hs.2⟩

/- (*** Depth_rest_domF ***) -/

theorem Depth_rest_domF {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (P |. n) (fstF ∘ M), failures (P |. n) M) ∈ domF (α := α) := by
  intro h
  exact ⟨Depth_rest_T2 h, (HC_T3_F4_iff.mp (Depth_rest_T3_F4 h)).1, Depth_rest_F3 h,
    (HC_T3_F4_iff.mp (Depth_rest_T3_F4 h)).2⟩

/- --------------------------------*
 |        Proc_name_dom           |
 *-------------------------------- -/

/- (*** T2 ***) -/

theorem Proc_name_T2 {p0 : p} {M : p → domFType α} :
    HC_T2 (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M) := by
  exact (M p0).2.1

/- (*** F3 ***) -/

theorem Proc_name_F3 {p0 : p} {M : p → domFType α} :
    HC_F3 (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M) := by
  exact (M p0).2.2.2.1

/- T3_F4 -/

theorem Proc_name_T3_F4 {p0 : p} {M : p → domFType α} :
    HC_T3_F4 (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M) := by
  exact HC_T3_F4_iff.mpr ⟨(M p0).2.2.1, (M p0).2.2.2.2⟩

/- (*** Proc_name_domF ***) -/

theorem Proc_name_domF {p0 : p} {M : p → domFType α} :
    (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M) ∈ domF (α := α) := by
  exact (M p0).2

/- --------------------------------*
 |             proc               |
 *-------------------------------- -/

@[simp]
theorem proc_domF {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) := by
  induction P with
  | STOP => exact STOP_domF
  | SKIP => exact SKIP_domF
  | DIV => exact DIV_domF
  | Act_prefix a P ih => exact Act_prefix_domF ih
  | Ext_pre_choice X Pf ih => exact Ext_pre_choice_domF ih
  | Ext_choice P Q ihP ihQ => exact Ext_choice_domF ihP ihQ
  | Int_choice P Q ihP ihQ => exact Int_choice_domF ihP ihQ
  | Rep_int_choice C Pf ih => exact Rep_int_choice_domF ih
  | «IF» b P Q ihP ihQ => exact IF_domF ihP ihQ
  | Parallel P X Q ihP ihQ => exact Parallel_domF ihP ihQ
  | Hiding P X ih => exact Hiding_domF ih
  | Renaming P r ih => exact Renaming_domF ih
  | Seq_compo P Q ihP ihQ => exact Seq_compo_domF ihP ihQ
  | Depth_rest P n ih => exact Depth_rest_domF ih
  | Proc_name p0 => exact Proc_name_domF

/- --------------------------------*
 |          fstF sndF             |
 *-------------------------------- -/

@[simp]
theorem fstF_proc_domF {P : proc p α} {M : p → domFType α} :
    fstF (traces P (fstF ∘ M) ,, failures P M) = traces P (fstF ∘ M) := by
  exact pairF_fstF (hSF := proc_domF (P := P) (M := M))

@[simp]
theorem sndF_proc_domF {P : proc p α} {M : p → domFType α} :
    sndF (traces P (fstF ∘ M) ,, failures P M) = failures P M := by
  exact pairF_sndF (hSF := proc_domF (P := P) (M := M))

@[simp]
theorem fstF_proc_domF2 {P : proc p α} {M : p → domFType α} :
    fstF (traces P (fun x => fstF (M x)) ,, failures P M) = traces P (fstF ∘ M) := by
  exact fstF_proc_domF

@[simp]
theorem sndF_proc_domF2 {P : proc p α} {M : p → domFType α} :
    sndF (traces P (fun x => fstF (M x)) ,, failures P M) = failures P M := by
  exact sndF_proc_domF

theorem fstF_proc_domF_fun {β : Type _} {f : β → proc p α} {M : p → domFType α} :
    fstF ∘ (fun p => traces (f p) (fstF ∘ M) ,, failures (f p) M) =
      fun p => traces (f p) (fstF ∘ M) := by
  funext p
  simp

theorem sndF_proc_domF_fun {β : Type _} {f : β → proc p α} {M : p → domFType α} :
    sndF ∘ (fun p => traces (f p) (fstF ∘ M) ,, failures (f p) M) = fun p => failures (f p) M := by
  funext p
  simp

@[simp]
theorem fstF_semFf {P : proc p α} {M : p → domFType α} :
    fstF (semFf P M) = traces P (fstF ∘ M) := by
  simp [semFf_def]

@[simp]
theorem fstF_semF [HasPNfun p α] [HasFPmode] {P : proc p α} :
    fstF (semF P) = traces P (fstF ∘ MF) := by
  simp [semF_def]

@[simp]
theorem sndF_semFf {P : proc p α} {M : p → domFType α} :
    sndF (semFf P M) = failures P M := by
  simp [semFf_def]

@[simp]
theorem sndF_semF [HasPNfun p α] [HasFPmode] {P : proc p α} :
    sndF (semF P) = failures P MF := by
  simp [semF_def]

/- (*** decomposition ***) -/

theorem semFf_decompo {P : proc p α} {M : p → domFType α} {SF : domFType α} :
    semFf P M = SF ↔ (traces P (fstF ∘ M) = fstF SF ∧ failures P M = sndF SF) := by
  constructor
  · intro h
    cases h
    simp
  · intro h
    exact (eqF_decompo (SF := semFf P M) (SE := SF)).2
      ⟨by simpa using h.1, by simpa using h.2⟩

theorem semF_decompo [HasPNfun p α] [HasFPmode] {P : proc p α} {SF : domFType α} :
    semF P = SF ↔ (traces P (fstF ∘ MF) = fstF SF ∧ failures P MF = sndF SF) := by
  simpa [semF_def] using (semFf_decompo (P := P) (M := MF) (SF := SF))

theorem semFf_decompo_fstF {P : proc p α} {M : p → domFType α} {SF : domFType α} :
    semFf P M = SF → traces P (fstF ∘ M) = fstF SF := by
  intro h
  exact (semFf_decompo (P := P) (M := M) (SF := SF)).1 h |>.1

theorem semF_decompo_fstF [HasPNfun p α] [HasFPmode] {P : proc p α} {SF : domFType α} :
    semF P = SF → traces P (fstF ∘ MF) = fstF SF := by
  intro h
  exact (semF_decompo (P := P) (SF := SF)).1 h |>.1

theorem semFf_decompo_sndF {P : proc p α} {M : p → domFType α} {SF : domFType α} :
    semFf P M = SF → failures P M = sndF SF := by
  intro h
  exact (semFf_decompo (P := P) (M := M) (SF := SF)).1 h |>.2

theorem semF_decompo_sndF [HasPNfun p α] [HasFPmode] {P : proc p α} {SF : domFType α} :
    semF P = SF → failures P MF = sndF SF := by
  intro h
  exact (semF_decompo (P := P) (SF := SF)).1 h |>.2

/- --------------------------------*
 |            [[p]]Ff            |
 *-------------------------------- -/

theorem semFf_Proc_name {p0 : p} :
    semFf (proc.Proc_name p0 : proc p α) = fun M : p → domFType α => M p0 := by
  funext M
  apply (eqF_decompo (SF := semFf (proc.Proc_name p0) M) (SE := M p0)).2
  simp [semFf, traces, failures]

/- --------------------------------*
 |          =F and <=F            |
 *-------------------------------- -/

theorem cspF_eqF_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q ↔
      (traces P (fstF ∘ M1) = traces Q (fstF ∘ M2) ∧
        failures P M1 = failures Q M2) := by
  rw [eqF_def]
  exact (eqF_decompo (SF := semFf P M1) (SE := semFf Q M2)).trans <| by simp

theorem cspF_refF_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    refF P M1 M2 Q ↔
      (traces Q (fstF ∘ M2) <= traces P (fstF ∘ M1) ∧
        failures Q M2 <= failures P M1) := by
  rw [refF_def]
  exact (subdomF_decompo (SF := semFf Q M2) (SE := semFf P M1)).trans <| by simp

/- The Isabelle theorem bundle `cspF_semantics` is represented by
   `cspF_eqF_semantics` and `cspF_refF_semantics`. -/

theorem cspF_cspT_eqF_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q ↔
      (eqT P (fstF ∘ M1) (fstF ∘ M2) Q ∧ failures P M1 = failures Q M2) := by
  rw [cspF_eqF_semantics, cspT_eqT_semantics]

theorem cspF_cspT_refF_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    refF P M1 M2 Q ↔
      (refT P (fstF ∘ M1) (fstF ∘ M2) Q ∧ failures Q M2 <= failures P M1) := by
  rw [cspF_refF_semantics, cspT_refT_semantics]

/- The Isabelle theorem bundle `cspF_cspT_semantics` is represented by
   `cspF_cspT_eqF_semantics` and `cspF_cspT_refF_semantics`. -/

/- --------------------------------*
 |            Timeout             |
 *-------------------------------- -/

theorem in_failures_Timeout1 {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (P [> Q) M) ↔
      (f :f failures Q M ∨
        (∃ s X, f = (s, X) ∧ s ≠ <> ∧ (s, X) :f failures P M) ∨
        ∃ X, f = (<>, X) ∧ X ⊆ Evset ∧
          (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M)) := by
  constructor
  · intro hf
    rcases in_failures_Ext_choice.mp hf with ⟨⟨W, hEq⟩, hPS, hQ⟩ | ⟨s, ⟨W, hEq⟩, hPQ, hne⟩ |
      ⟨W, hEq, hTick, hW⟩
    · exact Or.inl hQ
    · rcases hPQ with hPS | hQ
      · rcases in_failures_Int_choice.mp hPS with hP | hS
        · refine Or.inr (Or.inl ⟨s, W, hEq, hne, ?_⟩)
          rw [hEq] at hP
          exact hP
        · obtain ⟨W', hEq'⟩ := in_failures_STOP.mp hS
          rw [hEq, Prod.mk.injEq] at hEq'
          exact absurd hEq'.1 hne
      · exact Or.inl hQ
    · rcases hTick with hTPS | hTQ
      · rcases in_traces_Int_choice.mp hTPS with hTP | hTS
        · exact Or.inr (Or.inr ⟨W, hEq, hW, hTP⟩)
        · rw [in_traces_STOP] at hTS
          simp at hTS
      · refine Or.inl ?_
        rw [hEq]
        refine memF_F2 ((proc_domF (P := Q) (M := M)).2.2.2 <> ⟨?_, noTick_nil⟩) hW
        rw [appt_nil_left]
        exact hTQ
  · intro h
    rcases h with hQ | ⟨s, W, hEq, hne, hP⟩ | ⟨W, hEq, hW, hTP⟩
    · obtain ⟨s, W, hEq, hsW⟩ := memF_pair_iff.mp hQ
      by_cases hs : s = <>
      · refine in_failures_Ext_choice.mpr (Or.inl ⟨⟨W, by rw [hEq, hs]⟩, ?_, hQ⟩)
        exact in_failures_Int_choice.mpr (Or.inr (in_failures_STOP.mpr ⟨W, by rw [hEq, hs]⟩))
      · exact in_failures_Ext_choice.mpr (Or.inr (Or.inl ⟨s, ⟨W, hEq⟩, Or.inr hQ, hs⟩))
    · refine in_failures_Ext_choice.mpr (Or.inr (Or.inl ⟨s, ⟨W, hEq⟩, ?_, hne⟩))
      refine Or.inl (in_failures_Int_choice.mpr (Or.inl ?_))
      rw [hEq]
      exact hP
    · refine in_failures_Ext_choice.mpr (Or.inr (Or.inr ⟨W, hEq, ?_, hW⟩))
      exact Or.inl (in_traces_Int_choice.mpr (Or.inl hTP))

theorem in_failures_Timeout2 {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (Timeout P Q) M) ↔
      (f :f failures Q M ∨
        (∃ s X, f = (s, X) ∧ s ≠ <> ∧ (s, X) :f failures P M) ∨
        ∃ X, f = (<>, X) ∧ X ⊆ Evset ∧
          (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M)) := by
  simpa [Timeout_def] using (in_failures_Timeout1 (f := f) (P := P) (Q := Q) (M := M))

/- The Isabelle theorem bundle `in_failures_Timeout` is represented by
   `in_failures_Timeout1` and `in_failures_Timeout2`. -/

/- --------------------------------*
 |           Depth rest           |
 *-------------------------------- -/

theorem semFf_Depth_rest {P : proc p α} {n : Nat} {M : p → domFType α} :
    semFf (P |. n) M = semFf P M .|. n := by
  have h1 : Rep_domF (semFf P M) = (traces P (fstF ∘ M), failures P M) := by
    have h0 : (fstF (semFf P M), sndF (semFf P M)) = Rep_domF (semFf P M) := rfl
    rw [← h0, fstF_semFf, sndF_semFf]
  rw [rest_domF_def, restTF_def, h1]
  rfl

theorem semF_Depth_rest [HasPNfun p α] [HasFPmode] {P : proc p α} {n : Nat} :
    semF (P |. n) = semF P .|. n := by
  simpa [semF_def] using (semFf_Depth_rest (P := P) (n := n) (M := MF))

/- ---------------------------------------------------*
 |         Healthiness conditions for proc           |
 *--------------------------------------------------- -/

theorem proc_T2 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)} :
    (s, X) :f failures P M → s :t traces P (fstF ∘ M) := by
  intro h
  exact proc_domF.1 s X h

theorem proc_T3 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) →
      noTick s →
        (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f failures P M := by
  intro h1 h2
  exact proc_domF.2.1 s ⟨h1, h2⟩ X

theorem proc_T3_Tick {P : proc p α} {M : p → domFType α} {X : Set (event α)} :
    (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M) →
      ((Abs_trace [event.Tick] : traceType α), X) :f failures P M := by
  intro h
  have h0 : ((<> : traceType α) ^^^ (Abs_trace [event.Tick] : traceType α)) :t
      traces P (fstF ∘ M) := by
    rw [appt_nil_left]
    exact h
  have h1 := proc_T3 h0 noTick_nil (X := X)
  rwa [appt_nil_left] at h1

theorem proc_F4 {P : proc p α} {M : p → domFType α} {s : traceType α} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) →
      noTick s →
        (s, Evset) :f failures P M := by
  intro h1 h2
  exact proc_domF.2.2.2 s ⟨h1, h2⟩

theorem proc_F3 {P : proc p α} {M : p → domFType α} {s : traceType α}
    {X Y : Set (event α)} :
    (s, X) :f failures P M →
      noTick s →
        (∀ a, a ∈ Y → ¬ (s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) →
          (s, X ∪ Y) :f failures P M := by
  intro h1 h2 h3
  exact proc_domF.2.2.1 s X Y h1 h2 h3

theorem proc_F3I {P : proc p α} {M : p → domFType α} {s : traceType α}
    {X Y Z : Set (event α)} :
    (s, X) :f failures P M →
      noTick s →
        (∀ a, a ∈ Y → ¬ (s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) →
          Z = X ∪ Y →
            (s, Z) :f failures P M := by
  intro h1 h2 h3 h4
  rw [h4]
  exact proc_F3 h1 h2 h3

/- (*** F2_F4 ***) -/

theorem proc_F2_F4 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) →
      noTick s →
        X ⊆ Evset →
          (s, X) :f failures P M := by
  intro h1 h2 h3
  exact memF_F2 (proc_F4 h1 h2) h3

/- (*** T2_T3 ***) -/

theorem proc_T2_T3 {P : proc p α} {M : p → domFType α} {s : traceType α}
    {X Y : Set (event α)} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f failures P M →
      noTick s →
        (s ^^^ (Abs_trace [event.Tick] : traceType α), Y) :f failures P M := by
  intro h1 h2
  exact proc_T3 (proc_T2 h1) h2

/-
------------------------------------------------------*
 |   Union in domF  (used for generic internal choice   |
 *------------------------------------------------------ -/

theorem non_empty_UnionT_UnionF_T2 {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      HC_T2
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M}) := by
  intro hPs
  rw [HC_T2_pair]
  intro s X hf
  obtain ⟨F, ⟨P, hP, rfl⟩, hsX⟩ := memF_UnionF.mp hf
  exact memT_UnionT_if ⟨P, hP, rfl⟩ (proc_T2 hsX)

theorem non_empty_UnionT_UnionF_F3 {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      HC_F3
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M}) := by
  intro hPs
  rw [HC_F3_pair]
  intro s X Y hf hn hY
  obtain ⟨F, ⟨P, hP, rfl⟩, hsX⟩ := memF_UnionF.mp hf
  refine memF_UnionF_if ⟨P, hP, rfl⟩ (proc_F3 hsX hn ?_)
  intro a ha hmem
  exact hY a ha (memT_UnionT_if ⟨P, hP, rfl⟩ hmem)

theorem non_empty_UnionT_UnionF_T3_F4 {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      HC_T3_F4
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M}) := by
  intro hPs
  rw [HC_T3_F4_pair]
  intro s hs
  have hne : {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)} ≠ ∅ := by
    obtain ⟨P0, hP0⟩ := Set.nonempty_iff_ne_empty.mpr hPs
    intro h0
    have hmem : traces P0 (fstF ∘ M) ∈
        {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)} := ⟨P0, hP0, rfl⟩
    rw [h0] at hmem
    exact hmem
  obtain ⟨T, ⟨P, hP, rfl⟩, hsT⟩ := memT_UnionT_only_if hne hs.1
  exact ⟨memF_UnionF_if ⟨P, hP, rfl⟩ (proc_F4 hsT hs.2),
    fun X => memF_UnionF_if ⟨P, hP, rfl⟩ (proc_T3 hsT hs.2)⟩

theorem non_empty_UnionT_UnionF_domF {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
        UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M}) ∈ domF (α := α) := by
  intro hPs
  exact ⟨non_empty_UnionT_UnionF_T2 hPs,
    (HC_T3_F4_iff.mp (non_empty_UnionT_UnionF_T3_F4 hPs)).1,
    non_empty_UnionT_UnionF_F3 hPs,
    (HC_T3_F4_iff.mp (non_empty_UnionT_UnionF_T3_F4 hPs)).2⟩

/-
------------------------------------------------------*
 |   Union in domF  (used for generic internal choice   |
 *------------------------------------------------------ -/

theorem UnionT_UnionF_T2 {Ps : Set (proc p α)} {M : p → domFType α} :
    HC_T2
      (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
        CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M)) := by
  exact Union_proc_T2 (C := Ps) (Tf := fun P => traces P (fstF ∘ M))
    (Ff := fun P => failures P M) (fun _ => proc_domF)

theorem UnionT_UnionF_F3 {Ps : Set (proc p α)} {M : p → domFType α} :
    HC_F3
      (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
        CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M)) := by
  exact Union_proc_F3 (C := Ps) (Tf := fun P => traces P (fstF ∘ M))
    (Ff := fun P => failures P M) (fun _ => proc_domF)

theorem UnionT_UnionF_T3_F4 {Ps : Set (proc p α)} {M : p → domFType α} :
    HC_T3_F4
      (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
        CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M)) := by
  exact Union_proc_T3_F4 (C := Ps) (Tf := fun P => traces P (fstF ∘ M))
    (Ff := fun P => failures P M) (fun _ => proc_domF)

theorem UnionT_UnionF_domF {Ps : Set (proc p α)} {M : p → domFType α} :
    (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
      CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M)) ∈ domF (α := α) := by
  exact Union_proc_domF (C := Ps) (Tf := fun P => traces P (fstF ∘ M))
    (Ff := fun P => failures P M) (fun _ => proc_domF)

theorem fstF_semFf_comp {f : p → proc q α} {M : q → domFType α} :
    fstF ∘ (fun x => semFf (f x) M) = fun x => traces (f x) (fstF ∘ M) := by
  funext x
  exact fstF_semFf

theorem fstF_semF_comp [HasPNfun q α] [HasFPmode] {f : p → proc q α} :
    fstF ∘ (fun x => semF (f x)) = fun x => traces (f x) (fstF ∘ (MF : q → domFType α)) := by
  funext x
  exact fstF_semF

/- -----------------------------------------*
 |              substitution               |
 *----------------------------------------- -/

theorem failrues_subst {P : proc p α} {f : p → proc q α} {M : q → domFType α} :
    failures (P << f) M = failures P (fun q => semFf (f q) M) := by
  induction P with
  | STOP => rfl
  | SKIP => rfl
  | DIV => rfl
  | Act_prefix a P ih => simp only [Subst_procfun, failures, ih]
  | Ext_pre_choice X Pf ih => simp only [Subst_procfun, failures, ih]
  | Ext_choice P Q ihP ihQ =>
      simp only [Subst_procfun, failures, ihP, ihQ, traces_subst, fstF_semFf_comp]
  | Int_choice P Q ihP ihQ => simp only [Subst_procfun, failures, ihP, ihQ]
  | Rep_int_choice C Pf ih => simp only [Subst_procfun, failures, ih]
  | «IF» b P Q ihP ihQ => simp only [Subst_procfun, failures, ihP, ihQ]
  | Parallel P X Q ihP ihQ => simp only [Subst_procfun, failures, ihP, ihQ]
  | Hiding P X ih => simp only [Subst_procfun, failures, ih]
  | Renaming P r ih => simp only [Subst_procfun, failures, ih]
  | Seq_compo P Q ihP ihQ =>
      simp only [Subst_procfun, failures, ihP, ihQ, traces_subst, fstF_semFf_comp]
  | Depth_rest P n ih => simp only [Subst_procfun, failures, ih]
  | Proc_name x => simp only [Subst_procfun, failures, sndF_semFf]

theorem semF_subst [HasPNfun q α] [HasFPmode] {P : proc p α} {f : p → proc q α} :
    semF (P << f) = semFf P (fun q => semF (f q)) := by
  refine (eqF_decompo).mpr ⟨?_, ?_⟩
  · rw [fstF_semF, fstF_semFf, traces_subst, fstF_semF_comp]
  · rw [sndF_semF, sndF_semFf, failrues_subst]
    rfl

theorem semF_subst_semFfun [HasPNfun q α] [HasFPmode] {Pf : p → proc p α} {f : p → proc q α} :
    (fun q => semF ((Pf q) << f)) = semFfun Pf (fun q => semF (f q)) := by
  funext x
  exact semF_subst

/- -----------------------------------------*
 |               semT -- semF              |
 *----------------------------------------- -/

theorem semTfun_fstF_semFf {Pf : p → proc p α} {M : p → domFType α} {p0 : p} :
    semTfun Pf (fstF ∘ M) p0 = fstF (semFf (Pf p0) M) := by
  simp [semTfun_def, semTf_def, semFf_def]

end
