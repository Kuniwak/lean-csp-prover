           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Prefix

open event

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `(notick \/ t = <>)`.          -/

/- *****************************************************************

         1.
         2.
         3.
         4.

 ***************************************************************** -/

inductive hidex (X : Set α) : traceType α → traceType α → Prop where
  | hidex_nil :
      hidex X <> <>
  | hidex_Tick :
      hidex X (Abs_trace [Tick]) (Abs_trace [Tick])
  | hidex_in {s t : traceType α} {a : α} :
      hidex X s t → a ∈ X → hidex X (Abs_trace [Ev a] ^^^ s) t
  | hidex_notin {s t : traceType α} {a : α} :
      hidex X s t → a ∉ X → hidex X (Abs_trace [Ev a] ^^^ s) (Abs_trace [Ev a] ^^^ t)

/- (*** auxiliary lemmas for hidex (Lean port helpers) ***) -/

theorem sett_Ev_head_mem {e : event α} {a : α} {w : traceType α} :
    e ∈ sett (Abs_trace [Ev a] ^^^ w) ↔ (e = Ev a ∨ e ∈ sett w) := by
  rw [sett_appt1 (Or.inl (noTick_Ev a)), sett_one]
  simp

theorem Ev_mem_Ev_image {a : α} {X : Set α} : (Ev a ∈ Ev '' X) ↔ a ∈ X := by
  simp

theorem hidex_cases {X : Set α} {s t : traceType α} {P : Prop} :
    hidex X s t →
      (s = <> → t = <> → P) →
      (s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a s', s = Abs_trace [Ev a] ^^^ s' → hidex X s' t → a ∈ X → P) →
      (∀ a s' t', s = Abs_trace [Ev a] ^^^ s' → t = Abs_trace [Ev a] ^^^ t' →
          hidex X s' t' → a ∉ X → P) →
      P := by
  intro h h1 h2 h3 h4
  cases h with
  | hidex_nil => exact h1 rfl rfl
  | hidex_Tick => exact h2 rfl rfl
  | hidex_in hh ha => exact h3 _ _ rfl hh ha
  | hidex_notin hh ha => exact h4 _ _ _ rfl rfl hh ha

theorem hidex_unique_ind {X : Set α} {s t : traceType α} :
    hidex X s t → ∀ u, hidex X s u → t = u := by
  intro h
  induction h with
  | hidex_nil =>
      intro u hu
      refine hidex_cases hu ?_ ?_ ?_ ?_
      · intro _ h0
        exact h0.symm
      · intro h0 _
        simp at h0
      · intro a s' h0 _ _
        simp at h0
      · intro a s' t' h0 _ _ _
        simp at h0
  | hidex_Tick =>
      intro u hu
      refine hidex_cases hu ?_ ?_ ?_ ?_
      · intro h0 _
        simp at h0
      · intro _ h0
        exact h0.symm
      · intro a s' h0 _ _
        simp at h0
      · intro a s' t' h0 _ _ _
        simp at h0
  | hidex_in hh ha ih =>
      intro u hu
      refine hidex_cases hu ?_ ?_ ?_ ?_
      · intro h0 _
        simp at h0
      · intro h0 _
        simp at h0
      · intro b s' h0 hb hbX
        obtain ⟨hab, hss⟩ := appt_same_head_only_if h0
        subst hss
        exact ih u hb
      · intro b s' t' h0 _ _ hbX
        obtain ⟨hab, hss⟩ := appt_same_head_only_if h0
        subst hab
        exact absurd ha hbX
  | hidex_notin hh ha ih =>
      intro u hu
      refine hidex_cases hu ?_ ?_ ?_ ?_
      · intro h0 _
        simp at h0
      · intro h0 _
        simp at h0
      · intro b s' h0 _ hbX
        obtain ⟨hab, hss⟩ := appt_same_head_only_if h0
        subst hab
        exact absurd hbX ha
      · intro b s' t' h0 h0' hb hbX
        obtain ⟨hab, hss⟩ := appt_same_head_only_if h0
        subst hab
        subst hss
        subst h0'
        rw [ih t' hb]

theorem hidex_exists_lm (X : Set α) (s : traceType α) :
    ∃ t, hidex X s t := by
  refine induct_trace (P := fun w => ∃ t, hidex X w t) ?_ ?_ ?_
  · exact ⟨<>, hidex.hidex_nil⟩
  · exact ⟨Abs_trace [Tick], hidex.hidex_Tick⟩
  · rintro w a ⟨t, ht⟩
    by_cases ha : a ∈ X
    · exact ⟨t, hidex.hidex_in ht ha⟩
    · exact ⟨Abs_trace [Ev a] ^^^ t, hidex.hidex_notin ht ha⟩

theorem hidex_exists {X : Set α} {s : traceType α} :
    ∃ t, hidex X s t := by
  exact hidex_exists_lm X s

theorem hidex_unique_lm (X : Set α) (s t u : traceType α) :
    (hidex X s t ∧ hidex X s u) → t = u := by
  rintro ⟨h1, h2⟩
  exact hidex_unique_ind h1 u h2

theorem hidex_unique {X : Set α} {s t u : traceType α} :
    hidex X s t → hidex X s u → t = u := by
  intro h1 h2
  exact hidex_unique_ind h1 u h2

noncomputable def hide_tr (s : traceType α) (X : Set α) : traceType α :=
  Classical.choose (hidex_exists (X := X) (s := s))

notation:84 s:84 " --tr " X:85 => hide_tr s X

theorem hide_tr_spec {X : Set α} {s : traceType α} :
    hidex X s (hide_tr s X) :=
  Classical.choose_spec (hidex_exists (X := X) (s := s))

noncomputable def rest_tr (s : traceType α) (X : Set α) : traceType α :=
  hide_tr s Xᶜ

notation:84 s:84 " rest-tr " X:85 => rest_tr s X

theorem rest_tr_def {s : traceType α} {X : Set α} :
    rest_tr s X = hide_tr s Xᶜ :=
  rfl

/- *************************************************************
                       THE hidex
 ************************************************************* -/

theorem hidex_to_hide_tr {X : Set α} {s t : traceType α} :
    hidex X s t ↔ t = hide_tr s X := by
  constructor
  · intro h
    exact hidex_unique h hide_tr_spec
  · rintro rfl
    exact hide_tr_spec

theorem hide_tr_to_hidex {X : Set α} {s t : traceType α} :
    hide_tr s X = t ↔ hidex X s t := by
  constructor
  · rintro rfl
    exact hide_tr_spec
  · intro h
    exact hidex_unique hide_tr_spec h

theorem hide_tr_to_hidex_sym {X : Set α} {s t : traceType α} :
    t = hide_tr s X ↔ hidex X s t := by
  exact hidex_to_hide_tr.symm

theorem hide_tr_iff {X : Set α} {s t : traceType α} :
    (hide_tr s X = t) ∧ (t = hide_tr s X) ↔ hidex X s t := by
  constructor
  · rintro ⟨h, _⟩
    exact hide_tr_to_hidex.mp h
  · intro h
    exact ⟨hide_tr_to_hidex.mpr h, (hide_tr_to_hidex.mpr h).symm⟩

/- *************************************************************
                         hide_tr
 ************************************************************* -/

/- *------------------*
 |      intros      |
 *------------------* -/

@[simp] theorem hide_tr_nil {X : Set α} :
    hide_tr (<> : traceType α) X = <> := by
  exact hide_tr_to_hidex.mpr hidex.hidex_nil

@[simp] theorem hide_tr_Tick {X : Set α} :
    hide_tr (Abs_trace [Tick] : traceType α) X = Abs_trace [Tick] := by
  exact hide_tr_to_hidex.mpr hidex.hidex_Tick

theorem hide_tr_in_lm {a : α} {X : Set α} {s t : traceType α} :
    a ∈ X → t = hide_tr s X → hide_tr (Abs_trace [Ev a] ^^^ s) X = t := by
  intro ha ht
  subst ht
  exact hide_tr_to_hidex.mpr (hidex.hidex_in hide_tr_spec ha)

@[simp] theorem hide_tr_in {a : α} {X : Set α} {s : traceType α} :
    a ∈ X → hide_tr (Abs_trace [Ev a] ^^^ s) X = hide_tr s X := by
  intro ha
  exact hide_tr_in_lm ha rfl

@[simp] theorem hide_tr_in_one {a : α} {X : Set α} :
    a ∈ X → hide_tr (Abs_trace [Ev a] : traceType α) X = <> := by
  intro ha
  have h0 : (Abs_trace [Ev a] : traceType α) = Abs_trace [Ev a] ^^^ <> := by simp
  rw [h0, hide_tr_in ha, hide_tr_nil]

theorem hide_tr_notin_lm {a : α} {X : Set α} {s t : traceType α} :
    a ∉ X → t = hide_tr s X →
      hide_tr (Abs_trace [Ev a] ^^^ s) X = Abs_trace [Ev a] ^^^ t := by
  intro ha ht
  subst ht
  exact hide_tr_to_hidex.mpr (hidex.hidex_notin hide_tr_spec ha)

@[simp] theorem hide_tr_notin_appt {a : α} {X : Set α} {s : traceType α} :
    a ∉ X →
      hide_tr (Abs_trace [Ev a] ^^^ s) X = Abs_trace [Ev a] ^^^ hide_tr s X := by
  intro ha
  exact hide_tr_notin_lm ha rfl

@[simp] theorem hide_tr_notin {a : α} {X : Set α} :
    a ∉ X → hide_tr (Abs_trace [Ev a] : traceType α) X = Abs_trace [Ev a] := by
  intro ha
  have h0 : (Abs_trace [Ev a] : traceType α) = Abs_trace [Ev a] ^^^ <> := by simp
  rw [h0, hide_tr_notin_appt ha, hide_tr_nil]

/- *------------------*
 |      elims       |
 *------------------* -/

theorem hide_tr_elims_lm {s t : traceType α} {X : Set α} {P : Prop} :
    hide_tr s X = t →
      (((s = <> ∧ t = <>) → P)) →
      (((s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) → P)) →
      ((∀ a s', (s = Abs_trace [Ev a] ^^^ s' ∧ hide_tr s' X = t ∧ a ∈ X) → P)) →
      ((∀ a s' t', (s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t' ∧
          hide_tr s' X = t' ∧ a ∉ X) → P)) →
      P := by
  intro h h1 h2 h3 h4
  refine hidex_cases (hide_tr_to_hidex.mp h) ?_ ?_ ?_ ?_
  · intro hs ht
    exact h1 ⟨hs, ht⟩
  · intro hs ht
    exact h2 ⟨hs, ht⟩
  · intro a s' hs hh ha
    exact h3 a s' ⟨hs, hide_tr_to_hidex.mpr hh, ha⟩
  · intro a s' t' hs ht hh ha
    exact h4 a s' t' ⟨hs, ht, hide_tr_to_hidex.mpr hh, ha⟩

theorem hide_tr_elims {s t : traceType α} {X : Set α} {P : Prop} :
    hide_tr s X = t →
      (s = <> → t = <> → P) →
      (s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a s', s = Abs_trace [Ev a] ^^^ s' → hide_tr s' X = t → a ∈ X → P) →
      (∀ a s' t', s = Abs_trace [Ev a] ^^^ s' → t = Abs_trace [Ev a] ^^^ t' →
          hide_tr s' X = t' → a ∉ X → P) →
      P := by
  intro h h1 h2 h3 h4
  refine hidex_cases (hide_tr_to_hidex.mp h) ?_ ?_ ?_ ?_
  · exact h1
  · exact h2
  · intro a s' hs hh ha
    exact h3 a s' hs (hide_tr_to_hidex.mpr hh) ha
  · intro a s' t' hs ht hh ha
    exact h4 a s' t' hs ht (hide_tr_to_hidex.mpr hh) ha

/- *************************************************************
        a new event is not introduced by HIDE (trace)
 ************************************************************* -/

@[simp] theorem hide_tr_in_event {e : event α} {s : traceType α} {X : Set α} :
    e ∈ sett (hide_tr s X) ↔ e ∉ Ev '' X ∧ e ∈ sett s := by
  refine induct_trace (P := fun w => e ∈ sett (hide_tr w X) ↔ e ∉ Ev '' X ∧ e ∈ sett w) ?_ ?_ ?_
  · simp
  · dsimp only
    rw [hide_tr_Tick, sett_one]
    constructor
    · intro h
      rw [Set.mem_singleton_iff] at h
      subst h
      refine ⟨?_, rfl⟩
      rintro ⟨x, _, hx⟩
      cases hx
    · rintro ⟨_, h⟩
      exact h
  · intro w a ih
    by_cases ha : a ∈ X
    · rw [hide_tr_in ha, ih, sett_Ev_head_mem]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Or.inr h2⟩
      · rintro ⟨h1, (rfl | h2)⟩
        · exact absurd (Ev_mem_Ev_image.mpr ha) h1
        · exact ⟨h1, h2⟩
    · rw [hide_tr_notin_appt ha, sett_Ev_head_mem, sett_Ev_head_mem]
      constructor
      · rintro (rfl | h)
        · exact ⟨fun hm => ha (Ev_mem_Ev_image.mp hm), Or.inl rfl⟩
        · obtain ⟨h1, h2⟩ := ih.mp h
          exact ⟨h1, Or.inr h2⟩
      · rintro ⟨h1, (rfl | h2)⟩
        · exact Or.inl rfl
        · exact Or.inr (ih.mpr ⟨h1, h2⟩)

@[simp] theorem hide_tr_noTick {s : traceType α} {X : Set α} :
    noTick (hide_tr s X) ↔ noTick s := by
  simp [noTick]

/- *************************************************************
                  appended traces in hide
 ************************************************************* -/

theorem hide_tr_appt_noTick_lm {X : Set α} {s t : traceType α} :
    noTick s → hide_tr (s ^^^ t) X = hide_tr s X ^^^ hide_tr t X := by
  refine induct_trace (P := fun w => noTick w →
      hide_tr (w ^^^ t) X = hide_tr w X ^^^ hide_tr t X) ?_ ?_ ?_
  · intro _
    simp
  · intro hT
    exact absurd hT not_noTick_Tick
  · intro w a ih hn
    have hw : noTick w := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hn).2
    rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hw)]
    by_cases ha : a ∈ X
    · rw [hide_tr_in ha, hide_tr_in ha, ih hw]
    · rw [hide_tr_notin_appt ha, hide_tr_notin_appt ha, ih hw,
        appt_assoc (Or.inl (noTick_Ev a)) (Or.inl (hide_tr_noTick.mpr hw))]

@[simp] theorem hide_tr_appt {X : Set α} {s t : traceType α} :
    noTick s ∨ t = <> → hide_tr (s ^^^ t) X = hide_tr s X ^^^ hide_tr t X := by
  rintro (hs | rfl)
  · exact hide_tr_appt_noTick_lm hs
  · simp

/- *************************************************************
                 decompose traces in hide
 ************************************************************* -/

theorem hide_tr_decompo_only_if_lm {X : Set α} {u s t : traceType α} :
    (noTick s ∨ t = <>) ∧ hide_tr u X = s ^^^ t →
      ∃ s' t', (noTick s' ∨ t' = <>) ∧
        u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X := by
  have key : ∀ w s0 t0 : traceType α, (noTick s0 ∨ t0 = <>) →
      hide_tr w X = s0 ^^^ t0 →
      ∃ s' t', (noTick s' ∨ t' = <>) ∧ w = s' ^^^ t' ∧ s0 = hide_tr s' X ∧
        t0 = hide_tr t' X := by
    intro w
    refine induct_trace (P := fun w => ∀ s0 t0 : traceType α, (noTick s0 ∨ t0 = <>) →
        hide_tr w X = s0 ^^^ t0 →
        ∃ s' t', (noTick s' ∨ t' = <>) ∧ w = s' ^^^ t' ∧ s0 = hide_tr s' X ∧
          t0 = hide_tr t' X) ?_ ?_ ?_
    · intro s0 t0 hst h
      rw [hide_tr_nil] at h
      refine ⟨<>, <>, Or.inl noTick_nil, by simp, ?_, ?_⟩
      · rw [hide_tr_nil]
        rcases hst with hn | rfl
        · exact ((appt_nil hn).mp h.symm).1
        · simpa using h.symm
      · rw [hide_tr_nil]
        rcases hst with hn | rfl
        · exact ((appt_nil hn).mp h.symm).2
        · rfl
    · intro s0 t0 hst h
      rw [hide_tr_Tick] at h
      rcases (appt_decompo_one_sym hst).mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Abs_trace [Tick], <>, Or.inr rfl, by simp, by simp, by simp⟩
      · exact ⟨<>, Abs_trace [Tick], Or.inl noTick_nil, by simp, by simp, by simp⟩
    · intro w a ih s0 t0 hst h
      by_cases ha : a ∈ X
      · rw [hide_tr_in ha] at h
        obtain ⟨s', t', hc, hw, hs0, ht0⟩ := ih s0 t0 hst h
        refine ⟨Abs_trace [Ev a] ^^^ s', t', ?_, ?_, ?_, ht0⟩
        · rcases hc with hn | rfl
          · exact Or.inl (decompo_appt_noTick_if (noTick_Ev a) hn)
          · exact Or.inr rfl
        · rw [hw, appt_assoc (Or.inl (noTick_Ev a)) hc]
        · rw [hide_tr_in ha]
          exact hs0
      · rw [hide_tr_notin_appt ha] at h
        rcases trace_nil_or_Tick_or_Ev s0 with rfl | rfl | ⟨b, s1, rfl⟩
        · rw [appt_nil_left] at h
          refine ⟨<>, Abs_trace [Ev a] ^^^ w, Or.inl noTick_nil, by simp, by simp, ?_⟩
          rw [hide_tr_notin_appt ha]
          exact h.symm
        · exfalso
          rcases hst with hn | rfl
          · exact not_noTick_Tick hn
          · rw [appt_nil_right] at h
            rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp h with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
              simp at h1
        · have hc1 : noTick s1 ∨ t0 = <> := by
            rcases hst with hn | rfl
            · exact Or.inl (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hn).2
            · exact Or.inr rfl
          rw [appt_assoc (Or.inl (noTick_Ev b)) hc1] at h
          obtain ⟨hab, hrest⟩ := appt_same_head_only_if h
          obtain ⟨s', t', hc, hw, hs1, ht0⟩ := ih s1 t0 hc1 hrest
          have hb : b ∉ X := hab ▸ ha
          refine ⟨Abs_trace [Ev b] ^^^ s', t', ?_, ?_, ?_, ht0⟩
          · rcases hc with hn | rfl
            · exact Or.inl (decompo_appt_noTick_if (noTick_Ev b) hn)
            · exact Or.inr rfl
          · rw [hab, hw, appt_assoc (Or.inl (noTick_Ev b)) hc]
          · rw [hide_tr_notin_appt hb, hs1]
  rintro ⟨hst, hu⟩
  exact key u s t hst hu

theorem hide_tr_decompo_only_if {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      hide_tr u X = s ^^^ t →
        ∃ s' t', (noTick s' ∨ t' = <>) ∧
          u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X := by
  intro hst hu
  exact hide_tr_decompo_only_if_lm ⟨hst, hu⟩

theorem hide_tr_decompo_if {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      (∃ s' t', (noTick s' ∨ t' = <>) ∧
        u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X) →
        hide_tr u X = s ^^^ t := by
  rintro hst ⟨s', t', hc, rfl, rfl, rfl⟩
  exact hide_tr_appt hc

theorem hide_tr_decompo {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      (hide_tr u X = s ^^^ t ↔
        ∃ s' t', (noTick s' ∨ t' = <>) ∧
          u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X) := by
  intro hst
  exact ⟨hide_tr_decompo_only_if hst, hide_tr_decompo_if hst⟩

/- *************************************************************
                  hide trace prefix_closed
 ************************************************************* -/

theorem hide_tr_prefix_only_if_lm {X : Set α} {s u : traceType α} :
    «prefix» u (hide_tr s X) → ∃ t, u = hide_tr t X ∧ «prefix» t s := by
  rintro ⟨w, hw, hcond⟩
  obtain ⟨s', t', hc, rfl, hu, hwt⟩ := hide_tr_decompo_only_if hcond hw
  exact ⟨s', hu, prefix_appt_simp hc⟩

theorem hide_tr_prefix_only_if {X : Set α} {s u : traceType α} :
    «prefix» u (hide_tr s X) → ∃ t, u = hide_tr t X ∧ «prefix» t s := by
  exact hide_tr_prefix_only_if_lm

theorem hide_tr_prefix_if {X : Set α} {s t : traceType α} :
    «prefix» t s → «prefix» (hide_tr t X) (hide_tr s X) := by
  rintro ⟨w, rfl, hc⟩
  refine ⟨hide_tr w X, hide_tr_appt hc, ?_⟩
  rcases hc with h | rfl
  · exact Or.inl (hide_tr_noTick.mpr h)
  · exact Or.inr hide_tr_nil

theorem hide_tr_prefix {X : Set α} {s u : traceType α} :
    «prefix» u (hide_tr s X) ↔ ∃ t, u = hide_tr t X ∧ «prefix» t s := by
  constructor
  · exact hide_tr_prefix_only_if
  · rintro ⟨t, rfl, hp⟩
    exact hide_tr_prefix_if hp

/- *************************************************************
                  hide + alpha lemma
 ************************************************************* -/

theorem hide_tr_nilt_sett_only_if_lm {X : Set α} {s : traceType α} :
    hide_tr s X = <> → sett s ⊆ Ev '' X := by
  intro h e he
  by_contra hc
  have h0 : e ∈ sett (hide_tr s X) := hide_tr_in_event.mpr ⟨hc, he⟩
  rw [h] at h0
  simp at h0

theorem hide_tr_nilt_sett_only_if {X : Set α} {s : traceType α} :
    hide_tr s X = <> → sett s ⊆ Ev '' X := by
  exact hide_tr_nilt_sett_only_if_lm

theorem hide_tr_nilt_sett_if_lm {X : Set α} {s : traceType α} :
    sett s ⊆ Ev '' X → hide_tr s X = <> := by
  refine induct_trace (P := fun w => sett w ⊆ Ev '' X → hide_tr w X = <>) ?_ ?_ ?_
  · intro _
    exact hide_tr_nil
  · intro h
    have h0 : (Tick : event α) ∈ Ev '' X := h (by simp)
    rcases h0 with ⟨x, _, hx⟩
    cases hx
  · intro w a ih h
    have ha : a ∈ X := Ev_mem_Ev_image.mp (h (sett_Ev_head_mem.mpr (Or.inl rfl)))
    rw [hide_tr_in ha]
    exact ih (fun e he => h (sett_Ev_head_mem.mpr (Or.inr he)))

theorem hide_tr_nilt_sett_if {X : Set α} {s : traceType α} :
    sett s ⊆ Ev '' X → hide_tr s X = <> := by
  exact hide_tr_nilt_sett_if_lm

theorem hide_tr_nilt_sett {X : Set α} {s : traceType α} :
    (hide_tr s X = <>) ↔ sett s ⊆ Ev '' X := by
  exact ⟨hide_tr_nilt_sett_only_if, hide_tr_nilt_sett_if⟩

theorem hide_tr_sett_subseteq_sett {X Y : Set α} {u : traceType α} :
    X ⊆ Y → sett (hide_tr u Y) ⊆ sett (hide_tr u X) := by
  intro hXY e he
  obtain ⟨h1, h2⟩ := hide_tr_in_event.mp he
  refine hide_tr_in_event.mpr ⟨?_, h2⟩
  rintro ⟨x, hx, rfl⟩
  exact h1 ⟨x, hXY hx, rfl⟩

theorem hide_tr_Tick_sett_only_if_lm {X : Set α} {s : traceType α} :
    hide_tr s X = Abs_trace [Tick] →
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ sett s' ⊆ Ev '' X ∧ noTick s' := by
  intro h
  rcases trace_last_noTick_or_Tick s with hn | ⟨s0, hn0, rfl⟩
  · exfalso
    have h1 : noTick (hide_tr s X) := hide_tr_noTick.mpr hn
    rw [h] at h1
    exact not_noTick_Tick h1
  · rw [hide_tr_appt (Or.inl hn0), hide_tr_Tick] at h
    rcases (appt_decompo_one (Or.inl (hide_tr_noTick.mpr hn0))).mp h with ⟨_, h2⟩ | ⟨h1, _⟩
    · simp at h2
    · exact ⟨s0, rfl, hide_tr_nilt_sett_only_if h1, hn0⟩

theorem hide_tr_Tick_sett_only_if {X : Set α} {s : traceType α} :
    hide_tr s X = Abs_trace [Tick] →
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ sett s' ⊆ Ev '' X ∧ noTick s' := by
  exact hide_tr_Tick_sett_only_if_lm

theorem hide_tr_Tick_sett_if {X : Set α} {s : traceType α} :
    sett s ⊆ Ev '' X → hide_tr s X = <> := by
  exact hide_tr_nilt_sett_if

theorem hide_tr_Tick_sett {X : Set α} {s : traceType α} :
    (hide_tr s X = Abs_trace [Tick]) ↔
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ sett s' ⊆ Ev '' X ∧ noTick s' := by
  constructor
  · exact hide_tr_Tick_sett_only_if
  · rintro ⟨s', rfl, hsub, hn⟩
    rw [hide_tr_appt (Or.inl hn), hide_tr_nilt_sett_if hsub, hide_tr_Tick, appt_nil_left]

/- *--------------------------*
 |       commutativity      |
 *--------------------------* -/

theorem hide_tr_commute {X Y : Set α} {u : traceType α} :
    hide_tr (hide_tr u X) Y = hide_tr (hide_tr u Y) X := by
  refine induct_trace (P := fun w => hide_tr (hide_tr w X) Y = hide_tr (hide_tr w Y) X) ?_ ?_ ?_
  · simp
  · simp
  · intro w a ih
    by_cases ha : a ∈ X
    · by_cases hb : a ∈ Y
      · rw [hide_tr_in ha, hide_tr_in hb]
        exact ih
      · rw [hide_tr_in ha, hide_tr_notin_appt hb, hide_tr_in ha]
        exact ih
    · by_cases hb : a ∈ Y
      · rw [hide_tr_notin_appt ha, hide_tr_in hb, hide_tr_in hb]
        exact ih
      · rw [hide_tr_notin_appt ha, hide_tr_notin_appt hb, hide_tr_notin_appt hb,
          hide_tr_notin_appt ha, ih]

theorem hide_tr_of_hide_tr_subset1 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → hide_tr (hide_tr u X) Y = hide_tr u Y := by
  intro hXY
  refine induct_trace (P := fun w => hide_tr (hide_tr w X) Y = hide_tr w Y) ?_ ?_ ?_
  · simp
  · simp
  · intro w a ih
    by_cases ha : a ∈ X
    · rw [hide_tr_in ha, hide_tr_in (hXY ha)]
      exact ih
    · by_cases hb : a ∈ Y
      · rw [hide_tr_notin_appt ha, hide_tr_in hb, hide_tr_in hb]
        exact ih
      · rw [hide_tr_notin_appt ha, hide_tr_notin_appt hb, hide_tr_notin_appt hb, ih]

theorem hide_tr_of_hide_tr_subset2 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → hide_tr (hide_tr u Y) X = hide_tr u Y := by
  intro hXY
  refine induct_trace (P := fun w => hide_tr (hide_tr w Y) X = hide_tr w Y) ?_ ?_ ?_
  · simp
  · simp
  · intro w a ih
    by_cases hb : a ∈ Y
    · rw [hide_tr_in hb]
      exact ih
    · have ha : a ∉ X := fun h => hb (hXY h)
      rw [hide_tr_notin_appt hb, hide_tr_notin_appt ha, ih]

theorem hide_tr_of_hide_tr_subset {X Y : Set α} {u : traceType α} :
    X ⊆ Y →
      hide_tr (hide_tr u X) Y = hide_tr u Y ∧
        hide_tr (hide_tr u Y) X = hide_tr u Y := by
  intro hXY
  exact ⟨hide_tr_of_hide_tr_subset1 hXY, hide_tr_of_hide_tr_subset2 hXY⟩

theorem hide_tr_UNIV_lm {u : traceType α} :
    hide_tr u (Set.univ : Set α) = <> ∨
      hide_tr u (Set.univ : Set α) = Abs_trace [Tick] := by
  refine induct_trace (P := fun w => hide_tr w (Set.univ : Set α) = <> ∨
      hide_tr w (Set.univ : Set α) = Abs_trace [Tick]) ?_ ?_ ?_
  · exact Or.inl hide_tr_nil
  · exact Or.inr hide_tr_Tick
  · intro w a ih
    rw [hide_tr_in (Set.mem_univ a)]
    exact ih

theorem hide_tr_UNIV {u : traceType α} :
    hide_tr u (Set.univ : Set α) = <> ∨
      hide_tr u (Set.univ : Set α) = Abs_trace [Tick] := by
  exact hide_tr_UNIV_lm

/- *======================================================*
 |                                                      |
 |                        rest-tr                       |
 |                                                      |
 *======================================================* -/

/- *------------------*
 |      intros      |
 *------------------* -/

@[simp] theorem rest_tr_nil {X : Set α} :
    rest_tr (<> : traceType α) X = <> := by
  exact hide_tr_nil

@[simp] theorem rest_tr_Tick {X : Set α} :
    rest_tr (Abs_trace [Tick] : traceType α) X = Abs_trace [Tick] := by
  exact hide_tr_Tick

@[simp] theorem rest_tr_notin {a : α} {X : Set α} {s : traceType α} :
    a ∉ X → rest_tr (Abs_trace [Ev a] ^^^ s) X = rest_tr s X := by
  intro ha
  exact hide_tr_in ha

@[simp] theorem rest_tr_notin_one {a : α} {X : Set α} :
    a ∉ X → rest_tr (Abs_trace [Ev a] : traceType α) X = <> := by
  intro ha
  exact hide_tr_in_one ha

@[simp] theorem rest_tr_in_appt {a : α} {X : Set α} {s : traceType α} :
    a ∈ X →
      rest_tr (Abs_trace [Ev a] ^^^ s) X = Abs_trace [Ev a] ^^^ rest_tr s X := by
  intro ha
  exact hide_tr_notin_appt (fun h => h ha)

@[simp] theorem rest_tr_in {a : α} {X : Set α} :
    a ∈ X → rest_tr (Abs_trace [Ev a] : traceType α) X = Abs_trace [Ev a] := by
  intro ha
  exact hide_tr_notin (fun h => h ha)

/- *------------------*
 |      elims       |
 *------------------* -/

theorem rest_tr_elims {s t : traceType α} {X : Set α} {P : Prop} :
    rest_tr s X = t →
      (s = <> → t = <> → P) →
      (s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a s', s = Abs_trace [Ev a] ^^^ s' → rest_tr s' X = t → a ∉ X → P) →
      (∀ a s' t', s = Abs_trace [Ev a] ^^^ s' → t = Abs_trace [Ev a] ^^^ t' →
          rest_tr s' X = t' → a ∈ X → P) →
      P := by
  intro h h1 h2 h3 h4
  refine hide_tr_elims h ?_ ?_ ?_ ?_
  · exact h1
  · exact h2
  · intro a s' hs hh ha
    exact h3 a s' hs hh ha
  · intro a s' t' hs ht hh ha
    refine h4 a s' t' hs ht hh ?_
    by_contra hc
    exact ha hc

/- *************************************************************
        a new event is not introduced by rest (trace)
 ************************************************************* -/

@[simp] theorem rest_tr_in_event {e : event α} {s : traceType α} {X : Set α} :
    e ∈ sett (rest_tr s X) ↔ (e ∈ Ev '' X ∨ e = Tick) ∧ e ∈ sett s := by
  rw [rest_tr_def, hide_tr_in_event]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rcases event_Tick_or_Ev e with rfl | ⟨b, rfl⟩
    · exact Or.inr rfl
    · refine Or.inl (Ev_mem_Ev_image.mpr ?_)
      by_contra hc
      exact h1 (Ev_mem_Ev_image.mpr hc)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    rintro ⟨b, hb, rfl⟩
    rcases h1 with h1 | h1
    · exact hb (Ev_mem_Ev_image.mp h1)
    · cases h1

@[simp] theorem rest_tr_subset_event {s : traceType α} {X : Set α} :
    sett (rest_tr s X) ⊆ Set.insert Tick (Ev '' X) := by
  intro e he
  obtain ⟨h1, _⟩ := rest_tr_in_event.mp he
  rcases h1 with h1 | rfl
  · exact Set.mem_insert_of_mem _ h1
  · exact Set.mem_insert _ _

@[simp] theorem rest_tr_noTick {s : traceType α} {X : Set α} :
    noTick (rest_tr s X) ↔ noTick s := by
  exact hide_tr_noTick

/- *************************************************************
                  appended traces in rest
 ************************************************************* -/

@[simp] theorem rest_tr_appt {X : Set α} {s t : traceType α} :
    noTick s ∨ t = <> → rest_tr (s ^^^ t) X = rest_tr s X ^^^ rest_tr t X := by
  exact hide_tr_appt

/- *************************************************************
                 decompose traces in rest
 ************************************************************* -/

theorem rest_tr_decompo {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      (rest_tr u X = s ^^^ t ↔
        ∃ s' t', (noTick s' ∨ t' = <>) ∧
          u = s' ^^^ t' ∧ s = rest_tr s' X ∧ t = rest_tr t' X) := by
  exact hide_tr_decompo

/- *************************************************************
                  rest trace prefix_closed
 ************************************************************* -/

theorem rest_tr_prefix {X : Set α} {s u : traceType α} :
    «prefix» u (rest_tr s X) ↔ ∃ t, u = rest_tr t X ∧ «prefix» t s := by
  exact hide_tr_prefix

/- *************************************************************
                  rest + alpha lemma
 ************************************************************* -/

theorem rest_tr_nilt_sett {X : Set α} {s : traceType α} :
    (rest_tr s X = <>) ↔ sett s ∩ Set.insert Tick (Ev '' X) = ∅ := by
  rw [rest_tr_def, hide_tr_nilt_sett]
  constructor
  · intro hsub
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he1, he2⟩
    obtain ⟨b, hb, rfl⟩ := hsub he1
    rcases he2 with he2 | he2
    · cases he2
    · exact hb (Ev_mem_Ev_image.mp he2)
  · intro hint e he
    rw [Set.eq_empty_iff_forall_notMem] at hint
    rcases event_Tick_or_Ev e with rfl | ⟨b, rfl⟩
    · exact absurd ⟨he, Set.mem_insert _ _⟩ (hint Tick)
    · refine Ev_mem_Ev_image.mpr ?_
      intro hbX
      exact hint (Ev b) ⟨he, Set.mem_insert_of_mem _ (Ev_mem_Ev_image.mpr hbX)⟩

theorem rest_tr_sett_subseteq_sett {X Y : Set α} {u : traceType α} :
    X ⊆ Y → sett (rest_tr u X) ⊆ sett (rest_tr u Y) := by
  intro h
  exact hide_tr_sett_subseteq_sett (Set.compl_subset_compl.mpr h)

theorem rest_tr_Tick_sett {X : Set α} {s : traceType α} :
    (rest_tr s X = Abs_trace [Tick]) ↔
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ (sett s' ∩ Ev '' X = ∅) ∧ noTick s' := by
  rw [rest_tr_def, hide_tr_Tick_sett]
  constructor
  · rintro ⟨s', hs, hsub, hn⟩
    refine ⟨s', hs, ?_, hn⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he1, he2⟩
    obtain ⟨b, hb, rfl⟩ := hsub he1
    exact hb (Ev_mem_Ev_image.mp he2)
  · rintro ⟨s', hs, hint, hn⟩
    refine ⟨s', hs, ?_, hn⟩
    intro e he
    rcases event_Tick_or_Ev e with rfl | ⟨b, rfl⟩
    · exact absurd he hn
    · refine Ev_mem_Ev_image.mpr ?_
      intro hbX
      rw [Set.eq_empty_iff_forall_notMem] at hint
      exact hint (Ev b) ⟨he, Ev_mem_Ev_image.mpr hbX⟩

/- *--------------------------*
 |       commutativity      |
 *--------------------------* -/

theorem rest_tr_commute {X Y : Set α} {u : traceType α} :
    rest_tr (rest_tr u X) Y = rest_tr (rest_tr u Y) X := by
  exact hide_tr_commute

theorem rest_tr_of_rest_tr_subset1 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → rest_tr (rest_tr u X) Y = rest_tr u X := by
  intro h
  exact hide_tr_of_hide_tr_subset2 (Set.compl_subset_compl.mpr h)

theorem rest_tr_of_rest_tr_subset2 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → rest_tr (rest_tr u Y) X = rest_tr u X := by
  intro h
  exact hide_tr_of_hide_tr_subset1 (Set.compl_subset_compl.mpr h)

theorem rest_tr_of_rest_tr_subset {X Y : Set α} {u : traceType α} :
    X ⊆ Y →
      rest_tr (rest_tr u X) Y = rest_tr u X ∧
        rest_tr (rest_tr u Y) X = rest_tr u X := by
  intro h
  exact ⟨rest_tr_of_rest_tr_subset1 h, rest_tr_of_rest_tr_subset2 h⟩

theorem rest_tr_empty {u : traceType α} :
    rest_tr u (∅ : Set α) = <> ∨ rest_tr u (∅ : Set α) = Abs_trace [Tick] := by
  rw [rest_tr_def, Set.compl_empty]
  exact hide_tr_UNIV

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

theorem Ev_rest_tr_decompo {X : Set α} {s : traceType α} {a : α} :
    a ∈ X ∧ rest_tr s X = (Abs_trace [Ev a] : traceType α) →
      ∃ s1 s2, s = s1 ^^^ Abs_trace [Ev a] ^^^ s2 ∧
        noTick s1 ∧ noTick s2 ∧ rest_tr s1 X = <> ∧ rest_tr s2 X = <> := by
  rintro ⟨ha, h⟩
  revert h
  refine induct_trace (P := fun w => rest_tr w X = Abs_trace [Ev a] →
      ∃ s1 s2, w = s1 ^^^ Abs_trace [Ev a] ^^^ s2 ∧ noTick s1 ∧ noTick s2 ∧
        rest_tr s1 X = <> ∧ rest_tr s2 X = <>) ?_ ?_ ?_
  · intro h
    rw [rest_tr_nil] at h
    simp at h
  · intro h
    rw [rest_tr_Tick] at h
    simp at h
  · intro w b ih h
    by_cases hb : b ∈ X
    · rw [rest_tr_in_appt hb] at h
      rcases (appt_decompo_one (Or.inl (noTick_Ev b))).mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
      · rw [Event_eq] at h1
        have hba : b = a := inj_Ev h1
        subst hba
        have hw : noTick w := by
          intro hT
          have h3 := rest_tr_nilt_sett.mp h2
          rw [Set.eq_empty_iff_forall_notMem] at h3
          exact h3 Tick ⟨hT, Set.mem_insert _ _⟩
        exact ⟨<>, w, by simp, noTick_nil, hw, rest_tr_nil, h2⟩
      · simp at h1
    · rw [rest_tr_notin hb] at h
      obtain ⟨s1, s2, hw, hn1, hn2, hr1, hr2⟩ := ih h
      refine ⟨Abs_trace [Ev b] ^^^ s1, s2, ?_,
        decompo_appt_noTick_if (noTick_Ev b) hn1, hn2, ?_, hr2⟩
      · rw [hw, appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hn1)]
      · rw [rest_tr_notin hb]
        exact hr1

theorem hide_tr_rest_tr_sett {X Y : Set α} {s : traceType α} :
    sett s ⊆ Set.insert Tick (Ev '' Y) →
      hide_tr s X = rest_tr s (Y \ X) := by
  intro hsub
  revert hsub
  refine induct_trace (P := fun w => sett w ⊆ Set.insert Tick (Ev '' Y) →
      hide_tr w X = rest_tr w (Y \ X)) ?_ ?_ ?_
  · intro _
    rw [hide_tr_nil, rest_tr_nil]
  · intro _
    rw [hide_tr_Tick, rest_tr_Tick]
  · intro w a ih hsub
    have haY : a ∈ Y := by
      rcases hsub (sett_Ev_head_mem.mpr (Or.inl rfl)) with h0 | h0
      · cases h0
      · exact Ev_mem_Ev_image.mp h0
    have hsubw : sett w ⊆ Set.insert Tick (Ev '' Y) :=
      fun e he => hsub (sett_Ev_head_mem.mpr (Or.inr he))
    by_cases ha : a ∈ X
    · rw [hide_tr_in ha, rest_tr_notin (fun hc => hc.2 ha)]
      exact ih hsubw
    · rw [hide_tr_notin_appt ha,
        rest_tr_in_appt (X := Y \ X) (Set.mem_diff_of_mem haY ha), ih hsubw]

theorem hide_tr_id {X Y : Set α} {s : traceType α} :
    sett s ⊆ Set.insert Tick (Ev '' Y) ∧ X ∩ Y = ∅ →
      hide_tr s X = s := by
  rintro ⟨hsub, hXY⟩
  revert hsub
  refine induct_trace (P := fun w => sett w ⊆ Set.insert Tick (Ev '' Y) →
      hide_tr w X = w) ?_ ?_ ?_
  · intro _
    exact hide_tr_nil
  · intro _
    exact hide_tr_Tick
  · intro w a ih hsub
    have haY : a ∈ Y := by
      rcases hsub (sett_Ev_head_mem.mpr (Or.inl rfl)) with h0 | h0
      · cases h0
      · exact Ev_mem_Ev_image.mp h0
    have ha : a ∉ X := by
      intro hc
      rw [Set.eq_empty_iff_forall_notMem] at hXY
      exact hXY a ⟨hc, haY⟩
    rw [hide_tr_notin_appt ha, ih (fun e he => hsub (sett_Ev_head_mem.mpr (Or.inr he)))]

/- --------------------------------------------------- *
                   semantics for pipe
 * --------------------------------------------------- -/

theorem hide_tr_of_rest_tr_empty1 {X Y : Set α} {s : traceType α} :
    X ∩ Y = ∅ → rest_tr (hide_tr s X) Y = rest_tr s Y := by
  intro h
  refine hide_tr_of_hide_tr_subset1 ?_
  intro a ha hb
  rw [Set.eq_empty_iff_forall_notMem] at h
  exact h a ⟨ha, hb⟩

theorem hide_tr_of_rest_tr_empty2 {X Y : Set α} {s : traceType α} :
    X ∩ Y = ∅ → hide_tr (rest_tr s X) Y = rest_tr s X := by
  intro h
  refine hide_tr_of_hide_tr_subset2 ?_
  intro a ha hb
  rw [Set.eq_empty_iff_forall_notMem] at h
  exact h a ⟨hb, ha⟩

theorem noTick_hide_tr_of_rest_tr_empty {X Y : Set α} {s : traceType α} :
    noTick s → X ⊆ Y → hide_tr (rest_tr s X) Y = <> := by
  intro hn hXY
  refine hide_tr_nilt_sett_if ?_
  intro e he
  obtain ⟨h1, h2⟩ := rest_tr_in_event.mp he
  rcases h1 with h1 | rfl
  · obtain ⟨b, hb, rfl⟩ := h1
    exact ⟨b, hXY hb, rfl⟩
  · exact absurd h2 hn

theorem hide_tr_nohiden {X : Set α} {s : traceType α} :
    sett s ∩ Ev '' X = ∅ → hide_tr s X = s := by
  intro hsub
  revert hsub
  refine induct_trace (P := fun w => sett w ∩ Ev '' X = ∅ → hide_tr w X = w) ?_ ?_ ?_
  · intro _
    exact hide_tr_nil
  · intro _
    exact hide_tr_Tick
  · intro w a ih hsub
    rw [Set.eq_empty_iff_forall_notMem] at hsub
    have ha : a ∉ X := by
      intro hc
      exact hsub (Ev a) ⟨sett_Ev_head_mem.mpr (Or.inl rfl), Ev_mem_Ev_image.mpr hc⟩
    have hsubw : sett w ∩ Ev '' X = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e he
      exact hsub e ⟨sett_Ev_head_mem.mpr (Or.inr he.1), he.2⟩
    rw [hide_tr_notin_appt ha, ih hsubw]
