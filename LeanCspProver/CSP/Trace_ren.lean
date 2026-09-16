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

open Function
open event

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `(notick \/ t = <>)`.          -/

/- *****************************************************************

         1.
         2.
         3.
         4.

 ***************************************************************** -/

/- *************************************************************
               functions used for defining [[ ]]
 ************************************************************* -/

inductive renx (r : Set (α × β)) : traceType α → traceType β → Prop where
  | renx_nil :
      renx r <> <>
  | renx_Tick :
      renx r (Abs_trace [Tick]) (Abs_trace [Tick])
  | renx_Ev {s : traceType α} {t : traceType β} {a : α} {b : β} :
      renx r s t → (a, b) ∈ r →
        renx r ((Abs_trace [Ev a]) ^^^ s) ((Abs_trace [Ev b]) ^^^ t)

def ren_tr (s : traceType α) (r : Set (α × β)) (t : traceType β) : Prop :=
  renx r s t

syntax:1000 term:1000 " [[" term:1000 "]]*" term:1000 : term

macro_rules
  | `($s [[ $r ]]* $t) => `(ren_tr $s $r $t)

def ren_inv (r : Set (α × β)) (X : Set (event β)) : Set (event α) :=
  {ea | ∃ eb ∈ X, (ea = Tick ∧ eb = Tick) ∨ ∃ a b, (a, b) ∈ r ∧ ea = Ev a ∧ eb = Ev b}

syntax:1000 "[[" term:1000 "]]inv" term:1000 : term

macro_rules
  | `([[ $r ]]inv $X) => `(ren_inv $r $X)

theorem ren_tr_def {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    (s [[r]]* t) ↔ renx r s t :=
  Iff.rfl

theorem ren_inv_def {r : Set (α × β)} {X : Set (event β)} :
    [[r]]inv X =
      {ea | ∃ eb ∈ X, (ea = Tick ∧ eb = Tick) ∨ ∃ a b, (a, b) ∈ r ∧ ea = Ev a ∧ eb = Ev b} :=
  rfl

/- *************************************************************
                 ren_tr intros and elims
 ************************************************************* -/

/- -------------------*
 |      intros       |
 *------------------- -/

@[simp]
theorem ren_tr_nil {r : Set (α × β)} :
    (<> : traceType α) [[r]]* (<> : traceType β) :=
  renx.renx_nil

@[simp]
theorem ren_tr_Tick {r : Set (α × β)} :
    ren_tr (Abs_trace [Tick] : traceType α) r (Abs_trace [Tick] : traceType β) :=
  renx.renx_Tick

theorem ren_tr_Ev {s : traceType α} {t : traceType β} {r : Set (α × β)} {a : α} {b : β} :
    ren_tr s r t → (a, b) ∈ r →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t) := by
  intro h hmem
  exact renx.renx_Ev h hmem

/- Isabelle: lemmas ren_tr_intros = ren_tr_Ev -/

/- -------------------*
 |       elims       |
 *------------------- -/

theorem ren_tr_elims_lm {s : traceType α} {r : Set (α × β)} {t : traceType β} {P : Prop} :
    ren_tr s r t →
      ((s = <> ∧ t = <>) → P) →
      ((s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) → P) →
      (∀ a b s' t',
          (ren_tr s' r t' ∧ s = (Abs_trace [Ev a]) ^^^ s' ∧
            t = (Abs_trace [Ev b]) ^^^ t' ∧ (a, b) ∈ r) → P) →
      P := by
  intro h hNil hTick hEv
  cases h with
  | renx_nil =>
      exact hNil ⟨rfl, rfl⟩
  | renx_Tick =>
      exact hTick ⟨rfl, rfl⟩
  | renx_Ev hs hab =>
      exact hEv _ _ _ _ ⟨hs, rfl, rfl, hab⟩

theorem ren_tr_elims {s : traceType α} {r : Set (α × β)} {t : traceType β} {P : Prop} :
    ren_tr s r t →
      (s = <> → t = <> → P) →
      (s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a b s' t',
          ren_tr s' r t' → s = (Abs_trace [Ev a]) ^^^ s' →
            t = (Abs_trace [Ev b]) ^^^ t' → (a, b) ∈ r → P) →
      P := by
  intro h hNil hTick hEv
  refine ren_tr_elims_lm (s := s) (r := r) (t := t) h ?_ ?_ ?_
  · intro hs
    exact hNil hs.1 hs.2
  · intro hs
    exact hTick hs.1 hs.2
  · intro a b s' t' hs
    exact hEv a b s' t' hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/- (*** auxiliary lemmas for ren_tr (Lean port helpers) ***) -/

theorem ren_sett_Ev_appt {e : event α} {a : α} {w : traceType α} :
    e ∈ sett (Abs_trace [Ev a] ^^^ w) ↔ (e = Ev a ∨ e ∈ sett w) := by
  rw [sett_appt1 (Or.inl (noTick_Ev a)), sett_one]
  simp

theorem ren_tr_exists_of_fun {F : α → α} {s : traceType α} :
    ∃ t, ren_tr s (fun_to_rel F) t := by
  refine induct_trace (P := fun w => ∃ t, ren_tr w (fun_to_rel F) t) ?_ ?_ ?_
  · exact ⟨<>, ren_tr_nil⟩
  · exact ⟨Abs_trace [Tick], ren_tr_Tick⟩
  · rintro w a ⟨t, ht⟩
    exact ⟨Abs_trace [Ev (F a)] ^^^ t, ren_tr_Ev ht rfl⟩

theorem ren_tr_sym_of {r : Set (α × α)} {s t : traceType α} :
    (∀ a b, (a, b) ∈ r → (b, a) ∈ r) → ren_tr s r t → ren_tr t r s := by
  intro hsym h
  induction h with
  | renx_nil => exact ren_tr_nil
  | renx_Tick => exact ren_tr_Tick
  | renx_Ev hst hab ih => exact ren_tr_Ev ih (hsym _ _ hab)

theorem ren_tr_refl_of {r : Set (α × α)} {s : traceType α} :
    (∀ a, Ev a ∈ sett s → (a, a) ∈ r) → ren_tr s r s := by
  refine induct_trace (P := fun w => (∀ a, Ev a ∈ sett w → (a, a) ∈ r) → ren_tr w r w) ?_ ?_ ?_
  · intro _
    exact ren_tr_nil
  · intro _
    exact ren_tr_Tick
  · intro w a ih hcond
    exact ren_tr_Ev (ih (fun c hc => hcond c (ren_sett_Ev_appt.mpr (Or.inr hc))))
      (hcond a (ren_sett_Ev_appt.mpr (Or.inl rfl)))

theorem ren_tr_sett_inv {r : Set (α × β)} {s : traceType α} {t : traceType β}
    {A : Set α} {B : Set β} :
    ren_tr s r t → sett t ⊆ insert Tick (Ev '' B) →
      (∀ a b, (a, b) ∈ r → b ∈ B → a ∈ A) →
      sett s ⊆ insert Tick (Ev '' A) := by
  intro h
  induction h with
  | renx_nil =>
      intro _ _
      simp
  | renx_Tick =>
      intro _ _
      simp
  | renx_Ev hst hab ih =>
      rename_i s0 t0 a0 b0
      intro hsub hcond
      have hbB : b0 ∈ B := by
        rcases hsub (ren_sett_Ev_appt.mpr (Or.inl rfl)) with hb | hb
        · cases hb
        · obtain ⟨c, hc, hce⟩ := hb
          have hcb : c = b0 := inj_Ev hce
          subst hcb
          exact hc
      have hsubw : sett t0 ⊆ insert Tick (Ev '' B) :=
        fun e he => hsub (ren_sett_Ev_appt.mpr (Or.inr he))
      intro e he
      rcases ren_sett_Ev_appt.mp he with rfl | he
      · exact Set.mem_insert_of_mem _ ⟨a0, hcond a0 b0 hab hbB, rfl⟩
      · exact ih hsubw hcond he

theorem ren_tr_sett_img {r : Set (α × β)} {s : traceType α} {t : traceType β}
    {A : Set α} {B : Set β} :
    ren_tr s r t → sett s ⊆ insert Tick (Ev '' A) →
      (∀ a b, (a, b) ∈ r → a ∈ A → b ∈ B) →
      sett t ⊆ insert Tick (Ev '' B) := by
  intro h
  induction h with
  | renx_nil =>
      intro _ _
      simp
  | renx_Tick =>
      intro _ _
      simp
  | renx_Ev hst hab ih =>
      rename_i s0 t0 a0 b0
      intro hsub hcond
      have haA : a0 ∈ A := by
        rcases hsub (ren_sett_Ev_appt.mpr (Or.inl rfl)) with ha | ha
        · cases ha
        · obtain ⟨c, hc, hce⟩ := ha
          have hca : c = a0 := inj_Ev hce
          subst hca
          exact hc
      have hsubw : sett s0 ⊆ insert Tick (Ev '' A) :=
        fun e he => hsub (ren_sett_Ev_appt.mpr (Or.inr he))
      intro e he
      rcases ren_sett_Ev_appt.mp he with rfl | he
      · exact Set.mem_insert_of_mem _ ⟨b0, hcond a0 b0 hab haA, rfl⟩
      · exact ih hsubw hcond he

theorem ren_R1cf_fix {x α : Type _} {f g : x → α} {c : α}
    (hcf : ∀ y, f y ≠ c) (hcg : ∀ y, g y ≠ c) :
    Renaming1_channel_fun f g c = c := by
  by_cases hfg : ∀ x y, f x ≠ g y
  · exact Renaming1_channel_fun_h (h := fun _ : Unit => c) (x0 := ()) hfg
      (fun x _ => hcf x) (fun x _ => hcg x)
  · simp [Renaming1_channel_fun, hfg]

theorem ren_R2cf_fix {x α : Type _} {f g : x → α} {c : α} (hcf : ∀ y, f y ≠ c) :
    Renaming2_channel_fun f g c = c := by
  by_cases hfg : ∀ x y, f x ≠ g y
  · exact Renaming2_channel_fun_h (h := fun _ : Unit => c) (x0 := ()) hfg (fun x _ => hcf x)
  · simp [Renaming2_channel_fun, hfg]

/- *************************************************************
                 ren_tr decomposition
 ************************************************************* -/

/- -------------------*
 |     ren nil       |
 *------------------- -/

@[simp]
theorem ren_tr_nil1 {r : Set (α × β)} {s : traceType β} :
    ((<> : traceType α) [[r]]* s) ↔ s = <> := by
  constructor
  · intro h
    refine ren_tr_elims h ?_ ?_ ?_
    · intro _ ht
      exact ht
    · intro h0 _
      simp at h0
    · intro a b s' t' _ h0 _ _
      simp at h0
  · rintro rfl
    exact ren_tr_nil

@[simp]
theorem ren_tr_nil2 {r : Set (α × β)} {s : traceType α} :
    (s [[r]]* (<> : traceType β)) ↔ s = <> := by
  constructor
  · intro h
    refine ren_tr_elims h ?_ ?_ ?_
    · intro hs _
      exact hs
    · intro _ h0
      simp at h0
    · intro a b s' t' _ _ h0 _
      simp at h0
  · rintro rfl
    exact ren_tr_nil

/- -------------------*
 |     ren Tick      |
 *------------------- -/

@[simp]
theorem ren_tr_Tick1 {r : Set (α × β)} {s : traceType β} :
    ren_tr (Abs_trace [Tick] : traceType α) r s ↔ s = Abs_trace [Tick] := by
  constructor
  · intro h
    refine ren_tr_elims h ?_ ?_ ?_
    · intro h0 _
      simp at h0
    · intro _ ht
      exact ht
    · intro a b s' t' _ h0 _ _
      simp at h0
  · rintro rfl
    exact ren_tr_Tick

@[simp]
theorem ren_tr_Tick2 {r : Set (α × β)} {s : traceType α} :
    ren_tr s r (Abs_trace [Tick] : traceType β) ↔ s = Abs_trace [Tick] := by
  constructor
  · intro h
    refine ren_tr_elims h ?_ ?_ ?_
    · intro _ h0
      simp at h0
    · intro hs _
      exact hs
    · intro a b s' t' _ _ h0 _
      simp at h0
  · rintro rfl
    exact ren_tr_Tick

/- -------------------*
 |     ren Ev        |
 *------------------- -/

/- only if -/

theorem ren_tr_decompo_left_only_if {a : α} {s : traceType α} {r : Set (α × β)} {u : traceType β} :
    ren_tr ((Abs_trace [Ev a]) ^^^ s) r u →
      ∃ b t, u = (Abs_trace [Ev b]) ^^^ t ∧ (a, b) ∈ r ∧ ren_tr s r t := by
  intro h
  refine ren_tr_elims h ?_ ?_ ?_
  · intro h0 _
    simp at h0
  · intro h0 _
    simp at h0
  · intro c d s' t' hst h1 h2 hcd
    obtain ⟨hac, hss⟩ := appt_same_head_only_if h1
    subst hss
    refine ⟨d, t', h2, ?_, hst⟩
    rw [hac]
    exact hcd

/- if -/

theorem ren_tr_decompo_left_if {a : α} {b : β} {s : traceType α} {t : traceType β}
    {r : Set (α × β)} :
    (a, b) ∈ r → ren_tr s r t →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t) := by
  intro hab h
  exact ren_tr_Ev h hab

/- iff -/

theorem ren_tr_decompo_left {a : α} {s : traceType α} {r : Set (α × β)} {u : traceType β} :
    ren_tr ((Abs_trace [Ev a]) ^^^ s) r u ↔
      ∃ b t, u = (Abs_trace [Ev b]) ^^^ t ∧ (a, b) ∈ r ∧ ren_tr s r t := by
  constructor
  · exact ren_tr_decompo_left_only_if
  · rintro ⟨b, t, rfl, hab, h⟩
    exact ren_tr_Ev h hab

/- right -/

/- only if -/

theorem ren_tr_decompo_right_only_if {b : β} {t : traceType β} {r : Set (α × β)} {u : traceType α} :
    ren_tr u r ((Abs_trace [Ev b]) ^^^ t) →
      ∃ a s, u = (Abs_trace [Ev a]) ^^^ s ∧ (a, b) ∈ r ∧ ren_tr s r t := by
  intro h
  refine ren_tr_elims h ?_ ?_ ?_
  · intro _ h0
    simp at h0
  · intro _ h0
    simp at h0
  · intro c d s' t' hst h1 h2 hcd
    obtain ⟨hbd, htt⟩ := appt_same_head_only_if h2
    subst htt
    refine ⟨c, s', h1, ?_, hst⟩
    rw [hbd]
    exact hcd

/- if -/

theorem ren_tr_decompo_right_if {a : α} {b : β} {s : traceType α} {t : traceType β}
    {r : Set (α × β)} :
    (a, b) ∈ r → ren_tr s r t →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t) := by
  intro hab h
  exact ren_tr_Ev h hab

/- iff -/

theorem ren_tr_decompo_right {b : β} {t : traceType β} {r : Set (α × β)} {u : traceType α} :
    ren_tr u r ((Abs_trace [Ev b]) ^^^ t) ↔
      ∃ a s, u = (Abs_trace [Ev a]) ^^^ s ∧ (a, b) ∈ r ∧ ren_tr s r t := by
  constructor
  · exact ren_tr_decompo_right_only_if
  · rintro ⟨a, s, rfl, hab, h⟩
    exact ren_tr_Ev h hab

/- Isabelle: lemmas ren_tr_decompo = ren_tr_decompo_left ren_tr_decompo_right -/

/- -------------------*
 |     ren one       |
 *------------------- -/

@[simp]
theorem ren_tr_one {a : α} {b : β} {r : Set (α × β)} :
    (a, b) ∈ r →
      ren_tr (Abs_trace [Ev a] : traceType α) r (Abs_trace [Ev b] : traceType β) := by
  intro hab
  rw [show (Abs_trace [Ev a] : traceType α) = Abs_trace [Ev a] ^^^ <> by simp,
    show (Abs_trace [Ev b] : traceType β) = Abs_trace [Ev b] ^^^ <> by simp]
  exact ren_tr_Ev ren_tr_nil hab

theorem ren_tr_one_decompo_left_only_if {a : α} {r : Set (α × β)} {t : traceType β} :
    ren_tr (Abs_trace [Ev a] : traceType α) r t →
      ∃ b, t = Abs_trace [Ev b] ∧ (a, b) ∈ r := by
  intro h
  rw [show (Abs_trace [Ev a] : traceType α) = Abs_trace [Ev a] ^^^ <> by simp] at h
  obtain ⟨b, t', ht, hab, h'⟩ := ren_tr_decompo_left_only_if h
  have ht' : t' = <> := ren_tr_nil1.mp h'
  subst ht'
  exact ⟨b, by simpa using ht, hab⟩

theorem ren_tr_one_decompo_left {a : α} {r : Set (α × β)} {t : traceType β} :
    ren_tr (Abs_trace [Ev a] : traceType α) r t ↔
      ∃ b, t = Abs_trace [Ev b] ∧ (a, b) ∈ r := by
  constructor
  · exact ren_tr_one_decompo_left_only_if
  · rintro ⟨b, rfl, hab⟩
    exact ren_tr_one hab

theorem ren_tr_one_decompo_right_only_if {b : β} {r : Set (α × β)} {s : traceType α} :
    ren_tr s r (Abs_trace [Ev b] : traceType β) →
      ∃ a, s = Abs_trace [Ev a] ∧ (a, b) ∈ r := by
  intro h
  rw [show (Abs_trace [Ev b] : traceType β) = Abs_trace [Ev b] ^^^ <> by simp] at h
  obtain ⟨a, s', hs, hab, h'⟩ := ren_tr_decompo_right_only_if h
  have hs' : s' = <> := ren_tr_nil2.mp h'
  subst hs'
  exact ⟨a, by simpa using hs, hab⟩

theorem ren_tr_one_decompo_right {b : β} {r : Set (α × β)} {s : traceType α} :
    ren_tr s r (Abs_trace [Ev b] : traceType β) ↔
      ∃ a, s = Abs_trace [Ev a] ∧ (a, b) ∈ r := by
  constructor
  · exact ren_tr_one_decompo_right_only_if
  · rintro ⟨a, rfl, hab⟩
    exact ren_tr_one hab

/- Isabelle: lemmas ren_tr_one_decompo = ren_tr_one_decompo_left ren_tr_one_decompo_right -/

/- *************************************************************
                   ren_tr notick
 ************************************************************* -/

theorem ren_tr_noTick_left {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    s [[r]]* t → noTick s → noTick t := by
  intro h
  induction h with
  | renx_nil =>
      intro _
      exact noTick_nil
  | renx_Tick =>
      intro hs
      exact False.elim (not_noTick_Tick hs)
  | @renx_Ev s t a b hs hab ih =>
      intro hsNo
      have hs' : noTick s := by
        exact (decompo_appt_noTick_only_if (s := Abs_trace [Ev a]) (t := s)
          (Or.inl (noTick_Ev a)) hsNo).2
      exact decompo_appt_noTick_if (noTick_Ev b) (ih hs')

theorem ren_tr_noTick_right {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    s [[r]]* t → noTick t → noTick s := by
  intro h
  induction h with
  | renx_nil =>
      intro _
      exact noTick_nil
  | renx_Tick =>
      intro ht
      exact False.elim (not_noTick_Tick ht)
  | @renx_Ev s t a b hs hab ih =>
      intro htNo
      have ht' : noTick t := by
        exact (decompo_appt_noTick_only_if (s := Abs_trace [Ev b]) (t := t)
          (Or.inl (noTick_Ev b)) htNo).2
      exact decompo_appt_noTick_if (noTick_Ev a) (ih ht')

/- *************************************************************
                 ren_tr appending
 ************************************************************* -/

theorem ren_tr_appt_noTick_lm {s1 s2 : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    s1 [[r]]* t1 → s2 [[r]]* t2 → noTick s1 → noTick t1 → (s1 ^^^ s2) [[r]]* (t1 ^^^ t2) := by
  intro h1
  induction h1 with
  | renx_nil =>
      intro h2 _ _
      simpa using h2
  | renx_Tick =>
      intro _ hn _
      exact absurd hn not_noTick_Tick
  | renx_Ev hs hab ih =>
      intro h2 hn1 hn2
      have hs1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hn1).2
      have ht1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hn2).2
      rw [appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hs1),
        appt_assoc (Or.inl (noTick_Ev _)) (Or.inl ht1)]
      exact ren_tr_Ev (ih h2 hs1 ht1) hab

theorem ren_tr_appt {s1 s2 : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    s1 [[r]]* t1 → s2 [[r]]* t2 → (noTick s1 ∨ noTick t1 ∨ s2 = <> ∨ t2 = <>) →
      (s1 ^^^ s2) [[r]]* (t1 ^^^ t2) := by
  intro h1 h2 hc
  rcases hc with hn | hn | rfl | rfl
  · exact ren_tr_appt_noTick_lm h1 h2 hn (ren_tr_noTick_left h1 hn)
  · exact ren_tr_appt_noTick_lm h1 h2 (ren_tr_noTick_right h1 hn) hn
  · have ht2 : t2 = <> := ren_tr_nil1.mp h2
    subst ht2
    simpa using h1
  · have hs2 : s2 = <> := ren_tr_nil2.mp h2
    subst hs2
    simpa using h1

theorem ren_tr_appt_Ev {a : α} {b : β} {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    (a, b) ∈ r → ren_tr s r t →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t) := by
  intro hab h
  exact ren_tr_Ev h hab

theorem ren_tr_appt_decompo_left_only_if {s1 s2 : traceType α} {r : Set (α × β)} {t : traceType β} :
    (s1 ^^^ s2) [[r]]* t → (noTick s1 ∨ s2 = <>) →
      ∃ t1 t2, t = t1 ^^^ t2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick t1 ∨ t2 = <>) := by
  have key : ∀ w : traceType α, ∀ t0 : traceType β, (w ^^^ s2) [[r]]* t0 →
      (noTick w ∨ s2 = <>) →
      ∃ t1 t2, t0 = t1 ^^^ t2 ∧ w [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick t1 ∨ t2 = <>) := by
    intro w
    refine induct_trace (P := fun w => ∀ t0 : traceType β, (w ^^^ s2) [[r]]* t0 →
        (noTick w ∨ s2 = <>) →
        ∃ t1 t2, t0 = t1 ^^^ t2 ∧ w [[r]]* t1 ∧ s2 [[r]]* t2 ∧
          (noTick t1 ∨ t2 = <>)) ?_ ?_ ?_
    · intro t0 h _
      rw [appt_nil_left] at h
      exact ⟨<>, t0, by simp, ren_tr_nil, h, Or.inl noTick_nil⟩
    · intro t0 h hc
      rcases hc with hn | rfl
      · exact absurd hn not_noTick_Tick
      · rw [appt_nil_right] at h
        have ht : t0 = Abs_trace [Tick] := ren_tr_Tick1.mp h
        subst ht
        exact ⟨Abs_trace [Tick], <>, by simp, ren_tr_Tick, ren_tr_nil, Or.inr rfl⟩
    · intro w a ih t0 h hc
      have hw : noTick w ∨ s2 = <> := by
        rcases hc with hn | rfl
        · exact Or.inl (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hn).2
        · exact Or.inr rfl
      rw [appt_assoc (Or.inl (noTick_Ev a)) hw] at h
      obtain ⟨b, t', ht, hab, h'⟩ := ren_tr_decompo_left_only_if h
      obtain ⟨t1, t2, ht', hw1, hs2, hcond⟩ := ih t' h' hw
      refine ⟨Abs_trace [Ev b] ^^^ t1, t2, ?_, ren_tr_Ev hw1 hab, hs2, ?_⟩
      · rw [ht, ht', appt_assoc (Or.inl (noTick_Ev b)) hcond]
      · rcases hcond with hn | rfl
        · exact Or.inl (decompo_appt_noTick_if (noTick_Ev b) hn)
        · exact Or.inr rfl
  exact fun h hc => key s1 t h hc

theorem ren_tr_appt_decompo_left {s1 s2 : traceType α} {r : Set (α × β)} {t : traceType β} :
    (noTick s1 ∨ s2 = <>) →
      ((s1 ^^^ s2) [[r]]* t ↔
        ∃ t1 t2, t = t1 ^^^ t2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick t1 ∨ t2 = <>)) := by
  intro hc
  constructor
  · intro h
    exact ren_tr_appt_decompo_left_only_if h hc
  · rintro ⟨t1, t2, rfl, h1, h2, hc2⟩
    refine ren_tr_appt h1 h2 ?_
    rcases hc with hn | rfl
    · exact Or.inl hn
    · exact Or.inr (Or.inr (Or.inl rfl))

theorem ren_tr_appt_decompo_right_only_if {s : traceType α} {r : Set (α × β)}
    {t1 t2 : traceType β} :
    s [[r]]* (t1 ^^^ t2) → (noTick t1 ∨ t2 = <>) →
      ∃ s1 s2, s = s1 ^^^ s2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick s1 ∨ s2 = <>) := by
  have key : ∀ w : traceType β, ∀ s0 : traceType α, s0 [[r]]* (w ^^^ t2) →
      (noTick w ∨ t2 = <>) →
      ∃ s1 s2, s0 = s1 ^^^ s2 ∧ s1 [[r]]* w ∧ s2 [[r]]* t2 ∧ (noTick s1 ∨ s2 = <>) := by
    intro w
    refine induct_trace (P := fun w => ∀ s0 : traceType α, s0 [[r]]* (w ^^^ t2) →
        (noTick w ∨ t2 = <>) →
        ∃ s1 s2, s0 = s1 ^^^ s2 ∧ s1 [[r]]* w ∧ s2 [[r]]* t2 ∧
          (noTick s1 ∨ s2 = <>)) ?_ ?_ ?_
    · intro s0 h _
      rw [appt_nil_left] at h
      exact ⟨<>, s0, by simp, ren_tr_nil, h, Or.inl noTick_nil⟩
    · intro s0 h hc
      rcases hc with hn | rfl
      · exact absurd hn not_noTick_Tick
      · rw [appt_nil_right] at h
        have hs : s0 = Abs_trace [Tick] := ren_tr_Tick2.mp h
        subst hs
        exact ⟨Abs_trace [Tick], <>, by simp, ren_tr_Tick, ren_tr_nil, Or.inr rfl⟩
    · intro w b ih s0 h hc
      have hw : noTick w ∨ t2 = <> := by
        rcases hc with hn | rfl
        · exact Or.inl (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hn).2
        · exact Or.inr rfl
      rw [appt_assoc (Or.inl (noTick_Ev b)) hw] at h
      obtain ⟨a, s', hs, hab, h'⟩ := ren_tr_decompo_right_only_if h
      obtain ⟨s1, s2, hs', hw1, ht2, hcond⟩ := ih s' h' hw
      refine ⟨Abs_trace [Ev a] ^^^ s1, s2, ?_, ren_tr_Ev hw1 hab, ht2, ?_⟩
      · rw [hs, hs', appt_assoc (Or.inl (noTick_Ev a)) hcond]
      · rcases hcond with hn | rfl
        · exact Or.inl (decompo_appt_noTick_if (noTick_Ev a) hn)
        · exact Or.inr rfl
  exact fun h hc => key t1 s h hc

theorem ren_tr_appt_decompo_right {s : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    (noTick t1 ∨ t2 = <>) →
      (s [[r]]* (t1 ^^^ t2) ↔
        ∃ s1 s2, s = s1 ^^^ s2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick s1 ∨ s2 = <>)) := by
  intro hc
  constructor
  · intro h
    exact ren_tr_appt_decompo_right_only_if h hc
  · rintro ⟨s1, s2, rfl, h1, h2, hc2⟩
    refine ren_tr_appt h1 h2 ?_
    rcases hc with hn | rfl
    · exact Or.inr (Or.inl hn)
    · exact Or.inr (Or.inr (Or.inr rfl))

/- Isabelle: lemmas ren_tr_appt_decompo = ren_tr_appt_decompo_left ren_tr_appt_decompo_right -/

@[simp]
theorem ren_tr_head_decompo {a : α} {b : β} {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t) ↔
      ((a, b) ∈ r ∧ ren_tr s r t) := by
  constructor
  · intro h
    obtain ⟨b', t', ht, hab, h'⟩ := ren_tr_decompo_left_only_if h
    obtain ⟨hbb, htt⟩ := appt_same_head_only_if ht
    subst htt
    refine ⟨?_, h'⟩
    rw [hbb]
    exact hab
  · rintro ⟨hab, h⟩
    exact ren_tr_Ev h hab

@[simp]
theorem ren_tr_last_decompo_Ev {a : α} {b : β} {s : traceType α} {r : Set (α × β)}
    {t : traceType β} :
    noTick s → noTick t →
      (ren_tr (s ^^^ Abs_trace [Ev a]) r (t ^^^ Abs_trace [Ev b]) ↔
        (ren_tr s r t ∧ (a, b) ∈ r)) := by
  intro hns hnt
  constructor
  · intro h
    obtain ⟨t1, t2, ht, h1, h2, hcond⟩ :=
      ren_tr_appt_decompo_left_only_if h (Or.inl hns)
    obtain ⟨b', hb', hab⟩ := ren_tr_one_decompo_left_only_if h2
    subst hb'
    have hn1 : noTick t1 := by
      rcases hcond with hn | h0
      · exact hn
      · simp at h0
    obtain ⟨htt, hbb⟩ := appt_same_last_only_if hnt hn1 ht
    subst htt
    refine ⟨h1, ?_⟩
    rw [inj_Ev hbb]
    exact hab
  · rintro ⟨h, hab⟩
    exact ren_tr_appt h (ren_tr_one hab) (Or.inl hns)

@[simp]
theorem ren_tr_last_decompo_Tick {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    noTick s → noTick t →
      (ren_tr (s ^^^ Abs_trace [Tick]) r (t ^^^ Abs_trace [Tick]) ↔ ren_tr s r t) := by
  intro hns hnt
  constructor
  · intro h
    obtain ⟨t1, t2, ht, h1, h2, hcond⟩ :=
      ren_tr_appt_decompo_left_only_if h (Or.inl hns)
    have ht2 : t2 = Abs_trace [Tick] := ren_tr_Tick1.mp h2
    subst ht2
    have hn1 : noTick t1 := by
      rcases hcond with hn | h0
      · exact hn
      · simp at h0
    obtain ⟨htt, _⟩ := appt_same_last_only_if hnt hn1 ht
    subst htt
    exact h1
  · intro h
    exact ren_tr_appt h ren_tr_Tick (Or.inl hns)

/- *************************************************************
                 ren_tr lengtht
 ************************************************************* -/

theorem ren_tr_lengtht {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    s [[r]]* t → lengtht s = lengtht t := by
  intro h
  induction h with
  | renx_nil =>
      simp
  | renx_Tick =>
      simp
  | @renx_Ev s t a b hs hab ih =>
      simpa using congrArg Nat.succ ih

/- *************************************************************
                    ren_tr prefix
 ************************************************************* -/

theorem ren_tr_prefix_lm {r : Set (α × β)} {u v : traceType β} {s : traceType α} :
    «prefix» v u → s [[r]]* u → ∃ t, «prefix» t s ∧ t [[r]]* v := by
  rintro ⟨w, rfl, hc⟩ h
  obtain ⟨s1, s2, rfl, h1, h2, hc2⟩ := ren_tr_appt_decompo_right_only_if h hc
  exact ⟨s1, prefix_appt_simp hc2, h1⟩

theorem ren_tr_prefix {r : Set (α × β)} {u v : traceType β} {s : traceType α} :
    «prefix» v u → s [[r]]* u → ∃ t, «prefix» t s ∧ t [[r]]* v := by
  exact ren_tr_prefix_lm

theorem ren_tr_prefixE {r : Set (α × β)} {u v : traceType β} {s : traceType α} {R : Prop} :
    «prefix» v u → s [[r]]* u →
      (∀ t, «prefix» t s → t [[r]]* v → R) → R := by
  intro hp h hR
  obtain ⟨t, hpt, hrt⟩ := ren_tr_prefix hp h
  exact hR t hpt hrt

/- (*** more auxiliary lemmas for ren_tr (Lean port helpers) ***) -/

theorem ren_tr_fun_unique {F : α → α} {s t : traceType α} :
    ren_tr s (fun_to_rel F) t → ∀ t', ren_tr s (fun_to_rel F) t' → t = t' := by
  intro h
  induction h with
  | renx_nil =>
      intro t' h'
      exact (ren_tr_nil1.mp h').symm
  | renx_Tick =>
      intro t' h'
      exact (ren_tr_Tick1.mp h').symm
  | renx_Ev hst hab ih =>
      rename_i s0 t0 a0 b0
      intro t' h'
      obtain ⟨c, u', hu, hac, h''⟩ := ren_tr_decompo_left_only_if h'
      have hb : b0 = F a0 := hab
      have hc : c = F a0 := hac
      rw [hu, ih u' h'', hb, hc]

theorem ren_tr_fun_comp {F G : α → α} {s t : traceType α} :
    ren_tr s (fun_to_rel F) t → ∀ u : traceType α, ren_tr t (fun_to_rel G) u →
      ren_tr s (fun_to_rel (G ∘ F)) u := by
  intro h
  induction h with
  | renx_nil =>
      intro u h'
      rw [ren_tr_nil1.mp h']
      exact ren_tr_nil
  | renx_Tick =>
      intro u h'
      rw [ren_tr_Tick1.mp h']
      exact ren_tr_Tick
  | renx_Ev hst hab ih =>
      rename_i s0 t0 a0 b0
      intro u h'
      obtain ⟨c, u', hu, hbc, h''⟩ := ren_tr_decompo_left_only_if h'
      have hb : b0 = F a0 := hab
      have hc : c = G b0 := hbc
      subst hu
      have hmem : (a0, c) ∈ fun_to_rel (G ∘ F) := by
        rw [mem_fun_to_rel, hc, hb]
        rfl
      exact ren_tr_Ev (ih u' h'') hmem

theorem ren_R1cf_involutive {x α : Type _} {f g : x → α} (hf : Injective f) (hg : Injective g)
    (a : α) : Renaming1_channel_fun f g (Renaming1_channel_fun f g a) = a := by
  have h0 : (a, Renaming1_channel_fun f g a) ∈ (f <==> g) := by simp
  have h1 := Renaming_channel_sym_rule hf hg h0
  exact (by simpa using h1 :
    a = Renaming1_channel_fun f g (Renaming1_channel_fun f g a)).symm

theorem ren_inv_mem_Tick {r : Set (α × α)} {X : Set (event α)} :
    (Tick : event α) ∈ [[r]]inv X ↔ Tick ∈ X := by
  constructor
  · rintro ⟨eb, hebX, (⟨_, rfl⟩ | ⟨a, b, _, ha, _⟩)⟩
    · exact hebX
    · cases ha
  · intro hX
    exact ⟨Tick, hX, Or.inl ⟨rfl, rfl⟩⟩

theorem ren_inv_mem_Ev {r : Set (α × α)} {X : Set (event α)} {a : α} :
    (Ev a : event α) ∈ [[r]]inv X ↔ ∃ b, (a, b) ∈ r ∧ Ev b ∈ X := by
  constructor
  · rintro ⟨eb, hebX, (⟨ha, _⟩ | ⟨c, b, hr, hca, rfl⟩)⟩
    · cases ha
    · have hac : c = a := (inj_Ev hca).symm
      subst hac
      exact ⟨b, hr, hebX⟩
  · rintro ⟨b, hr, hb⟩
    exact ⟨Ev b, hb, Or.inr ⟨a, b, hr, rfl, rfl⟩⟩

/- *************************************************************
                    inj --> unique
 ************************************************************* -/

theorem ren_tr_inj_unique_ALL {f : α → β} {t : traceType β} {s1 s2 : traceType α} :
    Injective f →
      s1 [[{p | ∃ a, p = (a, f a)}]]* t →
      s2 [[{p | ∃ a, p = (a, f a)}]]* t →
      s1 = s2 := by
  intro hf h1
  induction h1 generalizing s2 with
  | renx_nil =>
      intro h2
      exact (ren_tr_nil2.mp h2).symm
  | renx_Tick =>
      intro h2
      exact (ren_tr_Tick2.mp h2).symm
  | renx_Ev hst hab ih =>
      rename_i s0 t0 a0 b0
      intro h2
      obtain ⟨c, s', hs, hcb, h'⟩ := ren_tr_decompo_right_only_if h2
      obtain ⟨x, hx⟩ := hab
      obtain ⟨y, hy⟩ := hcb
      rw [Prod.mk.injEq] at hx hy
      have hxy : x = y := hf (by rw [← hx.2, ← hy.2])
      rw [hs, ih h', hx.1, hy.1, hxy]

theorem ren_tr_inj_unique {f : α → β} {t : traceType β} {s1 s2 : traceType α} :
    Injective f →
      s1 [[{p | ∃ a, p = (a, f a)}]]* t →
      s2 [[{p | ∃ a, p = (a, f a)}]]* t →
      s1 = s2 := by
  exact ren_tr_inj_unique_ALL

/- *************************************************************
                       inverse R
 ************************************************************* -/

theorem ren_inv_sub_Evset {r : Set (α × β)} :
    [[r]]inv (Evset : Set (event β)) ⊆ (Evset : Set (event α)) := by
  intro ea hea
  rcases hea with ⟨eb, heb, hTick | ⟨a, b, _, hea', _⟩⟩
  · rcases hTick with ⟨heaTick, hebTick⟩
    subst ea
    subst eb
    simp [Evset] at heb
  · subst ea
    simp [Evset]

theorem ren_inv_sub {r : Set (α × β)} {X Y : Set (event β)} :
    X ⊆ Y → [[r]]inv X ⊆ [[r]]inv Y := by
  intro hXY ea hea
  rcases hea with ⟨eb, heb, h⟩
  exact ⟨eb, hXY heb, h⟩

@[simp]
theorem ren_inv_Un {r : Set (α × β)} {X Y : Set (event β)} :
    [[r]]inv (X ∪ Y) = [[r]]inv X ∪ [[r]]inv Y := by
  ext ea
  constructor
  · intro hea
    rcases hea with ⟨eb, heb, hrel⟩
    rcases heb with heb | heb
    · exact Or.inl ⟨eb, heb, hrel⟩
    · exact Or.inr ⟨eb, heb, hrel⟩
  · intro hea
    rcases hea with hea | hea
    · rcases hea with ⟨eb, heb, hrel⟩
      exact ⟨eb, Or.inl heb, hrel⟩
    · rcases hea with ⟨eb, heb, hrel⟩
      exact ⟨eb, Or.inr heb, hrel⟩

@[simp]
theorem ren_inv_no_Tick {r : Set (α × β)} {X : Set (event β)} :
    ([[r]]inv X ⊆ (Evset : Set (event α))) ↔ X ⊆ (Evset : Set (event β)) := by
  constructor
  · intro hX eb heb
    rcases event_Tick_or_Ev eb with rfl | ⟨b, rfl⟩
    · have hTick : (Tick : event α) ∈ [[r]]inv X := by
        exact ⟨Tick, heb, Or.inl ⟨rfl, rfl⟩⟩
      exact False.elim (by simpa [Evset] using hX hTick)
    · simp [Evset]
  · intro hX ea hea
    rcases hea with ⟨eb, heb, hTick | ⟨a, b, _, hea', heb'⟩⟩
    · rcases hTick with ⟨heaTick, hebTick⟩
      subst ea
      subst eb
      exact False.elim (by simpa [Evset] using hX heb)
    · subst ea
      simp [Evset]

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

/- -------------- *
         ren
 * -------------- -/

/- inverse set -/

@[simp]
theorem ren_inv_Int_Tick {r : Set (α × α)} {X : Set (event α)} :
    [[r]]inv (X ∩ {Tick}) = X ∩ {Tick} := by
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · rw [ren_inv_mem_Tick]
  · constructor
    · intro he
      obtain ⟨b, _, hb⟩ := ren_inv_mem_Ev.mp he
      exact absurd hb.2 (by simp)
    · intro he
      exact absurd he.2 (by simp)

@[simp]
theorem ren_inv_diff_Tick {r : Set (α × α)} {X : Set (event α)} :
    [[r]]inv (X \ {Tick}) = [[r]]inv X \ (X ∩ {Tick}) := by
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · constructor
    · intro he
      exact absurd rfl (ren_inv_mem_Tick.mp he).2
    · rintro ⟨h1, h2⟩
      exact absurd ⟨ren_inv_mem_Tick.mp h1, rfl⟩ h2
  · constructor
    · intro he
      obtain ⟨b, hr, hb⟩ := ren_inv_mem_Ev.mp he
      refine ⟨ren_inv_mem_Ev.mpr ⟨b, hr, hb.1⟩, ?_⟩
      rintro ⟨-, h0⟩
      exact absurd h0 (by simp)
    · rintro ⟨h1, -⟩
      obtain ⟨b, hr, hb⟩ := ren_inv_mem_Ev.mp h1
      exact ren_inv_mem_Ev.mpr ⟨b, hr, hb, by simp⟩

theorem ren_inv_insert_Tick {r : Set (α × α)} {X : Set (event α)} :
    [[r]]inv (insert Tick X) = insert Tick ([[r]]inv X) := by
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · constructor
    · intro _
      exact Set.mem_insert _ _
    · intro _
      exact ren_inv_mem_Tick.mpr (Set.mem_insert _ _)
  · constructor
    · intro he
      obtain ⟨b, hr, hb⟩ := ren_inv_mem_Ev.mp he
      rcases hb with hb | hb
      · cases hb
      · exact Set.mem_insert_of_mem _ (ren_inv_mem_Ev.mpr ⟨b, hr, hb⟩)
    · intro he
      rcases he with he | he
      · cases he
      · obtain ⟨b, hr, hb⟩ := ren_inv_mem_Ev.mp he
        exact ren_inv_mem_Ev.mpr ⟨b, hr, Set.mem_insert_of_mem _ hb⟩

/-  ren_tr -- noTick -/

theorem ren_tr_Tick_left {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    s [[r]]* t → ¬ noTick s → ¬ noTick t := by
  intro h hs ht
  exact hs (ren_tr_noTick_right h ht)

theorem ren_tr_Tick_right {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    s [[r]]* t → ¬ noTick t → ¬ noTick s := by
  intro h ht hs
  exact ht (ren_tr_noTick_left h hs)

/- --- Renaming channel & sett 1 --- -/

theorem Renaming1_channel_sett_lm {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <==> g) t →
      sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  intro hf hh hg hfg hfh hgh hsub h
  refine ren_tr_sett_inv h hsub ?_
  intro a b hab hbB
  have hba : (b, a) ∈ (f <==> g) := Renaming_channel_sym_rule hf hg hab
  have ha : a = Renaming1_channel_fun f g b := by simpa using hba
  rcases hbB with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [Renaming1_channel_fun_f hf hfg] at ha
    exact Or.inl ⟨x, ha.symm⟩
  · rw [ren_R1cf_fix (fun y => hfh y x) (fun y => hgh y x)] at ha
    exact Or.inr ⟨x, ha.symm⟩

theorem Renaming1_channel_sett1 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <==> g) t →
      sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  exact Renaming1_channel_sett_lm

theorem Renaming1_channel_sett2 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range f)) →
      ren_tr s (f <==> g) t →
      sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g)) := by
  intro hf hh hg hfg hfh hgh hsub h
  refine ren_tr_sett_inv h hsub ?_
  intro a b hab hbB
  have hba : (b, a) ∈ (f <==> g) := Renaming_channel_sym_rule hf hg hab
  have ha : a = Renaming1_channel_fun f g b := by simpa using hba
  rcases hbB with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [ren_R1cf_fix (fun y => hfh y x) (fun y => hgh y x)] at ha
    exact Or.inl ⟨x, ha.symm⟩
  · rw [Renaming1_channel_fun_f hf hfg] at ha
    exact Or.inr ⟨x, ha.symm⟩

theorem Renaming1_channel_sett3 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (g <==> f) t →
      sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  intro hf hh hg hfg hfh hgh hsub h
  rw [← Renaming_channel_commut (f := f) (g := g)] at h
  exact Renaming1_channel_sett1 hf hh hg hfg hfh hgh hsub h

theorem Renaming1_channel_sett4 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range f)) →
      ren_tr s (g <==> f) t →
      sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g)) := by
  intro hf hh hg hfg hfh hgh hsub h
  rw [← Renaming_channel_commut (f := f) (g := g)] at h
  exact Renaming1_channel_sett2 hf hh hg hfg hfh hgh hsub h

/- Isabelle: lemmas Renaming1_channel_sett =
       Renaming1_channel_sett1
       Renaming1_channel_sett2
       Renaming1_channel_sett3
       Renaming1_channel_sett4 -/

theorem Renaming2_channel_sett_lm {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett s ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <== g) t →
      sett t ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  intro hf hh hg hfg hfh hgh hsub h
  refine ren_tr_sett_img h hsub ?_
  intro a b hab haA
  have hb : b = Renaming2_channel_fun f g a := by simpa using hab
  rcases haA with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [Renaming2_channel_fun_f hf hfg] at hb
    exact Or.inl ⟨x, hb.symm⟩
  · rw [ren_R2cf_fix (fun y => hfh y x)] at hb
    exact Or.inr ⟨x, hb.symm⟩

theorem Renaming2_channel_sett {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett s ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <== g) t →
      sett t ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  exact Renaming2_channel_sett_lm

/- Isabelle: lemmas Renaming_channel_sett =
       Renaming1_channel_sett
       Renaming2_channel_sett -/

theorem ren_tr_Renaming_channel_sym_rule {x α : Type _} {f g : x → α}
    {s t : traceType α} :
    Injective f → Injective g → ren_tr s (f <==> g) t → ren_tr t (f <==> g) s := by
  intro hf hg h
  exact ren_tr_sym_of (fun a b hab => Renaming_channel_sym_rule hf hg hab) h

theorem ren_tr_Renaming_channel_sym {x α : Type _} {f g : x → α}
    {s t : traceType α} :
    Injective f → Injective g → (ren_tr s (f <==> g) t ↔ ren_tr t (f <==> g) s) := by
  intro hf hg
  exact ⟨ren_tr_Renaming_channel_sym_rule hf hg, ren_tr_Renaming_channel_sym_rule hf hg⟩

theorem Renaming1_channel_exist_left {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → ∃ t, ren_tr s (f <==> g) t := by
  intro _ _
  exact ren_tr_exists_of_fun

theorem Renaming1_channel_exist_right {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → ∃ t, ren_tr t (f <==> g) s := by
  intro hf hg
  obtain ⟨t, ht⟩ := Renaming1_channel_exist_left (s := s) hf hg
  exact ⟨t, ren_tr_Renaming_channel_sym_rule hf hg ht⟩

theorem Renaming2_channel_exist_left {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → ∃ t, ren_tr s (f <== g) t := by
  intro _ _
  exact ren_tr_exists_of_fun

/- Isabelle: lemmas Renaming_channel_exist_left =
       Renaming1_channel_exist_left
       Renaming2_channel_exist_left -/

/- Isabelle: lemmas Renaming_channel_exist_right =
       Renaming1_channel_exist_right -/

theorem Renaming_channel_ren_inv_Int_Tick_eq {x α : Type _} {f g : x → α} {X : Set (event α)} :
    ren_inv (f <==> g) X ∩ {Tick} = X ∩ {Tick} := by
  ext e
  constructor
  · rintro ⟨h1, h2⟩
    rw [Set.mem_singleton_iff] at h2
    subst h2
    exact ⟨ren_inv_mem_Tick.mp h1, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [Set.mem_singleton_iff] at h2
    subst h2
    exact ⟨ren_inv_mem_Tick.mpr h1, rfl⟩

theorem Renaming_channel_ren_inv_Int_eq {x y α : Type _} {f g : x → α} {h : y → α}
    {X : Set (event α)} :
    (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      ren_inv (f <==> g) X ∩ (Ev '' Set.range h) = X ∩ (Ev '' Set.range h) := by
  intro hfh hgh
  ext e
  constructor
  · rintro ⟨h1, c, ⟨x0, rfl⟩, rfl⟩
    refine ⟨?_, ⟨h x0, ⟨x0, rfl⟩, rfl⟩⟩
    obtain ⟨b, hr, hb⟩ := ren_inv_mem_Ev.mp h1
    have hbv : b = Renaming1_channel_fun f g (h x0) := by simpa using hr
    rw [ren_R1cf_fix (fun y => hfh y x0) (fun y => hgh y x0)] at hbv
    subst hbv
    exact hb
  · rintro ⟨h1, c, ⟨x0, rfl⟩, rfl⟩
    refine ⟨?_, ⟨h x0, ⟨x0, rfl⟩, rfl⟩⟩
    refine ren_inv_mem_Ev.mpr ⟨h x0, ?_, h1⟩
    simpa using
      (ren_R1cf_fix (f := f) (g := g) (fun y => hfh y x0) (fun y => hgh y x0)).symm

theorem Renaming_channel_ren_inv_ren_inv_eq {x α : Type _} {f g : x → α} {X : Set (event α)} :
    Injective f → Injective g → ren_inv (f <==> g) (ren_inv (f <==> g) X) = X := by
  intro hf hg
  ext e
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · rw [ren_inv_mem_Tick, ren_inv_mem_Tick]
  · constructor
    · intro he
      obtain ⟨b, hr, hb⟩ := ren_inv_mem_Ev.mp he
      obtain ⟨c, hr2, hc⟩ := ren_inv_mem_Ev.mp hb
      have hb1 : b = Renaming1_channel_fun f g a := by simpa using hr
      have hc1 : c = Renaming1_channel_fun f g b := by simpa using hr2
      rw [hb1, ren_R1cf_involutive hf hg] at hc1
      subst hc1
      exact hc
    · intro he
      refine ren_inv_mem_Ev.mpr ⟨Renaming1_channel_fun f g a, by simp, ?_⟩
      refine ren_inv_mem_Ev.mpr ⟨a, ?_, he⟩
      simpa using (ren_R1cf_involutive hf hg a).symm

theorem Renaming_channel_ren_tr_commut {x y α : Type _}
    {f1 f2 : x → α} {g1 g2 : y → α}
    {s1 s2 t1 t2 t2' : traceType α} :
    Injective f1 → Injective f2 → Injective g1 → Injective g2 →
      (∀ x y, f1 x ≠ f2 y) →
      (∀ x y, f1 x ≠ g1 y) →
      (∀ x y, f1 x ≠ g2 y) →
      (∀ x y, f2 x ≠ g1 y) →
      (∀ x y, f2 x ≠ g2 y) →
      (∀ x y, g1 x ≠ g2 y) →
      ren_tr s1 (f1 <==> f2) s2 →
      ren_tr s2 (g1 <==> g2) t2 →
      ren_tr s1 (g1 <==> g2) t1 →
      ren_tr t1 (f1 <==> f2) t2' →
      t2 = t2' := by
  intro hf1 hf2 hg1 hg2 h12 h1g1 h1g2 h2g1 h2g2 hg12 hs1 hs2 ht1 ht2
  have hcomm : (Renaming1_channel_fun g1 g2) ∘ (Renaming1_channel_fun f1 f2) =
      (Renaming1_channel_fun f1 f2) ∘ (Renaming1_channel_fun g1 g2) := by
    funext a
    exact Renaming_channel_independ f1 f2 g1 g2 a (Renaming1_channel_fun f1 f2 a)
      (Renaming1_channel_fun g1 g2 a)
      (Renaming1_channel_fun g1 g2 (Renaming1_channel_fun f1 f2 a))
      (Renaming1_channel_fun f1 f2 (Renaming1_channel_fun g1 g2 a))
      ⟨hf1, hf2, hg1, hg2, h12, h1g1, h1g2, h2g1, h2g2, hg12, by simp, by simp, by simp,
        by simp⟩
  have hs1' : ren_tr s1 (fun_to_rel (Renaming1_channel_fun f1 f2)) s2 := hs1
  have hs2' : ren_tr s2 (fun_to_rel (Renaming1_channel_fun g1 g2)) t2 := hs2
  have ht1' : ren_tr s1 (fun_to_rel (Renaming1_channel_fun g1 g2)) t1 := ht1
  have ht2' : ren_tr t1 (fun_to_rel (Renaming1_channel_fun f1 f2)) t2' := ht2
  have hA := ren_tr_fun_comp hs1' t2 hs2'
  have hB := ren_tr_fun_comp ht1' t2' ht2'
  rw [← hcomm] at hB
  exact ren_tr_fun_unique hA t2' hB

theorem Renaming_channel_ren_tr_commut_rule {x y α : Type _}
    {f1 f2 : x → α} {g1 g2 : y → α}
    {s1 s2 t1 t2 t2' : traceType α} :
    Injective f1 → Injective f2 → Injective g1 → Injective g2 →
      (∀ x y, f1 x ≠ f2 y) →
      (∀ x y, f1 x ≠ g1 y) →
      (∀ x y, f1 x ≠ g2 y) →
      (∀ x y, f2 x ≠ g1 y) →
      (∀ x y, f2 x ≠ g2 y) →
      (∀ x y, g1 x ≠ g2 y) →
      ren_tr s1 (f1 <==> f2) s2 →
      ren_tr s2 (g1 <==> g2) t2 →
      ren_tr s1 (g1 <==> g2) t1 →
      ren_tr t1 (f1 <==> f2) t2' →
      t2 = t2' := by
  exact Renaming_channel_ren_tr_commut

theorem Renaming1_channel_id {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      sett s ∩ (Ev '' Set.range f) = ∅ →
      sett s ∩ (Ev '' Set.range g) = ∅ →
      ren_tr s (f <==> g) s := by
  intro hf hg hfg h1 h2
  refine ren_tr_refl_of ?_
  intro a ha
  have haf : ∀ y, f y ≠ a := by
    intro y hy
    rw [Set.eq_empty_iff_forall_notMem] at h1
    exact h1 (Ev a) ⟨ha, ⟨f y, ⟨y, rfl⟩, by rw [hy]⟩⟩
  have hag : ∀ y, g y ≠ a := by
    intro y hy
    rw [Set.eq_empty_iff_forall_notMem] at h2
    exact h2 (Ev a) ⟨ha, ⟨g y, ⟨y, rfl⟩, by rw [hy]⟩⟩
  simpa using (ren_R1cf_fix haf hag).symm

theorem Renaming2_channel_id {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      sett s ∩ (Ev '' Set.range f) = ∅ →
      ren_tr s (f <== g) s := by
  intro hf hg hfg h1
  refine ren_tr_refl_of ?_
  intro a ha
  have haf : ∀ y, f y ≠ a := by
    intro y hy
    rw [Set.eq_empty_iff_forall_notMem] at h1
    exact h1 (Ev a) ⟨ha, ⟨f y, ⟨y, rfl⟩, by rw [hy]⟩⟩
  simpa using (ren_R2cf_fix (g := g) haf).symm

/- Isabelle: lemmas Renaming_channel_id =
       Renaming1_channel_id
       Renaming2_channel_id -/

theorem Renaming_channel_id_Un {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      sett s ∩ (Ev '' (Set.range f ∪ Set.range g)) = ∅ →
      ren_tr s (f <==> g) s := by
  intro hf hg hfg h
  rw [Set.eq_empty_iff_forall_notMem] at h
  refine Renaming1_channel_id hf hg hfg ?_ ?_
  · rw [Set.eq_empty_iff_forall_notMem]
    intro e he
    exact h e ⟨he.1, Set.image_mono Set.subset_union_left he.2⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    intro e he
    exact h e ⟨he.1, Set.image_mono Set.subset_union_right he.2⟩
