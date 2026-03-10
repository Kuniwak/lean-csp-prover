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

open Classical
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

/- *************************************************************
                 ren_tr decomposition
 ************************************************************* -/

/- -------------------*
 |     ren nil       |
 *------------------- -/

@[simp]
axiom ren_tr_nil1 {r : Set (α × β)} {s : traceType β} :
    ((<> : traceType α) [[r]]* s) ↔ s = <>

@[simp]
axiom ren_tr_nil2 {r : Set (α × β)} {s : traceType α} :
    (s [[r]]* (<> : traceType β)) ↔ s = <>

/- -------------------*
 |     ren Tick      |
 *------------------- -/

@[simp]
axiom ren_tr_Tick1 {r : Set (α × β)} {s : traceType β} :
    ren_tr (Abs_trace [Tick] : traceType α) r s ↔ s = Abs_trace [Tick]

@[simp]
axiom ren_tr_Tick2 {r : Set (α × β)} {s : traceType α} :
    ren_tr s r (Abs_trace [Tick] : traceType β) ↔ s = Abs_trace [Tick]

/- -------------------*
 |     ren Ev        |
 *------------------- -/

/- only if -/

axiom ren_tr_decompo_left_only_if {a : α} {s : traceType α} {r : Set (α × β)} {u : traceType β} :
    ren_tr ((Abs_trace [Ev a]) ^^^ s) r u →
      ∃ b t, u = (Abs_trace [Ev b]) ^^^ t ∧ (a, b) ∈ r ∧ ren_tr s r t

/- if -/

axiom ren_tr_decompo_left_if {a : α} {b : β} {s : traceType α} {t : traceType β}
    {r : Set (α × β)} :
    (a, b) ∈ r → ren_tr s r t →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t)

/- iff -/

axiom ren_tr_decompo_left {a : α} {s : traceType α} {r : Set (α × β)} {u : traceType β} :
    ren_tr ((Abs_trace [Ev a]) ^^^ s) r u ↔
      ∃ b t, u = (Abs_trace [Ev b]) ^^^ t ∧ (a, b) ∈ r ∧ ren_tr s r t

/- right -/

/- only if -/

axiom ren_tr_decompo_right_only_if {b : β} {t : traceType β} {r : Set (α × β)} {u : traceType α} :
    ren_tr u r ((Abs_trace [Ev b]) ^^^ t) →
      ∃ a s, u = (Abs_trace [Ev a]) ^^^ s ∧ (a, b) ∈ r ∧ ren_tr s r t

/- if -/

axiom ren_tr_decompo_right_if {a : α} {b : β} {s : traceType α} {t : traceType β}
    {r : Set (α × β)} :
    (a, b) ∈ r → ren_tr s r t →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t)

/- iff -/

axiom ren_tr_decompo_right {b : β} {t : traceType β} {r : Set (α × β)} {u : traceType α} :
    ren_tr u r ((Abs_trace [Ev b]) ^^^ t) ↔
      ∃ a s, u = (Abs_trace [Ev a]) ^^^ s ∧ (a, b) ∈ r ∧ ren_tr s r t

/- Isabelle: lemmas ren_tr_decompo = ren_tr_decompo_left ren_tr_decompo_right -/

/- -------------------*
 |     ren one       |
 *------------------- -/

@[simp]
axiom ren_tr_one {a : α} {b : β} {r : Set (α × β)} :
    (a, b) ∈ r →
      ren_tr (Abs_trace [Ev a] : traceType α) r (Abs_trace [Ev b] : traceType β)

axiom ren_tr_one_decompo_left_only_if {a : α} {r : Set (α × β)} {t : traceType β} :
    ren_tr (Abs_trace [Ev a] : traceType α) r t →
      ∃ b, t = Abs_trace [Ev b] ∧ (a, b) ∈ r

axiom ren_tr_one_decompo_left {a : α} {r : Set (α × β)} {t : traceType β} :
    ren_tr (Abs_trace [Ev a] : traceType α) r t ↔
      ∃ b, t = Abs_trace [Ev b] ∧ (a, b) ∈ r

axiom ren_tr_one_decompo_right_only_if {b : β} {r : Set (α × β)} {s : traceType α} :
    ren_tr s r (Abs_trace [Ev b] : traceType β) →
      ∃ a, s = Abs_trace [Ev a] ∧ (a, b) ∈ r

axiom ren_tr_one_decompo_right {b : β} {r : Set (α × β)} {s : traceType α} :
    ren_tr s r (Abs_trace [Ev b] : traceType β) ↔
      ∃ a, s = Abs_trace [Ev a] ∧ (a, b) ∈ r

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

axiom ren_tr_appt_noTick_lm {s1 s2 : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    s1 [[r]]* t1 → s2 [[r]]* t2 → noTick s1 → noTick t1 → (s1 ^^^ s2) [[r]]* (t1 ^^^ t2)

axiom ren_tr_appt {s1 s2 : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    s1 [[r]]* t1 → s2 [[r]]* t2 → (noTick s1 ∨ noTick t1 ∨ s2 = <> ∨ t2 = <>) →
      (s1 ^^^ s2) [[r]]* (t1 ^^^ t2)

axiom ren_tr_appt_Ev {a : α} {b : β} {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    (a, b) ∈ r → ren_tr s r t →
      ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t)

axiom ren_tr_appt_decompo_left_only_if {s1 s2 : traceType α} {r : Set (α × β)} {t : traceType β} :
    (s1 ^^^ s2) [[r]]* t → (noTick s1 ∨ s2 = <>) →
      ∃ t1 t2, t = t1 ^^^ t2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick t1 ∨ t2 = <>)

axiom ren_tr_appt_decompo_left {s1 s2 : traceType α} {r : Set (α × β)} {t : traceType β} :
    (noTick s1 ∨ s2 = <>) →
      ((s1 ^^^ s2) [[r]]* t ↔
        ∃ t1 t2, t = t1 ^^^ t2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick t1 ∨ t2 = <>))

axiom ren_tr_appt_decompo_right_only_if {s : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    s [[r]]* (t1 ^^^ t2) → (noTick t1 ∨ t2 = <>) →
      ∃ s1 s2, s = s1 ^^^ s2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick s1 ∨ s2 = <>)

axiom ren_tr_appt_decompo_right {s : traceType α} {r : Set (α × β)} {t1 t2 : traceType β} :
    (noTick t1 ∨ t2 = <>) →
      (s [[r]]* (t1 ^^^ t2) ↔
        ∃ s1 s2, s = s1 ^^^ s2 ∧ s1 [[r]]* t1 ∧ s2 [[r]]* t2 ∧ (noTick s1 ∨ s2 = <>))

/- Isabelle: lemmas ren_tr_appt_decompo = ren_tr_appt_decompo_left ren_tr_appt_decompo_right -/

@[simp]
axiom ren_tr_head_decompo {a : α} {b : β} {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    ren_tr ((Abs_trace [Ev a]) ^^^ s) r ((Abs_trace [Ev b]) ^^^ t) ↔
      ((a, b) ∈ r ∧ ren_tr s r t)

@[simp]
axiom ren_tr_last_decompo_Ev {a : α} {b : β} {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    noTick s → noTick t →
      (ren_tr (s ^^^ Abs_trace [Ev a]) r (t ^^^ Abs_trace [Ev b]) ↔
        (ren_tr s r t ∧ (a, b) ∈ r))

@[simp]
axiom ren_tr_last_decompo_Tick {s : traceType α} {r : Set (α × β)} {t : traceType β} :
    noTick s → noTick t →
      (ren_tr (s ^^^ Abs_trace [Tick]) r (t ^^^ Abs_trace [Tick]) ↔ ren_tr s r t)

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

axiom ren_tr_prefix_lm {r : Set (α × β)} {u v : traceType β} {s : traceType α} :
    «prefix» v u → s [[r]]* u → ∃ t, «prefix» t s ∧ t [[r]]* v

axiom ren_tr_prefix {r : Set (α × β)} {u v : traceType β} {s : traceType α} :
    «prefix» v u → s [[r]]* u → ∃ t, «prefix» t s ∧ t [[r]]* v

axiom ren_tr_prefixE {r : Set (α × β)} {u v : traceType β} {s : traceType α} {R : Prop} :
    «prefix» v u → s [[r]]* u →
      (∀ t, «prefix» t s → t [[r]]* v → R) → R

/- *************************************************************
                    inj --> unique
 ************************************************************* -/

axiom ren_tr_inj_unique_ALL {f : α → β} {t : traceType β} {s1 s2 : traceType α} :
    Injective f →
      s1 [[{p | ∃ a, p = (a, f a)}]]* t →
      s2 [[{p | ∃ a, p = (a, f a)}]]* t →
      s1 = s2

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
axiom ren_inv_Int_Tick {r : Set (α × α)} {X : Set (event α)} :
    [[r]]inv (X ∩ {Tick}) = X ∩ {Tick}

@[simp]
axiom ren_inv_diff_Tick {r : Set (α × α)} {X : Set (event α)} :
    [[r]]inv (X \ {Tick}) = [[r]]inv X \ (X ∩ {Tick})

axiom ren_inv_insert_Tick {r : Set (α × α)} {X : Set (event α)} :
    [[r]]inv (insert Tick X) = insert Tick ([[r]]inv X)

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

axiom Renaming1_channel_sett_lm {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <==> g) t →
      sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming1_channel_sett1 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <==> g) t →
      sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming1_channel_sett2 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range f)) →
      ren_tr s (f <==> g) t →
      sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g))

axiom Renaming1_channel_sett3 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (g <==> f) t →
      sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming1_channel_sett4 {x y α : Type _} {f g : x → α} {h : y → α}
    {t s : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett t ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range f)) →
      ren_tr s (g <==> f) t →
      sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g))

/- Isabelle: lemmas Renaming1_channel_sett =
       Renaming1_channel_sett1
       Renaming1_channel_sett2
       Renaming1_channel_sett3
       Renaming1_channel_sett4 -/

axiom Renaming2_channel_sett_lm {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett s ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <== g) t →
      sett t ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming2_channel_sett {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
    Injective f → Injective h → Injective g →
      (∀ x y, f x ≠ g y) →
      (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      sett s ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range h)) →
      ren_tr s (f <== g) t →
      sett t ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

/- Isabelle: lemmas Renaming_channel_sett =
       Renaming1_channel_sett
       Renaming2_channel_sett -/

axiom ren_tr_Renaming_channel_sym_rule {x α : Type _} {f g : x → α}
    {s t : traceType α} :
    Injective f → Injective g → ren_tr s (f <==> g) t → ren_tr t (f <==> g) s

axiom ren_tr_Renaming_channel_sym {x α : Type _} {f g : x → α}
    {s t : traceType α} :
    Injective f → Injective g → (ren_tr s (f <==> g) t ↔ ren_tr t (f <==> g) s)

axiom Renaming1_channel_exist_left {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → ∃ t, ren_tr s (f <==> g) t

axiom Renaming1_channel_exist_right {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → ∃ t, ren_tr t (f <==> g) s

axiom Renaming2_channel_exist_left {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → ∃ t, ren_tr s (f <== g) t

/- Isabelle: lemmas Renaming_channel_exist_left =
       Renaming1_channel_exist_left
       Renaming2_channel_exist_left -/

/- Isabelle: lemmas Renaming_channel_exist_right =
       Renaming1_channel_exist_right -/

axiom Renaming_channel_ren_inv_Int_Tick_eq {x α : Type _} {f g : x → α} {X : Set (event α)} :
    ren_inv (f <==> g) X ∩ {Tick} = X ∩ {Tick}

axiom Renaming_channel_ren_inv_Int_eq {x y α : Type _} {f g : x → α} {h : y → α}
    {X : Set (event α)} :
    (∀ x y, f x ≠ h y) →
      (∀ x y, g x ≠ h y) →
      ren_inv (f <==> g) X ∩ (Ev '' Set.range h) = X ∩ (Ev '' Set.range h)

axiom Renaming_channel_ren_inv_ren_inv_eq {x α : Type _} {f g : x → α} {X : Set (event α)} :
    Injective f → Injective g → ren_inv (f <==> g) (ren_inv (f <==> g) X) = X

axiom Renaming_channel_ren_tr_commut {x y α : Type _}
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
      t2 = t2'

axiom Renaming_channel_ren_tr_commut_rule {x y α : Type _}
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
      t2 = t2'

axiom Renaming1_channel_id {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      sett s ∩ (Ev '' Set.range f) = ∅ →
      sett s ∩ (Ev '' Set.range g) = ∅ →
      ren_tr s (f <==> g) s

axiom Renaming2_channel_id {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      sett s ∩ (Ev '' Set.range f) = ∅ →
      ren_tr s (f <== g) s

/- Isabelle: lemmas Renaming_channel_id =
       Renaming1_channel_id
       Renaming2_channel_id -/

axiom Renaming_channel_id_Un {x α : Type _} {f g : x → α} {s : traceType α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      sett s ∩ (Ev '' (Set.range f ∪ Set.range g)) = ∅ →
      ren_tr s (f <==> g) s
