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

axiom hidex_exists_lm (X : Set α) (s : traceType α) :
    ∃ t, hidex X s t

axiom hidex_exists {X : Set α} {s : traceType α} :
    ∃ t, hidex X s t

axiom hidex_unique_lm (X : Set α) (s t u : traceType α) :
    (hidex X s t ∧ hidex X s u) → t = u

axiom hidex_unique {X : Set α} {s t u : traceType α} :
    hidex X s t → hidex X s u → t = u

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

axiom hidex_to_hide_tr {X : Set α} {s t : traceType α} :
    hidex X s t ↔ t = hide_tr s X

axiom hide_tr_to_hidex {X : Set α} {s t : traceType α} :
    hide_tr s X = t ↔ hidex X s t

axiom hide_tr_to_hidex_sym {X : Set α} {s t : traceType α} :
    t = hide_tr s X ↔ hidex X s t

axiom hide_tr_iff {X : Set α} {s t : traceType α} :
    (hide_tr s X = t) ∧ (t = hide_tr s X) ↔ hidex X s t

/- *************************************************************
                         hide_tr
 ************************************************************* -/

/- *------------------*
 |      intros      |
 *------------------* -/

@[simp] axiom hide_tr_nil {X : Set α} :
    hide_tr (<> : traceType α) X = <>

@[simp] axiom hide_tr_Tick {X : Set α} :
    hide_tr (Abs_trace [Tick] : traceType α) X = Abs_trace [Tick]

axiom hide_tr_in_lm {a : α} {X : Set α} {s t : traceType α} :
    a ∈ X → t = hide_tr s X → hide_tr (Abs_trace [Ev a] ^^^ s) X = t

@[simp] axiom hide_tr_in {a : α} {X : Set α} {s : traceType α} :
    a ∈ X → hide_tr (Abs_trace [Ev a] ^^^ s) X = hide_tr s X

@[simp] axiom hide_tr_in_one {a : α} {X : Set α} :
    a ∈ X → hide_tr (Abs_trace [Ev a] : traceType α) X = <>

axiom hide_tr_notin_lm {a : α} {X : Set α} {s t : traceType α} :
    a ∉ X → t = hide_tr s X →
      hide_tr (Abs_trace [Ev a] ^^^ s) X = Abs_trace [Ev a] ^^^ t

@[simp] axiom hide_tr_notin_appt {a : α} {X : Set α} {s : traceType α} :
    a ∉ X →
      hide_tr (Abs_trace [Ev a] ^^^ s) X = Abs_trace [Ev a] ^^^ hide_tr s X

@[simp] axiom hide_tr_notin {a : α} {X : Set α} :
    a ∉ X → hide_tr (Abs_trace [Ev a] : traceType α) X = Abs_trace [Ev a]

/- *------------------*
 |      elims       |
 *------------------* -/

axiom hide_tr_elims_lm {s t : traceType α} {X : Set α} {P : Prop} :
    hide_tr s X = t →
      (((s = <> ∧ t = <>) → P)) →
      (((s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) → P)) →
      ((∀ a s', (s = Abs_trace [Ev a] ^^^ s' ∧ hide_tr s' X = t ∧ a ∈ X) → P)) →
      ((∀ a s' t', (s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t' ∧
          hide_tr s' X = t' ∧ a ∉ X) → P)) →
      P

axiom hide_tr_elims {s t : traceType α} {X : Set α} {P : Prop} :
    hide_tr s X = t →
      (s = <> → t = <> → P) →
      (s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a s', s = Abs_trace [Ev a] ^^^ s' → hide_tr s' X = t → a ∈ X → P) →
      (∀ a s' t', s = Abs_trace [Ev a] ^^^ s' → t = Abs_trace [Ev a] ^^^ t' →
          hide_tr s' X = t' → a ∉ X → P) →
      P

/- *************************************************************
        a new event is not introduced by HIDE (trace)
 ************************************************************* -/

@[simp] axiom hide_tr_in_event {e : event α} {s : traceType α} {X : Set α} :
    e ∈ sett (hide_tr s X) ↔ e ∉ Ev '' X ∧ e ∈ sett s

@[simp] axiom hide_tr_noTick {s : traceType α} {X : Set α} :
    noTick (hide_tr s X) ↔ noTick s

/- *************************************************************
                  appended traces in hide
 ************************************************************* -/

axiom hide_tr_appt_noTick_lm {X : Set α} {s t : traceType α} :
    noTick s → hide_tr (s ^^^ t) X = hide_tr s X ^^^ hide_tr t X

@[simp] axiom hide_tr_appt {X : Set α} {s t : traceType α} :
    noTick s ∨ t = <> → hide_tr (s ^^^ t) X = hide_tr s X ^^^ hide_tr t X

/- *************************************************************
                 decompose traces in hide
 ************************************************************* -/

axiom hide_tr_decompo_only_if_lm {X : Set α} {u s t : traceType α} :
    (noTick s ∨ t = <>) ∧ hide_tr u X = s ^^^ t →
      ∃ s' t', (noTick s' ∨ t' = <>) ∧
        u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X

axiom hide_tr_decompo_only_if {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      hide_tr u X = s ^^^ t →
        ∃ s' t', (noTick s' ∨ t' = <>) ∧
          u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X

axiom hide_tr_decompo_if {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      (∃ s' t', (noTick s' ∨ t' = <>) ∧
        u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X) →
        hide_tr u X = s ^^^ t

axiom hide_tr_decompo {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      (hide_tr u X = s ^^^ t ↔
        ∃ s' t', (noTick s' ∨ t' = <>) ∧
          u = s' ^^^ t' ∧ s = hide_tr s' X ∧ t = hide_tr t' X)

/- *************************************************************
                  hide trace prefix_closed
 ************************************************************* -/

axiom hide_tr_prefix_only_if_lm {X : Set α} {s u : traceType α} :
    «prefix» u (hide_tr s X) → ∃ t, u = hide_tr t X ∧ «prefix» t s

axiom hide_tr_prefix_only_if {X : Set α} {s u : traceType α} :
    «prefix» u (hide_tr s X) → ∃ t, u = hide_tr t X ∧ «prefix» t s

axiom hide_tr_prefix_if {X : Set α} {s t : traceType α} :
    «prefix» t s → «prefix» (hide_tr t X) (hide_tr s X)

axiom hide_tr_prefix {X : Set α} {s u : traceType α} :
    «prefix» u (hide_tr s X) ↔ ∃ t, u = hide_tr t X ∧ «prefix» t s

/- *************************************************************
                  hide + alpha lemma
 ************************************************************* -/

axiom hide_tr_nilt_sett_only_if_lm {X : Set α} {s : traceType α} :
    hide_tr s X = <> → sett s ⊆ Ev '' X

axiom hide_tr_nilt_sett_only_if {X : Set α} {s : traceType α} :
    hide_tr s X = <> → sett s ⊆ Ev '' X

axiom hide_tr_nilt_sett_if_lm {X : Set α} {s : traceType α} :
    sett s ⊆ Ev '' X → hide_tr s X = <>

axiom hide_tr_nilt_sett_if {X : Set α} {s : traceType α} :
    sett s ⊆ Ev '' X → hide_tr s X = <>

axiom hide_tr_nilt_sett {X : Set α} {s : traceType α} :
    (hide_tr s X = <>) ↔ sett s ⊆ Ev '' X

axiom hide_tr_sett_subseteq_sett {X Y : Set α} {u : traceType α} :
    X ⊆ Y → sett (hide_tr u Y) ⊆ sett (hide_tr u X)

axiom hide_tr_Tick_sett_only_if_lm {X : Set α} {s : traceType α} :
    hide_tr s X = Abs_trace [Tick] →
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ sett s' ⊆ Ev '' X ∧ noTick s'

axiom hide_tr_Tick_sett_only_if {X : Set α} {s : traceType α} :
    hide_tr s X = Abs_trace [Tick] →
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ sett s' ⊆ Ev '' X ∧ noTick s'

axiom hide_tr_Tick_sett_if {X : Set α} {s : traceType α} :
    sett s ⊆ Ev '' X → hide_tr s X = <>

axiom hide_tr_Tick_sett {X : Set α} {s : traceType α} :
    (hide_tr s X = Abs_trace [Tick]) ↔
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ sett s' ⊆ Ev '' X ∧ noTick s'

/- *--------------------------*
 |       commutativity      |
 *--------------------------* -/

axiom hide_tr_commute {X Y : Set α} {u : traceType α} :
    hide_tr (hide_tr u X) Y = hide_tr (hide_tr u Y) X

axiom hide_tr_of_hide_tr_subset1 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → hide_tr (hide_tr u X) Y = hide_tr u Y

axiom hide_tr_of_hide_tr_subset2 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → hide_tr (hide_tr u Y) X = hide_tr u Y

axiom hide_tr_of_hide_tr_subset {X Y : Set α} {u : traceType α} :
    X ⊆ Y →
      hide_tr (hide_tr u X) Y = hide_tr u Y ∧
        hide_tr (hide_tr u Y) X = hide_tr u Y

axiom hide_tr_UNIV_lm {u : traceType α} :
    hide_tr u (Set.univ : Set α) = <> ∨
      hide_tr u (Set.univ : Set α) = Abs_trace [Tick]

axiom hide_tr_UNIV {u : traceType α} :
    hide_tr u (Set.univ : Set α) = <> ∨
      hide_tr u (Set.univ : Set α) = Abs_trace [Tick]

/- *======================================================*
 |                                                      |
 |                        rest-tr                       |
 |                                                      |
 *======================================================* -/

/- *------------------*
 |      intros      |
 *------------------* -/

@[simp] axiom rest_tr_nil {X : Set α} :
    rest_tr (<> : traceType α) X = <>

@[simp] axiom rest_tr_Tick {X : Set α} :
    rest_tr (Abs_trace [Tick] : traceType α) X = Abs_trace [Tick]

@[simp] axiom rest_tr_notin {a : α} {X : Set α} {s : traceType α} :
    a ∉ X → rest_tr (Abs_trace [Ev a] ^^^ s) X = rest_tr s X

@[simp] axiom rest_tr_notin_one {a : α} {X : Set α} :
    a ∉ X → rest_tr (Abs_trace [Ev a] : traceType α) X = <>

@[simp] axiom rest_tr_in_appt {a : α} {X : Set α} {s : traceType α} :
    a ∈ X →
      rest_tr (Abs_trace [Ev a] ^^^ s) X = Abs_trace [Ev a] ^^^ rest_tr s X

@[simp] axiom rest_tr_in {a : α} {X : Set α} :
    a ∈ X → rest_tr (Abs_trace [Ev a] : traceType α) X = Abs_trace [Ev a]

/- *------------------*
 |      elims       |
 *------------------* -/

axiom rest_tr_elims {s t : traceType α} {X : Set α} {P : Prop} :
    rest_tr s X = t →
      (s = <> → t = <> → P) →
      (s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a s', s = Abs_trace [Ev a] ^^^ s' → rest_tr s' X = t → a ∉ X → P) →
      (∀ a s' t', s = Abs_trace [Ev a] ^^^ s' → t = Abs_trace [Ev a] ^^^ t' →
          rest_tr s' X = t' → a ∈ X → P) →
      P

/- *************************************************************
        a new event is not introduced by rest (trace)
 ************************************************************* -/

@[simp] axiom rest_tr_in_event {e : event α} {s : traceType α} {X : Set α} :
    e ∈ sett (rest_tr s X) ↔ (e ∈ Ev '' X ∨ e = Tick) ∧ e ∈ sett s

@[simp] axiom rest_tr_subset_event {s : traceType α} {X : Set α} :
    sett (rest_tr s X) ⊆ Set.insert Tick (Ev '' X)

@[simp] axiom rest_tr_noTick {s : traceType α} {X : Set α} :
    noTick (rest_tr s X) ↔ noTick s

/- *************************************************************
                  appended traces in rest
 ************************************************************* -/

@[simp] axiom rest_tr_appt {X : Set α} {s t : traceType α} :
    noTick s ∨ t = <> → rest_tr (s ^^^ t) X = rest_tr s X ^^^ rest_tr t X

/- *************************************************************
                 decompose traces in rest
 ************************************************************* -/

axiom rest_tr_decompo {X : Set α} {u s t : traceType α} :
    noTick s ∨ t = <> →
      (rest_tr u X = s ^^^ t ↔
        ∃ s' t', (noTick s' ∨ t' = <>) ∧
          u = s' ^^^ t' ∧ s = rest_tr s' X ∧ t = rest_tr t' X)

/- *************************************************************
                  rest trace prefix_closed
 ************************************************************* -/

axiom rest_tr_prefix {X : Set α} {s u : traceType α} :
    «prefix» u (rest_tr s X) ↔ ∃ t, u = rest_tr t X ∧ «prefix» t s

/- *************************************************************
                  rest + alpha lemma
 ************************************************************* -/

axiom rest_tr_nilt_sett {X : Set α} {s : traceType α} :
    (rest_tr s X = <>) ↔ sett s ∩ Set.insert Tick (Ev '' X) = ∅

axiom rest_tr_sett_subseteq_sett {X Y : Set α} {u : traceType α} :
    X ⊆ Y → sett (rest_tr u X) ⊆ sett (rest_tr u Y)

axiom rest_tr_Tick_sett {X : Set α} {s : traceType α} :
    (rest_tr s X = Abs_trace [Tick]) ↔
      ∃ s', s = s' ^^^ Abs_trace [Tick] ∧ (sett s' ∩ Ev '' X = ∅) ∧ noTick s'

/- *--------------------------*
 |       commutativity      |
 *--------------------------* -/

axiom rest_tr_commute {X Y : Set α} {u : traceType α} :
    rest_tr (rest_tr u X) Y = rest_tr (rest_tr u Y) X

axiom rest_tr_of_rest_tr_subset1 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → rest_tr (rest_tr u X) Y = rest_tr u X

axiom rest_tr_of_rest_tr_subset2 {X Y : Set α} {u : traceType α} :
    X ⊆ Y → rest_tr (rest_tr u Y) X = rest_tr u X

axiom rest_tr_of_rest_tr_subset {X Y : Set α} {u : traceType α} :
    X ⊆ Y →
      rest_tr (rest_tr u X) Y = rest_tr u X ∧
        rest_tr (rest_tr u Y) X = rest_tr u X

axiom rest_tr_empty {u : traceType α} :
    rest_tr u (∅ : Set α) = <> ∨ rest_tr u (∅ : Set α) = Abs_trace [Tick]

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

axiom Ev_rest_tr_decompo {X : Set α} {s : traceType α} {a : α} :
    a ∈ X ∧ rest_tr s X = (Abs_trace [Ev a] : traceType α) →
      ∃ s1 s2, s = s1 ^^^ Abs_trace [Ev a] ^^^ s2 ∧
        noTick s1 ∧ noTick s2 ∧ rest_tr s1 X = <> ∧ rest_tr s2 X = <>

axiom hide_tr_rest_tr_sett {X Y : Set α} {s : traceType α} :
    sett s ⊆ Set.insert Tick (Ev '' Y) →
      hide_tr s X = rest_tr s (Y \ X)

axiom hide_tr_id {X Y : Set α} {s : traceType α} :
    sett s ⊆ Set.insert Tick (Ev '' Y) ∧ X ∩ Y = ∅ →
      hide_tr s X = s

/- --------------------------------------------------- *
                   semantics for pipe
 * --------------------------------------------------- -/

axiom hide_tr_of_rest_tr_empty1 {X Y : Set α} {s : traceType α} :
    X ∩ Y = ∅ → rest_tr (hide_tr s X) Y = rest_tr s Y

axiom hide_tr_of_rest_tr_empty2 {X Y : Set α} {s : traceType α} :
    X ∩ Y = ∅ → hide_tr (rest_tr s X) Y = rest_tr s X

axiom noTick_hide_tr_of_rest_tr_empty {X Y : Set α} {s : traceType α} :
    noTick s → X ⊆ Y → hide_tr (rest_tr s X) Y = <>

axiom hide_tr_nohiden {X : Set α} {s : traceType α} :
    sett s ∩ Ev '' X = ∅ → hide_tr s X = s
