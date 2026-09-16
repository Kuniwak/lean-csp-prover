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
/-                                                                     -/
/-                  disj_not1: (~ P | Q) = (P --> Q)                   -/

/- *****************************************************************

         1. s |[X]|list t  : lists  --> list set
         2. s |[X]|tr t   : traces --> trace set
         3.
         4.

 ***************************************************************** -/

/- Isabelle 2005
consts
  parx :: "'a set => ('a trace * 'a trace * 'a trace) set"

inductive "parx X"
intros
parx_nil_nil:
  "(<>, <>, <>) : parx X"

parx_Tick_Tick:
  "(<Tick>, <Tick>, <Tick>) : parx X"

parx_Ev_nil:
  "[| (u, s, <>) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <>) : parx X"

parx_nil_Ev:
  "[| (u, <>, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <>, <Ev a> ^^^ t) : parx X"

parx_Ev_sync:
  "[| (u, s, t) : parx X ; a : X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, <Ev a> ^^^ t) : parx X"

parx_Ev_left:
  "[| (u, s, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, <Ev a> ^^^ s, t) : parx X"

parx_Ev_right:
  "[| (u, s, t) : parx X ; a ~: X |]
   ==> (<Ev a> ^^^ u, s, <Ev a> ^^^ t) : parx X"
-/

inductive parx (X : Set α) : traceType α → traceType α → traceType α → Prop where
  | parx_nil_nil :
      parx X <> <> <>
  | parx_Tick_Tick :
      parx X (Abs_trace [Tick]) (Abs_trace [Tick]) (Abs_trace [Tick])
  | parx_Ev_nil {u s : traceType α} {a : α} :
      parx X u s <> → a ∉ X →
        parx X (Abs_trace [Ev a] ^^^ u) (Abs_trace [Ev a] ^^^ s) <>
  | parx_nil_Ev {u t : traceType α} {a : α} :
      parx X u <> t → a ∉ X →
        parx X (Abs_trace [Ev a] ^^^ u) <> (Abs_trace [Ev a] ^^^ t)
  | parx_Ev_sync {u s t : traceType α} {a : α} :
      parx X u s t → a ∈ X →
        parx X (Abs_trace [Ev a] ^^^ u) (Abs_trace [Ev a] ^^^ s) (Abs_trace [Ev a] ^^^ t)
  | parx_Ev_left {u s t : traceType α} {a : α} :
      parx X u s t → a ∉ X →
        parx X (Abs_trace [Ev a] ^^^ u) (Abs_trace [Ev a] ^^^ s) t
  | parx_Ev_right {u s t : traceType α} {a : α} :
      parx X u s t → a ∉ X →
        parx X (Abs_trace [Ev a] ^^^ u) s (Abs_trace [Ev a] ^^^ t)

def par_tr (s : traceType α) (X : Set α) (t : traceType α) : Set (traceType α) :=
  {u | parx X u s t}

notation:76 s:76 " |[" X "]|tr " t:77 => par_tr s X t

theorem par_tr_def {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t ↔ parx X u s t :=
  Iff.rfl

theorem par_tr_defE {u s t : traceType α} {X : Set α} {R : Prop} :
    u ∈ s |[X]|tr t → (parx X u s t → R) → R := by
  intro hu hR
  exact hR ((par_tr_def.mp hu))

/- *************************************************************
                 par_tr intros and elims
 ************************************************************* -/

/- -------------------*
 |      intros       |
 *------------------- -/

theorem par_tr_nil_nil {X : Set α} :
    (<> : traceType α) ∈ ((<> : traceType α) |[X]|tr (<> : traceType α)) := by
  exact parx.parx_nil_nil

theorem par_tr_Tick_Tick {X : Set α} :
    (Abs_trace [Tick] : traceType α) ∈
      ((Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Tick] : traceType α)) := by
  exact parx.parx_Tick_Tick

theorem par_tr_Ev_nil {u s : traceType α} {X : Set α} {a : α} :
    u ∈ s |[X]|tr (<> : traceType α) → a ∉ X →
      Abs_trace [Ev a] ^^^ u ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr (<> : traceType α) := by
  intro hu ha
  exact parx.parx_Ev_nil hu ha

theorem par_tr_nil_Ev {u t : traceType α} {X : Set α} {a : α} :
    u ∈ (<> : traceType α) |[X]|tr t → a ∉ X →
      Abs_trace [Ev a] ^^^ u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t) := by
  intro hu ha
  exact parx.parx_nil_Ev hu ha

theorem par_tr_Ev_sync {u s t : traceType α} {X : Set α} {a : α} :
    u ∈ s |[X]|tr t → a ∈ X →
      Abs_trace [Ev a] ^^^ u ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr (Abs_trace [Ev a] ^^^ t) := by
  intro hu ha
  exact parx.parx_Ev_sync hu ha

theorem par_tr_Ev_left {u s t : traceType α} {X : Set α} {a : α} :
    u ∈ s |[X]|tr t → a ∉ X →
      Abs_trace [Ev a] ^^^ u ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr t := by
  intro hu ha
  exact parx.parx_Ev_left hu ha

theorem par_tr_Ev_right {u s t : traceType α} {X : Set α} {a : α} :
    u ∈ s |[X]|tr t → a ∉ X →
      Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr (Abs_trace [Ev a] ^^^ t) := by
  intro hu ha
  exact parx.parx_Ev_right hu ha

/- Isabelle: lemmas par_tr_intros =
       par_tr_nil_nil
       par_tr_Tick_Tick
       par_tr_Ev_nil
       par_tr_nil_Ev
       par_tr_Ev_sync
       par_tr_Ev_left
       par_tr_Ev_right -/

/- -------------------*
 |       elims       |
 *------------------- -/

theorem par_tr_elims_lm {u s t : traceType α} {X : Set α} {P : Prop} :
    u ∈ s |[X]|tr t →
      ((u = <> ∧ s = <> ∧ t = <>) → P) →
      ((u = Abs_trace [Tick] ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) → P) →
      (∀ a s' u',
        (u = Abs_trace [Ev a] ^^^ u' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = <> ∧
          u' ∈ s' |[X]|tr (<> : traceType α) ∧ a ∉ X) → P) →
      (∀ a t' u',
        (u = Abs_trace [Ev a] ^^^ u' ∧ s = <> ∧ t = Abs_trace [Ev a] ^^^ t' ∧
          u' ∈ (<> : traceType α) |[X]|tr t' ∧ a ∉ X) → P) →
      (∀ a s' t' u',
        (u = Abs_trace [Ev a] ^^^ u' ∧ s = Abs_trace [Ev a] ^^^ s' ∧
          t = Abs_trace [Ev a] ^^^ t' ∧ u' ∈ s' |[X]|tr t' ∧ a ∈ X) → P) →
      (∀ a s' u',
        (u = Abs_trace [Ev a] ^^^ u' ∧ s = Abs_trace [Ev a] ^^^ s' ∧
          u' ∈ s' |[X]|tr t ∧ a ∉ X) → P) →
      (∀ a t' u',
        (u = Abs_trace [Ev a] ^^^ u' ∧ t = Abs_trace [Ev a] ^^^ t' ∧
          u' ∈ s |[X]|tr t' ∧ a ∉ X) → P) →
      P := by
  intro hu h1 h2 h3 h4 h5 h6 h7
  cases hu with
  | parx_nil_nil => exact h1 ⟨rfl, rfl, rfl⟩
  | parx_Tick_Tick => exact h2 ⟨rfl, rfl, rfl⟩
  | parx_Ev_nil hu' ha => exact h3 _ _ _ ⟨rfl, rfl, rfl, hu', ha⟩
  | parx_nil_Ev hu' ha => exact h4 _ _ _ ⟨rfl, rfl, rfl, hu', ha⟩
  | parx_Ev_sync hu' ha => exact h5 _ _ _ _ ⟨rfl, rfl, rfl, hu', ha⟩
  | parx_Ev_left hu' ha => exact h6 _ _ _ ⟨rfl, rfl, hu', ha⟩
  | parx_Ev_right hu' ha => exact h7 _ _ _ ⟨rfl, rfl, hu', ha⟩

theorem par_tr_elims {u s t : traceType α} {X : Set α} {P : Prop} :
    u ∈ s |[X]|tr t →
      (u = <> → s = <> → t = <> → P) →
      (u = Abs_trace [Tick] → s = Abs_trace [Tick] → t = Abs_trace [Tick] → P) →
      (∀ a s' u',
        u = Abs_trace [Ev a] ^^^ u' → s = Abs_trace [Ev a] ^^^ s' → t = <> →
          u' ∈ s' |[X]|tr (<> : traceType α) → a ∉ X → P) →
      (∀ a t' u',
        u = Abs_trace [Ev a] ^^^ u' → s = <> → t = Abs_trace [Ev a] ^^^ t' →
          u' ∈ (<> : traceType α) |[X]|tr t' → a ∉ X → P) →
      (∀ a s' t' u',
        u = Abs_trace [Ev a] ^^^ u' → s = Abs_trace [Ev a] ^^^ s' →
          t = Abs_trace [Ev a] ^^^ t' → u' ∈ s' |[X]|tr t' → a ∈ X → P) →
      (∀ a s' u',
        u = Abs_trace [Ev a] ^^^ u' → s = Abs_trace [Ev a] ^^^ s' →
          u' ∈ s' |[X]|tr t → a ∉ X → P) →
      (∀ a t' u',
        u = Abs_trace [Ev a] ^^^ u' → t = Abs_trace [Ev a] ^^^ t' →
          u' ∈ s |[X]|tr t' → a ∉ X → P) →
      P := by
  intro hu h1 h2 h3 h4 h5 h6 h7
  cases hu with
  | parx_nil_nil => exact h1 rfl rfl rfl
  | parx_Tick_Tick => exact h2 rfl rfl rfl
  | parx_Ev_nil hu' ha => exact h3 _ _ _ rfl rfl rfl hu' ha
  | parx_nil_Ev hu' ha => exact h4 _ _ _ rfl rfl rfl hu' ha
  | parx_Ev_sync hu' ha => exact h5 _ _ _ _ rfl rfl rfl hu' ha
  | parx_Ev_left hu' ha => exact h6 _ _ _ rfl rfl hu' ha
  | parx_Ev_right hu' ha => exact h7 _ _ _ rfl rfl hu' ha

/- *************************************************************
                 par_tr decomposition
 ************************************************************* -/

/- -------------------*
 |     par nil       |
 *------------------- -/

/- (*** par_tr ***) -/

theorem par_tr_nil_only_if {s t : traceType α} {X : Set α} :
    (<> : traceType α) ∈ s |[X]|tr t → s = <> ∧ t = <> := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (repeat intro _) <;> simp_all

/- (*** iff ***) -/

@[simp] theorem par_tr_nil1 {s t : traceType α} {X : Set α} :
    ((<> : traceType α) ∈ s |[X]|tr t) ↔ (s = <> ∧ t = <>) := by
  constructor
  · exact par_tr_nil_only_if
  · rintro ⟨rfl, rfl⟩
    exact par_tr_nil_nil

@[simp] theorem par_tr_nil2 {u : traceType α} {X : Set α} :
    u ∈ ((<> : traceType α) |[X]|tr (<> : traceType α)) ↔ u = <> := by
  constructor
  · intro h
    refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (repeat intro _) <;> simp_all
  · rintro rfl
    exact par_tr_nil_nil

/- -------------------*
 |     par Tick      |
 *------------------- -/

/- (*** only if ***) -/

theorem par_tr_Tick_only_if {s t : traceType α} {X : Set α} :
    (Abs_trace [Tick] : traceType α) ∈ s |[X]|tr t →
      s = Abs_trace [Tick] ∧ t = Abs_trace [Tick] := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (repeat intro _) <;> simp_all

/- (*** iff ***) -/

@[simp] theorem par_tr_Tick1 {s t : traceType α} {X : Set α} :
    ((Abs_trace [Tick] : traceType α) ∈ s |[X]|tr t) ↔
      (s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) := by
  constructor
  · exact par_tr_Tick_only_if
  · rintro ⟨rfl, rfl⟩
    exact par_tr_Tick_Tick

@[simp] theorem par_tr_Tick2 {u : traceType α} {X : Set α} :
    u ∈ ((Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Tick] : traceType α)) ↔
      u = Abs_trace [Tick] := by
  constructor
  · intro h
    refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (repeat intro _) <;> simp_all
  · rintro rfl
    exact par_tr_Tick_Tick

/- -----------------*
 |     par Ev      |
 *----------------- -/

/- (*** only if ***) -/

theorem par_tr_Ev_only_if {a : α} {s t : traceType α} {X : Set α} :
    (Abs_trace [Ev a] : traceType α) ∈ s |[X]|tr t →
      ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
       (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
       (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a])) := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (repeat intro _) <;> simp_all

/- (*** if ***) -/

theorem par_tr_Ev_if {a : α} {s t : traceType α} {X : Set α} :
    ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
     (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
     (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a])) →
      (Abs_trace [Ev a] : traceType α) ∈ s |[X]|tr t := by
  rintro (⟨ha, rfl, rfl⟩ | ⟨ha, rfl, rfl⟩ | ⟨ha, rfl, rfl⟩)
  · simpa using par_tr_Ev_sync (u := <>) (s := <>) (t := <>) (X := X) (a := a) par_tr_nil_nil ha
  · simpa using par_tr_Ev_nil (u := <>) (s := <>) (X := X) (a := a) par_tr_nil_nil ha
  · simpa using par_tr_nil_Ev (u := <>) (t := <>) (X := X) (a := a) par_tr_nil_nil ha

theorem par_tr_Ev {a : α} {s t : traceType α} {X : Set α} :
    ((Abs_trace [Ev a] : traceType α) ∈ s |[X]|tr t) ↔
      ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
       (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
       (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a])) := by
  exact ⟨par_tr_Ev_only_if, par_tr_Ev_if⟩

/- --------------------------------------------*
 |                 par one                    |
 *-------------------------------------------- -/

theorem par_tr_one {e : event α} {s t : traceType α} {X : Set α} :
    ((Abs_trace [e] : traceType α) ∈ s |[X]|tr t) ↔
      ((e = Tick ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) ∨
       ∃ a, e = Ev a ∧
         ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
          (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
          (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a]))) := by
  constructor
  · intro h
    rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
    · exact Or.inl ⟨rfl, par_tr_Tick_only_if h⟩
    · exact Or.inr ⟨a, rfl, par_tr_Ev_only_if h⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨a, rfl, hcase⟩)
    · exact par_tr_Tick_Tick
    · exact par_tr_Ev_if hcase

/- --------------------------------------------*
 |                par head                    |
 *-------------------------------------------- -/

/- (*** only if ***) -/

theorem par_tr_head_only_if {a : α} {u s t : traceType α} {X : Set α} :
    Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t →
      (a ∈ X ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
      (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
      (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t') := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro h1 _ _
    simp at h1
  · intro h1 _ _
    simp at h1
  · intro b s' u' h1 h2 h3 h4 h5
    obtain ⟨hab, huu⟩ := appt_same_head_only_if h1
    subst huu
    subst hab
    exact Or.inr (Or.inl ⟨h5, s', by rw [h3]; exact h4, h2⟩)
  · intro b t' u' h1 h2 h3 h4 h5
    obtain ⟨hab, huu⟩ := appt_same_head_only_if h1
    subst huu
    subst hab
    exact Or.inr (Or.inr ⟨h5, t', by rw [h2]; exact h4, h3⟩)
  · intro b s' t' u' h1 h2 h3 h4 h5
    obtain ⟨hab, huu⟩ := appt_same_head_only_if h1
    subst huu
    subst hab
    exact Or.inl ⟨h5, s', t', h4, h2, h3⟩
  · intro b s' u' h1 h2 h3 h4
    obtain ⟨hab, huu⟩ := appt_same_head_only_if h1
    subst huu
    subst hab
    exact Or.inr (Or.inl ⟨h4, s', h3, h2⟩)
  · intro b t' u' h1 h2 h3 h4
    obtain ⟨hab, huu⟩ := appt_same_head_only_if h1
    subst huu
    subst hab
    exact Or.inr (Or.inr ⟨h4, t', h3, h2⟩)

/- (*** if ***) -/

theorem par_tr_head_if {a : α} {u s t : traceType α} {X : Set α} :
    ((a ∈ X ∧
        ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
     (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
     (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t')) →
      Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t := by
  rintro (⟨ha, s', t', hu, rfl, rfl⟩ | ⟨ha, s', hu, rfl⟩ | ⟨ha, t', hu, rfl⟩)
  · exact par_tr_Ev_sync hu ha
  · exact par_tr_Ev_left hu ha
  · exact par_tr_Ev_right hu ha

/- (*** iff ***) -/

theorem par_tr_head {a : α} {u s t : traceType α} {X : Set α} :
    (Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t) ↔
      ((a ∈ X ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
       (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
       (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t')) := by
  exact ⟨par_tr_head_only_if, par_tr_head_if⟩

/- erule -/

theorem par_tr_head_ifE {a : α} {u s t : traceType α} {X : Set α} {R : Prop} :
    Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t →
      (((a ∈ X ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
        (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
        (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t')) → R) →
      R := by
  intro hu hR
  exact hR ((par_tr_head.mp hu))

/- head Ev Ev -/

theorem par_tr_head_Ev_Ev {a b : α} {u s t : traceType α} {X : Set α} :
    (u ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr (Abs_trace [Ev b] ^^^ t)) ↔
      ∃ c v, u = Abs_trace [Ev c] ^^^ v ∧
        ((c ∈ X ∧ v ∈ s |[X]|tr t ∧ a = c ∧ b = c) ∨
         (c ∉ X ∧ v ∈ s |[X]|tr (Abs_trace [Ev b] ^^^ t) ∧ a = c) ∨
         (c ∉ X ∧ v ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr t ∧ b = c)) := by
  constructor
  · intro h
    refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro _ h2 _
      simp at h2
    · intro _ h2 _
      simp at h2
    · intro c s' u' _ _ h3 _ _
      simp at h3
    · intro c t' u' _ h2 _ _ _
      simp at h2
    · intro c s' t' u' h1 h2 h3 h4 h5
      obtain ⟨hac, hss⟩ := appt_same_head_only_if h2
      obtain ⟨hbc, htt⟩ := appt_same_head_only_if h3
      subst hss
      subst htt
      exact ⟨c, u', h1, Or.inl ⟨h5, h4, hac, hbc⟩⟩
    · intro c s' u' h1 h2 h3 h4
      obtain ⟨hac, hss⟩ := appt_same_head_only_if h2
      subst hss
      exact ⟨c, u', h1, Or.inr (Or.inl ⟨h4, h3, hac⟩)⟩
    · intro c t' u' h1 h2 h3 h4
      obtain ⟨hbc, htt⟩ := appt_same_head_only_if h2
      subst htt
      exact ⟨c, u', h1, Or.inr (Or.inr ⟨h4, h3, hbc⟩)⟩
  · rintro ⟨c, v, rfl, (⟨hc, hv, rfl, rfl⟩ | ⟨hc, hv, rfl⟩ | ⟨hc, hv, rfl⟩)⟩
    · exact par_tr_Ev_sync hv hc
    · exact par_tr_Ev_left hv hc
    · exact par_tr_Ev_right hv hc

/- step -/

theorem par_tr_step {u s t : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr t) ↔
      ((u = <> ∧ s = <> ∧ t = <>) ∨
       (u = Abs_trace [Tick] ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) ∨
       ∃ a v, u = Abs_trace [Ev a] ^^^ v ∧
         ((a ∈ X ∧
             ∃ s' t',
               v ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧
                 t = Abs_trace [Ev a] ^^^ t') ∨
          (a ∉ X ∧ ∃ s', v ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
          (a ∉ X ∧ ∃ t', v ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t'))) := by
  constructor
  · intro h
    rcases trace_nil_or_Tick_or_Ev u with rfl | rfl | ⟨a, v, rfl⟩
    · exact Or.inl ⟨rfl, par_tr_nil_only_if h⟩
    · exact Or.inr (Or.inl ⟨rfl, par_tr_Tick_only_if h⟩)
    · exact Or.inr (Or.inr ⟨a, v, rfl, par_tr_head_only_if h⟩)
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨a, v, rfl, hcase⟩)
    · exact par_tr_nil_nil
    · exact par_tr_Tick_Tick
    · exact par_tr_head_if hcase

theorem par_tr_stepI {u s t : traceType α} {X : Set α} :
    ((u = <> ∧ s = <> ∧ t = <>) ∨
     (u = Abs_trace [Tick] ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) ∨
     ∃ a v, u = Abs_trace [Ev a] ^^^ v ∧
       ((a ∈ X ∧
           ∃ s' t', v ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
        (a ∉ X ∧ ∃ s', v ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
        (a ∉ X ∧ ∃ t', v ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t'))) →
      u ∈ s |[X]|tr t := by
  intro h
  exact (par_tr_step.mpr h)

theorem par_tr_stepE {u s t : traceType α} {X : Set α} {R : Prop} :
    u ∈ s |[X]|tr t →
      (((u = <> ∧ s = <> ∧ t = <>) ∨
        (u = Abs_trace [Tick] ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) ∨
        ∃ a v, u = Abs_trace [Ev a] ^^^ v ∧
          ((a ∈ X ∧
              ∃ s' t',
                v ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧
                  t = Abs_trace [Ev a] ^^^ t') ∨
           (a ∉ X ∧ ∃ s', v ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
           (a ∉ X ∧ ∃ t', v ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t'))) → R) →
      R := by
  intro hu hR
  exact hR ((par_tr_step.mp hu))

/- --------------------------------------------*
 |                par last                    |
 *-------------------------------------------- -/

/- (*** auxiliary induction lemmas (Lean port helpers) ***) -/

theorem par_tr_noTick_ind {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → noTick s → noTick t → noTick u := by
  intro h
  induction h with
  | parx_nil_nil => intro _ _; exact noTick_nil
  | parx_Tick_Tick => intro hs _; exact absurd hs not_noTick_Tick
  | parx_Ev_nil hpar ha ih =>
      intro hs ht
      exact decompo_appt_noTick_if (noTick_Ev _)
        (ih (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hs).2 ht)
  | parx_nil_Ev hpar ha ih =>
      intro hs ht
      exact decompo_appt_noTick_if (noTick_Ev _)
        (ih hs (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) ht).2)
  | parx_Ev_sync hpar ha ih =>
      intro hs ht
      exact decompo_appt_noTick_if (noTick_Ev _)
        (ih (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hs).2
            (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) ht).2)
  | parx_Ev_left hpar ha ih =>
      intro hs ht
      exact decompo_appt_noTick_if (noTick_Ev _)
        (ih (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hs).2 ht)
  | parx_Ev_right hpar ha ih =>
      intro hs ht
      exact decompo_appt_noTick_if (noTick_Ev _)
        (ih hs (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) ht).2)

theorem par_tr_last_only_if_ind {w s t : traceType α} {X : Set α} :
    w ∈ s |[X]|tr t →
      ∀ (v : traceType α) (e : event α), w = v ^^^ Abs_trace [e] → noTick v →
        (((e ∈ Ev '' X ∨ e = Tick) ∧
            ∃ s' t', v ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
              noTick s' ∧ noTick t') ∨
         (e ∉ Ev '' X ∧ e ≠ Tick ∧
            ∃ s', v ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
         (e ∉ Ev '' X ∧ e ≠ Tick ∧
            ∃ t', v ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t')) := by
  intro h
  induction h with
  | parx_nil_nil =>
      intro v e hveq hv
      rw [appt_nil_sym hv] at hveq
      simp at hveq
  | parx_Tick_Tick =>
      intro v e hveq hv
      rcases (appt_decompo_one_sym (Or.inl hv)).mp hveq with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
      · simp at hv2
      · subst hv1
        rw [Event_eq] at hv2
        subst hv2
        exact Or.inl ⟨Or.inr rfl, <>, <>, par_tr_nil_nil, by simp, by simp,
          noTick_nil, noTick_nil⟩
  | parx_Ev_nil hpar ha ih =>
      rename_i u1 s1 a
      intro v e hveq hv
      rcases trace_nil_or_Tick_or_Ev v with rfl | rfl | ⟨b, v1, rfl⟩
      · rw [appt_nil_left] at hveq
        rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp hveq with ⟨he, hu1⟩ | ⟨he, _⟩
        · rw [Event_eq] at he
          subst he
          subst hu1
          have hs1 : s1 = <> := (par_tr_nil_only_if hpar).1
          subst hs1
          exact Or.inr (Or.inl ⟨by simp [ha], by simp, <>, par_tr_nil_nil, by simp,
            noTick_nil, noTick_nil⟩)
        · simp at he
      · exact absurd hv not_noTick_Tick
      · have hv1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hv).2
        rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hv1)] at hveq
        obtain ⟨hab, hu1⟩ := appt_same_head_only_if hveq
        subst hab
        rcases ih v1 e hu1 hv1 with
            ⟨hE, s2, t2, hmem, hs2, ht2, hns2, hnt2⟩ |
            ⟨hE1, hE2, s2, hmem, hs2, hns2, hnt⟩ |
            ⟨hE1, hE2, t2, hmem, ht2, hns, hnt2⟩
        · have h0 : t2 ^^^ Abs_trace [e] = <> := ht2.symm
          simp [hnt2] at h0
        · refine Or.inr (Or.inl ⟨hE1, hE2, Abs_trace [Ev _] ^^^ s2, par_tr_Ev_nil hmem ha, ?_,
            decompo_appt_noTick_if (noTick_Ev _) hns2, hnt⟩)
          rw [hs2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hns2)]
        · have h0 : t2 ^^^ Abs_trace [e] = <> := ht2.symm
          simp [hnt2] at h0
  | parx_nil_Ev hpar ha ih =>
      rename_i u1 t1 a
      intro v e hveq hv
      rcases trace_nil_or_Tick_or_Ev v with rfl | rfl | ⟨b, v1, rfl⟩
      · rw [appt_nil_left] at hveq
        rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp hveq with ⟨he, hu1⟩ | ⟨he, _⟩
        · rw [Event_eq] at he
          subst he
          subst hu1
          have ht1 : t1 = <> := (par_tr_nil_only_if hpar).2
          subst ht1
          exact Or.inr (Or.inr ⟨by simp [ha], by simp, <>, par_tr_nil_nil, by simp,
            noTick_nil, noTick_nil⟩)
        · simp at he
      · exact absurd hv not_noTick_Tick
      · have hv1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hv).2
        rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hv1)] at hveq
        obtain ⟨hab, hu1⟩ := appt_same_head_only_if hveq
        subst hab
        rcases ih v1 e hu1 hv1 with
            ⟨hE, s2, t2, hmem, hs2, ht2, hns2, hnt2⟩ |
            ⟨hE1, hE2, s2, hmem, hs2, hns2, hnt⟩ |
            ⟨hE1, hE2, t2, hmem, ht2, hns, hnt2⟩
        · have h0 : s2 ^^^ Abs_trace [e] = <> := hs2.symm
          simp [hns2] at h0
        · have h0 : s2 ^^^ Abs_trace [e] = <> := hs2.symm
          simp [hns2] at h0
        · refine Or.inr (Or.inr ⟨hE1, hE2, Abs_trace [Ev _] ^^^ t2, par_tr_nil_Ev hmem ha, ?_,
            hns, decompo_appt_noTick_if (noTick_Ev _) hnt2⟩)
          rw [ht2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hnt2)]
  | parx_Ev_sync hpar ha ih =>
      rename_i u1 s1 t1 a
      intro v e hveq hv
      rcases trace_nil_or_Tick_or_Ev v with rfl | rfl | ⟨b, v1, rfl⟩
      · rw [appt_nil_left] at hveq
        rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp hveq with ⟨he, hu1⟩ | ⟨he, _⟩
        · rw [Event_eq] at he
          subst he
          subst hu1
          obtain ⟨hs1, ht1⟩ := par_tr_nil_only_if hpar
          subst hs1
          subst ht1
          exact Or.inl ⟨Or.inl (by simp [ha]), <>, <>, par_tr_nil_nil, by simp, by simp,
            noTick_nil, noTick_nil⟩
        · simp at he
      · exact absurd hv not_noTick_Tick
      · have hv1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hv).2
        rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hv1)] at hveq
        obtain ⟨hab, hu1⟩ := appt_same_head_only_if hveq
        subst hab
        rcases ih v1 e hu1 hv1 with
            ⟨hE, s2, t2, hmem, hs2, ht2, hns2, hnt2⟩ |
            ⟨hE1, hE2, s2, hmem, hs2, hns2, hnt⟩ |
            ⟨hE1, hE2, t2, hmem, ht2, hns, hnt2⟩
        · refine Or.inl ⟨hE, Abs_trace [Ev _] ^^^ s2, Abs_trace [Ev _] ^^^ t2,
            par_tr_Ev_sync hmem ha, ?_, ?_,
            decompo_appt_noTick_if (noTick_Ev _) hns2,
            decompo_appt_noTick_if (noTick_Ev _) hnt2⟩
          · rw [hs2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hns2)]
          · rw [ht2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hnt2)]
        · refine Or.inr (Or.inl ⟨hE1, hE2, Abs_trace [Ev _] ^^^ s2, par_tr_Ev_sync hmem ha, ?_,
            decompo_appt_noTick_if (noTick_Ev _) hns2,
            decompo_appt_noTick_if (noTick_Ev _) hnt⟩)
          rw [hs2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hns2)]
        · refine Or.inr (Or.inr ⟨hE1, hE2, Abs_trace [Ev _] ^^^ t2, par_tr_Ev_sync hmem ha, ?_,
            decompo_appt_noTick_if (noTick_Ev _) hns,
            decompo_appt_noTick_if (noTick_Ev _) hnt2⟩)
          rw [ht2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hnt2)]
  | parx_Ev_left hpar ha ih =>
      rename_i u1 s1 t1 a
      intro v e hveq hv
      rcases trace_nil_or_Tick_or_Ev v with rfl | rfl | ⟨b, v1, rfl⟩
      · rw [appt_nil_left] at hveq
        rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp hveq with ⟨he, hu1⟩ | ⟨he, _⟩
        · rw [Event_eq] at he
          subst he
          subst hu1
          obtain ⟨hs1, ht1⟩ := par_tr_nil_only_if hpar
          subst hs1
          subst ht1
          exact Or.inr (Or.inl ⟨by simp [ha], by simp, <>, par_tr_nil_nil, by simp,
            noTick_nil, noTick_nil⟩)
        · simp at he
      · exact absurd hv not_noTick_Tick
      · have hv1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hv).2
        rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hv1)] at hveq
        obtain ⟨hab, hu1⟩ := appt_same_head_only_if hveq
        subst hab
        rcases ih v1 e hu1 hv1 with
            ⟨hE, s2, t2, hmem, hs2, ht2, hns2, hnt2⟩ |
            ⟨hE1, hE2, s2, hmem, hs2, hns2, hnt⟩ |
            ⟨hE1, hE2, t2, hmem, ht2, hns, hnt2⟩
        · refine Or.inl ⟨hE, Abs_trace [Ev _] ^^^ s2, t2, par_tr_Ev_left hmem ha, ?_, ht2,
            decompo_appt_noTick_if (noTick_Ev _) hns2, hnt2⟩
          rw [hs2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hns2)]
        · refine Or.inr (Or.inl ⟨hE1, hE2, Abs_trace [Ev _] ^^^ s2, par_tr_Ev_left hmem ha, ?_,
            decompo_appt_noTick_if (noTick_Ev _) hns2, hnt⟩)
          rw [hs2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hns2)]
        · exact Or.inr (Or.inr ⟨hE1, hE2, t2, par_tr_Ev_left hmem ha, ht2,
            decompo_appt_noTick_if (noTick_Ev _) hns, hnt2⟩)
  | parx_Ev_right hpar ha ih =>
      rename_i u1 s1 t1 a
      intro v e hveq hv
      rcases trace_nil_or_Tick_or_Ev v with rfl | rfl | ⟨b, v1, rfl⟩
      · rw [appt_nil_left] at hveq
        rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp hveq with ⟨he, hu1⟩ | ⟨he, _⟩
        · rw [Event_eq] at he
          subst he
          subst hu1
          obtain ⟨hs1, ht1⟩ := par_tr_nil_only_if hpar
          subst hs1
          subst ht1
          exact Or.inr (Or.inr ⟨by simp [ha], by simp, <>, par_tr_nil_nil, by simp,
            noTick_nil, noTick_nil⟩)
        · simp at he
      · exact absurd hv not_noTick_Tick
      · have hv1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hv).2
        rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hv1)] at hveq
        obtain ⟨hab, hu1⟩ := appt_same_head_only_if hveq
        subst hab
        rcases ih v1 e hu1 hv1 with
            ⟨hE, s2, t2, hmem, hs2, ht2, hns2, hnt2⟩ |
            ⟨hE1, hE2, s2, hmem, hs2, hns2, hnt⟩ |
            ⟨hE1, hE2, t2, hmem, ht2, hns, hnt2⟩
        · refine Or.inl ⟨hE, s2, Abs_trace [Ev _] ^^^ t2, par_tr_Ev_right hmem ha, hs2, ?_,
            hns2, decompo_appt_noTick_if (noTick_Ev _) hnt2⟩
          rw [ht2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hnt2)]
        · exact Or.inr (Or.inl ⟨hE1, hE2, s2, par_tr_Ev_right hmem ha, hs2, hns2,
            decompo_appt_noTick_if (noTick_Ev _) hnt⟩)
        · refine Or.inr (Or.inr ⟨hE1, hE2, Abs_trace [Ev _] ^^^ t2, par_tr_Ev_right hmem ha, ?_,
            hns, decompo_appt_noTick_if (noTick_Ev _) hnt2⟩)
          rw [ht2, appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hnt2)]

theorem par_tr_appt_ind {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → noTick s → noTick t →
      ∀ (u' s' t' : traceType α), u' ∈ s' |[X]|tr t' →
        u ^^^ u' ∈ (s ^^^ s') |[X]|tr (t ^^^ t') := by
  intro h
  induction h with
  | parx_nil_nil =>
      intro _ _ u' s' t' h'
      simpa using h'
  | parx_Tick_Tick =>
      intro hs _ _ _ _ _
      exact absurd hs not_noTick_Tick
  | parx_Ev_nil hpar ha ih =>
      intro hs ht u' s' t' h'
      have hs1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hs).2
      have hu1 := par_tr_noTick_ind hpar hs1 ht
      rw [appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hu1),
          appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hs1), appt_nil_left]
      exact par_tr_Ev_left (by simpa using ih hs1 ht u' s' t' h') ha
  | parx_nil_Ev hpar ha ih =>
      intro hs ht u' s' t' h'
      have ht1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) ht).2
      have hu1 := par_tr_noTick_ind hpar hs ht1
      rw [appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hu1),
          appt_assoc (Or.inl (noTick_Ev _)) (Or.inl ht1), appt_nil_left]
      exact par_tr_Ev_right (by simpa using ih hs ht1 u' s' t' h') ha
  | parx_Ev_sync hpar ha ih =>
      intro hs ht u' s' t' h'
      have hs1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hs).2
      have ht1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) ht).2
      have hu1 := par_tr_noTick_ind hpar hs1 ht1
      rw [appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hu1),
          appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hs1),
          appt_assoc (Or.inl (noTick_Ev _)) (Or.inl ht1)]
      exact par_tr_Ev_sync (ih hs1 ht1 u' s' t' h') ha
  | parx_Ev_left hpar ha ih =>
      intro hs ht u' s' t' h'
      have hs1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hs).2
      have hu1 := par_tr_noTick_ind hpar hs1 ht
      rw [appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hu1),
          appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hs1)]
      exact par_tr_Ev_left (ih hs1 ht u' s' t' h') ha
  | parx_Ev_right hpar ha ih =>
      intro hs ht u' s' t' h'
      have ht1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) ht).2
      have hu1 := par_tr_noTick_ind hpar hs ht1
      rw [appt_assoc (Or.inl (noTick_Ev _)) (Or.inl hu1),
          appt_assoc (Or.inl (noTick_Ev _)) (Or.inl ht1)]
      exact par_tr_Ev_right (ih hs ht1 u' s' t' h') ha

/- (*** only if ***) -/

theorem par_tr_last_only_if_lm {u s t : traceType α} {X : Set α} {e : event α} :
    (u ^^^ Abs_trace [e] ∈ s |[X]|tr t ∧ noTick u) →
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t')) := by
  rintro ⟨h, hu⟩
  exact par_tr_last_only_if_ind h u e rfl hu

/- (*** rule ***) -/

theorem par_tr_last_only_if {u s t : traceType α} {X : Set α} {e : event α} :
    u ^^^ Abs_trace [e] ∈ s |[X]|tr t → noTick u →
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t')) := by
  intro h hu
  exact par_tr_last_only_if_ind h u e rfl hu

/- (*** if ***) -/

theorem par_tr_last_if_lm {u s t : traceType α} {X : Set α} {e : event α} :
    (noTick u ∧
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t'))) →
      u ^^^ Abs_trace [e] ∈ s |[X]|tr t := by
  rintro ⟨hu, (⟨hE, s', t', hmem, rfl, rfl, hns, hnt⟩ |
    ⟨hE1, hE2, s', hmem, rfl, hns, hnt⟩ |
    ⟨hE1, hE2, t', hmem, rfl, hns, hnt⟩)⟩
  · have hbase : (Abs_trace [e] : traceType α) ∈ Abs_trace [e] |[X]|tr Abs_trace [e] := by
      rcases hE with hEv | rfl
      · rcases in_Ev_set.mp hEv with ⟨a, rfl, ha⟩
        exact par_tr_Ev_if (Or.inl ⟨ha, rfl, rfl⟩)
      · exact par_tr_Tick_Tick
    exact par_tr_appt_ind hmem hns hnt _ _ _ hbase
  · have hbase : (Abs_trace [e] : traceType α) ∈ Abs_trace [e] |[X]|tr (<> : traceType α) := by
      rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
      · exact absurd rfl hE2
      · exact par_tr_Ev_if (Or.inr (Or.inl ⟨by simpa using hE1, rfl, rfl⟩))
    simpa using par_tr_appt_ind hmem hns hnt _ _ _ hbase
  · have hbase : (Abs_trace [e] : traceType α) ∈ (<> : traceType α) |[X]|tr Abs_trace [e] := by
      rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
      · exact absurd rfl hE2
      · exact par_tr_Ev_if (Or.inr (Or.inr ⟨by simpa using hE1, rfl, rfl⟩))
    simpa using par_tr_appt_ind hmem hns hnt _ _ _ hbase

/- (*** rule ***) -/

theorem par_tr_last_if {u s t : traceType α} {X : Set α} {e : event α} :
    noTick u →
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t')) →
      u ^^^ Abs_trace [e] ∈ s |[X]|tr t := by
  intro hu hcase
  exact par_tr_last_if_lm ⟨hu, hcase⟩

/- (*** iff ***) -/

theorem par_tr_last {u s t : traceType α} {X : Set α} {e : event α} :
    noTick u →
      (u ^^^ Abs_trace [e] ∈ s |[X]|tr t ↔
        (((e ∈ Ev '' X ∨ e = Tick) ∧
            ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
              noTick s' ∧ noTick t') ∨
         (e ∉ Ev '' X ∧ e ≠ Tick ∧
            ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
         (e ∉ Ev '' X ∧ e ≠ Tick ∧
            ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t'))) := by
  intro hu
  exact ⟨fun h => par_tr_last_only_if h hu, fun h => par_tr_last_if hu h⟩

/- *************************************************************
                     symmetricity
 ************************************************************* -/

theorem par_tr_sym_only_if_lm {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → u ∈ t |[X]|tr s := by
  intro h
  induction h with
  | parx_nil_nil => exact par_tr_nil_nil
  | parx_Tick_Tick => exact par_tr_Tick_Tick
  | parx_Ev_nil hpar ha ih => exact par_tr_nil_Ev ih ha
  | parx_nil_Ev hpar ha ih => exact par_tr_Ev_nil ih ha
  | parx_Ev_sync hpar ha ih => exact par_tr_Ev_sync ih ha
  | parx_Ev_left hpar ha ih => exact par_tr_Ev_right ih ha
  | parx_Ev_right hpar ha ih => exact par_tr_Ev_left ih ha

theorem par_tr_sym_only_if {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → u ∈ t |[X]|tr s := by
  exact par_tr_sym_only_if_lm

theorem par_tr_sym {s t : traceType α} {X : Set α} :
    (s |[X]|tr t) = (t |[X]|tr s) := by
  ext u
  exact ⟨par_tr_sym_only_if, par_tr_sym_only_if⟩

/- (*** more auxiliary lemmas (Lean port helpers) ***) -/

theorem par_sett_Ev_inter {a : α} {u : traceType α} {X : Set α} :
    a ∉ X → sett u ∩ Ev '' X = ∅ → sett (Abs_trace [Ev a] ^^^ u) ∩ Ev '' X = ∅ := by
  intro ha hX
  rw [Set.eq_empty_iff_forall_notMem] at hX ⊢
  intro e he
  have he1 : e ∈ sett (Abs_trace [Ev a] ^^^ u) := he.1
  have he2 : e ∈ Ev '' X := he.2
  rw [sett_appt1 (Or.inl (noTick_Ev a)), sett_one] at he1
  rcases he1 with he1 | he1
  · rw [Set.mem_singleton_iff] at he1
    subst he1
    obtain ⟨b, hb, hEv⟩ := he2
    have hba : b = a := inj_Ev hEv
    subst hba
    exact ha hb
  · exact hX e ⟨he1, he2⟩

theorem par_sett_Ev_inter_rev {a : α} {u : traceType α} {X : Set α} :
    sett (Abs_trace [Ev a] ^^^ u) ∩ Ev '' X = ∅ → a ∉ X ∧ sett u ∩ Ev '' X = ∅ := by
  intro hX
  rw [Set.eq_empty_iff_forall_notMem] at hX
  constructor
  · intro ha
    exact hX (Ev a) ⟨by simp, by simp [ha]⟩
  · rw [Set.eq_empty_iff_forall_notMem]
    intro e he
    exact hX e ⟨by simp [he.1], he.2⟩

theorem par_tr_prefix_ind {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t →
      ∀ v : traceType α, «prefix» v u →
        ∃ s' t', v ∈ s' |[X]|tr t' ∧ «prefix» s' s ∧ «prefix» t' t := by
  intro h
  induction h with
  | parx_nil_nil =>
      intro v hv
      rw [prefix_of_nil] at hv
      subst hv
      exact ⟨<>, <>, par_tr_nil_nil, prefix_itself, prefix_itself⟩
  | parx_Tick_Tick =>
      intro v hv
      rw [prefix_of_one] at hv
      rcases hv with rfl | rfl
      · exact ⟨<>, <>, par_tr_nil_nil, nil_is_prefix, nil_is_prefix⟩
      · exact ⟨Abs_trace [Tick], Abs_trace [Tick], par_tr_Tick_Tick, prefix_itself,
          prefix_itself⟩
  | parx_Ev_nil hpar ha ih =>
      intro v hv
      rcases prefix_same_head_inv_only_if hv with rfl | ⟨v1, rfl, hv1⟩
      · exact ⟨<>, <>, par_tr_nil_nil, nil_is_prefix, nil_is_prefix⟩
      · obtain ⟨s2, t2, hmem, hps, hpt⟩ := ih v1 hv1
        rw [prefix_of_nil] at hpt
        subst hpt
        exact ⟨Abs_trace [Ev _] ^^^ s2, <>, par_tr_Ev_nil hmem ha,
          prefix_same_head_inv_if (Or.inr ⟨s2, rfl, hps⟩), nil_is_prefix⟩
  | parx_nil_Ev hpar ha ih =>
      intro v hv
      rcases prefix_same_head_inv_only_if hv with rfl | ⟨v1, rfl, hv1⟩
      · exact ⟨<>, <>, par_tr_nil_nil, nil_is_prefix, nil_is_prefix⟩
      · obtain ⟨s2, t2, hmem, hps, hpt⟩ := ih v1 hv1
        rw [prefix_of_nil] at hps
        subst hps
        exact ⟨<>, Abs_trace [Ev _] ^^^ t2, par_tr_nil_Ev hmem ha, nil_is_prefix,
          prefix_same_head_inv_if (Or.inr ⟨t2, rfl, hpt⟩)⟩
  | parx_Ev_sync hpar ha ih =>
      intro v hv
      rcases prefix_same_head_inv_only_if hv with rfl | ⟨v1, rfl, hv1⟩
      · exact ⟨<>, <>, par_tr_nil_nil, nil_is_prefix, nil_is_prefix⟩
      · obtain ⟨s2, t2, hmem, hps, hpt⟩ := ih v1 hv1
        exact ⟨Abs_trace [Ev _] ^^^ s2, Abs_trace [Ev _] ^^^ t2, par_tr_Ev_sync hmem ha,
          prefix_same_head_inv_if (Or.inr ⟨s2, rfl, hps⟩),
          prefix_same_head_inv_if (Or.inr ⟨t2, rfl, hpt⟩)⟩
  | parx_Ev_left hpar ha ih =>
      intro v hv
      rcases prefix_same_head_inv_only_if hv with rfl | ⟨v1, rfl, hv1⟩
      · exact ⟨<>, <>, par_tr_nil_nil, nil_is_prefix, nil_is_prefix⟩
      · obtain ⟨s2, t2, hmem, hps, hpt⟩ := ih v1 hv1
        exact ⟨Abs_trace [Ev _] ^^^ s2, t2, par_tr_Ev_left hmem ha,
          prefix_same_head_inv_if (Or.inr ⟨s2, rfl, hps⟩), hpt⟩
  | parx_Ev_right hpar ha ih =>
      intro v hv
      rcases prefix_same_head_inv_only_if hv with rfl | ⟨v1, rfl, hv1⟩
      · exact ⟨<>, <>, par_tr_nil_nil, nil_is_prefix, nil_is_prefix⟩
      · obtain ⟨s2, t2, hmem, hps, hpt⟩ := ih v1 hv1
        exact ⟨s2, Abs_trace [Ev _] ^^^ t2, par_tr_Ev_right hmem ha, hps,
          prefix_same_head_inv_if (Or.inr ⟨t2, rfl, hpt⟩)⟩

theorem par_tr_nil_left_ind {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → s = <> → u = t ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅ := by
  intro h
  induction h with
  | parx_nil_nil => intro _; exact ⟨rfl, by simp, by simp⟩
  | parx_Tick_Tick => intro h0; simp at h0
  | parx_Ev_nil hpar ha ih => intro h0; simp at h0
  | parx_nil_Ev hpar ha ih =>
      intro _
      obtain ⟨h1, h2, h3⟩ := ih rfl
      exact ⟨by rw [h1], decompo_appt_noTick_if (noTick_Ev _) h2,
        par_sett_Ev_inter ha h3⟩
  | parx_Ev_sync hpar ha ih => intro h0; simp at h0
  | parx_Ev_left hpar ha ih => intro h0; simp at h0
  | parx_Ev_right hpar ha ih =>
      intro h0
      obtain ⟨h1, h2, h3⟩ := ih h0
      exact ⟨by rw [h1], decompo_appt_noTick_if (noTick_Ev _) h2,
        par_sett_Ev_inter ha h3⟩

theorem par_tr_Tick_left_ind {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → s = Abs_trace [Tick] →
      u = t ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅ := by
  intro h
  induction h with
  | parx_nil_nil => intro h0; simp at h0
  | parx_Tick_Tick => intro _; exact ⟨rfl, by simp, by simp⟩
  | parx_Ev_nil hpar ha ih => intro h0; simp at h0
  | parx_nil_Ev hpar ha ih => intro h0; simp at h0
  | parx_Ev_sync hpar ha ih => intro h0; simp at h0
  | parx_Ev_left hpar ha ih => intro h0; simp at h0
  | parx_Ev_right hpar ha ih =>
      intro h0
      obtain ⟨h1, h2, h3⟩ := ih h0
      refine ⟨by rw [h1], ?_, par_sett_Ev_inter ha h3⟩
      simp [h2]

theorem par_tr_nil_left_if_ind {u : traceType α} {X : Set α} :
    Tick ∉ sett u → sett u ∩ Ev '' X = ∅ → u ∈ (<> : traceType α) |[X]|tr u := by
  refine induct_trace (P := fun w => Tick ∉ sett w → sett w ∩ Ev '' X = ∅ →
      w ∈ (<> : traceType α) |[X]|tr w) ?_ ?_ ?_
  · intro _ _
    exact par_tr_nil_nil
  · intro hT _
    exact absurd (by simp : Tick ∈ sett (Abs_trace [Tick] : traceType α)) hT
  · intro w a ih hT hX
    obtain ⟨ha, hXw⟩ := par_sett_Ev_inter_rev hX
    have hTw : Tick ∉ sett w := by
      intro hmem
      exact hT (by simp [hmem])
    exact par_tr_nil_Ev (ih hTw hXw) ha

theorem par_tr_Tick_left_if_ind {u : traceType α} {X : Set α} :
    Tick ∈ sett u → sett u ∩ Ev '' X = ∅ →
      u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr u := by
  refine induct_trace (P := fun w => Tick ∈ sett w → sett w ∩ Ev '' X = ∅ →
      w ∈ (Abs_trace [Tick] : traceType α) |[X]|tr w) ?_ ?_ ?_
  · intro hT _
    simp at hT
  · intro _ _
    exact par_tr_Tick_Tick
  · intro w a ih hT hX
    obtain ⟨ha, hXw⟩ := par_sett_Ev_inter_rev hX
    have hTw : Tick ∈ sett w := by simpa using hT
    exact par_tr_Ev_right (ih hTw hXw) ha

/- *************************************************************
                     prefix_closed
 ************************************************************* -/

theorem par_tr_prefix_lm {v u s t : traceType α} {X : Set α} :
    «prefix» v u ∧ u ∈ s |[X]|tr t →
      ∃ s' t', v ∈ s' |[X]|tr t' ∧ «prefix» s' s ∧ «prefix» t' t := by
  rintro ⟨hp, h⟩
  exact par_tr_prefix_ind h v hp

/- (*** rule ***) -/

theorem par_tr_prefix {v u s t : traceType α} {X : Set α} :
    «prefix» v u → u ∈ s |[X]|tr t →
      ∃ s' t', v ∈ s' |[X]|tr t' ∧ «prefix» s' s ∧ «prefix» t' t := by
  intro hp h
  exact par_tr_prefix_ind h v hp

theorem par_tr_prefixE {v u s t : traceType α} {X : Set α} {R : Prop} :
    «prefix» v u → u ∈ s |[X]|tr t →
      (∀ s' t', v ∈ s' |[X]|tr t' → «prefix» s' s → «prefix» t' t → R) →
      R := by
  intro hp h hR
  obtain ⟨s', t', hmem, hps, hpt⟩ := par_tr_prefix hp h
  exact hR s' t' hmem hps hpt

/- *************************************************************
                  parallel lemmas etc.
 ************************************************************* -/

/- *******************************
          par_tr lenght
 ******************************* -/

theorem par_tr_lengtht_lm {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → lengtht s ≤ lengtht u ∧ lengtht t ≤ lengtht u := by
  intro h
  induction h with
  | parx_nil_nil => simp
  | parx_Tick_Tick => simp
  | parx_Ev_nil hpar ha ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · simp
        omega
      · simp
  | parx_nil_Ev hpar ha ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩
      · simp
      · simp
        omega
  | parx_Ev_sync hpar ha ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩ <;> simp <;> omega
  | parx_Ev_left hpar ha ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩ <;> simp <;> omega
  | parx_Ev_right hpar ha ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨?_, ?_⟩ <;> simp <;> omega

/- (*** rule ***) -/

theorem par_tr_lengtht {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → lengtht s ≤ lengtht u ∧ lengtht t ≤ lengtht u := by
  exact par_tr_lengtht_lm

/- (*** ruleE ***) -/

theorem par_tr_lengthtE {u s t : traceType α} {X : Set α} {R : Prop} :
    u ∈ s |[X]|tr t →
      (lengtht s ≤ lengtht u → lengtht t ≤ lengtht u → R) →
      R := by
  intro h hR
  exact hR (par_tr_lengtht h).1 (par_tr_lengtht h).2

/- **************************************************
                    para
 ************************************************** -/

theorem par_tr_nil_Ev_rev {u t : traceType α} {X : Set α} {a : α} :
    u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t) →
      a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (<> : traceType α) |[X]|tr t := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ h3
    simp at h3
  · intro _ h2 _
    simp at h2
  · intro b s' u' _ h2 _ _ _
    simp at h2
  · intro b t' u' h1 _ h3 h4 h5
    obtain ⟨hab, htt⟩ := appt_same_head_only_if h3
    subst hab
    subst htt
    exact ⟨h5, u', h1, h4⟩
  · intro b s' t' u' _ h2 _ _ _
    simp at h2
  · intro b s' u' _ h2 _ _
    simp at h2
  · intro b t' u' h1 h2 h3 h4
    obtain ⟨hab, htt⟩ := appt_same_head_only_if h2
    subst hab
    subst htt
    exact ⟨h4, u', h1, h3⟩

theorem par_tr_Tick_Ev_rev {u t : traceType α} {X : Set α} {a : α} :
    u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t) →
      a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (Abs_trace [Tick] : traceType α) |[X]|tr t := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ h2 _
    simp at h2
  · intro _ _ h3
    simp at h3
  · intro b s' u' _ h2 _ _ _
    simp at h2
  · intro b t' u' _ h2 _ _ _
    simp at h2
  · intro b s' t' u' _ h2 _ _ _
    simp at h2
  · intro b s' u' _ h2 _ _
    simp at h2
  · intro b t' u' h1 h2 h3 h4
    obtain ⟨hab, htt⟩ := appt_same_head_only_if h2
    subst hab
    subst htt
    exact ⟨h4, u', h1, h3⟩

/- **************************************************
                    noTick
 ************************************************** -/

/- -----------------*
 |   par noTick    |
 *----------------- -/

/- (*** only if ***) -/

theorem par_tr_noTick_only_if_lm {u s t : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr t ∧ noTick s ∧ noTick t) → noTick u := by
  rintro ⟨h, hs, ht⟩
  exact par_tr_noTick_ind h hs ht

theorem par_tr_noTick_only_if {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → noTick s → noTick t → noTick u := by
  exact par_tr_noTick_ind

/- (*** if ***) -/

theorem par_tr_noTick_if_lm {u s t : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr t ∧ noTick u) → (noTick s ∧ noTick t) := by
  rintro ⟨h, hu⟩
  revert hu
  induction h with
  | parx_nil_nil => intro _; exact ⟨noTick_nil, noTick_nil⟩
  | parx_Tick_Tick => intro hu; exact absurd hu not_noTick_Tick
  | parx_Ev_nil hpar ha ih =>
      intro hu
      have hu1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hu).2
      exact ⟨decompo_appt_noTick_if (noTick_Ev _) (ih hu1).1, noTick_nil⟩
  | parx_nil_Ev hpar ha ih =>
      intro hu
      have hu1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hu).2
      exact ⟨noTick_nil, decompo_appt_noTick_if (noTick_Ev _) (ih hu1).2⟩
  | parx_Ev_sync hpar ha ih =>
      intro hu
      have hu1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hu).2
      exact ⟨decompo_appt_noTick_if (noTick_Ev _) (ih hu1).1,
        decompo_appt_noTick_if (noTick_Ev _) (ih hu1).2⟩
  | parx_Ev_left hpar ha ih =>
      intro hu
      have hu1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hu).2
      exact ⟨decompo_appt_noTick_if (noTick_Ev _) (ih hu1).1, (ih hu1).2⟩
  | parx_Ev_right hpar ha ih =>
      intro hu
      have hu1 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev _)) hu).2
      exact ⟨(ih hu1).1, decompo_appt_noTick_if (noTick_Ev _) (ih hu1).2⟩

theorem par_tr_noTick_if {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → noTick u → (noTick s ∧ noTick t) := by
  intro h hu
  exact par_tr_noTick_if_lm ⟨h, hu⟩

/- (*** iff ***) -/

theorem par_tr_noTick {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → ((noTick s ∧ noTick t) ↔ noTick u) := by
  intro h
  exact ⟨fun hst => par_tr_noTick_only_if h hst.1 hst.2, fun hu => par_tr_noTick_if h hu⟩

/- Isabelle: lemmas par_tr_noTick_compo = par_tr_noTick_only_if -/
/- Isabelle: lemmas par_tr_noTick_decompo = par_tr_noTick_if -/

/- (****** used in Alpha_parallel ******) -/

/- (*** nil-Tick ***) -/

@[simp] theorem par_tr_nil_Tick {u : traceType α} {X : Set α} :
    ¬ (u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Tick] : traceType α)) := by
  intro h
  refine par_tr_elims h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> (repeat intro _) <;> simp_all

@[simp] theorem par_tr_Tick_nil {u : traceType α} {X : Set α} :
    ¬ (u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr (<> : traceType α)) := by
  intro h
  exact par_tr_nil_Tick (par_tr_sym_only_if h)

/- (*** nil-Ev ***) -/

theorem par_tr_nil_Ev_iff {u t : traceType α} {X : Set α} {a : α} :
    (u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t)) ↔
      (a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (<> : traceType α) |[X]|tr t) := by
  constructor
  · exact par_tr_nil_Ev_rev
  · rintro ⟨ha, v, rfl, hv⟩
    exact par_tr_nil_Ev hv ha

/- (*** Tick-Ev ***) -/

theorem par_tr_Tick_Ev_iff {u t : traceType α} {X : Set α} {a : α} :
    (u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t)) ↔
      (a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧
        v ∈ (Abs_trace [Tick] : traceType α) |[X]|tr t) := by
  constructor
  · exact par_tr_Tick_Ev_rev
  · rintro ⟨ha, v, rfl, hv⟩
    exact par_tr_Ev_right hv ha

/- (****** nil ******) -/

theorem par_tr_nil_left_only_if_imp {u s : traceType α} {X : Set α} :
    u ∈ (<> : traceType α) |[X]|tr s →
      u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅ := by
  intro h
  exact par_tr_nil_left_ind h rfl

theorem par_tr_nil_left_only_if {u s : traceType α} {X : Set α} :
    u ∈ (<> : traceType α) |[X]|tr s →
      u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅ := by
  intro h
  exact par_tr_nil_left_ind h rfl

theorem par_tr_nil_left_if_imp {u : traceType α} {X : Set α} :
    (Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅) →
      u ∈ (<> : traceType α) |[X]|tr u := by
  rintro ⟨hT, hX⟩
  exact par_tr_nil_left_if_ind hT hX

theorem par_tr_nil_left_if {u : traceType α} {X : Set α} :
    Tick ∉ sett u → sett u ∩ Ev '' X = ∅ →
      u ∈ (<> : traceType α) |[X]|tr u := by
  intro hT hX
  exact par_tr_nil_left_if_ind hT hX

/- (*** nil left ***) -/

theorem par_tr_nil_left {u s : traceType α} {X : Set α} :
    (u ∈ (<> : traceType α) |[X]|tr s) ↔
      (u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅) := by
  constructor
  · exact par_tr_nil_left_only_if
  · rintro ⟨rfl, hT, hX⟩
    exact par_tr_nil_left_if hT hX

/- (*** nil right ***) -/

theorem par_tr_nil_right {u s : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr (<> : traceType α)) ↔
      (u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅) := by
  rw [par_tr_sym (s := s) (t := (<> : traceType α))]
  exact par_tr_nil_left

/- Isabelle: lemmas par_tr_nil = par_tr_nil_left par_tr_nil_right -/

/- (****** Tick ******) -/

theorem par_tr_Tick_left_only_if_imp {u s : traceType α} {X : Set α} :
    u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr s →
      u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅ := by
  intro h
  exact par_tr_Tick_left_ind h rfl

theorem par_tr_Tick_left_only_if {u s : traceType α} {X : Set α} :
    u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr s →
      u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅ := by
  intro h
  exact par_tr_Tick_left_ind h rfl

theorem par_tr_Tick_left_if_imp {u : traceType α} {X : Set α} :
    (Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅) →
      u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr u := by
  rintro ⟨hT, hX⟩
  exact par_tr_Tick_left_if_ind hT hX

theorem par_tr_Tick_left_if {u : traceType α} {X : Set α} :
    Tick ∈ sett u → sett u ∩ Ev '' X = ∅ →
      u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr u := by
  intro hT hX
  exact par_tr_Tick_left_if_ind hT hX

/- (*** Tick left ***) -/

theorem par_tr_Tick_left {u s : traceType α} {X : Set α} :
    (u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr s) ↔
      (u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅) := by
  constructor
  · exact par_tr_Tick_left_only_if
  · rintro ⟨rfl, hT, hX⟩
    exact par_tr_Tick_left_if hT hX

/- (*** Tick right ***) -/

theorem par_tr_Tick_right {u s : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr (Abs_trace [Tick] : traceType α)) ↔
      (u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅) := by
  rw [par_tr_sym (s := s) (t := (Abs_trace [Tick] : traceType α))]
  exact par_tr_Tick_left

/- Isabelle: lemmas par_tr_Tick = par_tr_Tick_left par_tr_Tick_right -/

/- (*** par sett ***) -/

theorem par_tr_sett {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → sett u ⊆ sett s ∪ sett t := by
  intro h
  induction h with
  | parx_nil_nil => simp
  | parx_Tick_Tick => simp
  | parx_Ev_nil hpar ha ih =>
      intro e he
      rw [sett_appt1 (Or.inl (noTick_Ev _)), sett_one] at he ⊢
      rcases he with he | he
      · exact Or.inl (Or.inl he)
      · rcases ih he with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
  | parx_nil_Ev hpar ha ih =>
      intro e he
      rw [sett_appt1 (Or.inl (noTick_Ev _)), sett_one] at he ⊢
      rcases he with he | he
      · exact Or.inr (Or.inl he)
      · rcases ih he with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
  | parx_Ev_sync hpar ha ih =>
      intro e he
      rw [sett_appt1 (Or.inl (noTick_Ev _)), sett_one] at he ⊢
      rw [sett_appt1 (Or.inl (noTick_Ev _)), sett_one]
      rcases he with he | he
      · exact Or.inl (Or.inl he)
      · rcases ih he with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr (Or.inr h1)
  | parx_Ev_left hpar ha ih =>
      intro e he
      rw [sett_appt1 (Or.inl (noTick_Ev _)), sett_one] at he ⊢
      rcases he with he | he
      · exact Or.inl (Or.inl he)
      · rcases ih he with h1 | h1
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
  | parx_Ev_right hpar ha ih =>
      intro e he
      rw [sett_appt1 (Or.inl (noTick_Ev _)), sett_one] at he ⊢
      rcases he with he | he
      · exact Or.inr (Or.inl he)
      · rcases ih he with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

theorem interleave_appt_left_lm {u s t v : traceType α} :
    (u ∈ s |[({} : Set α)]|tr t ∧ noTick v) →
      v ^^^ u ∈ (v ^^^ s) |[({} : Set α)]|tr t := by
  rintro ⟨hu, hv⟩
  have hvv : v ∈ v |[({} : Set α)]|tr (<> : traceType α) :=
    par_tr_nil_right.mpr ⟨rfl, hv, by simp⟩
  simpa using par_tr_appt_ind hvv hv noTick_nil u s t hu

theorem interleave_appt_left_step {u s t v : traceType α} :
    u ∈ s |[({} : Set α)]|tr t → noTick v →
      v ^^^ u ∈ (v ^^^ s) |[({} : Set α)]|tr t := by
  intro hu hv
  exact interleave_appt_left_lm ⟨hu, hv⟩

theorem interleave_appt_right_step {u s t v : traceType α} :
    u ∈ t |[({} : Set α)]|tr s → noTick v →
      v ^^^ u ∈ t |[({} : Set α)]|tr (v ^^^ s) := by
  intro hu hv
  exact par_tr_sym_only_if (interleave_appt_left_step (par_tr_sym_only_if hu) hv)

theorem interleave_appt_left_nil {u t v : traceType α} :
    u ∈ (<> : traceType α) |[({} : Set α)]|tr t → noTick v →
      v ^^^ u ∈ v |[({} : Set α)]|tr t := by
  intro hu hv
  simpa using interleave_appt_left_step (s := <>) hu hv

theorem interleave_appt_right_nil {u t v : traceType α} :
    u ∈ t |[({} : Set α)]|tr (<> : traceType α) → noTick v →
      v ^^^ u ∈ t |[({} : Set α)]|tr v := by
  intro hu hv
  simpa using interleave_appt_right_step (s := <>) hu hv

theorem interleave_appt_left_nil_nil {t : traceType α} :
    noTick t → t ∈ t |[({} : Set α)]|tr (<> : traceType α) := by
  intro ht
  exact par_tr_nil_right.mpr ⟨rfl, ht, by simp⟩

theorem interleave_appt_right_nil_nil {t : traceType α} :
    noTick t → t ∈ (<> : traceType α) |[({} : Set α)]|tr t := by
  intro ht
  exact par_tr_nil_left.mpr ⟨rfl, ht, by simp⟩

/- Isabelle: lemmas interleave_appt_left =
       interleave_appt_left_step
       interleave_appt_left_nil
       interleave_appt_left_nil_nil -/

/- Isabelle: lemmas interleave_appt_right =
       interleave_appt_right_step
       interleave_appt_right_nil
       interleave_appt_right_nil_nil -/

/-  par decompo -/

theorem par_tr_app_right {u v s t : traceType α} {X : Set α} :
    (noTick u ∧ sett u ∩ (Ev '' X) = ∅ ∧ v ∈ s |[X]|tr t) →
      u ^^^ v ∈ s |[X]|tr (u ^^^ t) := by
  rintro ⟨hu, hX, hv⟩
  have h0 : u ∈ (<> : traceType α) |[X]|tr u := par_tr_nil_left_if hu hX
  simpa using par_tr_appt_ind h0 noTick_nil hu v s t hv

/- (****************** to add it again ******************) -/
/- Isabelle note: this theory restored `disj_not1` to the simp set here. -/
