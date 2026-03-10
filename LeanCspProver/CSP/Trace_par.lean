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

axiom par_tr_elims_lm {u s t : traceType α} {X : Set α} {P : Prop} :
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
      P

axiom par_tr_elims {u s t : traceType α} {X : Set α} {P : Prop} :
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
      P

/- *************************************************************
                 par_tr decomposition
 ************************************************************* -/

/- -------------------*
 |     par nil       |
 *------------------- -/

/- (*** par_tr ***) -/

axiom par_tr_nil_only_if {s t : traceType α} {X : Set α} :
    (<> : traceType α) ∈ s |[X]|tr t → s = <> ∧ t = <>

/- (*** iff ***) -/

@[simp] axiom par_tr_nil1 {s t : traceType α} {X : Set α} :
    ((<> : traceType α) ∈ s |[X]|tr t) ↔ (s = <> ∧ t = <>)

@[simp] axiom par_tr_nil2 {u : traceType α} {X : Set α} :
    u ∈ ((<> : traceType α) |[X]|tr (<> : traceType α)) ↔ u = <>

/- -------------------*
 |     par Tick      |
 *------------------- -/

/- (*** only if ***) -/

axiom par_tr_Tick_only_if {s t : traceType α} {X : Set α} :
    (Abs_trace [Tick] : traceType α) ∈ s |[X]|tr t →
      s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]

/- (*** iff ***) -/

@[simp] axiom par_tr_Tick1 {s t : traceType α} {X : Set α} :
    ((Abs_trace [Tick] : traceType α) ∈ s |[X]|tr t) ↔
      (s = Abs_trace [Tick] ∧ t = Abs_trace [Tick])

@[simp] axiom par_tr_Tick2 {u : traceType α} {X : Set α} :
    u ∈ ((Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Tick] : traceType α)) ↔
      u = Abs_trace [Tick]

/- -----------------*
 |     par Ev      |
 *----------------- -/

/- (*** only if ***) -/

axiom par_tr_Ev_only_if {a : α} {s t : traceType α} {X : Set α} :
    (Abs_trace [Ev a] : traceType α) ∈ s |[X]|tr t →
      ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
       (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
       (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a]))

/- (*** if ***) -/

axiom par_tr_Ev_if {a : α} {s t : traceType α} {X : Set α} :
    ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
     (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
     (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a])) →
      (Abs_trace [Ev a] : traceType α) ∈ s |[X]|tr t

axiom par_tr_Ev {a : α} {s t : traceType α} {X : Set α} :
    ((Abs_trace [Ev a] : traceType α) ∈ s |[X]|tr t) ↔
      ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
       (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
       (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a]))

/- --------------------------------------------*
 |                 par one                    |
 *-------------------------------------------- -/

axiom par_tr_one {e : event α} {s t : traceType α} {X : Set α} :
    ((Abs_trace [e] : traceType α) ∈ s |[X]|tr t) ↔
      ((e = Tick ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) ∨
       ∃ a, e = Ev a ∧
         ((a ∈ X ∧ s = Abs_trace [Ev a] ∧ t = Abs_trace [Ev a]) ∨
          (a ∉ X ∧ s = Abs_trace [Ev a] ∧ t = <>) ∨
          (a ∉ X ∧ s = <> ∧ t = Abs_trace [Ev a])))

/- --------------------------------------------*
 |                par head                    |
 *-------------------------------------------- -/

/- (*** only if ***) -/

axiom par_tr_head_only_if {a : α} {u s t : traceType α} {X : Set α} :
    Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t →
      (a ∈ X ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
      (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
      (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t')

/- (*** if ***) -/

axiom par_tr_head_if {a : α} {u s t : traceType α} {X : Set α} :
    ((a ∈ X ∧
        ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
     (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
     (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t')) →
      Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t

/- (*** iff ***) -/

axiom par_tr_head {a : α} {u s t : traceType α} {X : Set α} :
    (Abs_trace [Ev a] ^^^ u ∈ s |[X]|tr t) ↔
      ((a ∈ X ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧ t = Abs_trace [Ev a] ^^^ t') ∨
       (a ∉ X ∧ ∃ s', u ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
       (a ∉ X ∧ ∃ t', u ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t'))

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

axiom par_tr_head_Ev_Ev {a b : α} {u s t : traceType α} {X : Set α} :
    (u ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr (Abs_trace [Ev b] ^^^ t)) ↔
      ∃ c v, u = Abs_trace [Ev c] ^^^ v ∧
        ((c ∈ X ∧ v ∈ s |[X]|tr t ∧ a = c ∧ b = c) ∨
         (c ∉ X ∧ v ∈ s |[X]|tr (Abs_trace [Ev b] ^^^ t) ∧ a = c) ∨
         (c ∉ X ∧ v ∈ (Abs_trace [Ev a] ^^^ s) |[X]|tr t ∧ b = c))

/- step -/

axiom par_tr_step {u s t : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr t) ↔
      ((u = <> ∧ s = <> ∧ t = <>) ∨
       (u = Abs_trace [Tick] ∧ s = Abs_trace [Tick] ∧ t = Abs_trace [Tick]) ∨
       ∃ a v, u = Abs_trace [Ev a] ^^^ v ∧
         ((a ∈ X ∧
             ∃ s' t',
               v ∈ s' |[X]|tr t' ∧ s = Abs_trace [Ev a] ^^^ s' ∧
                 t = Abs_trace [Ev a] ^^^ t') ∨
          (a ∉ X ∧ ∃ s', v ∈ s' |[X]|tr t ∧ s = Abs_trace [Ev a] ^^^ s') ∨
          (a ∉ X ∧ ∃ t', v ∈ s |[X]|tr t' ∧ t = Abs_trace [Ev a] ^^^ t')))

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

/- (*** only if ***) -/

axiom par_tr_last_only_if_lm {u s t : traceType α} {X : Set α} {e : event α} :
    (u ^^^ Abs_trace [e] ∈ s |[X]|tr t ∧ noTick u) →
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t'))

/- (*** rule ***) -/

axiom par_tr_last_only_if {u s t : traceType α} {X : Set α} {e : event α} :
    u ^^^ Abs_trace [e] ∈ s |[X]|tr t → noTick u →
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t'))

/- (*** if ***) -/

axiom par_tr_last_if_lm {u s t : traceType α} {X : Set α} {e : event α} :
    (noTick u ∧
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t'))) →
      u ^^^ Abs_trace [e] ∈ s |[X]|tr t

/- (*** rule ***) -/

axiom par_tr_last_if {u s t : traceType α} {X : Set α} {e : event α} :
    noTick u →
      (((e ∈ Ev '' X ∨ e = Tick) ∧
          ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
            noTick s' ∧ noTick t') ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
       (e ∉ Ev '' X ∧ e ≠ Tick ∧
          ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t')) →
      u ^^^ Abs_trace [e] ∈ s |[X]|tr t

/- (*** iff ***) -/

axiom par_tr_last {u s t : traceType α} {X : Set α} {e : event α} :
    noTick u →
      (u ^^^ Abs_trace [e] ∈ s |[X]|tr t ↔
        (((e ∈ Ev '' X ∨ e = Tick) ∧
            ∃ s' t', u ∈ s' |[X]|tr t' ∧ s = s' ^^^ Abs_trace [e] ∧ t = t' ^^^ Abs_trace [e] ∧
              noTick s' ∧ noTick t') ∨
         (e ∉ Ev '' X ∧ e ≠ Tick ∧
            ∃ s', u ∈ s' |[X]|tr t ∧ s = s' ^^^ Abs_trace [e] ∧ noTick s' ∧ noTick t) ∨
         (e ∉ Ev '' X ∧ e ≠ Tick ∧
            ∃ t', u ∈ s |[X]|tr t' ∧ t = t' ^^^ Abs_trace [e] ∧ noTick s ∧ noTick t')))

/- *************************************************************
                     symmetricity
 ************************************************************* -/

axiom par_tr_sym_only_if_lm {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → u ∈ t |[X]|tr s

axiom par_tr_sym_only_if {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → u ∈ t |[X]|tr s

axiom par_tr_sym {s t : traceType α} {X : Set α} :
    (s |[X]|tr t) = (t |[X]|tr s)

/- *************************************************************
                     prefix_closed
 ************************************************************* -/

axiom par_tr_prefix_lm {v u s t : traceType α} {X : Set α} :
    «prefix» v u ∧ u ∈ s |[X]|tr t →
      ∃ s' t', v ∈ s' |[X]|tr t' ∧ «prefix» s' s ∧ «prefix» t' t

/- (*** rule ***) -/

axiom par_tr_prefix {v u s t : traceType α} {X : Set α} :
    «prefix» v u → u ∈ s |[X]|tr t →
      ∃ s' t', v ∈ s' |[X]|tr t' ∧ «prefix» s' s ∧ «prefix» t' t

axiom par_tr_prefixE {v u s t : traceType α} {X : Set α} {R : Prop} :
    «prefix» v u → u ∈ s |[X]|tr t →
      (∀ s' t', v ∈ s' |[X]|tr t' → «prefix» s' s → «prefix» t' t → R) →
      R

/- *************************************************************
                  parallel lemmas etc.
 ************************************************************* -/

/- *******************************
          par_tr lenght
 ******************************* -/

axiom par_tr_lengtht_lm {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → lengtht s ≤ lengtht u ∧ lengtht t ≤ lengtht u

/- (*** rule ***) -/

axiom par_tr_lengtht {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → lengtht s ≤ lengtht u ∧ lengtht t ≤ lengtht u

/- (*** ruleE ***) -/

axiom par_tr_lengthtE {u s t : traceType α} {X : Set α} {R : Prop} :
    u ∈ s |[X]|tr t →
      (lengtht s ≤ lengtht u → lengtht t ≤ lengtht u → R) →
      R

/- **************************************************
                    para
 ************************************************** -/

axiom par_tr_nil_Ev_rev {u t : traceType α} {X : Set α} {a : α} :
    u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t) →
      a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (<> : traceType α) |[X]|tr t

axiom par_tr_Tick_Ev_rev {u t : traceType α} {X : Set α} {a : α} :
    u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t) →
      a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (Abs_trace [Tick] : traceType α) |[X]|tr t

/- **************************************************
                    noTick
 ************************************************** -/

/- -----------------*
 |   par noTick    |
 *----------------- -/

/- (*** only if ***) -/

axiom par_tr_noTick_only_if_lm {u s t : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr t ∧ noTick s ∧ noTick t) → noTick u

axiom par_tr_noTick_only_if {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → noTick s → noTick t → noTick u

/- (*** if ***) -/

axiom par_tr_noTick_if_lm {u s t : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr t ∧ noTick u) → (noTick s ∧ noTick t)

axiom par_tr_noTick_if {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → noTick u → (noTick s ∧ noTick t)

/- (*** iff ***) -/

axiom par_tr_noTick {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → ((noTick s ∧ noTick t) ↔ noTick u)

/- Isabelle: lemmas par_tr_noTick_compo = par_tr_noTick_only_if -/
/- Isabelle: lemmas par_tr_noTick_decompo = par_tr_noTick_if -/

/- (****** used in Alpha_parallel ******) -/

/- (*** nil-Tick ***) -/

@[simp] axiom par_tr_nil_Tick {u : traceType α} {X : Set α} :
    ¬ (u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Tick] : traceType α))

@[simp] axiom par_tr_Tick_nil {u : traceType α} {X : Set α} :
    ¬ (u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr (<> : traceType α))

/- (*** nil-Ev ***) -/

axiom par_tr_nil_Ev_iff {u t : traceType α} {X : Set α} {a : α} :
    (u ∈ (<> : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t)) ↔
      (a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (<> : traceType α) |[X]|tr t)

/- (*** Tick-Ev ***) -/

axiom par_tr_Tick_Ev_iff {u t : traceType α} {X : Set α} {a : α} :
    (u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr (Abs_trace [Ev a] ^^^ t)) ↔
      (a ∉ X ∧ ∃ v, u = Abs_trace [Ev a] ^^^ v ∧ v ∈ (Abs_trace [Tick] : traceType α) |[X]|tr t)

/- (****** nil ******) -/

axiom par_tr_nil_left_only_if_imp {u s : traceType α} {X : Set α} :
    u ∈ (<> : traceType α) |[X]|tr s →
      u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅

axiom par_tr_nil_left_only_if {u s : traceType α} {X : Set α} :
    u ∈ (<> : traceType α) |[X]|tr s →
      u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅

axiom par_tr_nil_left_if_imp {u : traceType α} {X : Set α} :
    (Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅) →
      u ∈ (<> : traceType α) |[X]|tr u

axiom par_tr_nil_left_if {u : traceType α} {X : Set α} :
    Tick ∉ sett u → sett u ∩ Ev '' X = ∅ →
      u ∈ (<> : traceType α) |[X]|tr u

/- (*** nil left ***) -/

axiom par_tr_nil_left {u s : traceType α} {X : Set α} :
    (u ∈ (<> : traceType α) |[X]|tr s) ↔
      (u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅)

/- (*** nil right ***) -/

axiom par_tr_nil_right {u s : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr (<> : traceType α)) ↔
      (u = s ∧ Tick ∉ sett u ∧ sett u ∩ Ev '' X = ∅)

/- Isabelle: lemmas par_tr_nil = par_tr_nil_left par_tr_nil_right -/

/- (****** Tick ******) -/

axiom par_tr_Tick_left_only_if_imp {u s : traceType α} {X : Set α} :
    u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr s →
      u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅

axiom par_tr_Tick_left_only_if {u s : traceType α} {X : Set α} :
    u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr s →
      u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅

axiom par_tr_Tick_left_if_imp {u : traceType α} {X : Set α} :
    (Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅) →
      u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr u

axiom par_tr_Tick_left_if {u : traceType α} {X : Set α} :
    Tick ∈ sett u → sett u ∩ Ev '' X = ∅ →
      u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr u

/- (*** Tick left ***) -/

axiom par_tr_Tick_left {u s : traceType α} {X : Set α} :
    (u ∈ (Abs_trace [Tick] : traceType α) |[X]|tr s) ↔
      (u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅)

/- (*** Tick right ***) -/

axiom par_tr_Tick_right {u s : traceType α} {X : Set α} :
    (u ∈ s |[X]|tr (Abs_trace [Tick] : traceType α)) ↔
      (u = s ∧ Tick ∈ sett u ∧ sett u ∩ Ev '' X = ∅)

/- Isabelle: lemmas par_tr_Tick = par_tr_Tick_left par_tr_Tick_right -/

/- (*** par sett ***) -/

axiom par_tr_sett {u s t : traceType α} {X : Set α} :
    u ∈ s |[X]|tr t → sett u ⊆ sett s ∪ sett t

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

axiom interleave_appt_left_lm {u s t v : traceType α} :
    (u ∈ s |[({} : Set α)]|tr t ∧ noTick v) →
      v ^^^ u ∈ (v ^^^ s) |[({} : Set α)]|tr t

axiom interleave_appt_left_step {u s t v : traceType α} :
    u ∈ s |[({} : Set α)]|tr t → noTick v →
      v ^^^ u ∈ (v ^^^ s) |[({} : Set α)]|tr t

axiom interleave_appt_right_step {u s t v : traceType α} :
    u ∈ t |[({} : Set α)]|tr s → noTick v →
      v ^^^ u ∈ t |[({} : Set α)]|tr (v ^^^ s)

axiom interleave_appt_left_nil {u t v : traceType α} :
    u ∈ (<> : traceType α) |[({} : Set α)]|tr t → noTick v →
      v ^^^ u ∈ v |[({} : Set α)]|tr t

axiom interleave_appt_right_nil {u t v : traceType α} :
    u ∈ t |[({} : Set α)]|tr (<> : traceType α) → noTick v →
      v ^^^ u ∈ t |[({} : Set α)]|tr v

axiom interleave_appt_left_nil_nil {t : traceType α} :
    noTick t → t ∈ t |[({} : Set α)]|tr (<> : traceType α)

axiom interleave_appt_right_nil_nil {t : traceType α} :
    noTick t → t ∈ (<> : traceType α) |[({} : Set α)]|tr t

/- Isabelle: lemmas interleave_appt_left =
       interleave_appt_left_step
       interleave_appt_left_nil
       interleave_appt_left_nil_nil -/

/- Isabelle: lemmas interleave_appt_right =
       interleave_appt_right_step
       interleave_appt_right_nil
       interleave_appt_right_nil_nil -/

/-  par decompo -/

axiom par_tr_app_right {u v s t : traceType α} {X : Set α} :
    (noTick u ∧ sett u ∩ (Ev '' X) = ∅ ∧ v ∈ s |[X]|tr t) →
      u ^^^ v ∈ s |[X]|tr (u ^^^ t)

/- (****************** to add it again ******************) -/
/- Isabelle note: this theory restored `disj_not1` to the simp set here. -/
