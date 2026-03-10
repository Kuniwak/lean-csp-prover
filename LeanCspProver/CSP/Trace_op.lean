           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Trace_hide
import LeanCspProver.CSP.Trace_par
import LeanCspProver.CSP.Trace_ren
import LeanCspProver.CSP.Trace_seq

open Function
open event

/- *****************************************************************

         1.

 ***************************************************************** -/

/- -------------- *
     hide & seq
 * -------------- -/

theorem rmTick_hide {s : traceType α} {X : Set α} :
    hide_tr (rmTick s) X = rmTick (hide_tr s X) := by
  rcases trace_last_noTick_or_Tick s with hs | ⟨s', hs', hsEq⟩
  · have hsX : noTick (hide_tr s X) := (hide_tr_noTick (s := s) (X := X)).2 hs
    rw [rmTick_nochange hs, rmTick_nochange hsX]
  · have hsX : noTick (hide_tr s' X) := (hide_tr_noTick (s := s') (X := X)).2 hs'
    rw [hsEq]
    calc
      hide_tr (rmTick (s' ^^^ (Abs_trace [Tick] : traceType α))) X
          = hide_tr s' X := by rw [rmTick_last_Tick hs']
      _ = rmTick (hide_tr s' X ^^^ (Abs_trace [Tick] : traceType α)) := by
            symm
            exact rmTick_last_Tick hsX
      _ = rmTick (hide_tr (s' ^^^ (Abs_trace [Tick] : traceType α)) X) := by
            rw [hide_tr_appt (X := X) (s := s') (t := Abs_trace [Tick]) (Or.inl hs'), hide_tr_Tick]

/- -------------- *
     hide & par
 * -------------- -/

axiom interleave_of_hide_tr_lm {u s t : traceType α} {X : Set α} :
  u ∈ par_tr s (∅ : Set α) t →
    hide_tr u X ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X)

/- interleave_of_hide_tr -/

theorem interleave_of_hide_tr {u s t : traceType α} {X : Set α} :
    u ∈ par_tr s (∅ : Set α) t →
      hide_tr u X ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) := by
  exact interleave_of_hide_tr_lm

/- -------------------------------------------------------------- -/

axiom interleave_of_hide_tr_ex_only_if_lm {u s t : traceType α} {X : Set α} :
  u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) →
    ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t

theorem interleave_of_hide_tr_ex_only_if {u s t : traceType α} {X : Set α} :
    u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) →
      ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t := by
  exact interleave_of_hide_tr_ex_only_if_lm

/- interleave_of_hide_tr_ex -/

theorem interleave_of_hide_tr_ex {u s t : traceType α} {X : Set α} :
    (u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X)) ↔
      ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t := by
  constructor
  · exact interleave_of_hide_tr_ex_only_if
  · rintro ⟨v, rfl, hv⟩
    exact interleave_of_hide_tr hv

/- --------------------------------------------------- *
        distribution renaming over Interleaving
 * --------------------------------------------------- -/

axiom interleave_of_ren_tr_only_if_all {u s t : traceType α} {r : Set (α × β)} {v : traceType β} :
   u ∈ par_tr s (∅ : Set α) t → u [[r]]* v →
     ∃ s' t', v ∈ par_tr s' (∅ : Set β) t' ∧ s [[r]]* s' ∧ t [[r]]* t'

theorem interleave_of_ren_tr_only_if
    {u s t : traceType α} {r : Set (α × β)} {v : traceType β} :
    u ∈ par_tr s (∅ : Set α) t → u [[r]]* v →
      ∃ s' t', v ∈ par_tr s' (∅ : Set β) t' ∧ s [[r]]* s' ∧ t [[r]]* t' := by
  intro hu hv
  exact interleave_of_ren_tr_only_if_all hu hv

axiom interleave_of_ren_tr_if_all {v : traceType β} {r : Set (α × β)}
    {s t : traceType α} {s' t' : traceType β} :
   v ∈ par_tr s' (∅ : Set β) t' → s [[r]]* s' → t [[r]]* t' →
     ∃ u, u ∈ par_tr s (∅ : Set α) t ∧ u [[r]]* v

theorem interleave_of_ren_tr_if
    {v : traceType β} {s' t' : traceType β} {r : Set (α × β)}
    {s t : traceType α} :
    v ∈ par_tr s' (∅ : Set β) t' → s [[r]]* s' → t [[r]]* t' →
      ∃ u, u ∈ par_tr s (∅ : Set α) t ∧ u [[r]]* v := by
  intro hv hs ht
  exact interleave_of_ren_tr_if_all hv hs ht

/- ------------------------------- *
         Renaming channel
 * ------------------------------- -/

/- Renaming_channel & rest-tr -/

axiom ren_tr_rest_Renaming_channel {x α : Type _} {left mid right : x → α}
    {s s1 s2 : traceType α} :
  Injective right → Injective mid → Injective left →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    s1 [[(right <==> mid)]]* (s rest-tr (Set.range left ∪ Set.range mid)) →
    s2 [[(left <==> mid)]]* (s rest-tr (Set.range mid ∪ Set.range right)) →
    (s1 rest-tr Set.range right) [[(right <==> left)]]* (s2 rest-tr Set.range left)

/- no renaming events -/

axiom Renaming_channel_tr_rest_eq {x α : Type _} {f g : x → α}
    {Y : Set α} {s t : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    Set.range f ∩ Y = ∅ →
    Set.range g ∩ Y = ∅ →
    s [[(f <==> g)]]* t →
    s rest-tr Y = t rest-tr Y

axiom Renaming_channel_tr_rest_eq_range {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* t →
    s rest-tr Set.range h = t rest-tr Set.range h

/- --- Renaming channel & sett 2 (no used) --- -/

axiom Renaming_channel_range_sett_lm {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* (t rest-tr (Set.range f ∪ Set.range h)) →
    sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming_channel_range_sett1 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* (t rest-tr (Set.range f ∪ Set.range h)) →
    sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming_channel_range_sett2 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* (t rest-tr (Set.range h ∪ Set.range f)) →
    sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g))

axiom Renaming_channel_range_sett3 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(g <==> f)]]* (t rest-tr (Set.range f ∪ Set.range h)) →
    sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h))

axiom Renaming_channel_range_sett4 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(g <==> f)]]* (t rest-tr (Set.range h ∪ Set.range f)) →
    sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g))

/- Isabelle: lemmas Renaming_channel_range_sett =
       Renaming_channel_range_sett1
       Renaming_channel_range_sett2
       Renaming_channel_range_sett3
       Renaming_channel_range_sett4 -/

/- --- compose restricted traces --- -/

axiom Renaming_channel_tr_par_comp {x α : Type _} {f g h : x → α}
    {n : Nat} {s t u : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    lengtht s + lengtht t ≤ n →
    sett s ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range g)) →
    sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range g)) →
    (s rest-tr Set.range f) [[(f <==> g)]]* (t rest-tr Set.range g) →
    ((noTick s ∧ noTick t ∧ noTick u) ∨ (¬ noTick s ∧ ¬ noTick t ∧ ¬ noTick u)) →
    ∃ sh th, (∃ v, v ∈ (sh |[Set.range h]|tr th)) ∧ s [[(f <==> h)]]* sh ∧ t [[(g <==> h)]]* th

/- -------------- distribution Renaming over restriction -------------- -/

axiom Renaming_channel_rest_tr_dist_only_if {x α : Type _}
    {left right mid : x → α}
    {n : Nat} {s t smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    lengtht s + lengtht t ≤ n →
    (s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left) →
    s [[(right <==> mid)]]* smid →
    t [[(left <==> mid)]]* tmid →
    smid rest-tr Set.range mid = tmid rest-tr Set.range mid

axiom Renaming_channel_rest_tr_dist_if {x α : Type _}
    {left right mid : x → α}
    {n : Nat} {s t smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    lengtht s + lengtht t ≤ n →
    sett s ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    sett t ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    smid rest-tr Set.range mid = tmid rest-tr Set.range mid →
    s [[(right <==> mid)]]* smid →
    t [[(left <==> mid)]]* tmid →
    (s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left)

theorem Renaming_channel_rest_tr_dist {x α : Type _}
    {left right mid : x → α}
    {s t smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    sett s ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    sett t ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    s [[(right <==> mid)]]* smid →
    t [[(left <==> mid)]]* tmid →
    (((s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left)) ↔
      smid rest-tr Set.range mid = tmid rest-tr Set.range mid) := by
  intro hleft hmid hright hrm hlm hrl hs ht hsren htren
  constructor
  · intro hrest
    exact Renaming_channel_rest_tr_dist_only_if
      (left := left) (mid := mid) (right := right)
      (n := lengtht s + lengtht t)
      hleft hmid hright hrm hlm hrl (le_rfl) hrest hsren htren
  · intro hmidEq
    exact Renaming_channel_rest_tr_dist_if
      (left := left) (mid := mid) (right := right)
      (n := lengtht s + lengtht t)
      hleft hmid hright hrm hlm hrl (le_rfl) hs ht hmidEq hsren htren

/- ----------------- Renaming, rest-tr, dist ------------------- -/

theorem Renaming_channel_rest_tr_dist_only_if_EX {x α : Type _}
    {left right mid : x → α} {smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    (∃ s t,
      (s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left) ∧
      s [[(right <==> mid)]]* smid ∧
      t [[(left <==> mid)]]* tmid) →
    smid rest-tr Set.range mid = tmid rest-tr Set.range mid := by
  intro hleft hmid hright hrm hlm hrl h
  rcases h with ⟨s, t, hrest, hsren, htren⟩
  exact Renaming_channel_rest_tr_dist_only_if
    (left := left) (mid := mid) (right := right)
    (n := lengtht s + lengtht t)
    hleft hmid hright hrm hlm hrl (le_rfl) hrest hsren htren

/- ----------------- TRenaming and rest-tr ------------------- -/

axiom Renaming_channel_rest_tr_eq_n {x α : Type _} {f g : x → α}
    {n : Nat} {s t s' t' : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    lengtht s + lengtht t ≤ n →
    s rest-tr Set.range f = t rest-tr Set.range f →
    s [[(f <==> g)]]* s' →
    t [[(f <==> g)]]* t' →
    s' rest-tr Set.range g = t' rest-tr Set.range g

theorem Renaming_channel_rest_tr_eq_EX {x α : Type _} {f g : x → α}
    {s' t' : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    (∃ s t,
      s rest-tr Set.range f = t rest-tr Set.range f ∧
      s [[(f <==> g)]]* s' ∧
      t [[(f <==> g)]]* t') →
    s' rest-tr Set.range g = t' rest-tr Set.range g := by
  intro hf hg hfg h
  rcases h with ⟨s, t, hrest, hsren, htren⟩
  exact Renaming_channel_rest_tr_eq_n
    (f := f) (g := g)
    (n := lengtht s + lengtht t)
    hf hg hfg (le_rfl) hrest hsren htren
