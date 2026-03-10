           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Trace

open event

/-  Isabelle note: this theory locally removed `disj_not1` from the simp set. -/
/-  Lean's simplifier does not require an analogous change here.              -/

/- ********************************************************* -/

def «prefix» (s t : traceType α) : Prop :=
  ∃ u, t = s ^^^ u ∧ (noTick s ∨ u = <>)

theorem prefix_def {s t : traceType α} :
    «prefix» s t ↔ ∃ u, t = s ^^^ u ∧ (noTick s ∨ u = <>) :=
  Iff.rfl

def prefix_closed (T : Set (traceType α)) : Prop :=
  ∀ s t, (t ∈ T ∧ «prefix» s t) → s ∈ T

theorem prefix_closed_def {T : Set (traceType α)} :
    prefix_closed T ↔ ∀ s t, (t ∈ T ∧ «prefix» s t) → s ∈ T :=
  Iff.rfl

/- ***********************************************************
                       lemmas (prefix)
 *********************************************************** -/

theorem prefix_closed_iff {T : Set (traceType α)} {s t : traceType α} :
    t ∈ T → «prefix» s t → prefix_closed T → s ∈ T := by
  intro ht hp hT
  exact hT s t ⟨ht, hp⟩

/- (*** Prefix itself ***) -/

@[simp]
theorem prefix_itself {s : traceType α} : «prefix» s s := by
  refine ⟨<>, by simp, Or.inr rfl⟩

/- (*** Prefix appt ***) -/

@[simp]
theorem prefix_appt_simp {s t : traceType α} :
    (noTick s ∨ t = <>) → «prefix» s (s ^^^ t) := by
  intro h
  exact ⟨t, rfl, h⟩

theorem prefix_appt {s t u : traceType α} :
    (noTick t ∨ u = <>) → «prefix» s t → «prefix» s (t ^^^ u) := by
  intro htu hp
  rcases hp with ⟨ua, rfl, hs⟩
  rcases htu with ht | rfl
  · have hs' : noTick s := (decompo_appt_noTick_only_if hs ht).1
    have hua : noTick ua := (decompo_appt_noTick_only_if hs ht).2
    refine ⟨ua ^^^ u, ?_, Or.inl hs'⟩
    simp [appt_assoc hs (Or.inl hua)]
  · simpa using prefix_appt_simp (s := s) (t := ua) hs

/- (*** <> is a prefix of any trace ***) -/

@[simp]
theorem nil_is_prefix {s : traceType α} : «prefix» <> s := by
  refine ⟨s, by simp, Or.inl noTick_nil⟩

/- (*** the prefix of <> is <> ***) -/

@[simp]
theorem prefix_of_nil {s : traceType α} : «prefix» s <> ↔ s = <> := by
  constructor
  · rintro ⟨u, hEq, hs⟩
    rcases hs with hs | rfl
    · exact ((appt_nil hs).mp hEq.symm).1
    · simpa using hEq.symm
  · rintro rfl
    exact prefix_itself

/- (*** prefix of [a]t ***) -/

@[simp]
theorem prefix_of_one {s : traceType α} {a : event α} :
    «prefix» s (Abs_trace [a]) ↔ s = <> ∨ s = Abs_trace [a] := by
  constructor
  · rintro ⟨u, hEq, hs⟩
    rcases (appt_decompo_one (s := s) (t := u) (a := a) hs).mp hEq.symm with h | h
    · exact Or.inr h.1
    · exact Or.inl h.1
  · intro hs
    rcases hs with rfl | rfl
    · exact nil_is_prefix
    · exact prefix_itself

/- (*** length of prefix ***) -/

theorem length_of_prefix {s t : traceType α} :
    «prefix» s t → lengtht s ≤ lengtht t := by
  rintro ⟨u, rfl, hs⟩
  have hlen : lengtht (s ^^^ u) = lengtht s + lengtht u := lengtht_app_decompo1 hs
  omega

/- (*** prefix closed & prefix ***) -/

theorem prefix_closed_prop {T : Set (traceType α)} {s t : traceType α} :
    prefix_closed T → t ∈ T → «prefix» s t → s ∈ T := by
  intro hT ht hp
  exact hT s t ⟨ht, hp⟩

/- ***********************************************************
                   convenient lemmas
 *********************************************************** -/

/- (*** prefix a#v u ***) -/

theorem prefix_same_head_only_if {a : α} {v u : traceType α} :
    «prefix» (Abs_trace [Ev a] ^^^ v) u →
      ∃ u', u = Abs_trace [Ev a] ^^^ u' ∧ «prefix» v u' := by
  rintro ⟨ua, hEq, hpre⟩
  rcases hpre with huv | huaNil
  · have hv : noTick v := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) huv).2
    refine ⟨v ^^^ ua, ?_, ?_⟩
    · simpa [hEq] using appt_assoc (s := Abs_trace [Ev a]) (t := v) (u := ua)
        (Or.inl (noTick_Ev a)) (Or.inl hv)
    · exact prefix_appt_simp (s := v) (t := ua) (Or.inl hv)
  · refine ⟨v, ?_, prefix_itself⟩
    simpa [huaNil] using hEq

theorem prefix_same_head_if {a : α} {v u : traceType α} :
    (∃ u', u = Abs_trace [Ev a] ^^^ u' ∧ «prefix» v u') →
      «prefix» (Abs_trace [Ev a] ^^^ v) u := by
  rintro ⟨u', rfl, hp⟩
  rcases hp with ⟨ua, hu', hv⟩
  refine ⟨ua, ?_, ?_⟩
  · rcases hv with hv | rfl
    · simpa [hu'] using appt_assoc_sym (s := Abs_trace [Ev a]) (t := v) (u := ua)
        (Or.inl (noTick_Ev a)) (Or.inl hv)
    · simpa [hu']
  · rcases hv with hv | rfl
    · exact Or.inl (decompo_appt_noTick_if (noTick_Ev a) hv)
    · exact Or.inr rfl

@[simp]
theorem prefix_same_head {a : α} {v u : traceType α} :
    «prefix» (Abs_trace [Ev a] ^^^ v) u ↔
      ∃ u', u = Abs_trace [Ev a] ^^^ u' ∧ «prefix» v u' := by
  constructor
  · exact prefix_same_head_only_if
  · exact prefix_same_head_if

/- (*** prefix v a#u ***) -/

theorem prefix_same_head_inv_only_if {a : α} {v u : traceType α} :
    «prefix» v (Abs_trace [Ev a] ^^^ u) →
      v = <> ∨ ∃ v', v = Abs_trace [Ev a] ^^^ v' ∧ «prefix» v' u := by
  rintro ⟨ua, hEq, hpre⟩
  rcases trace_nil_or_Tick_or_Ev v with rfl | hvTick | ⟨b, v', hv⟩
  · exact Or.inl rfl
  · rcases hpre with hvNo | huaNil
    · exfalso
      simpa [hvTick] using hvNo
    · exfalso
      have hEq' : Abs_trace [Ev a] ^^^ u = Abs_trace [Tick] := by
        simpa [hvTick, huaNil] using hEq
      have hrep := congrArg Rep_trace hEq'
      simp [appt, Abs_trace_inverse] at hrep
  · rcases hpre with hvNo | huaNil
    · have hv' : noTick v' := by
        rw [hv] at hvNo
        exact (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hvNo).2
      have hAssoc : v ^^^ ua = Abs_trace [Ev b] ^^^ (v' ^^^ ua) := by
        rw [hv]
        exact appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hv')
      have hHead : Abs_trace [Ev a] ^^^ u = Abs_trace [Ev b] ^^^ (v' ^^^ ua) := by
        calc
          Abs_trace [Ev a] ^^^ u = v ^^^ ua := hEq
          _ = Abs_trace [Ev b] ^^^ (v' ^^^ ua) := hAssoc
      have hab : a = b ∧ u = v' ^^^ ua := (appt_same_head.mp hHead)
      refine Or.inr ?_
      refine ⟨v', ?_, ?_⟩
      · simpa [hv, hab.1]
      · exact ⟨ua, hab.2, Or.inl hv'⟩
    · have hHead : Abs_trace [Ev a] ^^^ u = Abs_trace [Ev b] ^^^ v' := by
        simpa [hv, huaNil] using hEq
      have hab : a = b ∧ u = v' := (appt_same_head.mp hHead)
      refine Or.inr ?_
      refine ⟨v', ?_, ?_⟩
      · simpa [hv, hab.1]
      · simpa [hab.2] using (prefix_itself : «prefix» v' v')

theorem prefix_same_head_inv_if {a : α} {v u : traceType α} :
    (v = <> ∨ ∃ v', v = Abs_trace [Ev a] ^^^ v' ∧ «prefix» v' u) →
      «prefix» v (Abs_trace [Ev a] ^^^ u) := by
  intro hv
  rcases hv with rfl | ⟨v', hv, hp⟩
  · exact nil_is_prefix
  · rw [hv]
    exact prefix_same_head_if ⟨u, rfl, hp⟩

@[simp]
theorem prefix_same_head_inv {a : α} {v u : traceType α} :
    «prefix» v (Abs_trace [Ev a] ^^^ u) ↔
      (v = <> ∨ ∃ v', v = Abs_trace [Ev a] ^^^ v' ∧ «prefix» v' u) := by
  constructor
  · exact prefix_same_head_inv_only_if
  · exact prefix_same_head_inv_if

/- (*** prefix v u#a ***) -/

theorem prefix_last_inv_only_if {e : event α} {u v : traceType α} :
    noTick u → «prefix» v (u ^^^ Abs_trace [e]) →
      (v = u ^^^ Abs_trace [e] ∨ «prefix» v u) := by
  intro hu
  rintro ⟨ua, hEq, hpre⟩
  rcases trace_last_nil_or_unnil ua with rfl | ⟨ua', a, hua', hua⟩
  · left
    simpa using hEq.symm
  · right
    have hv : noTick v := by
      rcases hpre with hv | huaNil
      · exact hv
      · exfalso
        have : ua' ^^^ Abs_trace [a] = <> := by
          simpa [hua] using huaNil
        exact event_app_not_nil_right hua' this
    have hAssoc : v ^^^ ua = (v ^^^ ua') ^^^ Abs_trace [a] := by
      rw [hua]
      exact appt_assoc_sym (Or.inl hv) (Or.inl hua')
    have hLast : u ^^^ Abs_trace [e] = (v ^^^ ua') ^^^ Abs_trace [a] := by
      calc
        u ^^^ Abs_trace [e] = v ^^^ ua := hEq
        _ = (v ^^^ ua') ^^^ Abs_trace [a] := hAssoc
    have huv : noTick (v ^^^ ua') := decompo_appt_noTick_if hv hua'
    have hEq' : u = v ^^^ ua' ∧ e = a := (appt_same_last hu huv).mp hLast
    exact ⟨ua', hEq'.1, Or.inl hv⟩

theorem prefix_last_inv_if {e : event α} {u v : traceType α} :
    noTick u → (v = u ^^^ Abs_trace [e] ∨ «prefix» v u) →
      «prefix» v (u ^^^ Abs_trace [e]) := by
  intro hu hv
  rcases hv with rfl | hp
  · exact prefix_itself
  · exact prefix_appt (s := v) (t := u) (u := Abs_trace [e]) (Or.inl hu) hp

@[simp]
theorem prefix_last_inv {e : event α} {u v : traceType α} :
    noTick u →
      («prefix» v (u ^^^ Abs_trace [e]) ↔ (v = u ^^^ Abs_trace [e] ∨ «prefix» v u)) := by
  intro hu
  constructor
  · exact prefix_last_inv_only_if hu
  · exact prefix_last_inv_if hu

/- *-------------------------*
 |          sett           |
 *-------------------------* -/

theorem prefix_subsett {s t : traceType α} :
    «prefix» s t → sett s ⊆ sett t := by
  rintro ⟨u, rfl, hs⟩ x hx
  rw [sett_appt1 hs]
  exact Or.inl hx

theorem prefix_noTick {s t : traceType α} :
    «prefix» s t → noTick t → noTick s := by
  intro hp ht hTick
  exact ht (prefix_subsett hp hTick)

/- *-------------------------*
 |         Tick            |
 *-------------------------* -/

theorem prefix_Tick {t : traceType α} :
    «prefix» (Abs_trace [Tick]) t ↔ t = Abs_trace [Tick] := by
  constructor
  · rintro ⟨u, hEq, hpre⟩
    rcases hpre with hTick | rfl
    · exfalso
      exact not_noTick_Tick hTick
    · simpa using hEq
  · rintro rfl
    exact prefix_itself
