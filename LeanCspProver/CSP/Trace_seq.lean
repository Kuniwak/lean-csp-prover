           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Prefix

open event

/-  Isabelle note: this theory locally removed `disj_not1` from the simp set. -/
/-  Lean's simplifier does not require an analogous change here.              -/

/- ***********************************************************

         1.
         2.
         3.
         4.

 *********************************************************** -/

noncomputable def rmTick (s : traceType α) : traceType α := by
  classical
  exact if noTick s then s else butlastt s

/- ***********************************************************
                  nil and Tick
 *********************************************************** -/

/- (*** noTick s --> rmTick s ***) -/

@[simp]
theorem rmTick_nochange {s : traceType α} : noTick s → rmTick s = s := by
  classical
  intro hs
  simp [rmTick, hs]

/- (*** rmTick <> ***) -/

@[simp]
theorem rmTick_nil : rmTick (<> : traceType α) = <> := by
  classical
  simp [rmTick]

/- (*** rmTick <Tick> ***) -/

@[simp]
theorem rmTick_Tick : rmTick (Abs_trace [Tick] : traceType α) = <> := by
  classical
  simp [rmTick, not_noTick_Tick]

/- (*** noTick rmTick s ***) -/

@[simp]
theorem noTick_rmTick {s : traceType α} : noTick (rmTick s) := by
  classical
  by_cases hs : noTick s
  · simpa [rmTick, hs] using hs
  · have hne : s ≠ <> := not_noTick_unnil hs
    simpa [rmTick, hs] using noTick_butlast (s := s) hne

theorem noTick_rmTickE {s t : traceType α} {R : Prop} :
    t = rmTick s → (noTick t → R) → R := by
  intro ht hR
  exact hR (by simpa [ht] using (noTick_rmTick (s := s)))

/- ***********************************************************
                           appt
 *********************************************************** -/

/- -------------------------*
 |       rmTick last       |
 *------------------------- -/

@[simp]
theorem rmTick_last_Tick {s : traceType α} :
    noTick s → rmTick (s ^^^ Abs_trace [Tick]) = s := by
  classical
  intro hs
  have hnot : ¬ noTick (s ^^^ Abs_trace [Tick]) := by
    intro hst
    have hTick : noTick (Abs_trace [Tick] : traceType α) := by
      exact (decompo_appt_noTick_only_if (s := s) (t := Abs_trace [Tick]) (Or.inl hs) hst).2
    exact not_noTick_Tick hTick
  unfold rmTick
  simp [hnot, butlastt_appt hs]

/- (*** noTick butlast ***) -/

theorem rmTick_butlastt {s : traceType α} :
    ¬ noTick s → rmTick s = butlastt s := by
  classical
  intro hs
  simp [rmTick, hs]

/- -------------------------*
 |   rmTick distribution   |
 *------------------------- -/

@[simp]
theorem rmTick_appt_dist {s t : traceType α} :
    noTick s → rmTick (s ^^^ t) = s ^^^ rmTick t := by
  classical
  intro hs
  by_cases ht : noTick t
  · have hst : noTick (s ^^^ t) := decompo_appt_noTick_if hs ht
    rw [rmTick_nochange hst, rmTick_nochange ht]
  · have htnil : t ≠ <> := not_noTick_unnil ht
    have hbut : noTick (butlastt t) := noTick_butlast (s := t) htnil
    have htEq : t = butlastt t ^^^ (Abs_trace [Tick] : traceType α) := Tick_decompo ht
    have hst : noTick (s ^^^ butlastt t) := decompo_appt_noTick_if hs hbut
    have hassoc :
        s ^^^ (butlastt t ^^^ (Abs_trace [Tick] : traceType α)) =
          (s ^^^ butlastt t) ^^^ (Abs_trace [Tick] : traceType α) := by
      exact appt_assoc_sym (Or.inl hs) (Or.inl hbut)
    have hleft : rmTick (s ^^^ t) = rmTick ((s ^^^ butlastt t) ^^^ (Abs_trace [Tick] : traceType α)) := by
      have hstep1 : rmTick (s ^^^ t) = rmTick (s ^^^ (butlastt t ^^^ (Abs_trace [Tick] : traceType α))) := by
        exact congrArg rmTick (congrArg (fun x => s ^^^ x) htEq)
      have hstep2 :
          rmTick (s ^^^ (butlastt t ^^^ (Abs_trace [Tick] : traceType α))) =
            rmTick ((s ^^^ butlastt t) ^^^ (Abs_trace [Tick] : traceType α)) := by
        exact congrArg rmTick hassoc
      exact hstep1.trans hstep2
    calc
      rmTick (s ^^^ t)
          = rmTick ((s ^^^ butlastt t) ^^^ (Abs_trace [Tick] : traceType α)) := hleft
      _ = s ^^^ butlastt t := by
            exact rmTick_last_Tick hst
      _ = s ^^^ rmTick t := by
            rw [rmTick_butlastt ht]

/- ***********************************************************
                        prefix
 *********************************************************** -/

/- (*** rmTick prefix ***) -/

/- only if -/

theorem rmTick_prefix_only_if {s t : traceType α} :
    «prefix» s (rmTick t) → ∃ u, «prefix» u t ∧ s = rmTick u := by
  classical
  intro hp
  by_cases ht : noTick t
  · refine ⟨s, ?_, ?_⟩
    · simpa [rmTick, ht] using hp
    · have hs : noTick s := prefix_noTick (by simpa [rmTick, ht] using hp) ht
      simpa using (rmTick_nochange (s := s) hs).symm
  · have htnil : t ≠ <> := not_noTick_unnil ht
    have hbut : noTick (butlastt t) := noTick_butlast (s := t) htnil
    have htEq : t = butlastt t ^^^ (Abs_trace [Tick] : traceType α) := Tick_decompo ht
    have hp' : «prefix» s (butlastt t) := by
      simpa [rmTick, ht] using hp
    have hpt : «prefix» s t := by
      rw [htEq]
      exact prefix_appt (s := s) (t := butlastt t) (u := Abs_trace [Tick]) (Or.inl hbut) hp'
    refine ⟨s, hpt, ?_⟩
    have hs : noTick s := prefix_noTick hp' hbut
    simpa using (rmTick_nochange (s := s) hs).symm

/- if -/

theorem rmTick_prefix_if {s t : traceType α} :
    (∃ u, «prefix» u t ∧ s = rmTick u) → «prefix» s (rmTick t) := by
  classical
  rintro ⟨u, hu, hs⟩
  by_cases ht : noTick t
  · have huNo : noTick u := prefix_noTick hu ht
    have hs' : s = u := by
      calc
        s = rmTick u := hs
        _ = u := rmTick_nochange huNo
    simpa [rmTick, ht, hs'] using hu
  · have htnil : t ≠ <> := not_noTick_unnil ht
    have hbut : noTick (butlastt t) := noTick_butlast (s := t) htnil
    have htEq : t = butlastt t ^^^ (Abs_trace [Tick] : traceType α) := Tick_decompo ht
    have hu' : u = butlastt t ^^^ (Abs_trace [Tick] : traceType α) ∨ «prefix» u (butlastt t) := by
      rw [htEq] at hu
      exact (prefix_last_inv hbut).mp hu
    have hgoal : «prefix» s (butlastt t) := by
      rcases hu' with rfl | hup
      · have hs' : s = butlastt t := by
          calc
            s = rmTick (butlastt t ^^^ (Abs_trace [Tick] : traceType α)) := by simpa using hs
            _ = butlastt t := rmTick_last_Tick hbut
        simpa [hs'] using (prefix_itself : «prefix» (butlastt t) (butlastt t))
      · have huNo : noTick u := prefix_noTick hup hbut
        have hs' : s = u := by
          calc
            s = rmTick u := hs
            _ = u := rmTick_nochange huNo
        simpa [hs'] using hup
    simpa [rmTick, ht] using hgoal

/- iff -/

theorem rmTick_prefix {s t : traceType α} :
    «prefix» s (rmTick t) ↔ ∃ u, «prefix» u t ∧ s = rmTick u := by
  constructor
  · exact rmTick_prefix_only_if
  · exact rmTick_prefix_if

/- --------------*
 |   reverse    |
 *-------------- -/

theorem rmTick_prefix_rev {s t : traceType α} : «prefix» s t → «prefix» (rmTick s) t := by
  classical
  intro hp
  by_cases hs : noTick s
  · simpa [rmTick, hs] using hp
  · have hsnil : s ≠ <> := not_noTick_unnil hs
    have hbut : noTick (butlastt s) := noTick_butlast (s := s) hsnil
    have hsEq : s = butlastt s ^^^ (Abs_trace [Tick] : traceType α) := Tick_decompo hs
    have hp0 : «prefix» (butlastt s) s := by
      exact ⟨(Abs_trace [Tick] : traceType α), hsEq, Or.inl hbut⟩
    rcases hp with ⟨u, htEq, hsu⟩
    have hp1 : «prefix» (butlastt s) (s ^^^ u) := prefix_appt (s := butlastt s) (t := s) (u := u) hsu hp0
    simpa [rmTick, hs, htEq] using hp1

@[simp]
theorem rmTick_prefix_rev_simp {s : traceType α} : «prefix» (rmTick s) s := by
  exact rmTick_prefix_rev (s := s) (t := s) prefix_itself
