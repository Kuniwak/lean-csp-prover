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
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra

open Classical

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `(notick \/ t = <>)`.          -/

/- ***********************************************************

    Type Definitions
      'a event      : type of events      a,b,...
      'a trace      : type of traces      s,t,...

 *********************************************************** -/

inductive event (α : Type u) where
  | Ev : α → event α
  | Tick : event α
deriving DecidableEq

open event

def Evset : Set (event α) := {a | a ≠ Tick}

def EvsetTick : Set (event α) := Set.univ

/- EvsetTick seems to be useless, but it sometimes -/
/- makes proofs to be readable.                    -/

/- *******************************
    Evset contains all (Ev a)
 ******************************* -/

@[simp]
theorem Un_Evset {X : Set α} : Ev '' X ∪ Evset = (Evset : Set (event α)) := by
  ext e
  constructor
  · intro he
    simp [Evset] at *
    rcases he with ⟨a, _, rfl⟩ | he
    · simp
    · exact he
  · intro he
    simp [Evset] at he
    exact Or.inr he

/- *******************************
         Tick or Ev a
 ******************************* -/

theorem event_Tick_or_Ev : ∀ e : event α, e = Tick ∨ ∃ a, e = Ev a := by
  intro e
  cases e with
  | Tick => exact Or.inl rfl
  | Ev a => exact Or.inr ⟨a, rfl⟩

theorem not_Tick_to_Ev {e : event α} : (e ≠ Tick) ↔ ∃ a, e = Ev a := by
  constructor
  · intro h
    rcases event_Tick_or_Ev e with rfl | hEv
    · contradiction
    · exact hEv
  · rintro ⟨a, rfl⟩ h
    cases h

theorem in_Ev_set {e : event α} {X : Set α} : (e ∈ Ev '' X) ↔ ∃ a, e = Ev a ∧ a ∈ X := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  · rintro ⟨a, rfl, ha⟩
    exact ⟨a, ha, rfl⟩

theorem notin_Ev_set {e : event α} {X : Set α} :
    (e ∉ Ev '' X) ↔ e = Tick ∨ ∃ a, e = Ev a ∧ a ∉ X := by
  constructor
  · intro he
    rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a, rfl, fun ha => he ⟨a, ha, rfl⟩⟩
  · intro h he
    rcases h with rfl | ⟨a, rfl, ha⟩
    · rcases he with ⟨x, _, hx⟩
      cases hx
    · exact ha (by simpa using he)

/- *******************************
             inj
 ******************************* -/

@[simp]
theorem inj_Ev : Function.Injective (@Ev α) := by
  intro a b h
  cases h
  rfl

/- ***********************************************************
                    Definition of traces
 *********************************************************** -/

def trace : Set (List (event α)) := {ss | Tick ∉ set (butlast ss)}

abbrev traceType (α : Type u) := {ss : List (event α) // ss ∈ trace (α := α)}

def Rep_trace (s : traceType α) : List (event α) := s.1

noncomputable def Abs_trace (s : List (event α)) : traceType α :=
  if h : s ∈ trace (α := α) then ⟨s, h⟩ else ⟨[], by simp [trace]⟩

@[simp]
theorem Rep_trace_mk {s : List (event α)} {h : s ∈ trace (α := α)} :
    Rep_trace (Subtype.mk s h : traceType α) = s := rfl

@[simp]
theorem Abs_trace_inverse {s : List (event α)} (hs : s ∈ trace (α := α)) :
    Rep_trace (Abs_trace s) = s := by
  simp [Abs_trace, hs]

@[simp]
theorem Rep_trace_inverse (s : traceType α) : Abs_trace (Rep_trace s) = s := by
  cases s with
  | mk s hs =>
      simp [Abs_trace, hs]

theorem Abs_trace_inject {s t : List (event α)}
    (hs : s ∈ trace (α := α)) (ht : t ∈ trace (α := α)) :
    (Abs_trace s = Abs_trace t) ↔ s = t := by
  constructor
  · intro h
    simpa [Abs_trace_inverse hs, Abs_trace_inverse ht] using congrArg Rep_trace h
  · intro h
    subst h
    rfl

theorem Rep_trace_inject {s t : traceType α} : (Rep_trace s = Rep_trace t) ↔ s = t := by
  constructor
  · intro h
    cases s
    cases t
    cases h
    rfl
  · intro h
    cases h
    rfl

theorem Abs_trace_eq_of_mem {s : List (event α)} (hs : s ∈ trace (α := α)) :
    Abs_trace s = Subtype.mk s hs := by
  simp [Abs_trace, hs]

theorem Abs_trace_eq_nil_of_not_mem {s : List (event α)} (hs : s ∉ trace (α := α)) :
    Abs_trace s = (Subtype.mk [] (by simp [trace]) : traceType α) := by
  simp [Abs_trace, hs]

/- *****************************************************************
            directly convert from list to trace
 ***************************************************************** -/

/- *********************************************************** -/
/-                  operators over traces                  -/
/-                                                         -/
/-    memo    (infixr "@t" 65) = ("_ @t _" [66,65] 65)     -/
/-                                                         -/
/- *********************************************************** -/

noncomputable def nilt : traceType α := Abs_trace []

notation "<>" => nilt

def sett (s : traceType α) : Set (event α) := set (Rep_trace s)

def lengtht (s : traceType α) : Nat := (Rep_trace s).length

def noTick (s : traceType α) : Prop := Tick ∉ sett s

def hdt (s : traceType α) : event α :=
  match Rep_trace s with
  | [] => Tick
  | e :: _ => e

noncomputable def tlt (s : traceType α) : traceType α := Abs_trace (tl (Rep_trace s))

def lastt (s : traceType α) : event α :=
  match Rep_trace s with
  | [] => Tick
  | e :: es => (e :: es).getLast (by simp)

noncomputable def butlastt (s : traceType α) : traceType α := Abs_trace (butlast (Rep_trace s))

syntax "<" term,* ">" : term

macro_rules
  | `(<$xs,*>) => `(Abs_trace [$xs,*])

inductive TraceChk where
  | tr_nil
  | tr_noTick
  | tr_Tick
  | tr_error
deriving DecidableEq

noncomputable def appt (s t : traceType α) : traceType α := Abs_trace (Rep_trace s ++ Rep_trace t)

infixr:65 " ^^^ " => appt

/- ***********************************************************
                          lemmas
 *********************************************************** -/

/- ***************************************
         trace Rep and Abs lemmas
 *************************************** -/

/- *** Abs-Rep *** -/

theorem Abs_trace_Rep_trace_inverse_left {t : List (event α)} {s : traceType α} :
    t ∈ trace (α := α) → ((Abs_trace t = s) ↔ t = Rep_trace s) := by
  intro ht
  constructor
  · intro h
    simpa [Abs_trace_inverse ht] using congrArg Rep_trace h
  · intro h
    subst h
    exact Rep_trace_inverse s

theorem Abs_trace_Rep_trace_inverse_right {t : List (event α)} {s : traceType α} :
    t ∈ trace (α := α) → ((s = Abs_trace t) ↔ t = Rep_trace s) := by
  intro ht
  constructor
  · intro h
    simpa [Abs_trace_inverse ht] using congrArg Rep_trace h.symm
  · intro h
    subst h
    exact (Rep_trace_inverse s).symm

/- *** Rep-Abs *** -/

theorem Rep_trace_Abs_trace_inverse_left_only_if {t : traceType α} {s : List (event α)} :
    Rep_trace t = s → t = Abs_trace s := by
  intro h
  subst h
  exact (Rep_trace_inverse t).symm

theorem Rep_trace_Abs_trace_inverse_right_only_if {t : traceType α} {s : List (event α)} :
    s = Rep_trace t → t = Abs_trace s := by
  intro h
  subst h
  exact (Rep_trace_inverse t).symm

/- *** Abs image *** -/

theorem Abs_trace_inverse_in_only_if {X : Set (List (event α))} {t : traceType α} :
    (∀ s ∈ X, s ∈ trace (α := α)) → t ∈ Abs_trace '' X → Rep_trace t ∈ X := by
  intro hX ht
  rcases ht with ⟨x, hxX, hEq⟩
  have hxtr : x ∈ trace (α := α) := hX x hxX
  have hrep : x = Rep_trace t := by
    simpa [Abs_trace_inverse hxtr] using congrArg Rep_trace hEq
  simpa [hrep] using hxX

theorem Abs_trace_inverse_in_if {X : Set (List (event α))} {t : traceType α} :
    Rep_trace t ∈ X → t ∈ Abs_trace '' X := by
  intro ht
  exact ⟨Rep_trace t, ht, Rep_trace_inverse t⟩

theorem Abs_trace_inverse_in {X : Set (List (event α))} {t : traceType α} :
    (∀ s ∈ X, s ∈ trace (α := α)) →
      (t ∈ Abs_trace '' X ↔ Rep_trace t ∈ X) := by
  intro hX
  constructor
  · exact Abs_trace_inverse_in_only_if hX
  · exact Abs_trace_inverse_in_if

/- *******************************
         check in trace
 ******************************* -/

@[simp]
theorem nil_in_trace : ([] : List (event α)) ∈ trace (α := α) := by
  simp [trace]

@[simp]
theorem event_in_trace (a : event α) : ([a] : List (event α)) ∈ trace (α := α) := by
  simp [trace]

theorem notic_in_trace {s : List (event α)} : Tick ∉ set s → s ∈ trace (α := α) := by
  intro hs
  exact fun h => hs (in_set_butlast h)

/- --------------------------*
 |        decompo app       |
 *-------------------------- -/

theorem decompo_app_in_trace_only_if1 {s t : List (event α)} :
    s ++ t ∈ trace (α := α) → s ∈ trace (α := α) := by
  intro h
  simp [trace] at h ⊢
  have := (notin_butlast_decompo (e := Tick) (s := s) (t := t)).mp h
  rcases this with h' | h'
  · exact notin_set_butlast h'.1
  · exact h'.1

theorem decompo_app_in_trace_only_if2 {s t : List (event α)} :
    s ++ t ∈ trace (α := α) → t ∈ trace (α := α) := by
  intro h
  simp [trace] at h ⊢
  have := (notin_butlast_decompo (e := Tick) (s := s) (t := t)).mp h
  rcases this with h' | h'
  · exact h'.2
  · simpa [h'.2] using h'.1

theorem decompo_app_in_trace_only_if {s t : List (event α)} :
    s ++ t ∈ trace (α := α) →
      (s ∈ trace (α := α) ∧ t = []) ∨ (Tick ∉ set s ∧ t ∈ trace (α := α)) := by
  intro h
  rcases list_last_nil_or_unnil t with rfl | ⟨sa, a, rfl⟩
  · exact Or.inl ⟨decompo_app_in_trace_only_if1 h, rfl⟩
  · right
    constructor
    · have htrace : Tick ∉ set (butlast (s ++ (sa ++ [a]))) := by
        simpa [trace] using h
      have hdecomp :=
        (notin_butlast_decompo (e := Tick) (s := s) (t := sa ++ [a])).mp htrace
      rcases hdecomp with hnt | hnil
      · exact hnt.1
      · exfalso
        simpa using hnil.2
    · exact decompo_app_in_trace_only_if2 h

theorem decompo_app_in_trace_if {s t : List (event α)} :
    Tick ∉ set s → t ∈ trace (α := α) → s ++ t ∈ trace (α := α) := by
  intro hs ht
  simp [trace]
  exact (notin_butlast_decompo (e := Tick) (s := s) (t := t)).2 <| Or.inl ⟨hs, by simpa [trace] using ht⟩

theorem decompo_app_in_trace {s t : List (event α)} :
    (s ++ t ∈ trace (α := α)) ↔
      ((s ∈ trace (α := α) ∧ t = []) ∨ (Tick ∉ set s ∧ t ∈ trace (α := α))) := by
  constructor
  · exact decompo_app_in_trace_only_if
  · rintro (⟨hs, rfl⟩ | ⟨hs, ht⟩)
    · simpa using hs
    · exact decompo_app_in_trace_if hs ht

theorem decompo_appt_in_traceE {s t : List (event α)} {R : Prop} :
    s ++ t ∈ trace (α := α) →
      (s ++ t ∈ trace (α := α) → s ∈ trace (α := α) → t ∈ trace (α := α) → R) → R := by
  intro h hR
  exact hR h (decompo_app_in_trace_only_if1 h) (decompo_app_in_trace_only_if2 h)

/- --------------------------*
 |       decompo cons       |
 *-------------------------- -/

theorem decompo_head_in_trace_if {a : event α} {t : List (event α)} :
    a ≠ Tick → t ∈ trace (α := α) → a :: t ∈ trace (α := α) := by
  intro ha ht
  have hs : Tick ∉ set [a] := by
    intro hTick
    have : Tick = a := by simpa [_root_.set] using hTick
    exact ha this.symm
  simpa using decompo_app_in_trace_if (s := [a]) (t := t) hs ht

theorem decompo_head_in_trace {a : event α} {t : List (event α)} :
    (a :: t ∈ trace (α := α)) ↔ (t = [] ∨ (a ≠ Tick ∧ t ∈ trace (α := α))) := by
  constructor
  · intro h
    have happ : [a] ++ t ∈ trace (α := α) := by simpa using h
    rcases (decompo_app_in_trace (s := [a]) (t := t)).mp happ with hnil | hrest
    · exact Or.inl hnil.2
    · refine Or.inr ?_
      refine ⟨?_, hrest.2⟩
      intro hEq
      apply hrest.1
      simpa [_root_.set, hEq]
  · rintro (rfl | ⟨ha, ht⟩)
    · simpa using event_in_trace a
    · exact decompo_head_in_trace_if ha ht

theorem decompo_last_in_trace_if {s : List (event α)} {a : event α} :
    Tick ∉ set s → s ++ [a] ∈ trace (α := α) := by
  intro hs
  simpa using decompo_app_in_trace_if (s := s) (t := [a]) hs (event_in_trace a)

theorem decompo_last_in_trace {s : List (event α)} {a : event α} :
    (s ++ [a] ∈ trace (α := α)) ↔ Tick ∉ set s := by
  have := decompo_app_in_trace (s := s) (t := [a])
  simpa using this

/- --------------------------*
 |        app not in        |
 *-------------------------- -/

theorem app_notin_trace_left {s t : List (event α)} :
    s ∉ trace (α := α) → t ++ s ∉ trace (α := α) := by
  intro hs hts
  exact hs (decompo_app_in_trace_only_if2 hts)

theorem app_notin_trace_right {s t : List (event α)} :
    s ∉ trace (α := α) → s ++ t ∉ trace (α := α) := by
  intro hs hst
  exact hs (decompo_app_in_trace_only_if1 hst)

/- *******************************
            Tick
 ******************************* -/

theorem Tick_is_last {s : List (event α)} : Tick :: s ∈ trace (α := α) → s = [] := by
  intro h
  simpa using (decompo_head_in_trace.mp h)

/- *******************************
             Nil
 ******************************* -/

@[simp]
theorem one_neq_nil {a : event α} : (Abs_trace [a] : traceType α) ≠ <> := by
  intro h
  have := congrArg Rep_trace h
  simp [nilt, Abs_trace_inverse] at this

@[simp]
theorem one_neq_nil_sym {a : event α} : (<> : traceType α) ≠ Abs_trace [a] := by
  intro h
  exact one_neq_nil (a := a) h.symm

/- *******************************
           noTick
 ******************************* -/

@[simp]
theorem noTick_Ev (a : α) : noTick (Abs_trace [Ev a] : traceType α) := by
  intro hTick
  have : Tick = Ev a := by
    simpa [noTick, sett, Abs_trace_inverse, _root_.set] using hTick
  cases this

theorem noTick_EvI {e : event α} : (∃ a, e = Ev a) → noTick (Abs_trace [e] : traceType α) := by
  rintro ⟨a, rfl⟩
  simpa using noTick_Ev a

@[simp]
theorem noTick_nil : noTick (<> : traceType α) := by
  simp [noTick, sett, nilt, Abs_trace_inverse]

@[simp]
theorem not_noTick_Tick : ¬ noTick (Abs_trace [Tick] : traceType α) := by
  intro h
  exact h (by simp [sett, Abs_trace_inverse, _root_.set])

/- *******************************
            Event
 ******************************* -/

@[simp]
theorem Event_eq {e1 e2 : event α} :
    ((Abs_trace [e1] : traceType α) = Abs_trace [e2]) ↔ e1 = e2 := by
  simpa [Abs_trace_inject (event_in_trace e1) (event_in_trace e2)]

/- ***********************************************************
                   @ in trace
 *********************************************************** -/

/- ---------------------------------------------*
 |         Rep_trace s @ Rep_trace t           |
 *--------------------------------------------- -/

/- --------------------------*
 |       rep in_trace       |
 *-------------------------- -/

@[simp]
theorem Rep_compo_head_in_trace {a : α} {t : traceType α} :
    Ev a :: Rep_trace t ∈ trace (α := α) := by
  exact decompo_head_in_trace_if (by simp) t.2

@[simp]
theorem Rep_compo_last_in_trace {t : traceType α} {e : event α} :
    noTick t → Rep_trace t ++ [e] ∈ trace (α := α) := by
  intro ht
  exact decompo_last_in_trace_if (by simpa [noTick, sett] using ht)

@[simp]
theorem Rep_compo_app_in_trace {s t : traceType α} :
    (noTick s ∨ t = <>) → Rep_trace s ++ Rep_trace t ∈ trace (α := α) := by
  intro h
  rcases h with hs | rfl
  · exact decompo_app_in_trace_if (by simpa [noTick, sett] using hs) t.2
  · simpa [nilt, Abs_trace_inverse] using (show Rep_trace s ∈ trace (α := α) from s.2)

theorem decompo_apprep_in_traceI {s t : traceType α} :
    Rep_trace s ++ Rep_trace t ∈ trace (α := α) → (noTick s ∨ t = <>) := by
  intro h
  rcases decompo_app_in_trace.mp h with hst | hst
  · right
    apply (Rep_trace_inject).mp
    simp [nilt, Abs_trace_inverse, hst.2]
  · left
    simpa [noTick, sett] using hst.1

theorem decompo_apprep_in_trace {s t : traceType α} :
    (Rep_trace s ++ Rep_trace t ∈ trace (α := α)) ↔ (noTick s ∨ t = <>) := by
  constructor
  · exact decompo_apprep_in_traceI
  · exact Rep_compo_app_in_trace

theorem decompo_apprep_notin_traceI {s t : traceType α} :
    Rep_trace s ++ Rep_trace t ∉ trace (α := α) → (¬ noTick s ∧ t ≠ <>) := by
  intro h
  have hnot : ¬ (noTick s ∨ t = <>) := by
    intro h'
    exact h (Rep_compo_app_in_trace (s := s) (t := t) h')
  constructor
  · intro hs
    exact hnot (Or.inl hs)
  · intro ht
    exact hnot (Or.inr ht)

theorem decompo_apprep_in_traceE {s t : traceType α} {R : Prop} :
    Rep_trace s ++ Rep_trace t ∈ trace (α := α) →
      (noTick s ∨ t = <> → R) → R := by
  intro h hR
  exact hR (decompo_apprep_in_trace.mp h)

theorem decompo_apprep_notin_traceE {s t : traceType α} {R : Prop} :
    Rep_trace s ++ Rep_trace t ∉ trace (α := α) →
      (¬ noTick s → t ≠ <> → R) → R := by
  intro h hR
  exact hR (decompo_apprep_notin_traceI h).1 (decompo_apprep_notin_traceI h).2

/- ***********************************************************
                  lemmas for s ^^^ t
 *********************************************************** -/

/- -----------------------------*
 | Abs_trace distribution on @ |
 *----------------------------- -/

theorem Abs_trace_app_dist {s t : List (event α)} :
    s ++ t ∈ trace (α := α) → Abs_trace s ^^^ Abs_trace t = Abs_trace (s ++ t) := by
  intro h
  have hs : s ∈ trace (α := α) := decompo_app_in_trace_only_if1 h
  have ht : t ∈ trace (α := α) := decompo_app_in_trace_only_if2 h
  apply (Rep_trace_inject).mp
  simp [appt, Abs_trace_inverse, h, hs, ht]

/- --------------------------*
 |       append head        |
 *-------------------------- -/

theorem appt_head {a : event α} {s : traceType α} :
    Abs_trace [a] ^^^ s = Abs_trace (a :: Rep_trace s) := by
  apply (Rep_trace_inject).mp
  simp [appt, Abs_trace_inverse, Rep_compo_head_in_trace]

/- --------------------------*
 |       append last        |
 *-------------------------- -/

theorem appt_last {t : traceType α} {e : event α} :
    noTick t → t ^^^ Abs_trace [e] = Abs_trace (Rep_trace t ++ [e]) := by
  intro ht
  apply (Rep_trace_inject).mp
  simp [appt, Abs_trace_inverse, Rep_compo_last_in_trace ht]

/- ***********************************************************
                  lemmas for s ^^^ t
 *********************************************************** -/

@[simp]
theorem appt_nil_left {s : traceType α} : <> ^^^ s = s := by
  apply (Rep_trace_inject).mp
  simp [appt, nilt, Abs_trace_inverse]

@[simp]
theorem appt_nil_right {s : traceType α} : s ^^^ <> = s := by
  apply (Rep_trace_inject).mp
  simp [appt, nilt, Abs_trace_inverse]

@[simp]
theorem event_app_not_nil_left {a : α} {s : traceType α} :
    Abs_trace [Ev a] ^^^ s ≠ <> := by
  intro h
  have := congrArg Rep_trace h
  simp [appt, nilt, Abs_trace_inverse, Rep_compo_head_in_trace] at this

@[simp]
theorem event_app_not_nil_right {s : traceType α} {e : event α} :
    noTick s → s ^^^ Abs_trace [e] ≠ <> := by
  intro hs h
  have := congrArg Rep_trace h
  simp [appt, nilt, Abs_trace_inverse, Rep_compo_last_in_trace hs] at this

/- --------------------------*
 |   associativity of ^^^    |
 *-------------------------- -/

theorem appt_assoc {s t u : traceType α} :
    (noTick s ∨ t = <>) → (noTick t ∨ u = <>) →
      (s ^^^ t) ^^^ u = s ^^^ (t ^^^ u) := by
  intro hs ht
  rcases hs with hs | rfl
  · rcases ht with ht | rfl
    · have hst : Rep_trace s ++ Rep_trace t ∈ trace (α := α) := Rep_compo_app_in_trace (Or.inl hs)
      have htu : Rep_trace t ++ Rep_trace u ∈ trace (α := α) := Rep_compo_app_in_trace (Or.inl ht)
      have hstNo : noTick (s ^^^ t) := by
        intro hTick
        have hmem : Tick ∈ set (Rep_trace s ++ Rep_trace t) := by
          simpa [noTick, sett, appt, Abs_trace_inverse, hst, _root_.set] using hTick
        have hmem' : Tick ∈ set (Rep_trace s) ∨ Tick ∈ set (Rep_trace t) := by
          simpa [_root_.set] using hmem
        rcases hmem' with hs' | ht'
        · exact hs hs'
        · exact ht ht'
      have hsu : Rep_trace (s ^^^ t) ++ Rep_trace u ∈ trace (α := α) :=
        Rep_compo_app_in_trace (Or.inl hstNo)
      have htsu : Rep_trace s ++ Rep_trace (t ^^^ u) ∈ trace (α := α) :=
        Rep_compo_app_in_trace (Or.inl hs)
      apply (Rep_trace_inject).mp
      simp [appt, Abs_trace_inverse, hst, htu, hsu, htsu, List.append_assoc]
    · simp
  · simp

theorem appt_assoc_sym {s t u : traceType α} :
    (noTick s ∨ t = <>) → (noTick t ∨ u = <>) →
      s ^^^ (t ^^^ u) = (s ^^^ t) ^^^ u := by
  intro hs ht
  exact (appt_assoc hs ht).symm

@[simp]
theorem appt_nil {s t : traceType α} :
    noTick s → ((s ^^^ t = <>) ↔ (s = <> ∧ t = <>)) := by
  intro hs
  constructor
  · intro h
    have hvalid : Rep_trace s ++ Rep_trace t ∈ trace (α := α) :=
      Rep_compo_app_in_trace (Or.inl hs)
    have hrep : Rep_trace s ++ Rep_trace t = [] := by
      simpa [appt, nilt, Abs_trace_inverse, hvalid] using congrArg Rep_trace h
    rcases List.append_eq_nil_iff.mp hrep with ⟨hsnil, htnil⟩
    constructor
    · apply (Rep_trace_inject).mp
      simpa [nilt, Abs_trace_inverse] using hsnil
    · apply (Rep_trace_inject).mp
      simpa [nilt, Abs_trace_inverse] using htnil
  · rintro ⟨rfl, rfl⟩
    simp

@[simp]
theorem appt_nil_sym {s t : traceType α} :
    noTick s → (((<> : traceType α) = s ^^^ t) ↔ (s = <> ∧ t = <>)) := by
  intro hs
  constructor
  · intro h
    exact (appt_nil hs).mp h.symm
  · intro h
    exact ((appt_nil hs).mpr h).symm

/- --------------------------*
 |         length           |
 *-------------------------- -/

@[simp]
theorem lengtht_nil_zero : lengtht (<> : traceType α) = 0 := by
  simp [lengtht, nilt, Abs_trace_inverse]

@[simp]
theorem lengtht_one_event {e : event α} : lengtht (Abs_trace [e] : traceType α) = 1 := by
  simp [lengtht, Abs_trace_inverse]

@[simp]
theorem lengtht_app_event_Suc_last {s : traceType α} {a : event α} :
    noTick s → lengtht (s ^^^ Abs_trace [a]) = Nat.succ (lengtht s) := by
  intro hs
  simp [lengtht, appt, Abs_trace_inverse, Rep_compo_last_in_trace hs]

@[simp]
theorem lengtht_app_event_Suc_head {s : traceType α} {a : α} :
    lengtht (Abs_trace [Ev a] ^^^ s) = Nat.succ (lengtht s) := by
  simp [lengtht, appt, Abs_trace_inverse, Rep_compo_head_in_trace]

@[simp]
theorem lengtht_app_decompo1 {s t : traceType α} :
    (noTick s ∨ t = <>) → lengtht (s ^^^ t) = lengtht s + lengtht t := by
  intro h
  simp [lengtht, appt, Abs_trace_inverse, Rep_compo_app_in_trace h, List.length_append]

@[simp]
theorem lengtht_app_decompo2 {s t : traceType α} :
    Rep_trace s ++ Rep_trace t ∈ trace (α := α) → lengtht (s ^^^ t) = lengtht s + lengtht t := by
  intro h
  simp [lengtht, appt, Abs_trace_inverse, h, List.length_append]

/- ---------------------------*
 |           sett            |
 *--------------------------- -/

@[simp]
theorem sett_nil : sett (<> : traceType α) = ∅ := by
  ext x
  simp [sett, nilt, Abs_trace_inverse, _root_.set]

@[simp]
theorem sett_one {e : event α} : sett (Abs_trace [e] : traceType α) = {e} := by
  ext x
  simp [sett, Abs_trace_inverse, _root_.set]

@[simp]
theorem sett_appt1 {s t : traceType α} :
    (noTick s ∨ t = <>) → sett (s ^^^ t) = sett s ∪ sett t := by
  intro h
  ext x
  simp [sett, appt, Abs_trace_inverse, Rep_compo_app_in_trace h, _root_.set]

@[simp]
theorem sett_appt2 {s t : traceType α} :
    Rep_trace s ++ Rep_trace t ∈ trace (α := α) → sett (s ^^^ t) = sett s ∪ sett t := by
  intro h
  ext x
  simp [sett, appt, Abs_trace_inverse, h, _root_.set]

/- ---------------------------*
 |     decompo appt Tick     |
 *--------------------------- -/

theorem decompo_appt_noTick_only_if {s t : traceType α} :
    (noTick s ∨ t = <>) → noTick (s ^^^ t) → (noTick s ∧ noTick t) := by
  intro h hst
  rcases h with hs | rfl
  · constructor
    · exact hs
    · intro hx
      apply hst
      rw [sett_appt1 (s := s) (t := t) (Or.inl hs)]
      exact Or.inr hx
  · simp at hst
    exact ⟨by simpa using hst, noTick_nil⟩

theorem decompo_appt_noTick_if {s t : traceType α} :
    noTick s → noTick t → noTick (s ^^^ t) := by
  intro hs ht
  intro hTick
  rw [sett_appt1 (s := s) (t := t) (Or.inl hs)] at hTick
  rcases hTick with hs' | ht'
  · exact hs hs'
  · exact ht ht'

@[simp]
theorem decompo_appt_noTick {s t : traceType α} :
    (noTick s ∨ t = <>) → (noTick (s ^^^ t) ↔ (noTick s ∧ noTick t)) := by
  intro h
  constructor
  · exact decompo_appt_noTick_only_if h
  · rintro ⟨hs, ht⟩
    exact decompo_appt_noTick_if hs ht

/- ******************************************************************
                        head and tail
 ****************************************************************** -/

theorem tlt_trace {s : List (event α)} :
    s ∈ trace (α := α) → s ≠ [] → tl s ∈ trace (α := α) := by
  intro hs hnil
  cases s with
  | nil => contradiction
  | cons a t =>
      rcases (decompo_head_in_trace.mp hs) with rfl | hrest
      · simp
      · simpa using hrest.2

@[simp]
theorem hdt_appt {a : α} {s : traceType α} : hdt (Abs_trace [Ev a] ^^^ s) = Ev a := by
  simp [hdt, appt_head, Abs_trace_inverse]

@[simp]
theorem hdt_one {a : event α} : hdt (Abs_trace [a] : traceType α) = a := by
  simp [hdt, Abs_trace_inverse]

@[simp]
theorem tlt_appt {a : α} {s : traceType α} : tlt (Abs_trace [Ev a] ^^^ s) = s := by
  apply (Rep_trace_inject).mp
  simp [tlt, appt, Abs_trace_inverse, Rep_compo_head_in_trace]

@[simp]
theorem tlt_one {a : event α} : tlt (Abs_trace [a] : traceType α) = <> := by
  apply (Rep_trace_inject).mp
  simp [tlt, nilt, Abs_trace_inverse]

@[simp]
theorem hdt_appt_tail {s : traceType α} : s ≠ <> → Abs_trace [hdt s] ^^^ tlt s = s := by
  intro hs
  cases hrep : Rep_trace s with
  | nil =>
      exfalso
      apply hs
      apply (Rep_trace_inject).mp
      simp [nilt, Abs_trace_inverse, hrep]
  | cons e es =>
      have hsRep : Rep_trace s ∈ trace (α := α) := s.2
      have hsTrace : e :: es ∈ trace (α := α) := by simpa [hrep] using hsRep
      have htail : es ∈ trace (α := α) := tlt_trace hsTrace (by simp)
      apply (Rep_trace_inject).mp
      simp [hdt, tlt, appt, hrep, Abs_trace_inverse, hsTrace, htail]

/- ******************************************************************
                        butlast & last
 ****************************************************************** -/

theorem butlast_trace {s : List (event α)} :
    s ∈ trace (α := α) → s ≠ [] → butlast s ∈ trace (α := α) := by
  intro hs hnil
  simp [trace]
  exact notin_set_butlast (by simpa [trace] using hs)

theorem butlast_trace_Rep {s : traceType α} :
    s ≠ <> → butlast (Rep_trace s) ∈ trace (α := α) := by
  intro hs
  refine butlast_trace s.2 ?_
  intro hnil
  apply hs
  apply (Rep_trace_inject).mp
  simpa [nilt, Abs_trace_inverse] using hnil

@[simp]
theorem lastt_appt {s : traceType α} {e : event α} :
    noTick s → lastt (s ^^^ Abs_trace [e]) = e := by
  intro hs
  have hrep : Rep_trace (s ^^^ Abs_trace [e]) = Rep_trace s ++ [e] := by
    simp [appt, Abs_trace_inverse, Rep_compo_last_in_trace hs]
  rw [lastt, hrep]
  cases hsrep : Rep_trace s <;> simp [hsrep, List.getLast_append_singleton]

@[simp]
theorem lastt_one {a : event α} : lastt (Abs_trace [a] : traceType α) = a := by
  simp [lastt, Abs_trace_inverse]

@[simp]
theorem butlastt_appt {s : traceType α} {e : event α} :
    noTick s → butlastt (s ^^^ Abs_trace [e]) = s := by
  intro hs
  apply (Rep_trace_inject).mp
  simp [butlastt, appt, Abs_trace_inverse, Rep_compo_last_in_trace hs]

@[simp]
theorem butlastt_one {a : event α} : butlastt (Abs_trace [a] : traceType α) = <> := by
  apply (Rep_trace_inject).mp
  simp [butlastt, nilt, Abs_trace_inverse]

@[simp]
theorem butlastt_appt_lastt {s : traceType α} :
    s ≠ <> → butlastt s ^^^ Abs_trace [lastt s] = s := by
  intro hs
  have hnonempty : Rep_trace s ≠ [] := by
    intro hnil
    apply hs
    apply (Rep_trace_inject).mp
    simpa [nilt, Abs_trace_inverse] using hnil
  have hbut : butlast (Rep_trace s) ∈ trace (α := α) := butlast_trace_Rep hs
  have htrace : butlast (Rep_trace s) ++ [lastt s] ∈ trace (α := α) := by
    exact decompo_last_in_trace_if s.2
  apply (Rep_trace_inject).mp
  calc
    Rep_trace (butlastt s ^^^ Abs_trace [lastt s])
        = butlast (Rep_trace s) ++ [lastt s] := by
            simp [butlastt, appt, Abs_trace_inverse, hbut, htrace]
    _ = Rep_trace s := by
          cases hsrep : Rep_trace s with
          | nil => contradiction
          | cons e es =>
              simp [lastt, hsrep, List.dropLast_append_getLast]

/- ******************************************************************
                        noTick + alpha
 ****************************************************************** -/

@[simp]
theorem not_noTick_unnil {s : traceType α} : ¬ noTick s → s ≠ <> := by
  intro hs hnil
  apply hs
  simpa [hnil] using noTick_nil (α := α)

theorem noTick_butlast {s : traceType α} : s ≠ <> → noTick (butlastt s) := by
  intro hs
  have hbut : butlast (Rep_trace s) ∈ trace (α := α) := butlast_trace_Rep hs
  intro hTick
  have : Tick ∈ set (butlast (Rep_trace s)) := by
    simpa [noTick, sett, butlastt, Abs_trace_inverse, hbut, _root_.set] using hTick
  exact s.2 this

/- ---------------------------*
 |   a trace is ... or ...   |
 *--------------------------- -/

theorem trace_nil_or_Tick_or_Ev : ∀ t : traceType α,
    t = <> ∨ t = Abs_trace [Tick] ∨ ∃ a s, t = Abs_trace [Ev a] ^^^ s := by
  intro t
  cases t with
  | mk l hl =>
      rcases list_nil_or_unnil l with rfl | ⟨e, es, rfl⟩
      · left
        apply (Rep_trace_inject).mp
        simp [nilt, Abs_trace_inverse]
      · rcases (decompo_head_in_trace.mp hl) with rfl | hrest
        · rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
          · exact Or.inr <| Or.inl <| by
              apply (Rep_trace_inject).mp
              simp [Abs_trace_inverse]
          · exact Or.inr <| Or.inr ⟨a, <>, by
              apply (Rep_trace_inject).mp
              simp [appt, nilt, Abs_trace_inverse]⟩
        · rcases (not_Tick_to_Ev.mp hrest.1) with ⟨a, rfl⟩
          exact Or.inr <| Or.inr ⟨a, Abs_trace es, by
            apply (Rep_trace_inject).mp
            simp [appt, Abs_trace_inverse, hrest.2, hl]⟩

theorem trace_nil_or_unnil : ∀ t : traceType α,
    t = <> ∨ ∃ a s, t = Abs_trace [a] ^^^ s := by
  intro t
  rcases trace_nil_or_Tick_or_Ev t with rfl | rfl | ⟨a, s, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨Tick, <>, by simp [appt_head]⟩
  · exact Or.inr ⟨Ev a, s, hs⟩

theorem trace_last_nil_or_unnil : ∀ t : traceType α,
    t = <> ∨ ∃ s a, noTick s ∧ t = s ^^^ Abs_trace [a] := by
  intro t
  rcases list_last_nil_or_unnil (Rep_trace t) with hnil | ⟨ss, a, hs⟩
  · left
    apply (Rep_trace_inject).mp
    simpa [nilt, Abs_trace_inverse] using hnil
  · right
    refine ⟨Abs_trace ss, a, ?_, ?_⟩
    · have hss : ss ∈ trace (α := α) := by
        have hrep : Rep_trace t ∈ trace (α := α) := t.2
        rw [hs] at hrep
        exact decompo_app_in_trace_only_if1 hrep
      intro hTick
      have : Tick ∈ set ss := by
        simpa [sett, Abs_trace_inverse, hss, _root_.set] using hTick
      have hrep : Rep_trace t ∈ trace (α := α) := t.2
      rw [hs] at hrep
      exact (decompo_last_in_trace.mp hrep) this
    · apply (Rep_trace_inject).mp
      have hss : ss ∈ trace (α := α) := by
        have hrep : Rep_trace t ∈ trace (α := α) := t.2
        rw [hs] at hrep
        exact decompo_app_in_trace_only_if1 hrep
      have htrace : ss ++ [a] ∈ trace (α := α) := by
        have hrep : Rep_trace t ∈ trace (α := α) := t.2
        simpa [hs] using hrep
      simp [appt, Abs_trace_inverse, hs, hss, htrace]

theorem trace_last_noTick_or_Tick : ∀ t : traceType α,
    noTick t ∨ ∃ s, noTick s ∧ t = s ^^^ Abs_trace [Tick] := by
  intro t
  rcases trace_last_nil_or_unnil t with rfl | ⟨s, a, hs, ht⟩
  · exact Or.inl noTick_nil
  · rcases event_Tick_or_Ev a with rfl | ⟨b, rfl⟩
    · exact Or.inr ⟨s, hs, ht⟩
    · left
      rw [ht]
      exact decompo_appt_noTick_if hs (noTick_Ev b)

/- ---------------------------*
 |    same head and last     |
 *--------------------------- -/

theorem appt_same_head_only_if {a b : α} {s t : traceType α} :
    Abs_trace [Ev a] ^^^ s = Abs_trace [Ev b] ^^^ t → a = b ∧ s = t := by
  intro h
  have hrep := congrArg Rep_trace h
  simp [appt, Abs_trace_inverse] at hrep
  exact ⟨hrep.1, (Rep_trace_inject).mp hrep.2⟩

@[simp]
theorem appt_same_head {a b : α} {s t : traceType α} :
    (Abs_trace [Ev a] ^^^ s = Abs_trace [Ev b] ^^^ t) ↔ (a = b ∧ s = t) := by
  constructor
  · exact appt_same_head_only_if
  · rintro ⟨rfl, rfl⟩
    rfl

theorem appt_same_last_only_if {s t : traceType α} {a b : event α} :
    noTick s → noTick t → s ^^^ Abs_trace [a] = t ^^^ Abs_trace [b] → s = t ∧ a = b := by
  intro hs ht h
  have hrep := congrArg Rep_trace h
  simp [appt, Abs_trace_inverse, Rep_compo_last_in_trace hs, Rep_compo_last_in_trace ht] at hrep
  exact ⟨(Rep_trace_inject).mp hrep.1, hrep.2⟩

@[simp]
theorem appt_same_last {s t : traceType α} {a b : event α} :
    noTick s → noTick t → ((s ^^^ Abs_trace [a] = t ^^^ Abs_trace [b]) ↔ (s = t ∧ a = b)) := by
  intro hs ht
  constructor
  · exact appt_same_last_only_if hs ht
  · rintro ⟨rfl, rfl⟩
    rfl

/- ---------------------------*
 |     appt decompo one      |
 *--------------------------- -/

theorem appt_decompo_one_only_if {s t : traceType α} {a : event α} :
    (noTick s ∨ t = <>) → s ^^^ t = Abs_trace [a] →
      (s = Abs_trace [a] ∧ t = <>) ∨ (s = <> ∧ t = Abs_trace [a]) := by
  intro h hEq
  have hvalid : Rep_trace s ++ Rep_trace t ∈ trace (α := α) := Rep_compo_app_in_trace h
  have hrep : Rep_trace s ++ Rep_trace t = [a] := by
    simpa [appt, Abs_trace_inverse, hvalid] using congrArg Rep_trace hEq
  rcases (list_app_decompo_one (s := Rep_trace s) (t := Rep_trace t) (a := a)).mp hrep with hst | hst
  · left
    exact ⟨(Rep_trace_inject).mp (by simpa [Abs_trace_inverse] using hst.1),
      (Rep_trace_inject).mp (by simpa [nilt, Abs_trace_inverse] using hst.2)⟩
  · right
    exact ⟨(Rep_trace_inject).mp (by simpa [nilt, Abs_trace_inverse] using hst.1),
      (Rep_trace_inject).mp (by simpa [Abs_trace_inverse] using hst.2)⟩

@[simp]
theorem appt_decompo_one {s t : traceType α} {a : event α} :
    (noTick s ∨ t = <>) →
      ((s ^^^ t = Abs_trace [a]) ↔
        ((s = Abs_trace [a] ∧ t = <>) ∨ (s = <> ∧ t = Abs_trace [a]))) := by
  intro h
  constructor
  · exact appt_decompo_one_only_if h
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

@[simp]
theorem appt_decompo_one_sym {s t : traceType α} {a : event α} :
    (noTick s ∨ t = <>) →
      ((Abs_trace [a] = s ^^^ t) ↔
        ((s = Abs_trace [a] ∧ t = <>) ∨ (s = <> ∧ t = Abs_trace [a]))) := by
  intro h
  constructor
  · intro hs
    exact (appt_decompo_one h).mp hs.symm
  · intro hs
    exact ((appt_decompo_one h).mpr hs).symm

/- ******************************************************************
                        lengtht plus
 ****************************************************************** -/

@[simp]
theorem lengtht_zero {s : traceType α} : (lengtht s = 0) ↔ s = <> := by
  constructor
  · intro hs
    apply (Rep_trace_inject).mp
    simpa [lengtht, nilt, Abs_trace_inverse] using hs
  · intro hs
    simpa [hs] using lengtht_nil_zero (α := α)

@[simp]
theorem lengtht_one {s : traceType α} : (lengtht s = 1) ↔ ∃ e, s = Abs_trace [e] := by
  constructor
  · intro hs
    have hlen : (Rep_trace s).length = 1 := hs
    rcases list_length_one.mp hlen with ⟨e, he⟩
    refine ⟨e, ?_⟩
    apply (Rep_trace_inject).mp
    simpa [Abs_trace_inverse, he]
  · rintro ⟨e, rfl⟩
    simp [lengtht, Abs_trace_inverse]

/- -------------------*
 |  for Seq_compo T2 |
 *------------------- -/

theorem noTick_or_last_Tick : ∀ s : traceType α, noTick s ∨ ∃ t, s = t ^^^ Abs_trace [Tick] := by
  intro s
  rcases trace_last_noTick_or_Tick s with hs | ⟨t, ht, hs⟩
  · exact Or.inl hs
  · exact Or.inr ⟨t, hs⟩

/- --------------------------*
 |  used in Alpha_parallel  |
 *-------------------------- -/

theorem not_noTick_in_sett_imp {s : traceType α} :
    ¬ noTick s → ∃ t, s = t ^^^ Abs_trace [Tick] ∧ noTick t := by
  intro hs
  rcases trace_last_noTick_or_Tick s with hs' | ⟨t, ht, hsEq⟩
  · exact False.elim (hs hs')
  · exact ⟨t, hsEq, ht⟩

theorem Tick_in_sett_imp {s : traceType α} :
    Tick ∈ sett s → ∃ t, s = t ^^^ Abs_trace [Tick] ∧ noTick t := by
  intro hTick
  apply not_noTick_in_sett_imp
  intro hs
  exact hs hTick

theorem Tick_in_sett {s : traceType α} :
    (Tick ∈ sett s) ↔ ∃ t, s = t ^^^ Abs_trace [Tick] ∧ noTick t := by
  constructor
  · exact Tick_in_sett_imp
  · rintro ⟨t, rfl, ht⟩
    rw [sett_appt1 (s := t) (t := Abs_trace [Tick]) (Or.inl ht)]
    exact Or.inr (by simp [sett, Abs_trace_inverse, _root_.set])

/- --------------------------------*
 |   used in Inductive_parallel   |
 *-------------------------------- -/

theorem sett_subset_Tick_if {u : traceType α} :
    (u = <> ∨ u = Abs_trace [Tick]) → sett u ⊆ ({Tick} : Set (event α)) := by
  intro hu x hx
  rcases hu with rfl | rfl
  · simp [sett, nilt, Abs_trace_inverse, _root_.set] at hx
  · simpa [sett, Abs_trace_inverse, _root_.set] using hx

theorem sett_subset_Tick_only_if {u : traceType α} :
    sett u ⊆ ({Tick} : Set (event α)) → (u = <> ∨ u = Abs_trace [Tick]) := by
  intro hu
  cases hrep : Rep_trace u with
  | nil =>
      left
      apply (Rep_trace_inject).mp
      simp [nilt, Abs_trace_inverse, hrep]
  | cons e es =>
      have hemem : e ∈ sett u := by
        simpa [sett, hrep, _root_.set]
      have heTick : e = Tick := by
        simpa using hu hemem
      subst heTick
      have huTrace : Tick :: es ∈ trace (α := α) := by
        have huRep : Rep_trace u ∈ trace (α := α) := u.2
        simpa [hrep] using huRep
      have hesnil : es = [] := Tick_is_last huTrace
      right
      apply (Rep_trace_inject).mp
      simpa [Abs_trace_inverse, hrep, hesnil]

theorem sett_subset_Tick {u : traceType α} :
    (sett u ⊆ ({Tick} : Set (event α))) ↔ (u = <> ∨ u = Abs_trace [Tick]) := by
  constructor
  · exact sett_subset_Tick_only_if
  · exact sett_subset_Tick_if

theorem lengtht_Abs_trace {s : List (event α)} :
    s ∈ trace (α := α) → lengtht (Abs_trace s) = s.length := by
  intro hs
  simp [lengtht, Abs_trace_inverse, hs]

theorem lengtht_Abs_trace_noTick {s : List (event α)} :
    Tick ∉ set (butlast s) → lengtht (Abs_trace s) = s.length := by
  intro hs
  exact lengtht_Abs_trace hs

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

theorem not_noTick_in_sett {s : traceType α} :
    (¬ noTick s) ↔ ∃ t, s = t ^^^ Abs_trace [Tick] ∧ noTick t := by
  constructor
  · exact not_noTick_in_sett_imp
  · rintro ⟨t, ht, hnt⟩ hs
    have : Tick ∈ sett s := by
      rw [ht, sett_appt1 (s := t) (t := Abs_trace [Tick]) (Or.inl hnt)]
      exact Or.inr (by simp [sett, Abs_trace_inverse, _root_.set])
    exact hs this

theorem noTick_or_last_Tick2 : ∀ s : traceType α,
    noTick s ∨ ∃ t, s = t ^^^ Abs_trace [Tick] ∧ noTick t := by
  intro s
  by_cases hs : noTick s
  · exact Or.inl hs
  · exact Or.inr (not_noTick_in_sett_imp hs)

/- ***********************************************************
                 induction for traces
 *********************************************************** -/

theorem induct_event_list {s : List (event α)} {P : traceType α → Prop} :
    s ∈ trace (α := α) →
      P <> →
      P (Abs_trace [Tick]) →
      (∀ s a, P (Abs_trace s) → P (Abs_trace [Ev a] ^^^ Abs_trace s)) →
      P (Abs_trace s) := by
  revert P
  induction s with
  | nil =>
      intro P hs hnil _hTick _hstep
      simpa [nilt]
  | cons a s ih =>
      intro P hs hnil hTick hstep
      rcases (decompo_head_in_trace.mp hs) with rfl | hrest
      · rcases event_Tick_or_Ev a with rfl | ⟨b, rfl⟩
        · simpa using hTick
        · have hbase : P (Abs_trace [Ev b] ^^^ (<> : traceType α)) := by
            simpa [nilt] using (hstep [] b hnil)
          simpa using hbase
      · rcases (not_Tick_to_Ev.mp hrest.1) with ⟨b, rfl⟩
        have hs' : P (Abs_trace s) := ih (P := P) hrest.2 hnil hTick hstep
        simpa [appt_head, Abs_trace_inverse hrest.2] using hstep s b hs'

theorem induct_trace {P : traceType α → Prop} {s : traceType α} :
    P <> →
    P (Abs_trace [Tick]) →
    (∀ s a, P s → P (Abs_trace [Ev a] ^^^ s)) →
    P s := by
  intro hnil hTick hstep
  simpa using induct_event_list (s := Rep_trace s) (P := P) s.2 hnil hTick
    (fun xs a h => by simpa using hstep (Abs_trace xs) a h)

theorem rev_induct_event_list {s : List (event α)} {P : traceType α → Prop} :
    s ∈ trace (α := α) →
      P <> →
      (∀ s e, P (Abs_trace s) → noTick (Abs_trace s) → P (Abs_trace s ^^^ Abs_trace [e])) →
      P (Abs_trace s) := by
  revert P
  induction s using List.reverseRecOn with
  | nil =>
      intro P hs hnil _hstep
      simpa [nilt]
  | append_singleton xs a ih =>
      intro P hs hnil hstep
      have hxs : xs ∈ trace (α := α) := decompo_app_in_trace_only_if1 (by simpa using hs)
      have hno : noTick (Abs_trace xs) := by
        intro hTick
        have : Tick ∈ set xs := by
          simpa [noTick, sett, Abs_trace_inverse, hxs, _root_.set] using hTick
        exact (decompo_last_in_trace.mp (by simpa using hs)) this
      have hrec : P (Abs_trace xs) := ih (P := P) hxs hnil hstep
      simpa [appt_last hno, Abs_trace_inverse hxs] using hstep xs a hrec hno

theorem rev_induct_trace {P : traceType α → Prop} {s : traceType α} :
    P <> →
    (∀ s e, P s → noTick s → P (s ^^^ Abs_trace [e])) →
    P s := by
  intro hnil hstep
  simpa using rev_induct_event_list (s := Rep_trace s) (P := P) s.2 hnil
    (fun xs e h hs => by simpa using hstep (Abs_trace xs) e h hs)

/- Tick decomposition -/

theorem Tick_decompo_lm : ∀ s : traceType α, ¬ noTick s → s = butlastt s ^^^ Abs_trace [Tick] := by
  intro s hs
  rcases not_noTick_in_sett_imp hs with ⟨t, hsEq, ht⟩
  rw [hsEq, butlastt_appt ht]

theorem Tick_decompo {s : traceType α} : ¬ noTick s → s = butlastt s ^^^ Abs_trace [Tick] := by
  exact Tick_decompo_lm s

private theorem rep_trace_ne_nil {s : traceType α} (hs : s ≠ <>) : Rep_trace s ≠ [] := by
  intro hnil
  apply hs
  apply (Rep_trace_inject).mp
  simpa [nilt, Abs_trace_inverse] using hnil

theorem appt_decompo_lm :
    ∀ s1 s2 t1 t2 : traceType α,
      noTick s1 → s2 ≠ <> → noTick t1 → t2 ≠ <> →
        ((s1 ^^^ s2 = t1 ^^^ t2) ↔
          (∃ u, s1 ^^^ u = t1 ∧ s2 = u ^^^ t2 ∧ noTick u) ∨
          (∃ u, s1 = t1 ^^^ u ∧ u ^^^ s2 = t2 ∧ noTick u)) := by
  intro s1 s2 t1 t2 hs1 hs2 ht1 ht2
  constructor
  · intro hEq
    have hvalid1 : Rep_trace s1 ++ Rep_trace s2 ∈ trace (α := α) := Rep_compo_app_in_trace (Or.inl hs1)
    have hvalid2 : Rep_trace t1 ++ Rep_trace t2 ∈ trace (α := α) := Rep_compo_app_in_trace (Or.inl ht1)
    have hrep : Rep_trace s1 ++ Rep_trace s2 = Rep_trace t1 ++ Rep_trace t2 := by
      simpa [appt, Abs_trace_inverse, hvalid1, hvalid2] using congrArg Rep_trace hEq
    rcases (list_app_app (s1 := Rep_trace s1) (s2 := Rep_trace s2)
      (t1 := Rep_trace t1) (t2 := Rep_trace t2)).mp hrep with hleft | hright
    · rcases hleft with ⟨uList, hs1eq, ht2eq⟩
      have hs2rep : Rep_trace s2 ≠ [] := rep_trace_ne_nil hs2
      have huNoSet : Tick ∉ _root_.set uList := by
        have ht2trace' : Rep_trace t2 ∈ trace (α := α) := t2.2
        have htrace : uList ++ Rep_trace s2 ∈ trace (α := α) := by simpa [ht2eq] using ht2trace'
        rcases (decompo_app_in_trace.mp htrace) with hnil | hrest
        · exfalso
          exact hs2rep hnil.2
        · exact hrest.1
      have huTrace : uList ∈ trace (α := α) := notic_in_trace huNoSet
      have hs1trace : Rep_trace t1 ++ uList ∈ trace (α := α) := by
        have hs1trace' : Rep_trace s1 ∈ trace (α := α) := s1.2
        simpa [hs1eq] using hs1trace'
      have ht2trace : uList ++ Rep_trace s2 ∈ trace (α := α) := by
        have ht2trace' : Rep_trace t2 ∈ trace (α := α) := t2.2
        simpa [ht2eq] using ht2trace'
      let u : traceType α := Abs_trace uList
      right
      refine ⟨u, ?_, ?_, ?_⟩
      · apply (Rep_trace_inject).mp
        simp [u, appt, Abs_trace_inverse, huTrace, hs1trace, hs1eq]
      · apply (Rep_trace_inject).mp
        simp [u, appt, Abs_trace_inverse, huTrace, ht2trace, ht2eq]
      · simpa [u, noTick, sett, Abs_trace_inverse, huTrace] using huNoSet
    · rcases hright with ⟨uList, ht1eq, hs2eq⟩
      have ht2rep : Rep_trace t2 ≠ [] := rep_trace_ne_nil ht2
      have huNoSet : Tick ∉ _root_.set uList := by
        have hs2trace' : Rep_trace s2 ∈ trace (α := α) := s2.2
        have htrace : uList ++ Rep_trace t2 ∈ trace (α := α) := by simpa [hs2eq] using hs2trace'
        rcases (decompo_app_in_trace.mp htrace) with hnil | hrest
        · exfalso
          exact ht2rep hnil.2
        · exact hrest.1
      have huTrace : uList ∈ trace (α := α) := notic_in_trace huNoSet
      have ht1trace : Rep_trace s1 ++ uList ∈ trace (α := α) := by
        have ht1trace' : Rep_trace t1 ∈ trace (α := α) := t1.2
        simpa [ht1eq] using ht1trace'
      have hs2trace : uList ++ Rep_trace t2 ∈ trace (α := α) := by
        have hs2trace' : Rep_trace s2 ∈ trace (α := α) := s2.2
        simpa [hs2eq] using hs2trace'
      let u : traceType α := Abs_trace uList
      left
      refine ⟨u, ?_, ?_, ?_⟩
      · apply (Rep_trace_inject).mp
        simp [u, appt, Abs_trace_inverse, huTrace, ht1eq, ht1trace]
      · apply (Rep_trace_inject).mp
        simp [u, appt, Abs_trace_inverse, huTrace, hs2eq, hs2trace]
      · simpa [u, noTick, sett, Abs_trace_inverse, huTrace] using huNoSet
  · intro h
    rcases h with ⟨u, hsEq, htEq, hu⟩ | ⟨u, hsEq, htEq, hu⟩
    · calc
        s1 ^^^ s2 = s1 ^^^ (u ^^^ t2) := by rw [htEq]
        _ = (s1 ^^^ u) ^^^ t2 := by
              symm
              exact appt_assoc (Or.inl hs1) (Or.inl hu)
        _ = t1 ^^^ t2 := by rw [hsEq]
    · calc
        s1 ^^^ s2 = (t1 ^^^ u) ^^^ s2 := by rw [hsEq]
        _ = t1 ^^^ (u ^^^ s2) := by
              exact appt_assoc (Or.inl ht1) (Or.inl hu)
        _ = t1 ^^^ t2 := by rw [htEq]

theorem appt_decompo {s1 s2 t1 t2 : traceType α} :
    (noTick s1 ∨ s2 = <>) → (noTick t1 ∨ t2 = <>) →
      ((s1 ^^^ s2 = t1 ^^^ t2) ↔
        (∃ u, s1 ^^^ u = t1 ∧ s2 = u ^^^ t2 ∧ (noTick u ∨ (noTick s1 ∧ t2 = <>))) ∨
        (∃ u, s1 = t1 ^^^ u ∧ u ^^^ s2 = t2 ∧ (noTick u ∨ (noTick t1 ∧ s2 = <>)))) := by
  intro hs ht
  by_cases hs2 : s2 = <>
  · by_cases ht2 : t2 = <>
    · constructor
      · intro hEq
        right
        refine ⟨<>, ?_, ?_, ?_⟩
        · simpa [hs2, ht2] using hEq
        · simp [hs2, ht2]
        · exact Or.inl noTick_nil
      · rintro (⟨u, hsEq, htEq, hu⟩ | ⟨u, hsEq, htEq, hu⟩)
        · have huEq : u = <> := by simpa [hs2, ht2] using htEq.symm
          simpa [huEq, hs2, ht2] using hsEq
        · have huEq : u = <> := by simpa [hs2, ht2] using htEq
          simpa [huEq, hs2, ht2] using hsEq
    · have ht1' : noTick t1 := by
        rcases ht with ht1' | h
        · exact ht1'
        · exact False.elim (ht2 h)
      constructor
      · intro hEq
        right
        refine ⟨t2, ?_, ?_, ?_⟩
        · simpa [hs2] using hEq
        · simp [hs2]
        · exact Or.inr ⟨ht1', hs2⟩
      · rintro (⟨u, hsEq, htEq, hu⟩ | ⟨u, hsEq, htEq, hu⟩)
        · have hu' : noTick u := by
            rcases hu with hu | ⟨_, ht2'⟩
            · exact hu
            · exact False.elim (ht2 ht2')
          have : t2 = <> := by
            have hnil : u ^^^ t2 = <> := by simpa [hs2] using htEq.symm
            exact (appt_nil hu').mp hnil |>.2
          exact False.elim (ht2 this)
        · have huEq : u = t2 := by simpa [hs2] using htEq
          simpa [huEq, hs2] using hsEq
  · by_cases ht2 : t2 = <>
    · have hs1' : noTick s1 := by
        rcases hs with hs1' | h
        · exact hs1'
        · exact False.elim (hs2 h)
      constructor
      · intro hEq
        left
        refine ⟨s2, ?_, ?_, ?_⟩
        · simpa [ht2] using hEq
        · simpa [ht2] using hEq
        · exact Or.inr ⟨hs1', ht2⟩
      · rintro (⟨u, hsEq, htEq, hu⟩ | ⟨u, hsEq, htEq, hu⟩)
        · have huEq : s2 = u := by simpa [ht2] using htEq
          simpa [huEq, ht2] using hsEq
        · have hu' : noTick u := by
            rcases hu with hu | ⟨_, hs2'⟩
            · exact hu
            · exact False.elim (hs2 hs2')
          have : s2 = <> := by
            have hnil : u ^^^ s2 = <> := by simpa [ht2] using htEq
            exact (appt_nil hu').mp hnil |>.2
          exact False.elim (hs2 this)
    · have hs1' : noTick s1 := by
        rcases hs with hs1' | h
        · exact hs1'
        · exact False.elim (hs2 h)
      have ht1' : noTick t1 := by
        rcases ht with ht1' | h
        · exact ht1'
        · exact False.elim (ht2 h)
      simpa [hs2, ht2] using appt_decompo_lm s1 s2 t1 t2 hs1' hs2 ht1' ht2
