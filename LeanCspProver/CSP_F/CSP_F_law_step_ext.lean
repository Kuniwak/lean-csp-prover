           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_step_ext
import LeanCspProver.CSP_F.CSP_F_simp

open Function
open SumType
open event

noncomputable section

/-
(*****************************************************************

         1. step laws
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(*********************************************************
              (P1 [> P2) |[X]| (Q1 [> Q2)
 *********************************************************)
-/

/- The following law in p.288 does not hold.                               -/
/-     (P1 [> P2) |[X]| (Q1 [> Q2)                                         -/
/-  =F (P1 |[X]| Q1) [> ((P2 |[X]| (Q1 [> Q2)) |~| ((P1 [> P2) |[X]| Q2))  -/
/-                                                                         -/
/- a counter example:                                                      -/
/-  P1 = a -> STOP, P2 = STOP, Q1 = STOP, Q2 = b -> STOP, X = {}           -/
/-  where (a ~= b)                                                         -/
/-                                                                         -/
/-  check the following lemmas                                             -/

/- Isabelle's anonymous lemmas are given explicit Lean names below. -/

axiom cspF_Parallel_Timeout_counterexample_notin_failures
    {a b : α} {M : p → domFType α} :
    a ≠ b →
      (Abs_trace [event.Ev a], {event.Ev b}) ~:f
        failures
          ((Timeout (a ~> proc.STOP) proc.STOP) |[({} : Set α)]|
            (Timeout proc.STOP (b ~> proc.STOP)))
          M

axiom cspF_Parallel_Timeout_counterexample_in_failures
    {a b : α} {X : Set α} {M : p → domFType α} :
    (Abs_trace [event.Ev a], {event.Ev b}) :f
      (failures
        (Timeout
          ((a ~> proc.STOP) |[({} : Set α)]| proc.STOP)
          ((proc.STOP |[({} : Set α)]| Timeout proc.STOP (b ~> proc.STOP)) |~|
            ((Timeout (a ~> proc.STOP) proc.STOP) |[X]| (b ~> proc.STOP))))
        M)

/-
(*********************************************************
              (P [> Q) |[X]| (? :Y -> Rf)
 *********************************************************)
-/

/- The following law in p.289 does not hold.                               -/
/-                                                                         -/
/-     (P [> Q) |[X]| (? :Y -> Rf) =F[M,M]                                 -/
/-     (? x:(Y - X) -> ((P [> Q) |[X]| Rf x))                              -/
/-     [+] ((P |[X]| (? :Y -> Rf)) [> (Q |[X]| (? :Y -> Rf)))              -/
/-                                                                         -/
/- a counter example:                                                      -/
/-  P = STOP, Q = b -> STOP, Y = {a}, Rf = (%x. STOP), X = {}              -/
/-  where (a ~= b)                                                         -/
/-                                                                         -/
/-  check the following lemmas                                             -/

axiom cspF_Timeout_Parallel_input_counterexample_notin_failures
    {a b : α} {M : p → domFType α} :
    a ≠ b →
      (Abs_trace [event.Ev a], {event.Ev b}) ~:f
        failures
          ((Timeout proc.STOP (b ~> proc.STOP)) |[({} : Set α)]|
            (proc.Ext_pre_choice ({a} : Set α) (fun _ => proc.STOP)))
          M

axiom cspF_Timeout_Parallel_input_counterexample_in_failures
    {a b : α} {M : p → domFType α} :
    a ≠ b →
      (Abs_trace [event.Ev a], {event.Ev b}) :f
        (failures
          ((proc.Ext_pre_choice (({a} : Set α) \ ({} : Set α))
            (fun _ => (Timeout proc.STOP (b ~> proc.STOP) |[({} : Set α)]| proc.STOP))) [+]
            (Timeout
              (proc.STOP |[({} : Set α)]| proc.Ext_pre_choice ({a} : Set α) (fun _ => proc.STOP))
              ((b ~> proc.STOP) |[({} : Set α)]|
                proc.Ext_pre_choice ({a} : Set α) (fun _ => proc.STOP))))
          M)

/-
(*********************************************************
              Parallel expansion & distribbution
 *********************************************************)
-/

/-- `Ev`-headed failure membership in an external prefix choice. -/
theorem Ev_appt_in_failures_Ext_pre_choice
    {a : α} {s : traceType α} {Xa : Set (event α)} {A : Set α}
    {Pf : α → proc p α} {M : p → domFType α} :
    ((Abs_trace [Ev a] ^^^ s, Xa) :f failures (proc.Ext_pre_choice A Pf) M) ↔
      ((s, Xa) :f failures (Pf a) M ∧ a ∈ A) := by
  rw [in_failures_Ext_pre_choice]
  constructor
  · rintro (⟨Y', heq, -⟩ | ⟨b, s', Y', heq, hf, hb⟩)
    · simp only [Prod.mk.injEq] at heq
      exact absurd heq.1 event_app_not_nil_left
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, rfl⟩ := heq
      obtain ⟨rfl, rfl⟩ := appt_same_head.mp h1
      exact ⟨hf, hb⟩
  · rintro ⟨hf, ha⟩
    exact Or.inr ⟨a, s, Xa, rfl, hf, ha⟩

/-- `nil` failure membership in an external prefix choice: the refusal must
    avoid all offered events. -/
theorem nil_in_failures_Ext_pre_choice
    {Xa : Set (event α)} {A : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (((<> : traceType α), Xa) :f failures (proc.Ext_pre_choice A Pf) M) ↔
      (Ev '' A) ∩ Xa = ∅ := by
  rw [in_failures_Ext_pre_choice]
  constructor
  · rintro (⟨Y', heq, hint⟩ | ⟨b, s', Y', heq, -, -⟩)
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      exact hint
    · simp only [Prod.mk.injEq] at heq
      exact absurd heq.1.symm event_app_not_nil_left
  · intro h
    exact Or.inl ⟨Xa, rfl, h⟩

/-- Failures of `? :A -> Pf [> R`: either a failure of `R`, or an `Ev`-headed
    failure through the prefix choice (the timeout hides the `nil` refusals of
    the choice, and `<Tick>` is never a trace of it). -/
theorem in_failures_Timeout_Ext_pre_choice
    {s : traceType α} {Xa : Set (event α)} {A : Set α}
    {Pf : α → proc p α} {R : proc p α} {M : p → domFType α} :
    ((s, Xa) :f failures ((proc.Ext_pre_choice A Pf) [> R) M) ↔
      ((s, Xa) :f failures R M ∨
        ∃ a s', s = Abs_trace [Ev a] ^^^ s' ∧ (s', Xa) :f failures (Pf a) M ∧ a ∈ A) := by
  rw [in_failures_Timeout1]
  constructor
  · rintro (h | ⟨s₁, X₁, heq, hne, hE⟩ | ⟨X₁, heq, -, hTick⟩)
    · exact Or.inl h
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [in_failures_Ext_pre_choice] at hE
      rcases hE with ⟨Y', heq2, -⟩ | ⟨b, s', Y', heq2, hf, hb⟩
      · simp only [Prod.mk.injEq] at heq2
        exact absurd heq2.1 hne
      · simp only [Prod.mk.injEq] at heq2
        obtain ⟨h1, rfl⟩ := heq2
        exact Or.inr ⟨b, s', h1, hf, hb⟩
    · exact absurd hTick Tick_notin_traces_Ext_pre_choice
  · rintro (h | ⟨a, s', rfl, hf, ha⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨Abs_trace [Ev a] ^^^ s', Xa, rfl, event_app_not_nil_left,
        Ev_appt_in_failures_Ext_pre_choice.mpr ⟨hf, ha⟩⟩)

/-- The event set of an `Ev`-headed trace. -/
theorem sett_Ev_appt {b : α} {s : traceType α} :
    sett (Abs_trace [Ev b] ^^^ s) = {Ev b} ∪ sett s := by
  rw [sett_appt1 (Or.inl (noTick_Ev b)), sett_one]

-- Hand-written semantic proof following the Isabelle original
-- (CSP_F_law_step_ext.thy): the traces part is `cspT_Parallel_Timeout_split`;
-- the failures part decomposes the parallel failure and supplies the
-- refusal-set witnesses by hand.
theorem cspF_Parallel_Timeout_split
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P Q : proc p α} {M : p → domFType α} :
    eqF ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]|
      (Timeout (proc.Ext_pre_choice Z Qf) Q)) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q)
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))))
        ((P |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
          ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Q))) := by
  refine cspF_eqF_of_eqT cspT_Parallel_Timeout_split ?_
  intro w Xa
  simp only [Timeout_def]
  rw [in_failures_Parallel, in_failures_Timeout_Ext_pre_choice, in_failures_Int_choice,
    in_failures_Parallel, in_failures_Parallel]
  constructor
  -- ==> direction
  · rintro ⟨u, Ya, Za, heq, hsep, s, t, hpar, hsF, htF⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [in_failures_Timeout_Ext_pre_choice] at hsF htF
    rcases hsF with hsP | ⟨b, s', rfl, hsf, hbY⟩
    · -- (s, Ya) is a failure of P : the timeout tail, left component
      exact Or.inl (Or.inl ⟨_, Ya, Za, rfl, hsep, s, t, hpar,
        hsP, (in_failures_Timeout_Ext_pre_choice).mpr htF⟩)
    rcases htF with htQ | ⟨c, t', rfl, htf, hcZ⟩
    · -- (t, Za) is a failure of Q : the timeout tail, right component
      exact Or.inl (Or.inr ⟨_, Ya, Za, rfl, hsep, _, t, hpar,
        (in_failures_Timeout_Ext_pre_choice).mpr
          (Or.inr ⟨b, s', rfl, hsf, hbY⟩), htQ⟩)
    · -- main part: both components step
      rcases par_tr_head_Ev_Ev.mp hpar with ⟨a, v, rfl, hcase⟩
      refine Or.inr ⟨a, v, rfl, ?_⟩
      rcases hcase with ⟨haX, hv, rfl, rfl⟩ | ⟨haX, hv, rfl⟩ | ⟨haX, hv, rfl⟩
      · -- synchronised step
        refine ⟨?_, ?_⟩
        · simp only [procIte_pos haX, in_failures_Parallel]
          exact ⟨v, Ya, Za, rfl, hsep, s', t', hv, hsf, htf⟩
        · simp only [Set.mem_union, Set.mem_inter_iff]
          exact Or.inl (Or.inl ⟨⟨haX, hbY⟩, hcZ⟩)
      · -- left step (the head event is `b`)
        refine ⟨?_, ?_⟩
        · simp only [procIte_neg haX]
          by_cases hbZ : b ∈ Z
          · simp only [procIte_pos (⟨hbY, hbZ⟩ : b ∈ Y ∧ b ∈ Z), in_failures_Int_choice,
              in_failures_Parallel]
            exact Or.inl ⟨v, Ya, Za, rfl, hsep, s', _, hv, hsf,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨c, t', rfl, htf, hcZ⟩)⟩
          · simp only [procIte_neg (fun h : b ∈ Y ∧ b ∈ Z => hbZ h.2), procIte_pos hbY,
              in_failures_Parallel]
            exact ⟨v, Ya, Za, rfl, hsep, s', _, hv, hsf,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨c, t', rfl, htf, hcZ⟩)⟩
        · simp only [Set.mem_union, Set.mem_diff]
          exact Or.inl (Or.inr ⟨hbY, haX⟩)
      · -- right step (the head event is `c`)
        refine ⟨?_, ?_⟩
        · simp only [procIte_neg haX]
          by_cases hcY : c ∈ Y
          · simp only [procIte_pos (⟨hcY, hcZ⟩ : c ∈ Y ∧ c ∈ Z), in_failures_Int_choice,
              in_failures_Parallel]
            exact Or.inr ⟨v, Ya, Za, rfl, hsep, _, t', hv,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨b, s', rfl, hsf, hbY⟩), htf⟩
          · simp only [procIte_neg (fun h : c ∈ Y ∧ c ∈ Z => hcY h.1), procIte_neg hcY,
              in_failures_Parallel]
            exact ⟨v, Ya, Za, rfl, hsep, _, t', hv,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨b, s', rfl, hsf, hbY⟩), htf⟩
        · simp only [Set.mem_union, Set.mem_diff]
          exact Or.inr ⟨hcZ, haX⟩
  -- <== direction
  · rintro ((hTail | hTail) | ⟨a, w', rfl, hbr, haS⟩)
    · -- timeout tail, left
      obtain ⟨u, Ya, Za, heq, hsep, s, t, hpar, hsP, htTO⟩ := hTail
      exact ⟨u, Ya, Za, heq, hsep, s, t, hpar,
        (in_failures_Timeout_Ext_pre_choice).mpr (Or.inl hsP), htTO⟩
    · -- timeout tail, right
      obtain ⟨u, Ya, Za, heq, hsep, s, t, hpar, hsTO, htQ⟩ := hTail
      exact ⟨u, Ya, Za, heq, hsep, s, t, hpar, hsTO,
        (in_failures_Timeout_Ext_pre_choice).mpr (Or.inl htQ)⟩
    · -- an initial step through the prefix choice
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at haS
      by_cases haX : a ∈ X
      · simp only [procIte_pos haX, in_failures_Parallel] at hbr
        obtain ⟨u', Ya, Za, heq, hsep, s', t', hpar', hf1, hf2⟩ := hbr
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have haY : a ∈ Y := by
          rcases haS with (⟨⟨-, hy⟩, -⟩ | ⟨-, hx⟩) | ⟨-, hx⟩
          · exact hy
          · exact absurd haX hx
          · exact absurd haX hx
        have haZ : a ∈ Z := by
          rcases haS with (⟨-, hz⟩ | ⟨-, hx⟩) | ⟨-, hx⟩
          · exact hz
          · exact absurd haX hx
          · exact absurd haX hx
        exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
          Abs_trace [Ev a] ^^^ s', Abs_trace [Ev a] ^^^ t',
          par_tr_head.mpr (Or.inl ⟨haX, s', t', hpar', rfl, rfl⟩),
          (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, s', rfl, hf1, haY⟩),
          (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, t', rfl, hf2, haZ⟩)⟩
      · simp only [procIte_neg haX] at hbr
        by_cases haYZ : a ∈ Y ∧ a ∈ Z
        · simp only [procIte_pos haYZ, in_failures_Int_choice, in_failures_Parallel] at hbr
          rcases hbr with ⟨u', Ya, Za, heq, hsep, s', t, hpar', hf1, hf2⟩ |
            ⟨u', Ya, Za, heq, hsep, s, t', hpar', hf1, hf2⟩
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              Abs_trace [Ev a] ^^^ s', t,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, s', rfl, hf1, haYZ.1⟩),
              hf2⟩
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              s, Abs_trace [Ev a] ^^^ t',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, t', hpar', rfl⟩)),
              hf1,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, t', rfl, hf2, haYZ.2⟩)⟩
        · simp only [procIte_neg haYZ] at hbr
          by_cases haY : a ∈ Y
          · simp only [procIte_pos haY, in_failures_Parallel] at hbr
            obtain ⟨u', Ya, Za, heq, hsep, s', t, hpar', hf1, hf2⟩ := hbr
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              Abs_trace [Ev a] ^^^ s', t,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, s', rfl, hf1, haY⟩),
              hf2⟩
          · simp only [procIte_neg haY, in_failures_Parallel] at hbr
            obtain ⟨u', Ya, Za, heq, hsep, s, t', hpar', hf1, hf2⟩ := hbr
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            have haZ : a ∈ Z := by
              rcases haS with (⟨⟨-, hy⟩, -⟩ | ⟨hy, -⟩) | ⟨hz, -⟩
              · exact absurd hy haY
              · exact absurd hy haY
              · exact hz
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              s, Abs_trace [Ev a] ^^^ t',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, t', hpar', rfl⟩)),
              hf1,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, t', rfl, hf2, haZ⟩)⟩

/-
(*********************************************************
            Parallel expansion & distribbution 2
 *********************************************************)
-/

/- (*** left ****) -/

-- Hand-written semantic proof following the Isabelle original.
theorem cspF_Parallel_Timeout_input_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| proc.Ext_pre_choice Z Qf) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| proc.Ext_pre_choice Z Qf)
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))))
        (P |[X]| proc.Ext_pre_choice Z Qf)) := by
  refine cspF_eqF_of_eqT cspT_Parallel_Timeout_input_l ?_
  intro w Xa
  simp only [Timeout_def]
  rw [in_failures_Parallel, in_failures_Timeout_Ext_pre_choice, in_failures_Parallel]
  constructor
  -- ==> direction
  · rintro ⟨u, Ya, Za, heq, hsep, s, t, hpar, hsF, htF⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [in_failures_Timeout_Ext_pre_choice] at hsF
    rcases hsF with hsP | ⟨b, s', rfl, hsf, hbY⟩
    · -- (s, Ya) is a failure of P : the timeout tail
      exact Or.inl ⟨_, Ya, Za, rfl, hsep, s, t, hpar, hsP, htF⟩
    rw [in_failures_Ext_pre_choice] at htF
    rcases htF with ⟨Za', heqt, hZa⟩ | ⟨c, t', Za', heqt, htf, hcZ⟩
    · -- the right component refuses at nil
      simp only [Prod.mk.injEq] at heqt
      obtain ⟨rfl, rfl⟩ := heqt
      obtain ⟨rfl, hnT, hset⟩ := par_tr_nil_right.mp hpar
      have hbEv : Ev b ∈ sett (Abs_trace [Ev b] ^^^ s') := by
        rw [sett_Ev_appt]
        exact Or.inl rfl
      have hbX : b ∉ X := fun hbx =>
        Set.eq_empty_iff_forall_notMem.mp hset (Ev b) ⟨hbEv, ⟨b, hbx, rfl⟩⟩
      have hnT' : Tick ∉ sett s' := fun h => by
        rw [sett_Ev_appt] at hnT
        exact hnT (Or.inr h)
      have hset' : sett s' ∩ Ev '' X = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro e ⟨he, heX⟩
        refine Set.eq_empty_iff_forall_notMem.mp hset e ⟨?_, heX⟩
        rw [sett_Ev_appt]
        exact Or.inr he
      refine Or.inr ⟨b, s', rfl, ?_, ?_⟩
      · simp only [procIte_neg hbX]
        by_cases hbZ : b ∈ Z
        · simp only [procIte_pos (⟨hbY, hbZ⟩ : b ∈ Y ∧ b ∈ Z), in_failures_Int_choice,
            in_failures_Parallel]
          exact Or.inl ⟨s', Ya, Za, rfl, hsep, s', <>,
            par_tr_nil_right.mpr ⟨rfl, hnT', hset'⟩, hsf,
            nil_in_failures_Ext_pre_choice.mpr hZa⟩
        · simp only [procIte_neg (fun h : b ∈ Y ∧ b ∈ Z => hbZ h.2), procIte_pos hbY,
            in_failures_Parallel]
          exact ⟨s', Ya, Za, rfl, hsep, s', <>,
            par_tr_nil_right.mpr ⟨rfl, hnT', hset'⟩, hsf,
            nil_in_failures_Ext_pre_choice.mpr hZa⟩
      · simp only [Set.mem_union, Set.mem_diff]
        exact Or.inl (Or.inr ⟨hbY, hbX⟩)
    · -- both components step
      simp only [Prod.mk.injEq] at heqt
      obtain ⟨rfl, rfl⟩ := heqt
      rcases par_tr_head_Ev_Ev.mp hpar with ⟨a, v, rfl, hcase⟩
      refine Or.inr ⟨a, v, rfl, ?_⟩
      rcases hcase with ⟨haX, hv, rfl, rfl⟩ | ⟨haX, hv, rfl⟩ | ⟨haX, hv, rfl⟩
      · -- synchronised step (survivor: b)
        refine ⟨?_, ?_⟩
        · simp only [procIte_pos haX, in_failures_Parallel]
          exact ⟨v, Ya, Za, rfl, hsep, s', t', hv, hsf, htf⟩
        · simp only [Set.mem_union, Set.mem_inter_iff]
          exact Or.inl (Or.inl ⟨⟨haX, hbY⟩, hcZ⟩)
      · -- left step (survivor: b)
        refine ⟨?_, ?_⟩
        · simp only [procIte_neg haX]
          by_cases hbZ : b ∈ Z
          · simp only [procIte_pos (⟨hbY, hbZ⟩ : b ∈ Y ∧ b ∈ Z), in_failures_Int_choice,
              in_failures_Parallel]
            exact Or.inl ⟨v, Ya, Za, rfl, hsep, s', _, hv, hsf,
              Ev_appt_in_failures_Ext_pre_choice.mpr ⟨htf, hcZ⟩⟩
          · simp only [procIte_neg (fun h : b ∈ Y ∧ b ∈ Z => hbZ h.2), procIte_pos hbY,
              in_failures_Parallel]
            exact ⟨v, Ya, Za, rfl, hsep, s', _, hv, hsf,
              Ev_appt_in_failures_Ext_pre_choice.mpr ⟨htf, hcZ⟩⟩
        · simp only [Set.mem_union, Set.mem_diff]
          exact Or.inl (Or.inr ⟨hbY, haX⟩)
      · -- right step (survivor: c)
        refine ⟨?_, ?_⟩
        · simp only [procIte_neg haX]
          by_cases hcY : c ∈ Y
          · simp only [procIte_pos (⟨hcY, hcZ⟩ : c ∈ Y ∧ c ∈ Z), in_failures_Int_choice,
              in_failures_Parallel]
            exact Or.inr ⟨v, Ya, Za, rfl, hsep, _, t', hv,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨b, s', rfl, hsf, hbY⟩), htf⟩
          · simp only [procIte_neg (fun h : c ∈ Y ∧ c ∈ Z => hcY h.1), procIte_neg hcY,
              in_failures_Parallel]
            exact ⟨v, Ya, Za, rfl, hsep, _, t', hv,
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨b, s', rfl, hsf, hbY⟩), htf⟩
        · simp only [Set.mem_union, Set.mem_diff]
          exact Or.inr ⟨hcZ, haX⟩
  -- <== direction
  · rintro (hTail | ⟨a, w', rfl, hbr, haS⟩)
    · -- the timeout tail
      obtain ⟨u, Ya, Za, heq, hsep, s, t, hpar, hsP, htE⟩ := hTail
      exact ⟨u, Ya, Za, heq, hsep, s, t, hpar,
        (in_failures_Timeout_Ext_pre_choice).mpr (Or.inl hsP), htE⟩
    · -- an initial step through the prefix choice
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at haS
      by_cases haX : a ∈ X
      · simp only [procIte_pos haX, in_failures_Parallel] at hbr
        obtain ⟨u', Ya, Za, heq, hsep, s', t', hpar', hf1, hf2⟩ := hbr
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have haY : a ∈ Y := by
          rcases haS with (⟨⟨-, hy⟩, -⟩ | ⟨-, hx⟩) | ⟨-, hx⟩
          · exact hy
          · exact absurd haX hx
          · exact absurd haX hx
        have haZ : a ∈ Z := by
          rcases haS with (⟨-, hz⟩ | ⟨-, hx⟩) | ⟨-, hx⟩
          · exact hz
          · exact absurd haX hx
          · exact absurd haX hx
        exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
          Abs_trace [Ev a] ^^^ s', Abs_trace [Ev a] ^^^ t',
          par_tr_head.mpr (Or.inl ⟨haX, s', t', hpar', rfl, rfl⟩),
          (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, s', rfl, hf1, haY⟩),
          Ev_appt_in_failures_Ext_pre_choice.mpr ⟨hf2, haZ⟩⟩
      · simp only [procIte_neg haX] at hbr
        by_cases haYZ : a ∈ Y ∧ a ∈ Z
        · simp only [procIte_pos haYZ, in_failures_Int_choice, in_failures_Parallel] at hbr
          rcases hbr with ⟨u', Ya, Za, heq, hsep, s', t, hpar', hf1, hf2⟩ |
            ⟨u', Ya, Za, heq, hsep, s, t', hpar', hf1, hf2⟩
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              Abs_trace [Ev a] ^^^ s', t,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, s', rfl, hf1, haYZ.1⟩),
              hf2⟩
          · simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              s, Abs_trace [Ev a] ^^^ t',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, t', hpar', rfl⟩)),
              hf1,
              Ev_appt_in_failures_Ext_pre_choice.mpr ⟨hf2, haYZ.2⟩⟩
        · simp only [procIte_neg haYZ] at hbr
          by_cases haY : a ∈ Y
          · simp only [procIte_pos haY, in_failures_Parallel] at hbr
            obtain ⟨u', Ya, Za, heq, hsep, s', t, hpar', hf1, hf2⟩ := hbr
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              Abs_trace [Ev a] ^^^ s', t,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_failures_Timeout_Ext_pre_choice).mpr (Or.inr ⟨a, s', rfl, hf1, haY⟩),
              hf2⟩
          · simp only [procIte_neg haY, in_failures_Parallel] at hbr
            obtain ⟨u', Ya, Za, heq, hsep, s, t', hpar', hf1, hf2⟩ := hbr
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            have haZ : a ∈ Z := by
              rcases haS with (⟨⟨-, hy⟩, -⟩ | ⟨hy, -⟩) | ⟨hz, -⟩
              · exact absurd hy haY
              · exact absurd hy haY
              · exact hz
            exact ⟨Abs_trace [Ev a] ^^^ w', Ya, Za, rfl, hsep,
              s, Abs_trace [Ev a] ^^^ t',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, t', hpar', rfl⟩)),
              hf1,
              Ev_appt_in_failures_Ext_pre_choice.mpr ⟨hf2, haZ⟩⟩

/- (*** right ****) -/

-- Derived from `cspF_Parallel_Timeout_input_l` by commutativity, following
-- the Isabelle original.
theorem cspF_Parallel_Timeout_input_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice Y Pf |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
                (proc.Ext_pre_choice Y Pf |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q)
                (proc.Ext_pre_choice Y Pf |[X]| Qf x))))
        (proc.Ext_pre_choice Y Pf |[X]| Q)) := by
  refine cspF_rw_left_eq cspF_Parallel_commut ?_
  refine cspF_rw_left_eq cspF_Parallel_Timeout_input_l ?_
  have hS : ((X ∩ Z ∩ Y) ∪ (Z \ X) ∪ (Y \ X))
      = ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  refine cspF_Timeout_cong (cspF_Ext_pre_choice_cong hS fun a ha => ?_) cspF_Parallel_commut
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at ha
  by_cases haX : a ∈ X
  · rw [procIte_pos haX, procIte_pos haX]
    exact cspF_Parallel_commut
  · rw [procIte_neg haX, procIte_neg haX]
    by_cases haY : a ∈ Y <;> by_cases haZ : a ∈ Z
    · rw [procIte_pos (⟨haZ, haY⟩ : a ∈ Z ∧ a ∈ Y), procIte_pos ⟨haY, haZ⟩]
      refine cspF_rw_left_eq cspF_Int_choice_commut ?_
      exact cspF_Int_choice_cong cspF_Parallel_commut cspF_Parallel_commut
    · rw [procIte_neg (fun h : a ∈ Z ∧ a ∈ Y => haZ h.1),
          procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haZ h.2),
          procIte_neg haZ, procIte_pos haY]
      exact cspF_Parallel_commut
    · rw [procIte_neg (fun h : a ∈ Z ∧ a ∈ Y => haY h.2),
          procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haY h.1),
          procIte_pos haZ, procIte_neg haY]
      exact cspF_Parallel_commut
    · exact absurd ha (by tauto)

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_input` is
   represented by `cspF_Parallel_Timeout_input_l` and
   `cspF_Parallel_Timeout_input_r`. -/

/-
(*** cspF_step_ext ***)
-/

/- The Isabelle theorem bundle `cspF_step_ext` is represented by
   `cspF_Parallel_Timeout_split`, `cspF_Parallel_Timeout_input_l`, and
   `cspF_Parallel_Timeout_input_r`. -/
