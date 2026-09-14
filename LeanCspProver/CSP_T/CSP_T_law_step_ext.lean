           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_basic
import LeanCspProver.CSP_T.CSP_T_simp

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
             Parallel expansion & distribution
 *********************************************************)
-/

/-- An `Ev`-headed trace is in `? :A -> Pf` iff its head is offered and its
    tail is a trace of the chosen branch.  Used by the hand-written timeout
    step proofs below (the Isabelle originals get this from `in_traces` +
    `Act_prefix` clauses). -/
theorem Ev_appt_in_traces_Ext_pre_choice
    {a : α} {s : traceType α} {A : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    (Abs_trace [Ev a] ^^^ s :t traces (proc.Ext_pre_choice A Pf) M) ↔
      (s :t traces (Pf a) M ∧ a ∈ A) := by
  rw [in_traces_Ext_pre_choice]
  constructor
  · rintro (h | ⟨b, s', heq, hs', hb⟩)
    · exact absurd h event_app_not_nil_left
    · obtain ⟨rfl, rfl⟩ := appt_same_head.mp heq
      exact ⟨hs', hb⟩
  · rintro ⟨hs, ha⟩
    exact Or.inr ⟨a, s, rfl, hs, ha⟩

/-- `<Tick>` is never a trace of an external prefix choice. -/
theorem Tick_notin_traces_Ext_pre_choice
    {A : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    ¬ ((Abs_trace [Tick] : traceType α) :t traces (proc.Ext_pre_choice A Pf) M) := by
  rw [in_traces_Ext_pre_choice]
  rintro (h | ⟨b, s', heq, -, -⟩)
  · exact one_neq_nil h
  · exact Tick_neq_Ev_appt heq

-- Hand-written semantic proof following the Isabelle original
-- (CSP_T_law_step_ext.thy): unfold to trace membership, decompose the
-- parallel trace with `par_tr_head`, and supply the witnesses by hand.
theorem cspT_Parallel_Timeout_split
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P Q : proc p α} {M : p → domTType α} :
    eqT ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| (Timeout (proc.Ext_pre_choice Z Qf) Q)) M M
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
  simp only [cspT_eqT_iff, Timeout_def]
  intro t
  rw [in_traces_Parallel, in_traces_Timeout1, in_traces_Ext_pre_choice, in_traces_Int_choice,
    in_traces_Parallel, in_traces_Parallel]
  constructor
  -- ==> direction
  · rintro ⟨s, u, hpar, hs, hu⟩
    rw [in_traces_Timeout1] at hs hu
    rcases hs with hsE | hsP
    · rcases hu with huE | huQ
      · -- both components are external-prefix traces
        rcases trace_nil_or_Tick_or_Ev t with rfl | rfl | ⟨a, t', rfl⟩
        · exact Or.inl (Or.inl rfl)
        · obtain ⟨rfl, rfl⟩ := par_tr_Tick1.mp hpar
          exact absurd hsE Tick_notin_traces_Ext_pre_choice
        · rcases par_tr_head.mp hpar with
            ⟨haX, s', u', hpar', rfl, rfl⟩ | ⟨haX, s', hpar', rfl⟩ | ⟨haX, u', hpar', rfl⟩
          · -- synchronised head: a ∈ X, both components step on a
            obtain ⟨hs', haY⟩ := Ev_appt_in_traces_Ext_pre_choice.mp hsE
            obtain ⟨hu', haZ⟩ := Ev_appt_in_traces_Ext_pre_choice.mp huE
            refine Or.inl (Or.inr ⟨a, t', rfl, ?_, ?_⟩)
            · simp only [procIte_pos haX, in_traces_Parallel]
              exact ⟨s', u', hpar', hs', hu'⟩
            · simp only [Set.mem_union, Set.mem_inter_iff]
              exact Or.inl (Or.inl ⟨⟨haX, haY⟩, haZ⟩)
          · -- left head: a ∉ X, the left component steps on a
            obtain ⟨hs', haY⟩ := Ev_appt_in_traces_Ext_pre_choice.mp hsE
            refine Or.inl (Or.inr ⟨a, t', rfl, ?_, ?_⟩)
            · simp only [procIte_neg haX]
              by_cases haZ : a ∈ Z
              · simp only [procIte_pos (⟨haY, haZ⟩ : a ∈ Y ∧ a ∈ Z), in_traces_Int_choice,
                  in_traces_Parallel]
                exact Or.inl ⟨s', u, hpar', hs', (in_traces_Timeout1).mpr (Or.inl huE)⟩
              · simp only [procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haZ h.2), procIte_pos haY,
                  in_traces_Parallel]
                exact ⟨s', u, hpar', hs', (in_traces_Timeout1).mpr (Or.inl huE)⟩
            · simp only [Set.mem_union, Set.mem_diff]
              exact Or.inl (Or.inr ⟨haY, haX⟩)
          · -- right head: a ∉ X, the right component steps on a
            obtain ⟨hu', haZ⟩ := Ev_appt_in_traces_Ext_pre_choice.mp huE
            refine Or.inl (Or.inr ⟨a, t', rfl, ?_, ?_⟩)
            · simp only [procIte_neg haX]
              by_cases haY : a ∈ Y
              · simp only [procIte_pos (⟨haY, haZ⟩ : a ∈ Y ∧ a ∈ Z), in_traces_Int_choice,
                  in_traces_Parallel]
                exact Or.inr ⟨s, u', hpar', (in_traces_Timeout1).mpr (Or.inl hsE), hu'⟩
              · simp only [procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haY h.1), procIte_neg haY,
                  in_traces_Parallel]
                exact ⟨s, u', hpar', (in_traces_Timeout1).mpr (Or.inl hsE), hu'⟩
            · simp only [Set.mem_union, Set.mem_diff]
              exact Or.inr ⟨haZ, haX⟩
      · -- u ∈ traces Q : the timeout tail, right component
        exact Or.inr (Or.inr ⟨s, u, hpar, (in_traces_Timeout1).mpr (Or.inl hsE), huQ⟩)
    · -- s ∈ traces P : the timeout tail, left component
      exact Or.inr (Or.inl ⟨s, u, hpar, hsP, (in_traces_Timeout1).mpr hu⟩)
  -- <== direction
  · rintro ((rfl | ⟨a, t', rfl, hbr, haS⟩) | hTail | hTail)
    · exact ⟨<>, <>, par_tr_nil2.mpr rfl, (in_traces_Timeout1).mpr (Or.inl nilt_in_T),
        (in_traces_Timeout1).mpr (Or.inl nilt_in_T)⟩
    · -- t = <Ev a> ^^^ t' from the step part
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at haS
      by_cases haX : a ∈ X
      · -- synchronised branch
        simp only [procIte_pos haX, in_traces_Parallel] at hbr
        obtain ⟨s', u', hpar', hs', hu'⟩ := hbr
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
        exact ⟨Abs_trace [Ev a] ^^^ s', Abs_trace [Ev a] ^^^ u',
          par_tr_head.mpr (Or.inl ⟨haX, s', u', hpar', rfl, rfl⟩),
          (in_traces_Timeout1).mpr (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hs', haY⟩)),
          (in_traces_Timeout1).mpr (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hu', haZ⟩))⟩
      · simp only [procIte_neg haX] at hbr
        by_cases haYZ : a ∈ Y ∧ a ∈ Z
        · simp only [procIte_pos haYZ, in_traces_Int_choice, in_traces_Parallel] at hbr
          rcases hbr with ⟨s', u, hpar', hs', hu⟩ | ⟨s, u', hpar', hs, hu'⟩
          · exact ⟨Abs_trace [Ev a] ^^^ s', u,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_traces_Timeout1).mpr
                (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hs', haYZ.1⟩)),
              hu⟩
          · exact ⟨s, Abs_trace [Ev a] ^^^ u',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, u', hpar', rfl⟩)),
              hs,
              (in_traces_Timeout1).mpr
                (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hu', haYZ.2⟩))⟩
        · simp only [procIte_neg haYZ] at hbr
          by_cases haY : a ∈ Y
          · simp only [procIte_pos haY, in_traces_Parallel] at hbr
            obtain ⟨s', u, hpar', hs', hu⟩ := hbr
            exact ⟨Abs_trace [Ev a] ^^^ s', u,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_traces_Timeout1).mpr
                (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hs', haY⟩)),
              hu⟩
          · simp only [procIte_neg haY, in_traces_Parallel] at hbr
            obtain ⟨s, u', hpar', hs, hu'⟩ := hbr
            have haZ : a ∈ Z := by
              rcases haS with (⟨⟨-, hy⟩, -⟩ | ⟨hy, -⟩) | ⟨hz, -⟩
              · exact absurd hy haY
              · exact absurd hy haY
              · exact hz
            exact ⟨s, Abs_trace [Ev a] ^^^ u',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, u', hpar', rfl⟩)),
              hs,
              (in_traces_Timeout1).mpr
                (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hu', haZ⟩))⟩
    · -- timeout tail, left: t ∈ traces (P |[X]| (E_Z [> Q))
      obtain ⟨s, u, hpar, hs, hu⟩ := hTail
      exact ⟨s, u, hpar, (in_traces_Timeout1).mpr (Or.inr hs), hu⟩
    · -- timeout tail, right: t ∈ traces ((E_Y [> P) |[X]| Q)
      obtain ⟨s, u, hpar, hs, hu⟩ := hTail
      exact ⟨s, u, hpar, hs, (in_traces_Timeout1).mpr (Or.inr hu)⟩

/-
(*********************************************************
            Parallel expansion & distribution 2
 *********************************************************)
-/

-- Hand-written semantic proof following the Isabelle original.
theorem cspT_Parallel_Timeout_input_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| proc.Ext_pre_choice Z Qf) M M
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
  simp only [cspT_eqT_iff, Timeout_def]
  intro t
  rw [in_traces_Parallel, in_traces_Timeout1, in_traces_Ext_pre_choice, in_traces_Parallel]
  constructor
  -- ==> direction
  · rintro ⟨s, u, hpar, hs, hu⟩
    rw [in_traces_Timeout1] at hs
    rcases hs with hsE | hsP
    · rcases trace_nil_or_Tick_or_Ev t with rfl | rfl | ⟨a, t', rfl⟩
      · exact Or.inl (Or.inl rfl)
      · obtain ⟨rfl, rfl⟩ := par_tr_Tick1.mp hpar
        exact absurd hsE Tick_notin_traces_Ext_pre_choice
      · rcases par_tr_head.mp hpar with
          ⟨haX, s', u', hpar', rfl, rfl⟩ | ⟨haX, s', hpar', rfl⟩ | ⟨haX, u', hpar', rfl⟩
        · -- synchronised head
          obtain ⟨hs', haY⟩ := Ev_appt_in_traces_Ext_pre_choice.mp hsE
          obtain ⟨hu', haZ⟩ := Ev_appt_in_traces_Ext_pre_choice.mp hu
          refine Or.inl (Or.inr ⟨a, t', rfl, ?_, ?_⟩)
          · simp only [procIte_pos haX, in_traces_Parallel]
            exact ⟨s', u', hpar', hs', hu'⟩
          · simp only [Set.mem_union, Set.mem_inter_iff]
            exact Or.inl (Or.inl ⟨⟨haX, haY⟩, haZ⟩)
        · -- left head
          obtain ⟨hs', haY⟩ := Ev_appt_in_traces_Ext_pre_choice.mp hsE
          refine Or.inl (Or.inr ⟨a, t', rfl, ?_, ?_⟩)
          · simp only [procIte_neg haX]
            by_cases haZ : a ∈ Z
            · simp only [procIte_pos (⟨haY, haZ⟩ : a ∈ Y ∧ a ∈ Z), in_traces_Int_choice,
                in_traces_Parallel]
              exact Or.inl ⟨s', u, hpar', hs', hu⟩
            · simp only [procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haZ h.2), procIte_pos haY,
                in_traces_Parallel]
              exact ⟨s', u, hpar', hs', hu⟩
          · simp only [Set.mem_union, Set.mem_diff]
            exact Or.inl (Or.inr ⟨haY, haX⟩)
        · -- right head
          obtain ⟨hu', haZ⟩ := Ev_appt_in_traces_Ext_pre_choice.mp hu
          refine Or.inl (Or.inr ⟨a, t', rfl, ?_, ?_⟩)
          · simp only [procIte_neg haX]
            by_cases haY : a ∈ Y
            · simp only [procIte_pos (⟨haY, haZ⟩ : a ∈ Y ∧ a ∈ Z), in_traces_Int_choice,
                in_traces_Parallel]
              exact Or.inr ⟨s, u', hpar', (in_traces_Timeout1).mpr (Or.inl hsE), hu'⟩
            · simp only [procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haY h.1), procIte_neg haY,
                in_traces_Parallel]
              exact ⟨s, u', hpar', (in_traces_Timeout1).mpr (Or.inl hsE), hu'⟩
          · simp only [Set.mem_union, Set.mem_diff]
            exact Or.inr ⟨haZ, haX⟩
    · exact Or.inr ⟨s, u, hpar, hsP, hu⟩
  -- <== direction
  · rintro ((rfl | ⟨a, t', rfl, hbr, haS⟩) | hTail)
    · exact ⟨<>, <>, par_tr_nil2.mpr rfl, (in_traces_Timeout1).mpr (Or.inl nilt_in_T),
        nilt_in_T⟩
    · simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at haS
      by_cases haX : a ∈ X
      · simp only [procIte_pos haX, in_traces_Parallel] at hbr
        obtain ⟨s', u', hpar', hs', hu'⟩ := hbr
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
        exact ⟨Abs_trace [Ev a] ^^^ s', Abs_trace [Ev a] ^^^ u',
          par_tr_head.mpr (Or.inl ⟨haX, s', u', hpar', rfl, rfl⟩),
          (in_traces_Timeout1).mpr (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hs', haY⟩)),
          Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hu', haZ⟩⟩
      · simp only [procIte_neg haX] at hbr
        by_cases haYZ : a ∈ Y ∧ a ∈ Z
        · simp only [procIte_pos haYZ, in_traces_Int_choice, in_traces_Parallel] at hbr
          rcases hbr with ⟨s', u, hpar', hs', hu⟩ | ⟨s, u', hpar', hs, hu'⟩
          · exact ⟨Abs_trace [Ev a] ^^^ s', u,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_traces_Timeout1).mpr
                (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hs', haYZ.1⟩)),
              hu⟩
          · exact ⟨s, Abs_trace [Ev a] ^^^ u',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, u', hpar', rfl⟩)),
              hs,
              Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hu', haYZ.2⟩⟩
        · simp only [procIte_neg haYZ] at hbr
          by_cases haY : a ∈ Y
          · simp only [procIte_pos haY, in_traces_Parallel] at hbr
            obtain ⟨s', u, hpar', hs', hu⟩ := hbr
            exact ⟨Abs_trace [Ev a] ^^^ s', u,
              par_tr_head.mpr (Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)),
              (in_traces_Timeout1).mpr
                (Or.inl (Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hs', haY⟩)),
              hu⟩
          · simp only [procIte_neg haY, in_traces_Parallel] at hbr
            obtain ⟨s, u', hpar', hs, hu'⟩ := hbr
            have haZ : a ∈ Z := by
              rcases haS with (⟨⟨-, hy⟩, -⟩ | ⟨hy, -⟩) | ⟨hz, -⟩
              · exact absurd hy haY
              · exact absurd hy haY
              · exact hz
            exact ⟨s, Abs_trace [Ev a] ^^^ u',
              par_tr_head.mpr (Or.inr (Or.inr ⟨haX, u', hpar', rfl⟩)),
              hs,
              Ev_appt_in_traces_Ext_pre_choice.mpr ⟨hu', haZ⟩⟩
    · obtain ⟨s, u, hpar, hs, hu⟩ := hTail
      exact ⟨s, u, hpar, (in_traces_Timeout1).mpr (Or.inr hs), hu⟩

-- Derived from `cspT_Parallel_Timeout_input_l` by commutativity, following
-- the Isabelle original.
theorem cspT_Parallel_Timeout_input_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice Y Pf |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) M M
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
  refine cspT_rw_left_eq cspT_Parallel_commut ?_
  refine cspT_rw_left_eq cspT_Parallel_Timeout_input_l ?_
  have hS : ((X ∩ Z ∩ Y) ∪ (Z \ X) ∪ (Y \ X))
      = ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  refine cspT_Timeout_cong (cspT_Ext_pre_choice_cong hS fun a ha => ?_) cspT_Parallel_commut
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at ha
  by_cases haX : a ∈ X
  · rw [procIte_pos haX, procIte_pos haX]
    exact cspT_Parallel_commut
  · rw [procIte_neg haX, procIte_neg haX]
    by_cases haY : a ∈ Y <;> by_cases haZ : a ∈ Z
    · rw [procIte_pos (⟨haZ, haY⟩ : a ∈ Z ∧ a ∈ Y), procIte_pos ⟨haY, haZ⟩]
      refine cspT_rw_left_eq cspT_Int_choice_commut ?_
      exact cspT_Int_choice_cong cspT_Parallel_commut cspT_Parallel_commut
    · rw [procIte_neg (fun h : a ∈ Z ∧ a ∈ Y => haZ h.1),
          procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haZ h.2),
          procIte_neg haZ, procIte_pos haY]
      exact cspT_Parallel_commut
    · rw [procIte_neg (fun h : a ∈ Z ∧ a ∈ Y => haY h.2),
          procIte_neg (fun h : a ∈ Y ∧ a ∈ Z => haY h.1),
          procIte_pos haZ, procIte_neg haY]
      exact cspT_Parallel_commut
    · exact absurd ha (by tauto)

/- The Isabelle theorem bundle `cspT_Parallel_Timeout_input` is
   represented by `cspT_Parallel_Timeout_input_l` and
   `cspT_Parallel_Timeout_input_r`. -/

/-
(*** cspT_step_ext ***)
-/

/- The Isabelle theorem bundle `cspT_step_ext` is represented by
   `cspT_Parallel_Timeout_split`, `cspT_Parallel_Timeout_input_l`, and
   `cspT_Parallel_Timeout_input_r`. -/
