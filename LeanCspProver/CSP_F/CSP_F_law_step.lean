           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_law_step
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
                    stop expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_STOP_step
    {Pf : α → proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.STOP : proc p α) M1 M2 (proc.Ext_pre_choice (∅ : Set α) Pf) := by
  rw [cspF_cspT_eqF_semantics]
  constructor
  · simpa using (cspT_STOP_step (Pf := Pf) (M1 := fstF ∘ M1) (M2 := fstF ∘ M2))
  · apply le_antisymm
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_STOP] at hs
      rw [in_failures_Ext_pre_choice]
      rcases hs with ⟨Y, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      exact Or.inl ⟨X, rfl, by simp⟩
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_Ext_pre_choice] at hs
      rw [in_failures_STOP]
      rcases hs with ⟨Y, hEq, _hEmpty⟩ | ⟨a, t, Y, _hEq, _htY, haEmpty⟩
      · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact ⟨X, rfl⟩
      · simp at haEmpty

/- to avoide producing free variables in tactics -/

theorem cspF_STOP_step_DIV
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.STOP : proc p α) M1 M2
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => (proc.DIV : proc q α))) := by
  rw [cspF_cspT_eqF_semantics]
  constructor
  · simpa using (cspT_STOP_step_DIV (M1 := fstF ∘ M1) (M2 := fstF ∘ M2))
  · apply le_antisymm
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_STOP] at hs
      rw [in_failures_Ext_pre_choice]
      rcases hs with ⟨Y, hEq⟩
      rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
      exact Or.inl ⟨X, rfl, by simp⟩
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_Ext_pre_choice] at hs
      rw [in_failures_STOP]
      rcases hs with ⟨Y, hEq, _hEmpty⟩ | ⟨a, t, Y, _hEq, _htY, haEmpty⟩
      · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact ⟨X, rfl⟩
      · simp at haEmpty

/-
(*********************************************************
                    Act_prefix expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Act_prefix_step
    {a : α} {P : proc p α} {M : p → domFType α} :
    eqF (a ~> P) M M (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) := by
  rw [cspF_cspT_eqF_semantics]
  constructor
  · simpa using (cspT_Act_prefix_step (a := a) (P := P) (M := fstF ∘ M))
  · apply le_antisymm
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_Act_prefix] at hs
      rw [in_failures_Ext_pre_choice]
      rcases hs with ⟨Y, hEq, hNotIn⟩ | ⟨t, Y, hEq, htY⟩
      · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact Or.inl ⟨X, rfl, by simpa [Set.image_singleton] using hNotIn⟩
      · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact Or.inr ⟨a, t, X, rfl, htY, by simp⟩
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_Ext_pre_choice] at hs
      rw [in_failures_Act_prefix]
      rcases hs with ⟨Y, hEq, hEmpty⟩ | ⟨x, t, Y, hEq, htY, hx⟩
      · rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact Or.inl ⟨X, rfl, by simpa [Set.image_singleton] using hEmpty⟩
      · have hx' : x = a := by simpa using hx
        subst x
        rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
        exact Or.inr ⟨t, X, rfl, htY⟩

/-
(*********************************************************
                    Ext choice expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Ext_choice_step
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf)) M M
      (proc.Ext_pre_choice (X ∪ Y) fun x =>
        procIte (x ∈ X ∧ x ∈ Y) (Pf x |~| Qf x)
          (procIte (x ∈ X) (Pf x) (Qf x))) := by
  refine cspF_eqF_of_eqT cspT_Ext_choice_step ?_
  intro t W
  rw [in_failures_Ext_pre_choice
      (Pf := fun x => procIte (x ∈ X ∧ x ∈ Y) (Pf x |~| Qf x) (procIte (x ∈ X) (Pf x) (Qf x))),
    in_failures_Ext_choice]
  constructor
  · rintro (⟨⟨V, hEq⟩, hP, hQ⟩ | ⟨s, ⟨V, hEq⟩, hor, hne⟩ | ⟨V, hEq, hTk, -⟩)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
      rw [in_failures_Ext_pre_choice] at hP hQ
      rcases hP with ⟨V1, hE1, hX⟩ | ⟨a, s, V1, hE1, -, -⟩
      · rcases hQ with ⟨V2, hE2, hY⟩ | ⟨a, s, V2, hE2, -, -⟩
        · refine Or.inl ⟨W, rfl, ?_⟩
          rw [Set.image_union, Set.union_inter_distrib_right]
          have hX' : Ev '' X ∩ W = ∅ := by
            rw [← (Prod.mk.inj hE1).2] at hX; exact hX
          have hY' : Ev '' Y ∩ W = ∅ := by
            rw [← (Prod.mk.inj hE2).2] at hY; exact hY
          rw [hX', hY', Set.union_self]
        · exact absurd (Prod.mk.inj hE2).1 (by simp)
      · exact absurd (Prod.mk.inj hE1).1 (by simp)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
      rcases hor with hP | hQ
      · rw [in_failures_Ext_pre_choice] at hP
        rcases hP with ⟨V1, hE1, -⟩ | ⟨a, s', V1, hE1, hPf, haX⟩
        · exact absurd (Prod.mk.inj hE1).1 hne
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
          refine Or.inr ⟨a, s', W, rfl, ?_, Or.inl haX⟩
          by_cases haY : a ∈ Y
          · rw [procIte_pos ⟨haX, haY⟩, in_failures_Int_choice]
            exact Or.inl hPf
          · rw [procIte_neg (by tauto), procIte_pos haX]
            exact hPf
      · rw [in_failures_Ext_pre_choice] at hQ
        rcases hQ with ⟨V1, hE1, -⟩ | ⟨a, s', V1, hE1, hQf, haY⟩
        · exact absurd (Prod.mk.inj hE1).1 hne
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
          refine Or.inr ⟨a, s', W, rfl, ?_, Or.inr haY⟩
          by_cases haX : a ∈ X
          · rw [procIte_pos ⟨haX, haY⟩, in_failures_Int_choice]
            exact Or.inr hQf
          · rw [procIte_neg (by tauto), procIte_neg haX]
            exact hQf
    · rcases hTk with h | h
      · exact absurd h Tick_notin_traces_Ext_pre_choice
      · exact absurd h Tick_notin_traces_Ext_pre_choice
  · rintro (⟨V, hEq, hXY⟩ | ⟨a, s', V, hEq, hf, haXY⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [Set.image_union, Set.union_inter_distrib_right,
        Set.union_empty_iff] at hXY
      exact Or.inl ⟨⟨W, rfl⟩,
        in_failures_Ext_pre_choice.mpr (Or.inl ⟨W, rfl, hXY.1⟩),
        in_failures_Ext_pre_choice.mpr (Or.inl ⟨W, rfl, hXY.2⟩)⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      refine Or.inr (Or.inl ⟨Abs_trace [Ev a] ^^^ s', ⟨W, rfl⟩, ?_, by simp⟩)
      rcases haXY with haX | haY
      · by_cases haY : a ∈ Y
        · rw [procIte_pos ⟨haX, haY⟩, in_failures_Int_choice] at hf
          rcases hf with hP | hQ
          · exact Or.inl (in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', W, rfl, hP, haX⟩))
          · exact Or.inr (in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', W, rfl, hQ, haY⟩))
        · rw [procIte_neg (by tauto), procIte_pos haX] at hf
          exact Or.inl (in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', W, rfl, hf, haX⟩))
      · by_cases haX : a ∈ X
        · rw [procIte_pos ⟨haX, haY⟩, in_failures_Int_choice] at hf
          rcases hf with hP | hQ
          · exact Or.inl (in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', W, rfl, hP, haX⟩))
          · exact Or.inr (in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', W, rfl, hQ, haY⟩))
        · rw [procIte_neg (by tauto), procIte_neg haX] at hf
          exact Or.inr (in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', W, rfl, hf, haY⟩))

/-
(*********************************************************
                    Parallel expansion
 *********************************************************)
-/

/- set 1 -/

theorem cspF_Parallel_step_set1
    {X Y Z : Set α} {Ya Za : Set (event α)} :
    Ya \ insert Tick (Ev '' X) = Za \ insert Tick (Ev '' X) →
      Ev '' Y ∩ Ya = ∅ → Ev '' Z ∩ Za = ∅ →
        Ev '' (X ∩ Y ∩ Z) ∩ (Ya ∪ Za) = ∅ := by
  cspF_auto

/- set 2 -/

theorem cspF_Parallel_step_set2
    {X Y Z : Set α} {Ya Za : Set (event α)} :
    Ya \ insert Tick (Ev '' X) = Za \ insert Tick (Ev '' X) →
      Ev '' Y ∩ Ya = ∅ → Ev '' Z ∩ Za = ∅ →
        Ev '' (Y \ X) ∩ (Ya ∪ Za) = ∅ := by
  intro hEq hY _
  rw [Set.eq_empty_iff_forall_notMem]
  rintro e ⟨⟨a, ⟨haY, haX⟩, rfl⟩, he⟩
  have h1 : (Ev a : event α) ∉ Ya := by
    intro h
    have hm : (Ev a : event α) ∈ Ev '' Y ∩ Ya := ⟨⟨a, haY, rfl⟩, h⟩
    rw [hY] at hm
    exact hm
  rcases he with h | h
  · exact h1 h
  · have hmem : (Ev a : event α) ∈ Za \ insert Tick (Ev '' X) := by
      refine ⟨h, ?_⟩
      rw [Set.mem_insert_iff]
      rintro (hT | ⟨b, hb, hEv⟩)
      · exact absurd hT (by simp)
      · exact haX (by cases hEv; exact hb)
    rw [← hEq] at hmem
    exact h1 hmem.1

/- set 3 -/

theorem cspF_Parallel_step_set3
    {X Y Z : Set α} {Ya Za : Set (event α)} :
    Ya \ insert Tick (Ev '' X) = Za \ insert Tick (Ev '' X) →
      Ev '' Y ∩ Ya = ∅ → Ev '' Z ∩ Za = ∅ →
        Ev '' (Z \ X) ∩ (Ya ∪ Za) = ∅ := by
  intro hEq _ hZ
  rw [Set.eq_empty_iff_forall_notMem]
  rintro e ⟨⟨a, ⟨haZ, haX⟩, rfl⟩, he⟩
  have h1 : (Ev a : event α) ∉ Za := by
    intro h
    have hm : (Ev a : event α) ∈ Ev '' Z ∩ Za := ⟨⟨a, haZ, rfl⟩, h⟩
    rw [hZ] at hm
    exact hm
  rcases he with h | h
  · have hmem : (Ev a : event α) ∈ Ya \ insert Tick (Ev '' X) := by
      refine ⟨h, ?_⟩
      rw [Set.mem_insert_iff]
      rintro (hT | ⟨b, hb, hEv⟩)
      · exact absurd hT (by simp)
      · exact haX (by cases hEv; exact hb)
    rw [hEq] at hmem
    exact h1 hmem.1
  · exact h1 h

/- set 4 -/

theorem cspF_Parallel_step_set4
    {X Y Z : Set α} {Xa : Set (event α)} :
    Ev '' ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) ∩ Xa = ∅ →
      Xa =
        (Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Y)) ∪
          ((Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Z))) := by
  cspF_auto_step

/- set 5 -/

theorem cspF_Parallel_step_set5
    {X Y Z : Set α} {Xa : Set (event α)} :
    Ev '' ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) ∩ Xa = ∅ →
      Ev '' Y ∩ ((Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Y))) = ∅ ∧
        Ev '' Z ∩
            ((Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Z))) = ∅ := by
  cspF_auto

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/-- A failure of `? :Y -> Pf` whose trace starts with `Ev a`. -/
private theorem failures_Ext_pre_choice_cons {Y : Set α} {Pf : α → proc p α}
    {a : α} {s : traceType α} {V : Set (event α)} {M : p → domFType α}
    (h : (Abs_trace [Ev a] ^^^ s, V) :f failures (proc.Ext_pre_choice Y Pf) M) :
    a ∈ Y ∧ (s, V) :f failures (Pf a) M := by
  rw [in_failures_Ext_pre_choice] at h
  rcases h with ⟨V1, hE1, -⟩ | ⟨b, s2, V1, hE1, hPf, hbY⟩
  · exact absurd (Prod.mk.inj hE1).1 (by simp)
  · obtain ⟨hs, rfl⟩ := Prod.mk.inj hE1
    obtain ⟨rfl, rfl⟩ := appt_same_head.mp hs
    exact ⟨hbY, hPf⟩

/-- `? :Y -> Pf` has no failure at the trace `<Tick>`. -/
private theorem failures_Ext_pre_choice_Tick {Y : Set α} {Pf : α → proc p α}
    {V : Set (event α)} {M : p → domFType α} :
    ¬ (((Abs_trace [Tick] : traceType α), V) :f failures (proc.Ext_pre_choice Y Pf) M) := by
  intro h
  rw [in_failures_Ext_pre_choice] at h
  rcases h with ⟨V1, hE1, -⟩ | ⟨b, s2, V1, hE1, -, -⟩
  · exact absurd (Prod.mk.inj hE1).1 (by simp)
  · have hhd := congrArg hdt (Prod.mk.inj hE1).1
    simp [hdt_appt] at hhd

theorem cspF_Parallel_step
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.Ext_pre_choice Z Qf)) M M
      (proc.Ext_pre_choice (((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X))) fun x =>
        procIte (x ∈ X) ((Pf x) |[X]| (Qf x))
          (procIte (x ∈ Y ∧ x ∈ Z)
            (((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
              (proc.Ext_pre_choice Y Pf |[X]| Qf x)))
            (procIte (x ∈ Y)
              (Pf x |[X]| proc.Ext_pre_choice Z Qf)
              (proc.Ext_pre_choice Y Pf |[X]| Qf x)))) := by
  refine cspF_eqF_of_eqT cspT_Parallel_step ?_
  intro u W
  have hD : (Ev '' X ∪ ({Tick} : Set (event α))) = insert Tick (Ev '' X) := by
    rw [Set.insert_eq, Set.union_comm]
  rw [in_failures_Parallel, in_failures_Ext_pre_choice
      (Pf := fun x =>
        procIte (x ∈ X) ((Pf x) |[X]| (Qf x))
          (procIte (x ∈ Y ∧ x ∈ Z)
            (((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
              (proc.Ext_pre_choice Y Pf |[X]| Qf x)))
            (procIte (x ∈ Y)
              (Pf x |[X]| proc.Ext_pre_choice Z Qf)
              (proc.Ext_pre_choice Y Pf |[X]| Qf x))))]
  constructor
  · rintro ⟨u', Ya, Za, hEq, hdiff, s, t, hpar, hs, ht⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [hD] at hdiff
    rcases par_tr_step.mp hpar with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨a, v, rfl, hcase⟩
    · rw [in_failures_Ext_pre_choice] at hs ht
      rcases hs with ⟨V1, hE1, hY⟩ | ⟨b, s2, V1, hE1, -, -⟩
      · rcases ht with ⟨V2, hE2, hZ⟩ | ⟨b, t2, V2, hE2, -, -⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj hE1
          obtain ⟨-, rfl⟩ := Prod.mk.inj hE2
          refine Or.inl ⟨Ya ∪ Za, rfl, ?_⟩
          rw [Set.image_union, Set.image_union, Set.union_inter_distrib_right,
            Set.union_inter_distrib_right, Set.union_empty_iff, Set.union_empty_iff]
          exact ⟨⟨cspF_Parallel_step_set1 hdiff hY hZ,
            cspF_Parallel_step_set2 (Z := Z) hdiff hY hZ⟩,
            cspF_Parallel_step_set3 (Y := Y) hdiff hY hZ⟩
        · exact absurd (Prod.mk.inj hE2).1 (by simp)
      · exact absurd (Prod.mk.inj hE1).1 (by simp)
    · exact absurd hs failures_Ext_pre_choice_Tick
    · rcases hcase with ⟨haX, s', t', hpar', rfl, rfl⟩ |
        ⟨haX, s', hpar', rfl⟩ | ⟨haX, t', hpar', rfl⟩
      · obtain ⟨haY, hPf⟩ := failures_Ext_pre_choice_cons hs
        obtain ⟨haZ, hQf⟩ := failures_Ext_pre_choice_cons ht
        refine Or.inr ⟨a, v, Ya ∪ Za, rfl, ?_, Or.inl (Or.inl ⟨⟨haX, haY⟩, haZ⟩)⟩
        rw [procIte_pos haX, in_failures_Parallel]
        exact ⟨v, Ya, Za, rfl, by rw [hD]; exact hdiff, s', t', hpar', hPf, hQf⟩
      · obtain ⟨haY, hPf⟩ := failures_Ext_pre_choice_cons hs
        refine Or.inr ⟨a, v, Ya ∪ Za, rfl, ?_, Or.inl (Or.inr ⟨haY, haX⟩)⟩
        rw [procIte_neg haX]
        have hcore : (v, Ya ∪ Za) :f
            failures (Pf a |[X]| proc.Ext_pre_choice Z Qf) M :=
          in_failures_Parallel.mpr
            ⟨v, Ya, Za, rfl, by rw [hD]; exact hdiff, s', t, hpar', hPf, ht⟩
        by_cases haZ : a ∈ Z
        · rw [procIte_pos ⟨haY, haZ⟩, in_failures_Int_choice]
          exact Or.inl hcore
        · rw [procIte_neg (by tauto), procIte_pos haY]
          exact hcore
      · obtain ⟨haZ, hQf⟩ := failures_Ext_pre_choice_cons ht
        refine Or.inr ⟨a, v, Ya ∪ Za, rfl, ?_, Or.inr ⟨haZ, haX⟩⟩
        rw [procIte_neg haX]
        have hcore : (v, Ya ∪ Za) :f
            failures (proc.Ext_pre_choice Y Pf |[X]| Qf a) M :=
          in_failures_Parallel.mpr
            ⟨v, Ya, Za, rfl, by rw [hD]; exact hdiff, s, t', hpar', hs, hQf⟩
        by_cases haY : a ∈ Y
        · rw [procIte_pos ⟨haY, haZ⟩, in_failures_Int_choice]
          exact Or.inr hcore
        · rw [procIte_neg (by tauto), procIte_neg haY]
          exact hcore
  · rintro (⟨V, hEq, hidx⟩ | ⟨a, v, V, hEq, hf, haidx⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      refine ⟨<>, (W \ insert Tick (Ev '' X)) ∪ ((W ∩ insert Tick (Ev '' X)) \ Ev '' Y),
        (W \ insert Tick (Ev '' X)) ∪ ((W ∩ insert Tick (Ev '' X)) \ Ev '' Z),
        congrArg (fun z => ((<> : traceType α), z)) (cspF_Parallel_step_set4 hidx), ?_,
        <>, <>, par_tr_nil_nil, ?_, ?_⟩
      · rw [hD]
        ext e
        constructor
        · rintro ⟨he, hnd⟩
          rcases he with he | he
          · exact ⟨Or.inl he, hnd⟩
          · exact absurd he.1.2 hnd
        · rintro ⟨he, hnd⟩
          rcases he with he | he
          · exact ⟨Or.inl he, hnd⟩
          · exact absurd he.1.2 hnd
      · exact in_failures_Ext_pre_choice.mpr
          (Or.inl ⟨_, rfl, (cspF_Parallel_step_set5 hidx).1⟩)
      · exact in_failures_Ext_pre_choice.mpr
          (Or.inl ⟨_, rfl, (cspF_Parallel_step_set5 hidx).2⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      by_cases haX : a ∈ X
      · rw [procIte_pos haX, in_failures_Parallel] at hf
        obtain ⟨v', Ya, Za, hE', hdiff, s', t', hpar', hPf, hQf⟩ := hf
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE'
        have haY : a ∈ Y := by
          rcases haidx with (h | h) | h
          · exact h.1.2
          · exact h.1
          · exact absurd haX h.2
        have haZ : a ∈ Z := by
          rcases haidx with (h | h) | h
          · exact h.2
          · exact absurd haX h.2
          · exact h.1
        refine ⟨Abs_trace [Ev a] ^^^ v, Ya, Za, rfl, hdiff,
          Abs_trace [Ev a] ^^^ s', Abs_trace [Ev a] ^^^ t',
          par_tr_step.mpr (Or.inr (Or.inr ⟨a, v, rfl, Or.inl ⟨haX, s', t', hpar', rfl, rfl⟩⟩)),
          in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', Ya, rfl, hPf, haY⟩),
          in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, t', Za, rfl, hQf, haZ⟩)⟩
      · rw [procIte_neg haX] at hf
        have hleft : ∀ {W' : Set (event α)},
            ((v, W') :f failures (Pf a |[X]| proc.Ext_pre_choice Z Qf) M) → a ∈ Y →
              ∃ u' Ya Za, ((Abs_trace [Ev a] ^^^ v, W') = (u', Ya ∪ Za)) ∧
                Ya \ (Ev '' X ∪ ({Tick} : Set (event α))) =
                  Za \ (Ev '' X ∪ ({Tick} : Set (event α))) ∧
                ∃ s t, u' ∈ s |[X]|tr t ∧
                  (s, Ya) :f failures (proc.Ext_pre_choice Y Pf) M ∧
                  (t, Za) :f failures (proc.Ext_pre_choice Z Qf) M := by
          intro W' hc haY
          obtain ⟨v', Ya, Za, hE', hdiff, s', t, hpar', hPf, hQ⟩ := in_failures_Parallel.mp hc
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE'
          exact ⟨Abs_trace [Ev a] ^^^ v, Ya, Za, rfl, hdiff,
            Abs_trace [Ev a] ^^^ s', t,
            par_tr_step.mpr (Or.inr (Or.inr ⟨a, v, rfl, Or.inr (Or.inl ⟨haX, s', hpar', rfl⟩)⟩)),
            in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', Ya, rfl, hPf, haY⟩), hQ⟩
        have hright : ∀ {W' : Set (event α)},
            ((v, W') :f failures (proc.Ext_pre_choice Y Pf |[X]| Qf a) M) → a ∈ Z →
              ∃ u' Ya Za, ((Abs_trace [Ev a] ^^^ v, W') = (u', Ya ∪ Za)) ∧
                Ya \ (Ev '' X ∪ ({Tick} : Set (event α))) =
                  Za \ (Ev '' X ∪ ({Tick} : Set (event α))) ∧
                ∃ s t, u' ∈ s |[X]|tr t ∧
                  (s, Ya) :f failures (proc.Ext_pre_choice Y Pf) M ∧
                  (t, Za) :f failures (proc.Ext_pre_choice Z Qf) M := by
          intro W' hc haZ
          obtain ⟨v', Ya, Za, hE', hdiff, s, t', hpar', hP, hQf⟩ := in_failures_Parallel.mp hc
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE'
          exact ⟨Abs_trace [Ev a] ^^^ v, Ya, Za, rfl, hdiff,
            s, Abs_trace [Ev a] ^^^ t',
            par_tr_step.mpr (Or.inr (Or.inr ⟨a, v, rfl, Or.inr (Or.inr ⟨haX, t', hpar', rfl⟩)⟩)),
            hP, in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, t', Za, rfl, hQf, haZ⟩)⟩
        by_cases hYZ : a ∈ Y ∧ a ∈ Z
        · rw [procIte_pos hYZ, in_failures_Int_choice] at hf
          rcases hf with hc | hc
          · exact hleft hc hYZ.1
          · exact hright hc hYZ.2
        · rw [procIte_neg hYZ] at hf
          by_cases haY : a ∈ Y
          · rw [procIte_pos haY] at hf
            exact hleft hf haY
          · rw [procIte_neg haY] at hf
            have haZ : a ∈ Z := by
              rcases haidx with (h | h) | h
              · exact absurd h.1.1 haX
              · exact absurd h.1 haY
              · exact h.1
            exact hright hf haZ

/-
(*********************************************************
                      Hide expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/-- Failures of `(? :Y -> Pf) -- X`, split by whether the hidden trace is empty. -/
private theorem in_failures_Hiding_Ext_pre_choice'
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α}
    (u : traceType α) (W : Set (event α)) :
    ((u, W) :f failures (proc.Hiding (proc.Ext_pre_choice Y Pf) X) M) ↔
      ((u = <> ∧ Ev '' Y ∩ (Ev '' X ∪ W) = ∅) ∨
        ∃ a s', a ∈ Y ∧ (s', Ev '' X ∪ W) :f failures (Pf a) M ∧
          u = hide_tr (Abs_trace [Ev a] ^^^ s') X) := by
  rw [in_failures_Hiding]
  constructor
  · rintro ⟨s, V, hEq, hf⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Ext_pre_choice] at hf
    rcases hf with ⟨V1, hE1, hY⟩ | ⟨a, s', V1, hE1, hPf, haY⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
      exact Or.inl ⟨by simp, hY⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
      exact Or.inr ⟨a, s', haY, hPf, rfl⟩
  · rintro (⟨rfl, hY⟩ | ⟨a, s', haY, hPf, rfl⟩)
    · exact ⟨<>, W, by simp, in_failures_Ext_pre_choice.mpr (Or.inl ⟨Ev '' X ∪ W, rfl, hY⟩)⟩
    · exact ⟨Abs_trace [Ev a] ^^^ s', W, rfl,
        in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s', Ev '' X ∪ W, rfl, hPf, haY⟩)⟩

theorem cspF_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Hiding (proc.Ext_pre_choice Y Pf) X) M M
      (procIte (Y ∩ X = ∅)
        (proc.Ext_pre_choice Y (fun x => proc.Hiding (Pf x) X))
        ((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X))
          [> Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) := by
  refine cspF_eqF_of_eqT cspT_Hiding_step ?_
  intro u W
  by_cases hYX : Y ∩ X = ∅
  · have hnotX : ∀ a, a ∈ Y → a ∉ X := by
      intro a haY haX
      have hm : a ∈ Y ∩ X := ⟨haY, haX⟩
      rw [hYX] at hm
      exact hm
    rw [procIte_pos hYX, in_failures_Hiding_Ext_pre_choice',
      in_failures_Ext_pre_choice (Pf := fun x => proc.Hiding (Pf x) X)]
    constructor
    · rintro (⟨rfl, hY⟩ | ⟨a, s', haY, hPf, rfl⟩)
      · refine Or.inl ⟨W, rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨he1, he2⟩
        have hm : e ∈ Ev '' Y ∩ (Ev '' X ∪ W) := ⟨he1, Or.inr he2⟩
        rw [hY] at hm
        exact hm
      · refine Or.inr ⟨a, hide_tr s' X, W, ?_, ?_, haY⟩
        · rw [hide_tr_notin_appt (hnotX a haY)]
        · exact in_failures_Hiding.mpr ⟨s', W, rfl, hPf⟩
    · rintro (⟨V, hEq, hY⟩ | ⟨a, s, V, hEq, hf, haY⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        refine Or.inl ⟨rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨b, hbY, rfl⟩, he2⟩
        rcases he2 with ⟨c, hcX, hce⟩ | he2
        · exact hnotX b hbY (by rw [← (inj_Ev hce : c = b)]; exact hcX)
        · have hm : (Ev b : event α) ∈ Ev '' Y ∩ W := ⟨⟨b, hbY, rfl⟩, he2⟩
          rw [hY] at hm
          exact hm
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        rw [in_failures_Hiding] at hf
        obtain ⟨s', V', hE', hPf⟩ := hf
        obtain ⟨hs, rfl⟩ := Prod.mk.inj hE'
        refine Or.inr ⟨a, s', haY, hPf, ?_⟩
        rw [hide_tr_notin_appt (hnotX a haY), hs]
  · obtain ⟨c, hcY, hcX⟩ : ∃ c, c ∈ Y ∧ c ∈ X := by
      by_contra hcon
      exact hYX (Set.eq_empty_iff_forall_notMem.mpr
        (fun c hc => hcon ⟨c, hc.1, hc.2⟩))
    rw [procIte_neg hYX, in_failures_Hiding_Ext_pre_choice', in_failures_Ext_choice]
    constructor
    · rintro (⟨rfl, hY⟩ | ⟨a, s', haY, hPf, rfl⟩)
      · exact absurd (Set.eq_empty_iff_forall_notMem.mp hY (Ev c)
          ⟨⟨c, hcY, rfl⟩, Or.inl ⟨c, hcX, rfl⟩⟩) not_false
      · by_cases haX : a ∈ X
        · have hQ : (hide_tr s' X, W) :f
              failures (Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X)) M :=
            in_failures_Rep_int_choice_com.mpr
              ⟨a, ⟨haY, haX⟩, in_failures_Hiding.mpr ⟨s', W, rfl, hPf⟩⟩
          rw [hide_tr_in haX]
          by_cases hnil : hide_tr s' X = <>
          · rw [hnil] at hQ ⊢
            exact Or.inl ⟨⟨W, rfl⟩,
              in_failures_Int_choice.mpr (Or.inr (in_failures_STOP.mpr ⟨W, rfl⟩)), hQ⟩
          · exact Or.inr (Or.inl ⟨hide_tr s' X, ⟨W, rfl⟩, Or.inr hQ, hnil⟩)
        · rw [hide_tr_notin_appt haX]
          refine Or.inr (Or.inl ⟨Abs_trace [Ev a] ^^^ hide_tr s' X, ⟨W, rfl⟩, Or.inl ?_, by simp⟩)
          exact in_failures_Int_choice.mpr (Or.inl
            (in_failures_Ext_pre_choice.mpr
              (Or.inr ⟨a, hide_tr s' X, W, rfl,
                in_failures_Hiding.mpr ⟨s', W, rfl, hPf⟩, ⟨haY, haX⟩⟩)))
    · have hrep : ∀ (v : traceType α),
          ((v, W) :f failures
              (Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X)) M) →
            ∃ a s', a ∈ Y ∧ (s', Ev '' X ∪ W) :f failures (Pf a) M ∧
              v = hide_tr (Abs_trace [Ev a] ^^^ s') X := by
        intro v hv
        obtain ⟨a, ⟨haY, haX⟩, hf⟩ := in_failures_Rep_int_choice_com.mp hv
        rw [in_failures_Hiding] at hf
        obtain ⟨s', V', hE', hPf⟩ := hf
        obtain ⟨hs, rfl⟩ := Prod.mk.inj hE'
        exact ⟨a, s', haY, hPf, by rw [hide_tr_in haX, hs]⟩
      rintro (⟨⟨V, hEq⟩, -, hQ⟩ | ⟨v, ⟨V, hEq⟩, hor, hne⟩ | ⟨V, hEq, hTk, hsub⟩)
      · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
        exact Or.inr (hrep <> hQ)
      · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
        rcases hor with hP | hQ
        · rcases in_failures_Int_choice.mp hP with hpre | hstop
          · rcases in_failures_Ext_pre_choice.mp hpre with ⟨V1, hE1, -⟩ | ⟨a, v', V1, hE1, hf, ha⟩
            · exact absurd (Prod.mk.inj hE1).1 hne
            · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
              rw [in_failures_Hiding] at hf
              obtain ⟨s', V', hE', hPf⟩ := hf
              obtain ⟨hs, rfl⟩ := Prod.mk.inj hE'
              exact Or.inr ⟨a, s', ha.1, hPf, by rw [hide_tr_notin_appt ha.2, hs]⟩
          · obtain ⟨V1, hE1⟩ := in_failures_STOP.mp hstop
            exact absurd (Prod.mk.inj hE1).1 hne
        · exact Or.inr (hrep u hQ)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        have hTkQ : (Abs_trace [Tick] : traceType α) :t
            traces (Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X)) (fstF ∘ M) := by
          rcases hTk with hTkP | hTkQ
          · rcases in_traces_Int_choice.mp hTkP with h | h
            · exact absurd h Tick_notin_traces_Ext_pre_choice
            · exact absurd (in_traces_STOP.mp h) (by simp)
          · exact hTkQ
        have hT := cspT_eqT_iff.mp
          (cspT_Hiding_step (X := X) (Y := Y) (Pf := Pf) (M := fstF ∘ M))
          (Abs_trace [Tick] : traceType α)
        rw [procIte_neg hYX] at hT
        have hTickL : (Abs_trace [Tick] : traceType α) :t
            traces (proc.Hiding (proc.Ext_pre_choice Y Pf) X) (fstF ∘ M) :=
          hT.mpr (in_traces_Ext_choice.mpr (Or.inr hTkQ))
        refine (in_failures_Hiding_Ext_pre_choice' (X := X) (Y := Y) (Pf := Pf) (M := M)
          <> W).mp (failures_F2_F4 ?_ noTick_nil hsub)
        simpa using hTickL

/-
(*********************************************************
                    Renaming expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Renaming_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[r]]) M M
      (proc.Ext_pre_choice {y | ∃ x, x ∈ X ∧ (x, y) ∈ r} fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ (x, y) ∈ r} (fun x => (Pf x)[[r]])) := by
  refine cspF_eqF_of_eqT cspT_Renaming_step ?_
  intro u W
  rw [in_failures_Ext_pre_choice
      (Pf := fun y => Rep_int_choice_com {x | x ∈ X ∧ (x, y) ∈ r} (fun x => (Pf x)[[r]])),
    in_failures_Renaming (P := proc.Ext_pre_choice X Pf)]
  constructor
  · rintro ⟨s, t, V, hEq, hren, hf⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Ext_pre_choice] at hf
    rcases hf with ⟨V1, hE1, hX⟩ | ⟨a, sa, V1, hE1, hPfa, haX⟩
    · obtain ⟨hs, hV1⟩ := Prod.mk.inj hE1
      subst hs
      refine Or.inl ⟨W, congrArg (fun z => (z, W)) ((ren_tr_nil1 (r := r) (s := u)).1 hren), ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨⟨y, ⟨x, hxX, hxy⟩, rfl⟩, heW⟩
      have hm : (Ev x : event α) ∈ Ev '' X ∩ [[r]]inv W :=
        ⟨⟨x, hxX, rfl⟩, ren_inv_mem_Ev.mpr ⟨y, hxy, heW⟩⟩
      rw [← hV1] at hX
      rw [hX] at hm
      exact hm
    · obtain ⟨hs, hV1⟩ := Prod.mk.inj hE1
      subst hs
      rcases (ren_tr_decompo_left (a := a) (s := sa) (r := r) (u := u)).1 hren with
        ⟨b, ta, htEq, hab, hrena⟩
      subst htEq
      refine Or.inr ⟨b, ta, W, rfl, ?_, ⟨a, haX, hab⟩⟩
      rw [in_failures_Rep_int_choice_com]
      refine ⟨a, ⟨haX, hab⟩, ?_⟩
      rw [in_failures_Renaming]
      exact ⟨sa, ta, W, rfl, hrena, by rw [hV1]; exact hPfa⟩
  · rintro (⟨V, hEq, hX⟩ | ⟨y, ta, V, hEq, hf, hy⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      refine ⟨<>, <>, W, rfl, ren_tr_nil, ?_⟩
      rw [in_failures_Ext_pre_choice]
      refine Or.inl ⟨[[r]]inv W, rfl, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨⟨x, hxX, rfl⟩, he⟩
      obtain ⟨b, hxb, hbW⟩ := ren_inv_mem_Ev.mp he
      have hm : (Ev b : event α) ∈ Ev '' {y | ∃ x, x ∈ X ∧ (x, y) ∈ r} ∩ W :=
        ⟨⟨b, ⟨x, hxX, hxb⟩, rfl⟩, hbW⟩
      rw [hX] at hm
      exact hm
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Rep_int_choice_com] at hf
      obtain ⟨x, hx, hxf⟩ := hf
      rw [in_failures_Renaming] at hxf
      obtain ⟨sa, ta', V', hE', hrena, hPfa⟩ := hxf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE'
      refine ⟨Abs_trace [Ev x] ^^^ sa, Abs_trace [Ev y] ^^^ ta, W, rfl,
        ren_tr_decompo_left_if hx.2 hrena, ?_⟩
      rw [in_failures_Ext_pre_choice]
      exact Or.inr ⟨x, sa, [[r]]inv W, rfl, hPfa, hx.1⟩

/-
(*********************************************************
            Sequential composition expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) ;; Q) M M
      (proc.Ext_pre_choice X (fun x => Pf x ;; Q)) := by
  refine cspF_eqF_of_eqT cspT_Seq_compo_step ?_
  intro u W
  rw [in_failures_Ext_pre_choice (Pf := fun x => Pf x ;; Q),
    in_failures_Seq_compo (P := proc.Ext_pre_choice X Pf) (Q := Q)]
  constructor
  · rintro (⟨t', V, hEq, hPf, hnoT⟩ | ⟨s, t', V, hEq, hsTick, ht', hsNo⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Ext_pre_choice] at hPf
      rcases hPf with ⟨V1, hE1, hX⟩ | ⟨a, s, V1, hE1, hPfa, haX⟩
      · obtain ⟨rfl, hV⟩ := Prod.mk.inj hE1
        refine Or.inl ⟨W, rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨he1, he2⟩
        have hm : e ∈ Ev '' X ∩ V1 := ⟨he1, by rw [← hV]; exact Or.inl he2⟩
        rw [hX] at hm
        exact hm
      · obtain ⟨rfl, hV⟩ := Prod.mk.inj hE1
        refine Or.inr ⟨a, s, W, rfl, ?_, haX⟩
        rw [in_failures_Seq_compo]
        refine Or.inl ⟨s, W, rfl, ?_, ?_⟩
        · rw [hV]; exact hPfa
        · exact (decompo_appt_noTick_only_if (s := Abs_trace [Ev a]) (t := s)
            (Or.inl (noTick_Ev a)) (by simpa using hnoT)).2
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_traces_Ext_pre_choice] at hsTick
      rcases hsTick with hnil | ⟨a, sa, hEqa, hsa, haX⟩
      · exact False.elim (event_app_not_nil_right hsNo hnil)
      · rcases trace_nil_or_Tick_or_Ev s with rfl | hsT | ⟨b, sb, rfl⟩
        · have hhd : (Tick : event α) = Ev a := by
            simpa [appt_nil_left, hdt_appt] using congrArg hdt hEqa
          cases hhd
        · subst hsT
          exact False.elim (not_noTick_Tick hsNo)
        · have hsbNo : noTick sb :=
            (decompo_appt_noTick_only_if (s := Abs_trace [Ev b]) (t := sb)
              (Or.inl (noTick_Ev b)) (by simpa using hsNo)).2
          have hAssoc :
              (Abs_trace [Ev b] ^^^ sb) ^^^ (Abs_trace [Tick] : traceType α) =
                Abs_trace [Ev b] ^^^ (sb ^^^ (Abs_trace [Tick] : traceType α)) :=
            appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hsbNo)
          have hHead :
              Abs_trace [Ev b] ^^^ (sb ^^^ (Abs_trace [Tick] : traceType α)) =
                Abs_trace [Ev a] ^^^ sa := hAssoc.symm.trans hEqa
          obtain ⟨rfl, htail⟩ := appt_same_head.mp hHead
          refine Or.inr ⟨b, sb ^^^ t', W, ?_, ?_, haX⟩
          · exact congrArg (fun z => (z, W))
              (appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hsbNo))
          · rw [in_failures_Seq_compo]
            exact Or.inr ⟨sb, t', W, rfl, by rw [htail]; exact hsa, ht', hsbNo⟩
  · rintro (⟨V, hEq, hX⟩ | ⟨a, v, V, hEq, hv, haX⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      refine Or.inl ⟨<>, W, rfl, ?_, noTick_nil⟩
      rw [in_failures_Ext_pre_choice]
      refine Or.inl ⟨W ∪ {Tick}, rfl, ?_⟩
      rw [Set.eq_empty_iff_forall_notMem]
      rintro e ⟨⟨b, hb, rfl⟩, he2⟩
      rcases he2 with he2 | he2
      · have hm : (Ev b : event α) ∈ Ev '' X ∩ W := ⟨⟨b, hb, rfl⟩, he2⟩
        rw [hX] at hm
        exact hm
      · exact absurd he2 (by simp)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Seq_compo] at hv
      rcases hv with ⟨t2, V2, hE2, hPfa, hnoT2⟩ | ⟨sb, t2, V2, hE2, hsTick, ht2, hsbNo⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE2
        refine Or.inl ⟨Abs_trace [Ev a] ^^^ v, W, rfl, ?_, ?_⟩
        · rw [in_failures_Ext_pre_choice]
          exact Or.inr ⟨a, v, W ∪ {Tick}, rfl, hPfa, haX⟩
        · exact decompo_appt_noTick_if (noTick_Ev a) hnoT2
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE2
        refine Or.inr ⟨Abs_trace [Ev a] ^^^ sb, t2, W, ?_, ?_, ht2, ?_⟩
        · exact congrArg (fun z => (z, W))
            (appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)).symm
        · rw [in_traces_Ext_pre_choice]
          refine Or.inr ⟨a, sb ^^^ (Abs_trace [Tick] : traceType α),
            appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo), hsTick, haX⟩
        · exact decompo_appt_noTick_if (noTick_Ev a) hsbNo

/-
(*********************************************************
                    Depth_rest expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/-- If `<Ev a> ^^^ s` ends in `Tick` (with a `Tick`-free prefix), then so does `s`. -/
private theorem Ev_cons_tick_split {a : α} {s s0 : traceType α}
    (hEq : Abs_trace [Ev a] ^^^ s = s0 ^^^ (Abs_trace [Tick] : traceType α))
    (hno : noTick s0) :
    ∃ s1, s = s1 ^^^ (Abs_trace [Tick] : traceType α) ∧ noTick s1 := by
  rcases trace_nil_or_Tick_or_Ev s0 with rfl | rfl | ⟨b, s1, rfl⟩
  · rw [appt_nil_left] at hEq
    have hhd := congrArg hdt hEq
    simp [hdt_appt] at hhd
  · exact absurd hno not_noTick_Tick
  · have hs1 : noTick s1 :=
      (decompo_appt_noTick_only_if (s := Abs_trace [Ev b]) (t := s1)
        (Or.inl (noTick_Ev b)) (by simpa using hno)).2
    have hAssoc :
        (Abs_trace [Ev b] ^^^ s1) ^^^ (Abs_trace [Tick] : traceType α) =
          Abs_trace [Ev b] ^^^ (s1 ^^^ (Abs_trace [Tick] : traceType α)) :=
      appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hs1)
    obtain ⟨-, htail⟩ := appt_same_head.mp (hEq.trans hAssoc)
    exact ⟨s1, htail, hs1⟩

theorem cspF_Depth_rest_step
    {X : Set α} {Pf : α → proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) |. Nat.succ n) M M
      (proc.Ext_pre_choice X (fun x => (Pf x) |. n)) := by
  refine cspF_eqF_of_eqT cspT_Depth_rest_step ?_
  intro u W
  rw [in_failures_Ext_pre_choice (Pf := fun x => (Pf x) |. n),
    in_failures_Depth_rest (P := proc.Ext_pre_choice X Pf)]
  simp only [tickTrace_eq]
  constructor
  · rintro ⟨t, V, hEq, hf, hrest⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Ext_pre_choice] at hf
    rcases hf with ⟨V1, hE1, hX⟩ | ⟨a, s, V1, hE1, hPfa, haX⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
      exact Or.inl ⟨W, rfl, hX⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
      refine Or.inr ⟨a, s, W, rfl, ?_, haX⟩
      rw [in_failures_Depth_rest]
      simp only [tickTrace_eq]
      refine ⟨s, W, rfl, hPfa, ?_⟩
      rw [lengtht_app_event_Suc_head] at hrest
      rcases hrest with hlt | ⟨hlen, s0, hs0, hno⟩
      · exact Or.inl (Nat.succ_lt_succ_iff.mp hlt)
      · exact Or.inr ⟨Nat.succ_injective hlen, Ev_cons_tick_split hs0 hno⟩
  · rintro (⟨V, hEq, hX⟩ | ⟨a, s, V, hEq, hf, haX⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      exact ⟨<>, W, rfl, in_failures_Ext_pre_choice.mpr (Or.inl ⟨W, rfl, hX⟩),
        Or.inl (by simp)⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Depth_rest] at hf
      simp only [tickTrace_eq] at hf
      obtain ⟨s', V', hE', hPfa, hrest⟩ := hf
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE'
      refine ⟨Abs_trace [Ev a] ^^^ s, W, rfl,
        in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s, W, rfl, hPfa, haX⟩), ?_⟩
      rw [lengtht_app_event_Suc_head]
      rcases hrest with hlt | ⟨hlen, s1, hs1, hno1⟩
      · exact Or.inl (Nat.succ_lt_succ hlt)
      · refine Or.inr ⟨by rw [hlen], Abs_trace [Ev a] ^^^ s1, ?_,
          decompo_appt_noTick_if (noTick_Ev a) hno1⟩
        rw [hs1]
        exact (appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hno1)).symm

/- The Isabelle theorem bundle `cspF_step` is represented by
   `cspF_STOP_step`, `cspF_Act_prefix_step`, `cspF_Ext_choice_step`,
   `cspF_Parallel_step`, `cspF_Hiding_step`, `cspF_Renaming_step`,
   `cspF_Seq_compo_step`, and `cspF_Depth_rest_step`. -/

/- The Isabelle theorem bundle `cspF_light_step` is represented by
   `cspF_STOP_step` and `cspF_Act_prefix_step`. -/

/- The Isabelle theorem bundle `cspF_step_rw` is represented by
   `cspF_STOP_step_DIV`, `cspF_Act_prefix_step`, `cspF_Ext_choice_step`,
   `cspF_Parallel_step`, `cspF_Hiding_step`, `cspF_Renaming_step`,
   `cspF_Seq_compo_step`, and `cspF_Depth_rest_step`. -/

/- The Isabelle theorem bundle `cspF_light_step_rw` is represented by
   `cspF_STOP_step_DIV` and `cspF_Act_prefix_step`. -/

end
