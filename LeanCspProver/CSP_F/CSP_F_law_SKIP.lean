           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_SKIP
import LeanCspProver.CSP_F.CSP_F_simp

open Function
open SumType
open event

noncomputable section

/-
(*****************************************************************

         1. SKIP |[X]| SKIP
         2. SKIP |[X]| P
         3. P |[X]| SKIP
         4. SKIP -- X
         5. SKIP [[r]]
         6. SKIP ;; P
         7. P ;; SKIP
         8. SKIP |. n

 *****************************************************************)
-/

/-
(*********************************************************
                    SKIP |[X]| SKIP
 *********************************************************)
-/


theorem cspF_Parallel_term
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| proc.SKIP)) M1 M2 (proc.SKIP : proc q α) := by
  refine cspF_eqF_of_eqT cspT_Parallel_term ?_
  intro t W
  rw [in_failures_Parallel, in_failures_SKIP_split]
  constructor
  · rintro ⟨u, Y, Z, hEq, hYZ, s, t1, hpar, hs, ht1⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_SKIP_split] at hs ht1
    rcases hs with ⟨rfl, hY⟩ | rfl
    · rcases ht1 with ⟨rfl, hZ⟩ | rfl
      · rw [par_tr_nil2] at hpar
        subst hpar
        refine Or.inl ⟨rfl, ?_⟩
        rintro e (he | he)
        · exact hY he
        · exact hZ he
      · exact absurd hpar (by simp)
    · rcases ht1 with ⟨rfl, hZ⟩ | rfl
      · exact absurd hpar (by simp)
      · rw [par_tr_Tick2] at hpar
        exact Or.inr hpar
  · rintro (⟨rfl, hW⟩ | rfl)
    · exact ⟨<>, W, W, by rw [Set.union_self], rfl, <>, <>, par_tr_nil_nil,
        in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hW⟩),
        in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hW⟩)⟩
    · exact ⟨Abs_trace [Tick], W, W, by rw [Set.union_self], rfl,
        Abs_trace [Tick], Abs_trace [Tick], par_tr_Tick_Tick,
        in_failures_SKIP_split.mpr (Or.inr rfl), in_failures_SKIP_split.mpr (Or.inr rfl)⟩

/-
(*********************************************************
                      SKIP |[X]| P
 *********************************************************)
-/

theorem cspF_Parallel_preterm_l_set1
    {X Y : Set α} {Ya Z : Set (event α)}
    (hEq : Ya \ insert Tick (Ev '' X) = Z \ insert Tick (Ev '' X))
    (hDisj : Ev '' Y ∩ Z = ∅) :
    Ev '' (Y \ X) ∩ (Ya ∪ Z) = ∅ := by
  ext e
  constructor
  · intro he
    exfalso
    rcases he with ⟨heYX, heUnion⟩
    rcases heYX with ⟨a, haYX, rfl⟩
    rcases haYX with ⟨haY, haNotX⟩
    have hNotMem : Ev a ∉ insert Tick (Ev '' X) := by
      intro hMem
      rcases hMem with hTick | hEvX
      · cases hTick
      · rcases hEvX with ⟨b, hbX, hbEq⟩
        cases hbEq
        exact haNotX hbX
    have hNotDisj : Ev a ∉ Z := by
      intro haZ
      have hInter : Ev a ∈ Ev '' Y ∩ Z := ⟨⟨a, haY, rfl⟩, haZ⟩
      simp [hDisj] at hInter
    rcases heUnion with haYa | haZ
    · have hDiff : Ev a ∈ Ya \ insert Tick (Ev '' X) := ⟨haYa, hNotMem⟩
      exact hNotDisj ((hEq ▸ hDiff).1)
    · exact hNotDisj haZ
  · intro he
    cases he


theorem cspF_Parallel_preterm_l
    {X Y : Set α} {Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Qf)) M M
      (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Qf x))) := by
  refine cspF_eqF_of_eqT cspT_Parallel_preterm_l ?_
  intro t W
  rw [in_failures_Parallel, in_failures_Ext_pre_choice]
  constructor
  · rintro ⟨u, A, B, hEq, hAB, s, t1, hpar, hs, ht1⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_SKIP_split] at hs
    rw [in_failures_Ext_pre_choice] at ht1
    rcases hs with ⟨rfl, hA⟩ | rfl
    · rw [par_tr_nil_left] at hpar
      obtain ⟨rfl, hnoT, hEmpty⟩ := hpar
      rcases ht1 with ⟨B2, hEqB, hdisj⟩ | ⟨a, t2, B2, hEqB, hQ, haY⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqB
        refine Or.inl ⟨A ∪ B, rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨a, ⟨haY, haX⟩, rfl⟩, he⟩
        have hB : (Ev a : event α) ∉ B := by
          intro hb
          have hm : (Ev a : event α) ∈ (Ev '' Y) ∩ B := ⟨⟨a, haY, rfl⟩, hb⟩
          rw [hdisj] at hm
          exact hm
        rcases he with he | he
        · have hnotA' : (Ev a : event α) ∉ ((Ev '' X) ∪ ({Tick} : Set (event α))) := by
            rintro (⟨b, hb, hEv⟩ | hTk)
            · exact haX (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
            · exact absurd (Set.mem_singleton_iff.mp hTk) (by simp)
          have hm : (Ev a : event α) ∈ A \ ((Ev '' X) ∪ {Tick}) := ⟨he, hnotA'⟩
          rw [hAB] at hm
          exact hB hm.1
        · exact hB he
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqB
        have haX : a ∉ X := by
          intro ha
          have hm : (Ev a : event α) ∈ sett (Abs_trace [Ev a] ^^^ t2) ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inl rfl), ⟨a, ha, rfl⟩⟩
          rw [hEmpty] at hm
          exact hm
        refine Or.inr ⟨a, t2, A ∪ B, rfl, ?_, ⟨haY, haX⟩⟩
        rw [in_failures_Parallel]
        refine ⟨t2, A, B, rfl, hAB, <>, t2, par_tr_nil_left.mpr ⟨rfl, ?_, ?_⟩,
          in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hA⟩), hQ⟩
        · intro hTk
          exact hnoT (sett_Ev_head_mem.mpr (Or.inr hTk))
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          have hm : e ∈ sett (Abs_trace [Ev a] ^^^ t2) ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inr he1), he2⟩
          rw [hEmpty] at hm
          exact hm
    · rw [par_tr_Tick_left] at hpar
      obtain ⟨rfl, hTk, hEmpty⟩ := hpar
      rcases ht1 with ⟨B2, hEqB, -⟩ | ⟨a, t2, B2, hEqB, hQ, haY⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj hEqB
        simp at hTk
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqB
        have haX : a ∉ X := by
          intro ha
          have hm : (Ev a : event α) ∈ sett (Abs_trace [Ev a] ^^^ t2) ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inl rfl), ⟨a, ha, rfl⟩⟩
          rw [hEmpty] at hm
          exact hm
        refine Or.inr ⟨a, t2, A ∪ B, rfl, ?_, ⟨haY, haX⟩⟩
        rw [in_failures_Parallel]
        refine ⟨t2, A, B, rfl, hAB, Abs_trace [Tick], t2,
          par_tr_Tick_left.mpr ⟨rfl, ?_, ?_⟩,
          in_failures_SKIP_split.mpr (Or.inr rfl), hQ⟩
        · rcases sett_Ev_head_mem.mp hTk with hEq | h
          · exact absurd hEq (by simp)
          · exact h
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          have hm : e ∈ sett (Abs_trace [Ev a] ^^^ t2) ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inr he1), he2⟩
          rw [hEmpty] at hm
          exact hm
  · rintro (⟨V, hEq, hdisj⟩ | ⟨a, v, V, hEq, hv, ha⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      refine ⟨<>, W \ {Tick}, W \ (Ev '' Y), ?_, ?_, <>, <>, par_tr_nil_nil,
        in_failures_SKIP_split.mpr (Or.inl ⟨rfl, ?_⟩), ?_⟩
      · congr 1
        ext e
        simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
        constructor
        · intro he
          by_cases hTe : e = Tick
          · refine Or.inr ⟨he, ?_⟩
            rintro ⟨b, -, hb⟩
            rw [hTe] at hb
            exact absurd hb.symm (by simp)
          · exact Or.inl ⟨he, hTe⟩
        · rintro (⟨he, -⟩ | ⟨he, -⟩) <;> exact he
      · ext e
        simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨he, hTe⟩, hA⟩
          refine ⟨⟨he, ?_⟩, hA⟩
          rintro ⟨b, hbY, rfl⟩
          have hbX : b ∉ X := by
            intro hbX
            exact hA (Or.inl ⟨b, hbX, rfl⟩)
          have hm : (Ev b : event α) ∈ (Ev '' (Y \ X)) ∩ W := ⟨⟨b, ⟨hbY, hbX⟩, rfl⟩, he⟩
          rw [hdisj] at hm
          exact hm
        · rintro ⟨⟨he, -⟩, hA⟩
          refine ⟨⟨he, ?_⟩, hA⟩
          intro hTe
          exact hA (Or.inr (Set.mem_singleton_iff.mpr hTe))
      · rintro e ⟨-, hTe⟩ hEv
        exact hTe (Set.mem_singleton_iff.mpr hEv)
      · rw [in_failures_Ext_pre_choice]
        refine Or.inl ⟨W \ (Ev '' Y), rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨he, -, hnY⟩
        exact hnY he
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Parallel] at hv
      obtain ⟨v', A, B, hEqv, hAB, s, t1, hpar, hs, ht1⟩ := hv
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqv
      rw [in_failures_SKIP_split] at hs
      rcases hs with ⟨rfl, hA⟩ | rfl
      · rw [par_tr_nil_left] at hpar
        obtain ⟨rfl, hnoT, hEmpty⟩ := hpar
        refine ⟨Abs_trace [Ev a] ^^^ v, A, B, rfl, hAB, <>, Abs_trace [Ev a] ^^^ v,
          par_tr_nil_left.mpr ⟨rfl, ?_, ?_⟩,
          in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hA⟩), ?_⟩
        · intro hTk
          rcases sett_Ev_head_mem.mp hTk with hEq | h
          · exact absurd hEq (by simp)
          · exact hnoT h
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rcases sett_Ev_head_mem.mp he1 with rfl | h
          · rcases he2 with ⟨b, hb, hEv⟩
            exact ha.2 (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
          · have hm : e ∈ sett v ∩ Ev '' X := ⟨h, he2⟩
            rw [hEmpty] at hm
            exact hm
        · rw [in_failures_Ext_pre_choice]
          exact Or.inr ⟨a, v, B, rfl, ht1, ha.1⟩
      · rw [par_tr_Tick_left] at hpar
        obtain ⟨rfl, hTk, hEmpty⟩ := hpar
        refine ⟨Abs_trace [Ev a] ^^^ v, A, B, rfl, hAB, Abs_trace [Tick],
          Abs_trace [Ev a] ^^^ v, par_tr_Tick_left.mpr ⟨rfl, ?_, ?_⟩,
          in_failures_SKIP_split.mpr (Or.inr rfl), ?_⟩
        · exact sett_Ev_head_mem.mpr (Or.inr hTk)
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rcases sett_Ev_head_mem.mp he1 with rfl | h
          · rcases he2 with ⟨b, hb, hEv⟩
            exact ha.2 (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
          · have hm : e ∈ sett v ∩ Ev '' X := ⟨h, he2⟩
            rw [hEmpty] at hm
            exact hm
        · rw [in_failures_Ext_pre_choice]
          exact Or.inr ⟨a, v, B, rfl, ht1, ha.1⟩

theorem cspF_Parallel_preterm_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
      (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) := by
  have h₁ :
      eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
        (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) :=
    cspF_Parallel_commut
  have h₂ :
      eqF (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) :=
    cspF_Parallel_preterm_l
  have h₃ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_Parallel_preterm` is represented by
   `cspF_Parallel_preterm_l` and `cspF_Parallel_preterm_r`. -/

/-
(*********************************************************
                      SKIP and Parallel
 *********************************************************)
-/

/- p.288 -/

theorem cspF_SKIP_Parallel_Ext_choice_SKIP_l
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
        proc.SKIP)) := by
  refine cspF_eqF_of_eqT cspT_SKIP_Parallel_Ext_choice_SKIP_l ?_
  intro t W
  rw [in_failures_Parallel, in_failures_Ext_pre_choice_Ext_choice (Or.inl rfl)]
  constructor
  · rintro ⟨u, A, B, hEq, hAB, s, t1, hpar, hs, ht1⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Ext_pre_choice_Ext_choice (Or.inl rfl)] at hs
    rw [in_failures_SKIP_split] at ht1
    rcases hs with ⟨a, s', rfl, hPf, haY⟩ | ⟨-, rfl⟩ | ⟨-, rfl, hA⟩
    · rcases ht1 with ⟨rfl, hB⟩ | rfl
      · rw [par_tr_nil_right] at hpar
        obtain ⟨rfl, hnoT, hEmpty⟩ := hpar
        have haX : a ∉ X := by
          intro ha
          have hm : (Ev a : event α) ∈ sett (Abs_trace [Ev a] ^^^ s') ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inl rfl), ⟨a, ha, rfl⟩⟩
          rw [hEmpty] at hm
          exact hm
        refine Or.inl ⟨a, s', rfl, ?_, ⟨haY, haX⟩⟩
        rw [in_failures_Parallel]
        refine ⟨s', A, B, rfl, hAB, s', <>, par_tr_nil_right.mpr ⟨rfl, ?_, ?_⟩, hPf,
          in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hB⟩)⟩
        · intro hTk
          exact hnoT (sett_Ev_head_mem.mpr (Or.inr hTk))
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          have hm : e ∈ sett (Abs_trace [Ev a] ^^^ s') ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inr he1), he2⟩
          rw [hEmpty] at hm
          exact hm
      · rw [par_tr_Tick_right] at hpar
        obtain ⟨rfl, hTk, hEmpty⟩ := hpar
        have haX : a ∉ X := by
          intro ha
          have hm : (Ev a : event α) ∈ sett (Abs_trace [Ev a] ^^^ s') ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inl rfl), ⟨a, ha, rfl⟩⟩
          rw [hEmpty] at hm
          exact hm
        refine Or.inl ⟨a, s', rfl, ?_, ⟨haY, haX⟩⟩
        rw [in_failures_Parallel]
        refine ⟨s', A, B, rfl, hAB, s', Abs_trace [Tick],
          par_tr_Tick_right.mpr ⟨rfl, ?_, ?_⟩, hPf,
          in_failures_SKIP_split.mpr (Or.inr rfl)⟩
        · rcases sett_Ev_head_mem.mp hTk with hEq2 | h
          · exact absurd hEq2 (by simp)
          · exact h
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          have hm : e ∈ sett (Abs_trace [Ev a] ^^^ s') ∩ Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inr he1), he2⟩
          rw [hEmpty] at hm
          exact hm
    · rcases ht1 with ⟨rfl, -⟩ | rfl
      · exact absurd hpar (by simp)
      · rw [par_tr_Tick2] at hpar
        subst hpar
        exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rcases ht1 with ⟨rfl, hB⟩ | rfl
      · rw [par_tr_nil2] at hpar
        subst hpar
        refine Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)
        rintro e (he | he)
        · exact hA he
        · exact hB he
      · exact absurd hpar (by simp)
  · rintro (⟨a, v, rfl, hv, ⟨haY, haX⟩⟩ | ⟨-, rfl⟩ | ⟨-, rfl, hW⟩)
    · rw [in_failures_Parallel] at hv
      obtain ⟨v', A, B, hEqv, hAB, s, t1, hpar, hs, ht1⟩ := hv
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqv
      rw [in_failures_SKIP_split] at ht1
      rcases ht1 with ⟨rfl, hB⟩ | rfl
      · rw [par_tr_nil_right] at hpar
        obtain ⟨rfl, hnoT, hEmpty⟩ := hpar
        refine ⟨Abs_trace [Ev a] ^^^ v, A, B, rfl, hAB, Abs_trace [Ev a] ^^^ v, <>,
          par_tr_nil_right.mpr ⟨rfl, ?_, ?_⟩, ?_,
          in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hB⟩)⟩
        · intro hTk
          rcases sett_Ev_head_mem.mp hTk with hEq2 | h
          · exact absurd hEq2 (by simp)
          · exact hnoT h
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rcases sett_Ev_head_mem.mp he1 with rfl | h
          · rcases he2 with ⟨b, hb, hEv⟩
            exact haX (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
          · have hm : e ∈ sett v ∩ Ev '' X := ⟨h, he2⟩
            rw [hEmpty] at hm
            exact hm
        · exact (in_failures_Ext_pre_choice_Ext_choice (Or.inl rfl)).mpr
            (Or.inl ⟨a, v, rfl, hs, haY⟩)
      · rw [par_tr_Tick_right] at hpar
        obtain ⟨rfl, hTk, hEmpty⟩ := hpar
        refine ⟨Abs_trace [Ev a] ^^^ v, A, B, rfl, hAB, Abs_trace [Ev a] ^^^ v,
          Abs_trace [Tick], par_tr_Tick_right.mpr ⟨rfl, ?_, ?_⟩, ?_,
          in_failures_SKIP_split.mpr (Or.inr rfl)⟩
        · exact sett_Ev_head_mem.mpr (Or.inr hTk)
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rcases sett_Ev_head_mem.mp he1 with rfl | h
          · rcases he2 with ⟨b, hb, hEv⟩
            exact haX (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
          · have hm : e ∈ sett v ∩ Ev '' X := ⟨h, he2⟩
            rw [hEmpty] at hm
            exact hm
        · exact (in_failures_Ext_pre_choice_Ext_choice (Or.inl rfl)).mpr
            (Or.inl ⟨a, v, rfl, hs, haY⟩)
    · exact ⟨Abs_trace [Tick], W, W, by rw [Set.union_self], rfl,
        Abs_trace [Tick], Abs_trace [Tick], par_tr_Tick_Tick,
        (in_failures_Ext_pre_choice_Ext_choice (Or.inl rfl)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        in_failures_SKIP_split.mpr (Or.inr rfl)⟩
    · exact ⟨<>, W, W, by rw [Set.union_self], rfl, <>, <>, par_tr_nil_nil,
        (in_failures_Ext_pre_choice_Ext_choice (Or.inl rfl)).mpr
          (Or.inr (Or.inr ⟨rfl, rfl, hW⟩)),
        in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hW⟩)⟩

theorem cspF_SKIP_Parallel_Ext_choice_SKIP_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.SKIP))) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+]
        proc.SKIP)) := by
  have h₁ :
      eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.SKIP))) M M
        ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
          proc.SKIP)) :=
    cspF_SKIP_Parallel_Ext_choice_SKIP_l
  have h₃₁ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  have h₃ :
      eqF
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
          proc.SKIP))
        M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+]
          proc.SKIP)) := by
    exact cspF_Ext_choice_cong h₃₁ cspF_reflex_eq_SKIP
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_SKIP_Parallel_Ext_choice_SKIP` is
   represented by `cspF_SKIP_Parallel_Ext_choice_SKIP_l` and
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`. -/

/-
(*********************************************************
                      SKIP -- X
 *********************************************************)
-/

theorem cspF_SKIP_Hiding_Id
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.Hiding (proc.SKIP : proc p α) X) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_SKIP_Hiding_Id, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Hiding] at hs
    rcases hs with ⟨t, Z, hEq, htZ⟩
    rw [in_failures_SKIP] at htZ
    rw [in_failures_SKIP]
    rcases htZ with ⟨W, hPair, hSub⟩ | ⟨W, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨htEq, hWEq⟩
      subst t
      subst W
      rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      refine Or.inl ⟨Z, by simp, ?_⟩
      intro e he
      exact hSub (Or.inr he)
    · rcases Prod.mk.inj hPair with ⟨htEq, hWEq⟩
      subst t
      subst W
      rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      exact Or.inr ⟨Z, by simp⟩
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_SKIP] at hs
    rw [in_failures_Hiding]
    rcases hs with ⟨Z, hPair, hSub⟩ | ⟨Z, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      refine ⟨<>, Z, by simp, ?_⟩
      rw [in_failures_SKIP]
      refine Or.inl ⟨Ev '' X ∪ Z, rfl, ?_⟩
      intro e he
      rcases he with he | he
      · rcases he with ⟨a, haX, rfl⟩
        simp [Evset]
      · exact hSub he
    · rcases Prod.mk.inj hPair with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      refine ⟨Abs_trace [Tick], Z, by simp, ?_⟩
      rw [in_failures_SKIP]
      exact Or.inr ⟨Ev '' X ∪ Z, rfl⟩

/-
(*********************************************************
                      SKIP and Hiding
 *********************************************************)
-/

/- p.288 version
  "((? :Y -> Pf) [+] SKIP) -- X =F[M,M]
       IF (Y Int X = {}) THEN ((? x:Y -> (Pf x -- X)) [+] SKIP)
                         ELSE (((? x:(Y-X) -> (Pf x -- X)) [+] SKIP)
                               |~| (! x:(Y Int X) .. (Pf x -- X)))"
-/

theorem cspF_SKIP_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] proc.SKIP) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) :=
  cspF_eqF_of_eqT cspT_SKIP_Hiding_step
    (fun t W => in_failures_Hiding_Ext_pre_choice_Ext_choice (Or.inl rfl) t W)

/-
(*********************************************************
                      SKIP [[r]]
 *********************************************************)
-/

theorem cspF_SKIP_Renaming_Id
    {r : Set (α × α)} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α)[[r]])) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_SKIP_Renaming_Id, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Renaming] at hs
    rcases hs with ⟨t, u, Y, hEq, hRen, htY⟩
    rw [in_failures_SKIP] at htY
    rw [in_failures_SKIP]
    rcases htY with ⟨Z, hPair, hSub⟩ | ⟨Z, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨htEq, hZEq⟩
      subst t
      subst Z
      have huNil : u = <> := (ren_tr_nil1 (r := r) (s := u)).1 hRen
      rcases Prod.mk.inj hEq with ⟨hsEq, hXEq⟩
      subst s
      subst X
      subst u
      refine Or.inl ⟨Y, rfl, ?_⟩
      exact (ren_inv_no_Tick (r := r) (X := Y)).1 hSub
    · rcases Prod.mk.inj hPair with ⟨htEq, hZEq⟩
      subst t
      subst Z
      have huTick : u = Abs_trace [Tick] := (ren_tr_Tick1 (r := r) (s := u)).1 hRen
      rcases Prod.mk.inj hEq with ⟨hsEq, hXEq⟩
      subst s
      subst X
      subst u
      exact Or.inr ⟨Y, rfl⟩
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_SKIP] at hs
    rw [in_failures_Renaming]
    rcases hs with ⟨Y, hPair, hSub⟩ | ⟨Y, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨<>, <>, Y, rfl, ren_tr_nil, ?_⟩
      rw [in_failures_SKIP]
      refine Or.inl ⟨[[r]]inv Y, rfl, ?_⟩
      exact Set.Subset.trans (ren_inv_sub hSub) (ren_inv_sub_Evset (r := r))
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨Abs_trace [Tick], Abs_trace [Tick], Y, rfl, ren_tr_Tick, ?_⟩
      rw [in_failures_SKIP]
      exact Or.inr ⟨[[r]]inv Y, rfl⟩

/-
(*********************************************************
                       SKIP ;; P
 *********************************************************)
-/

theorem cspF_Seq_compo_unit_l
    {P : proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) ;; P)) M M P := by
  refine cspF_eqF_of_eqT cspT_Seq_compo_unit_l ?_
  intro t W
  rw [in_failures_Seq_compo]
  constructor
  · rintro (⟨t1, W1, hEq, hS, hno⟩ | ⟨s, t1, W1, hEq, hT, hQ, hno⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_SKIP_split] at hS
      rcases hS with ⟨-, hsub⟩ | hTk
      · exact absurd (hsub (Or.inr rfl)) (by simp [Evset])
      · exact absurd (hTk ▸ hno) not_noTick_Tick
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_traces_SKIP] at hT
      rcases hT with hnil | hTk
      · exact absurd ((appt_nil hno).mp hnil).2 (by simp)
      · have hs0 : s = <> := by
          have := (appt_same_last hno noTick_nil).mp (by simpa using hTk)
          exact this.1
        subst hs0
        rw [appt_nil_left]
        exact hQ
  · intro hf
    refine Or.inr ⟨<>, t, W, by rw [appt_nil_left], ?_, hf, noTick_nil⟩
    rw [appt_nil_left]
    exact in_traces_SKIP.mpr (Or.inr rfl)

/-
(*********************************************************
                       P ;; SKIP
 *********************************************************)
-/

theorem cspF_Seq_compo_unit_r
    {P : proc p α} {M : p → domFType α} :
    eqF ((P ;; (proc.SKIP : proc p α))) M M P := by
  refine cspF_eqF_of_eqT cspT_Seq_compo_unit_r ?_
  intro t W
  rw [in_failures_Seq_compo]
  constructor
  · rintro (⟨t1, W1, hEq, hP, -⟩ | ⟨s, t1, W1, hEq, hT, hS, hno⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      exact failures_F2 hP Set.subset_union_left
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_SKIP_split] at hS
      rcases hS with ⟨rfl, hsub⟩ | rfl
      · rw [appt_nil_right]
        exact failures_F2_F4 hT hno hsub
      · exact failures_T3 hT hno
  · intro hf
    rcases trace_last_noTick_or_Tick t with hno | ⟨t', hno', rfl⟩
    · by_cases hTk : (Tick : event α) ∈ W
      · refine Or.inl ⟨t, W, rfl, ?_, hno⟩
        have : W ∪ {Tick} = W := by
          ext e
          constructor
          · rintro (he | he)
            · exact he
            · rw [Set.mem_singleton_iff] at he
              rw [he]
              exact hTk
          · exact Or.inl
        rw [this]
        exact hf
      · by_cases hTr : (t ^^^ (Abs_trace [Tick] : traceType α) : traceType α) :t
            traces P (fstF ∘ M)
        · refine Or.inr ⟨t, <>, W, by rw [appt_nil_right], hTr, ?_, hno⟩
          refine in_failures_SKIP_split.mpr (Or.inl ⟨rfl, ?_⟩)
          intro e he hTe
          exact hTk (hTe ▸ he)
        · refine Or.inl ⟨t, W, rfl, ?_, hno⟩
          refine failures_F3 hf hno ?_
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          subst ha
          exact hTr
    · refine Or.inr ⟨t', Abs_trace [Tick], W, rfl, failures_T2 hf, ?_, hno'⟩
      exact in_failures_SKIP_split.mpr (Or.inr rfl)

/- The Isabelle theorem bundle `cspF_Seq_compo_unit` is represented by
   `cspF_Seq_compo_unit_l` and `cspF_Seq_compo_unit_r`. -/

/-
(*********************************************************
               SKIP and Sequential composition
 *********************************************************)
-/

/- p.141 -/

theorem cspF_SKIP_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice X Pf) [> (proc.SKIP : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> Q)) := by
  refine cspF_eqF_of_eqT cspT_SKIP_Seq_compo_step ?_
  intro t W
  rw [in_failures_Seq_compo, in_failures_Timeout1]
  constructor
  · rintro (⟨t1, W1, hEq, hP0, hno⟩ | ⟨s, t1, W1, hEq, hT, hQ, hno⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Timeout1] at hP0
      rcases hP0 with hS | ⟨s1, V, hEq1, hne, hpre⟩ | ⟨V, hEq1, hsub, hTk⟩
      · rw [in_failures_SKIP_split] at hS
        rcases hS with ⟨-, hsub⟩ | hTk
        · exact absurd (hsub (Or.inr rfl)) (by simp [Evset])
        · exact absurd (hTk ▸ hno) not_noTick_Tick
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq1
        rw [in_failures_Ext_pre_choice] at hpre
        rcases hpre with ⟨V', hEqn, -⟩ | ⟨a, s', V', hEqn, hPf, ha⟩
        · exact absurd (Prod.mk.inj hEqn).1 hne
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqn
          refine Or.inr (Or.inl ⟨Abs_trace [Ev a] ^^^ s', W, rfl, by simp, ?_⟩)
          rw [in_failures_Ext_pre_choice]
          refine Or.inr ⟨a, s', W, rfl, ?_, ha⟩
          rw [in_failures_Seq_compo]
          exact Or.inl ⟨s', W, rfl, hPf,
            (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hno).2⟩
      · exact absurd hTk Tick_notin_traces_Ext_pre_choice
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_traces_Timeout1, in_traces_Ext_pre_choice, in_traces_SKIP] at hT
      rcases hT with (hnil | ⟨a, u, hu, hu', ha⟩) | (hnil | hTk)
      · exact absurd ((appt_nil hno).mp hnil).2 (by simp)
      · rcases trace_nil_or_Tick_or_Ev s with rfl | rfl | ⟨b, s2, rfl⟩
        · exfalso
          rw [appt_nil_left] at hu
          exact absurd hu.symm (by simp)
        · exact absurd hno not_noTick_Tick
        · have hno2 : noTick s2 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hno).2
          rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hno2)] at hu
          obtain ⟨rfl, hs2⟩ := appt_same_head.mp hu.symm
          refine Or.inr (Or.inl ⟨(Abs_trace [Ev a] ^^^ s2) ^^^ t1, W, rfl, ?_, ?_⟩)
          · rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hno2)]
            simp
          · rw [in_failures_Ext_pre_choice]
            refine Or.inr ⟨a, s2 ^^^ t1, W,
              (by rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hno2)]), ?_, ha⟩
            rw [in_failures_Seq_compo]
            exact Or.inr ⟨s2, t1, W, rfl, by rw [← hs2]; exact hu', hQ, hno2⟩
      · exact absurd ((appt_nil hno).mp hnil).2 (by simp)
      · have hs0 : s = <> := by
          rcases trace_nil_or_Tick_or_Ev s with h | rfl | ⟨b, s2, rfl⟩
          · exact h
          · exact absurd hno not_noTick_Tick
          · exfalso
            have hno2 : noTick s2 := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev b)) hno).2
            rw [appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hno2)] at hTk
            simp at hTk
        subst hs0
        rw [appt_nil_left]
        exact Or.inl hQ
  · rintro (hQ | ⟨s1, V, hEq, hne, hpre⟩ | ⟨V, hEq, hsub, hTk⟩)
    · refine Or.inr ⟨<>, t, W, by rw [appt_nil_left], ?_, hQ, noTick_nil⟩
      rw [appt_nil_left, in_traces_Timeout1]
      exact Or.inr (in_traces_SKIP.mpr (Or.inr rfl))
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Ext_pre_choice] at hpre
      rcases hpre with ⟨V', hEqn, -⟩ | ⟨a, v, V', hEqn, hv, ha⟩
      · exact absurd (Prod.mk.inj hEqn).1 hne
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqn
        rw [in_failures_Seq_compo] at hv
        rcases hv with ⟨t2, V2, hEq2, hPf, hno2⟩ | ⟨s2, t2, V2, hEq2, hT2, hQ2, hno2⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq2
          refine Or.inl ⟨Abs_trace [Ev a] ^^^ v, W, rfl, ?_,
            decompo_appt_noTick_if (noTick_Ev a) hno2⟩
          rw [in_failures_Timeout1]
          refine Or.inr (Or.inl ⟨Abs_trace [Ev a] ^^^ v, W ∪ {Tick}, rfl, by simp, ?_⟩)
          rw [in_failures_Ext_pre_choice]
          exact Or.inr ⟨a, v, W ∪ {Tick}, rfl, hPf, ha⟩
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq2
          refine Or.inr ⟨Abs_trace [Ev a] ^^^ s2, t2, W,
            (by rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hno2)]), ?_, hQ2,
            decompo_appt_noTick_if (noTick_Ev a) hno2⟩
          rw [in_traces_Timeout1]
          refine Or.inl (in_traces_Ext_pre_choice.mpr
            (Or.inr ⟨a, (s2 ^^^ (Abs_trace [Tick] : traceType α) : traceType α), ?_, hT2, ha⟩))
          rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hno2)]
    · exact absurd hTk Tick_notin_traces_Ext_pre_choice

/-
(*********************************************************
                      SKIP |. n
 *********************************************************)
-/

theorem cspF_SKIP_Depth_rest
    {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) |. Nat.succ n)) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_SKIP_Depth_rest, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Depth_rest] at hs
    rcases hs with ⟨t, Y, hEq, htY, hRest⟩
    simpa [hEq] using htY
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_SKIP] at hs
    rw [in_failures_Depth_rest]
    rcases hs with ⟨Y, hPair, hSub⟩ | ⟨Y, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨<>, Y, rfl, ?_, Or.inl (by simp)⟩
      exact (in_failures_SKIP (f := ((<>, Y) : failure α)) (M := M1)).2 (Or.inl ⟨Y, rfl, hSub⟩)
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨Abs_trace [Tick], Y, rfl, ?_, ?_⟩
      · exact (in_failures_SKIP (f := ((Abs_trace [Tick], Y) : failure α)) (M := M1)).2
          (Or.inr ⟨Y, rfl⟩)
      · by_cases hPos : 0 < n
        · exact Or.inl (by simpa using Nat.succ_lt_succ hPos)
        · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hPos
          subst n
          refine Or.inr ?_
          refine ⟨by simp, ?_⟩
          refine ⟨<>, by simp [tickTrace, noTick]⟩

/- The Isabelle theorem bundle `cspF_SKIP` is represented by
   `cspF_Parallel_term`, `cspF_Parallel_preterm_l`,
   `cspF_Parallel_preterm_r`, `cspF_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`, `cspF_SKIP_Hiding_Id`,
   `cspF_SKIP_Hiding_step`, `cspF_SKIP_Renaming_Id`,
   `cspF_Seq_compo_unit_l`, `cspF_Seq_compo_unit_r`,
   `cspF_SKIP_Seq_compo_step`, and `cspF_SKIP_Depth_rest`. -/

/-
(*********************************************************
                       P [+] SKIP
 *********************************************************)
-/

/- p.141 -/

theorem cspF_Ext_choice_SKIP_resolve
    {P : proc p α} {M : p → domFType α} :
    eqF (P [+] (proc.SKIP : proc p α)) M M (P [> (proc.SKIP : proc p α)) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_Ext_choice_SKIP_resolve, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Ext_choice] at hs
    rw [in_failures_Timeout1]
    rcases hs with hs | hs
    · rcases hs with ⟨⟨Y, hEq⟩, hsP, hsQ⟩
      exact Or.inl (by simpa [hEq] using hsQ)
    · rcases hs with hs | hs
      · rcases hs with ⟨t, ⟨Y, hEq⟩, hsPQ, htNe⟩
        rcases hsPQ with hsP | hsQ
        · exact Or.inr <| Or.inl ⟨t, Y, hEq, htNe, by simpa [hEq] using hsP⟩
        · exact Or.inl (by simpa [hEq] using hsQ)
      · rcases hs with ⟨Y, hEq, hTick, hSub⟩
        rcases hTick with hTick | hTick
        · exact Or.inr <| Or.inr ⟨Y, hEq, hSub, hTick⟩
        · exact Or.inl <| by
            simpa [hEq] using
              (in_failures_SKIP (f := ((<>, Y) : failure α)) (M := M)).2
                (Or.inl ⟨Y, rfl, hSub⟩)
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Timeout1] at hs
    rw [in_failures_Ext_choice]
    rcases hs with hSkip | hs
    · rw [in_failures_SKIP] at hSkip
      rcases hSkip with hSkip | hSkip
      · rcases hSkip with ⟨Y, hEq, hSub⟩
        exact Or.inr <| Or.inr ⟨Y, hEq, Or.inr <|
          (in_traces_SKIP (t := Abs_trace [Tick]) (M := fstF ∘ M)).2 (Or.inr rfl), hSub⟩
      · rcases hSkip with ⟨Y, hEq⟩
        exact Or.inr <| Or.inl ⟨Abs_trace [Tick], ⟨Y, hEq⟩, Or.inr <| by
          simpa [hEq] using
            (in_failures_SKIP (f := ((Abs_trace [Tick], Y) : failure α)) (M := M)).2
              (Or.inr ⟨Y, rfl⟩), by simp⟩
    · rcases hs with hs | hs
      · rcases hs with ⟨t, Y, hEq, htNe, htY⟩
        exact Or.inr <| Or.inl ⟨t, ⟨Y, hEq⟩, Or.inl <| by simpa [hEq] using htY, htNe⟩
      · rcases hs with ⟨Y, hEq, hSub, hTick⟩
        exact Or.inr <| Or.inr ⟨Y, hEq, Or.inl hTick, hSub⟩

theorem cspF_Ext_choice_SKIP_resolve_sym
    {P : proc p α} {M : p → domFType α} :
    eqF (P [> (proc.SKIP : proc p α)) M M (P [+] (proc.SKIP : proc p α)) := by
  exact cspF_sym cspF_Ext_choice_SKIP_resolve

end
