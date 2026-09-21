           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005               |
            |                  April 2006  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_DIV
import LeanCspProver.CSP_F.CSP_F_simp

open Function
open SumType
open event

noncomputable section

/-
(*****************************************************************

         1. DIV |[X]| DIV
         2. DIV |[X]| P
         3. P |[X]| DIV
         4. DIV -- X
         5. DIV [[r]]
         6. DIV ;; P
         7. P ;; DIV
         8. DIV |. n

 *****************************************************************)
-/

/-
(*********************************************************
                       DIV |[X]| DIV
 *********************************************************)
-/

theorem cspF_DIV_Parallel
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.DIV : proc p α) |[X]| proc.DIV)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Parallel, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Parallel] at hs
    rcases hs with ⟨u, Z, W, hEq, hZW, t, r, hu, htZ, hrW⟩
    exact False.elim ((in_failures_DIV (f := (t, Z)) (M := M1)) htZ)
  · rw [subsetF_iff]
    intro s Y hs
    exact False.elim ((in_failures_DIV (f := (s, Y)) (M := M2)) hs)

/-
(*********************************************************
                       DIV |[X]| P
 *********************************************************)
-/

theorem cspF_DIV_Parallel_step_l
    {X Y : Set α} {Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.DIV : proc p α) |[X]| proc.Ext_pre_choice Y Qf)) M M
      ((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.DIV : proc p α) |[X]| Qf x))) [+]
        proc.DIV) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Parallel_step_l, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s Z hs
    rw [in_failures_Parallel] at hs
    rcases hs with ⟨u, Y1, Z1, hEq, hYZ, t, r, hu, htY, hrZ⟩
    exact False.elim ((in_failures_DIV (f := (t, Y1)) (M := M)) htY)
  · rw [subsetF_iff]
    intro s Z hs
    have hFalse : False := by
      rw [in_failures_Ext_choice] at hs
      rcases hs with hs | hs
      · rcases hs with ⟨⟨W, hEq⟩, hsP, hsQ⟩
        exact (in_failures_DIV (f := (s, Z)) (M := M)) hsQ
      · rcases hs with hs | hs
        · rcases hs with ⟨u, ⟨W, hEq⟩, hsP, huNe⟩
          rcases Prod.mk.inj hEq with ⟨hsu, hZW⟩
          subst u W
          rcases hsP with hsP | hsP
          · rw [in_failures_Ext_pre_choice] at hsP
            rcases hsP with hsP | hsP
            · rcases hsP with ⟨W', hEq', hEmpty⟩
              rcases Prod.mk.inj hEq' with ⟨huNil, hW'⟩
              exact huNe huNil
            · rcases hsP with ⟨a, t, W', hEq', htW, haYX⟩
              rw [in_failures_Parallel] at htW
              rcases htW with ⟨v, Y1, Z1, hEq'', hYZ, s1, r1, hv, hs1, hr1⟩
              exact (in_failures_DIV (f := (s1, Y1)) (M := M)) hs1
          · exact (in_failures_DIV (f := (s, Z)) (M := M)) hsP
        · rcases hs with ⟨W, hEq, hTick, hSub⟩
          rcases hTick with hTick | hTick
          · rw [in_traces_Ext_pre_choice] at hTick
            simp at hTick
          · rw [in_traces_DIV] at hTick
            simp at hTick
    exact False.elim hFalse

theorem cspF_DIV_Parallel_step_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.DIV : proc p α)) M M
      ((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.DIV : proc p α)))) [+]
        proc.DIV) := by
  have h₁ :
      eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.DIV : proc p α)) M M
        (((proc.DIV : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) :=
    cspF_Parallel_commut
  have h₂ :
      eqF (((proc.DIV : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) M M
        ((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.DIV : proc p α) |[X]| Pf x))) [+]
          proc.DIV) :=
    cspF_DIV_Parallel_step_l
  have h₃₁ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.DIV : proc p α) |[X]| Pf x))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.DIV : proc p α)))) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  have h₃ :
      eqF
        (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.DIV : proc p α) |[X]| Pf x))) [+]
          proc.DIV))
        M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.DIV : proc p α)))) [+]
          proc.DIV)) := by
    exact cspF_Ext_choice_cong h₃₁ cspF_reflex_eq_DIV
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_DIV_Parallel_step` is represented by
   `cspF_DIV_Parallel_step_l` and `cspF_DIV_Parallel_step_r`. -/

/-
(*********************************************************
                      DIV and Parallel
 *********************************************************)
-/

theorem cspF_DIV_Parallel_Ext_choice_DIV_l
    {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (((P [+] proc.DIV) |[X]| (proc.DIV : proc p α))) M M
      (P |[X]| (proc.DIV : proc p α)) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Parallel_Ext_choice_DIV_l, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s Z hs
    rw [in_failures_Parallel] at hs
    rcases hs with ⟨u, Y1, Z1, hEq, hYZ, t, r, hu, htY, hrZ⟩
    exact False.elim ((in_failures_DIV (f := (r, Z1)) (M := M)) hrZ)
  · rw [subsetF_iff]
    intro s Z hs
    rw [in_failures_Parallel] at hs
    rcases hs with ⟨u, Y1, Z1, hEq, hYZ, t, r, hu, htY, hrZ⟩
    exact False.elim ((in_failures_DIV (f := (r, Z1)) (M := M)) hrZ)

theorem cspF_DIV_Parallel_Ext_choice_DIV_r
    {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (((proc.DIV : proc p α) |[X]| (P [+] proc.DIV))) M M ((proc.DIV : proc p α) |[X]| P) := by
  have h₁ :
      eqF (((proc.DIV : proc p α) |[X]| (P [+] proc.DIV))) M M
        (((P [+] proc.DIV) |[X]| (proc.DIV : proc p α))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF (((P [+] proc.DIV) |[X]| (proc.DIV : proc p α))) M M (P |[X]| (proc.DIV : proc p α)) :=
    cspF_DIV_Parallel_Ext_choice_DIV_l
  have h₃ : eqF (P |[X]| (proc.DIV : proc p α)) M M (((proc.DIV : proc p α) |[X]| P)) :=
    cspF_Parallel_commut
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_DIV_Parallel_Ext_choice_DIV` is
   represented by `cspF_DIV_Parallel_Ext_choice_DIV_l` and
   `cspF_DIV_Parallel_Ext_choice_DIV_r`. -/

/-
(*********************************************************
                      DIV -- X
 *********************************************************)
-/

theorem cspF_DIV_Hiding_Id
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.Hiding (proc.DIV : proc p α) X) M1 M2 (proc.DIV : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Hiding_Id, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Hiding] at hs
    rcases hs with ⟨t, Z, hEq, htZ⟩
    exact False.elim ((in_failures_DIV (f := (t, (Ev '' X) ∪ Z)) (M := M1)) htZ)
  · rw [subsetF_iff]
    intro s Y hs
    exact False.elim ((in_failures_DIV (f := (s, Y)) (M := M2)) hs)

/- (*** div-hide-step ***) -/

theorem cspF_DIV_Hiding_step
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] proc.DIV) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) :=
  cspF_eqF_of_eqT cspT_DIV_Hiding_step
    (fun t W => in_failures_Hiding_Ext_pre_choice_Ext_choice (Or.inr rfl) t W)

/-
(*********************************************************
                      DIV [[r]]
 *********************************************************)
-/

theorem cspF_DIV_Renaming_Id
    {r : Set (α × α)} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.DIV : proc p α)[[r]])) M1 M2 (proc.DIV : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Renaming_Id, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Renaming] at hs
    rcases hs with ⟨t, u, Y, hEq, hRen, htY⟩
    exact False.elim ((in_failures_DIV (f := (t, [[r]]inv Y)) (M := M1)) htY)
  · rw [subsetF_iff]
    intro s X hs
    exact False.elim ((in_failures_DIV (f := (s, X)) (M := M2)) hs)

/-
(*********************************************************
                       DIV ;; P
 *********************************************************)
-/

theorem cspF_DIV_Seq_compo
    {P : proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.DIV : proc p α) ;; P)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Seq_compo, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro u X hs
    rw [in_failures_Seq_compo] at hs
    rcases hs with hs | hs
    · rcases hs with ⟨t, Y, hEq, htY, htNo⟩
      exact False.elim ((in_failures_DIV (f := (t, Y ∪ {Tick})) (M := M1)) htY)
    · rcases hs with ⟨s, t, Y, hEq, hTick, htY, hsNo⟩
      rw [in_traces_DIV] at hTick
      exact False.elim (event_app_not_nil_right hsNo hTick)
  · rw [subsetF_iff]
    intro s X hs
    exact False.elim ((in_failures_DIV (f := (s, X)) (M := M2)) hs)

/-
(*********************************************************
               DIV and Sequential composition
 *********************************************************)
-/

theorem cspF_DIV_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> (proc.DIV : proc p α))) := by
  refine cspF_eqF_of_eqT cspT_DIV_Seq_compo_step ?_
  intro t W
  rw [in_failures_Seq_compo, in_failures_Timeout1]
  constructor
  · rintro (⟨t1, W1, hEq, hP0, hno⟩ | ⟨s, t1, W1, hEq, hT, hQ, hno⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Timeout1] at hP0
      rcases hP0 with hD | ⟨s1, V, hEq1, hne, hpre⟩ | ⟨V, hEq1, -, hTk⟩
      · exact absurd hD in_failures_DIV
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
      rw [in_traces_Timeout1, in_traces_Ext_pre_choice, in_traces_DIV] at hT
      rcases hT with (hnil | ⟨a, u, hu, hu', ha⟩) | hnil
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
  · rintro (hD | ⟨s1, V, hEq, hne, hpre⟩ | ⟨V, hEq, -, hTk⟩)
    · exact absurd hD in_failures_DIV
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
                      DIV |. n
 *********************************************************)
-/

theorem cspF_DIV_Depth_rest
    {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.DIV : proc p α) |. n)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_DIV_Depth_rest, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Depth_rest] at hs
    rcases hs with ⟨t, Y, hEq, htY, hRest⟩
    exact False.elim ((in_failures_DIV (f := (t, Y)) (M := M1)) htY)
  · rw [subsetF_iff]
    intro s X hs
    exact False.elim ((in_failures_DIV (f := (s, X)) (M := M2)) hs)

/- The Isabelle theorem bundle `cspF_DIV` is represented by
   `cspF_DIV_Parallel`, `cspF_DIV_Parallel_step_l`,
   `cspF_DIV_Parallel_step_r`, `cspF_DIV_Parallel_Ext_choice_DIV_l`,
   `cspF_DIV_Parallel_Ext_choice_DIV_r`, `cspF_DIV_Hiding_Id`,
   `cspF_DIV_Hiding_step`, `cspF_DIV_Renaming_Id`, `cspF_DIV_Seq_compo`,
   `cspF_DIV_Seq_compo_step`, and `cspF_DIV_Depth_rest`. -/

/-
(*********************************************************
                       P [+] DIV
 *********************************************************)
-/

theorem cspF_Ext_choice_DIV_resolve
    {P : proc p α} {M : p → domFType α} :
    eqF (P [+] (proc.DIV : proc p α)) M M (P [> (proc.DIV : proc p α)) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_Ext_choice_DIV_resolve, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Ext_choice] at hs
    rw [in_failures_Timeout1]
    rcases hs with hs | hs
    · rcases hs with ⟨⟨Y, hEq⟩, hsP, hsQ⟩
      exact False.elim ((in_failures_DIV (f := (s, X)) (M := M)) hsQ)
    · rcases hs with hs | hs
      · rcases hs with ⟨t, ⟨Y, hEq⟩, hsP, htNe⟩
        rcases hsP with hsP | hsP
        · have htY : (t, Y) :f failures P M := by
            simpa [hEq] using hsP
          exact Or.inr <| Or.inl ⟨t, Y, hEq, htNe, htY⟩
        · exact False.elim ((in_failures_DIV (f := (s, X)) (M := M)) hsP)
      · rcases hs with ⟨Y, hEq, hTick, hSub⟩
        rcases hTick with hTick | hTick
        · exact Or.inr <| Or.inr ⟨Y, hEq, hSub, hTick⟩
        · rw [in_traces_DIV] at hTick
          simp at hTick
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Timeout1] at hs
    rw [in_failures_Ext_choice]
    rcases hs with hs | hs
    · exact False.elim ((in_failures_DIV (f := (s, X)) (M := M)) hs)
    · rcases hs with hs | hs
      · rcases hs with ⟨t, Y, hEq, htNe, htY⟩
        have hsP : (s, X) :f failures P M := by
          simpa [hEq] using htY
        refine Or.inr <| Or.inl ?_
        exact ⟨t, ⟨Y, hEq⟩, Or.inl hsP, htNe⟩
      · rcases hs with ⟨Y, hEq, hSub, hTick⟩
        exact Or.inr <| Or.inr ⟨Y, hEq, Or.inl hTick, hSub⟩

end
