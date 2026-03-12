           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_basic

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

theorem cspT_Parallel_term
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.SKIP : proc p α) |[X]| proc.SKIP)) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Parallel] at hu
    rcases hu with ⟨s, t, hu, hs, ht⟩
    rw [in_traces_SKIP] at hs ht
    rw [in_traces_SKIP]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Or.inl ((par_tr_nil_left.mp hu).1)
    · exact False.elim (par_tr_nil_Tick hu)
    · exact False.elim (par_tr_Tick_nil hu)
    · exact Or.inr ((par_tr_Tick_left.mp hu).1)
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_SKIP] at ht
    rw [in_traces_Parallel]
    rcases ht with rfl | rfl
    · exact ⟨<>, <>, par_tr_nil_nil,
        (in_traces_SKIP (t := <>) (M := M1)).2 (Or.inl rfl),
        (in_traces_SKIP (t := <>) (M := M1)).2 (Or.inl rfl)⟩
    · exact ⟨Abs_trace [Tick], Abs_trace [Tick], par_tr_Tick_Tick,
        (in_traces_SKIP (t := Abs_trace [Tick]) (M := M1)).2 (Or.inr rfl),
        (in_traces_SKIP (t := Abs_trace [Tick]) (M := M1)).2 (Or.inr rfl)⟩

/-
(*********************************************************
                      SKIP |[X]| P
 *********************************************************)
-/

axiom cspT_Parallel_preterm_l
    {X Y : Set α} {Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Qf)) M M
      (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Qf x)))

theorem cspT_Parallel_preterm_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
      (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) := by
  have h₁ :
      eqT ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
        (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) :=
    cspT_Parallel_commut
  have h₂ :
      eqT (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) :=
    cspT_Parallel_preterm_l
  have h₃ :
      eqT (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) := by
    apply cspT_Ext_pre_choice_cong rfl
    intro a ha
    exact cspT_Parallel_commut
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_Parallel_preterm` is represented by
   `cspT_Parallel_preterm_l` and `cspT_Parallel_preterm_r`. -/

/-
(*********************************************************
                      SKIP and Parallel
 *********************************************************)
-/

/- p.288 -/

axiom cspT_SKIP_Parallel_Ext_choice_SKIP_l
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+] proc.SKIP))

theorem cspT_SKIP_Parallel_Ext_choice_SKIP_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.SKIP)) ) M M
      (((proc.Ext_pre_choice (Y \ X)
          (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+] proc.SKIP)) := by
  have h₁ :
      eqT (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.SKIP))) M M
        ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) :=
    cspT_Parallel_commut
  have h₂ :
      eqT ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X)
            (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+] proc.SKIP)) :=
    cspT_SKIP_Parallel_Ext_choice_SKIP_l
  have h₃₁ :
      eqT (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) := by
    apply cspT_Ext_pre_choice_cong rfl
    intro a ha
    exact cspT_Parallel_commut
  have h₃ :
      eqT
        (((proc.Ext_pre_choice (Y \ X)
            (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+] proc.SKIP)) M M
        (((proc.Ext_pre_choice (Y \ X)
            (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+] proc.SKIP)) := by
    exact cspT_Ext_choice_cong h₃₁ cspT_reflex_eq_SKIP
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_SKIP_Parallel_Ext_choice_SKIP` is
   represented by `cspT_SKIP_Parallel_Ext_choice_SKIP_l` and
   `cspT_SKIP_Parallel_Ext_choice_SKIP_r`. -/

/-
(*********************************************************
                      SKIP -- X
 *********************************************************)
-/

theorem cspT_SKIP_Hiding_Id
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.Hiding (proc.SKIP : proc p α) X) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Hiding] at ht
    rcases ht with ⟨s, rfl, hs⟩
    rw [in_traces_SKIP] at hs
    rw [in_traces_SKIP]
    rcases hs with rfl | rfl <;> simp
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_SKIP] at ht
    rw [in_traces_Hiding]
    rcases ht with rfl | rfl
    · exact ⟨<>, by simp, (in_traces_SKIP (t := <>) (M := M1)).2 (Or.inl rfl)⟩
    · exact ⟨Abs_trace [Tick], by simp,
        (in_traces_SKIP (t := Abs_trace [Tick]) (M := M1)).2 (Or.inr rfl)⟩

/-
(*********************************************************
                      SKIP and Hiding
 *********************************************************)
-/

axiom cspT_SKIP_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] proc.SKIP) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X)))

/-
(*********************************************************
                      SKIP [[r]]
 *********************************************************)
-/

theorem cspT_SKIP_Renaming_Id
    {r : Set (α × α)} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.SKIP : proc p α)[[r]])) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Renaming] at ht
    rcases ht with ⟨s, hs, ht⟩
    rw [in_traces_SKIP] at ht
    rw [in_traces_SKIP]
    rcases ht with rfl | rfl
    · exact Or.inl ((ren_tr_nil1 (r := r) (s := t)).1 hs)
    · exact Or.inr ((ren_tr_Tick1 (r := r) (s := t)).1 hs)
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_SKIP] at ht
    rw [in_traces_Renaming]
    rcases ht with rfl | rfl
    · exact ⟨<>, ren_tr_nil, (in_traces_SKIP (t := <>) (M := M1)).2 (Or.inl rfl)⟩
    · exact ⟨Abs_trace [Tick], ren_tr_Tick,
        (in_traces_SKIP (t := Abs_trace [Tick]) (M := M1)).2 (Or.inr rfl)⟩

/-
(*********************************************************
                       SKIP ;; P
 *********************************************************)
-/

theorem cspT_Seq_compo_unit_l
    {P : proc p α} {M : p → domTType α} :
    eqT (((proc.SKIP : proc p α) ;; P)) M M P := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo] at hu
    rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, hu, hs, ht, hsNo⟩
    · rw [in_traces_SKIP] at hs
      rcases hs with rfl | rfl
      · rw [rmTick_nil]
        exact nilt_in_T (T := traces P M)
      · rw [rmTick_Tick]
        exact nilt_in_T (T := traces P M)
    · rw [in_traces_SKIP] at hs
      rcases hs with hs | hs
      · exact False.elim (event_app_not_nil_right hsNo hs)
      · have hsNil : s = <> := by
          have hEq :
              s ^^^ (Abs_trace [Tick] : traceType α) =
                (<> : traceType α) ^^^ Abs_trace [Tick] := by
            simpa [appt_nil_left] using hs
          exact (appt_same_last hsNo (by simp)).mp hEq |>.1
        subst s
        have hu' : u = t := by
          simpa [appt_nil_left] using hu
        simpa [hu'] using ht
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo]
    right
    refine ⟨<>, u, by simp, ?_, hu, by simp [noTick]⟩
    simpa [appt_nil_left] using
      (in_traces_SKIP (t := Abs_trace [Tick]) (M := M)).2 (Or.inr rfl)

/-
(*********************************************************
                       P ;; SKIP
 *********************************************************)
-/

theorem cspT_Seq_compo_unit_r
    {P : proc p α} {M : p → domTType α} :
    eqT ((P ;; (proc.SKIP : proc p α))) M M P := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo] at hu
    rcases hu with ⟨s, hu, hs⟩ | ⟨s, t, hu, hs, ht, hsNo⟩
    · subst u
      exact memT_prefix_closed hs rmTick_prefix_rev_simp
    · rw [in_traces_SKIP] at ht
      rcases ht with rfl | rfl
      · have hs' : s :t traces P M := by
          simpa [rmTick_appt_dist (s := s) (t := Abs_trace [Tick]) hsNo] using
            (memT_prefix_closed hs (rmTick_prefix_rev_simp (s := s ^^^ Abs_trace [Tick])))
        have hu' : u = s := by
          simpa [appt_nil_right] using hu
        simpa [hu'] using hs'
      · subst u
        simpa using hs
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo]
    rcases trace_last_noTick_or_Tick u with huNo | ⟨s, hsNo, huEq⟩
    · left
      exact ⟨u, (rmTick_nochange huNo).symm, hu⟩
    · right
      have hsTrace : s ^^^ (Abs_trace [Tick] : traceType α) :t traces P M := by
        simpa [huEq] using hu
      exact ⟨s, Abs_trace [Tick], huEq, hsTrace,
        (in_traces_SKIP (t := Abs_trace [Tick]) (M := M)).2 (Or.inr rfl), hsNo⟩

/- The Isabelle theorem bundle `cspT_Seq_compo_unit` is represented by
   `cspT_Seq_compo_unit_l` and `cspT_Seq_compo_unit_r`. -/

/-
(*********************************************************
               SKIP and Sequential composition
 *********************************************************)
-/

/- p.141 -/

axiom cspT_SKIP_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((((proc.Ext_pre_choice X Pf) [> (proc.SKIP : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> Q))

/-
(*********************************************************
                      SKIP |. n
 *********************************************************)
-/

theorem cspT_SKIP_Depth_rest
    {n : Nat} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.SKIP : proc p α) |. Nat.succ n)) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Depth_rest] at ht
    rw [in_traces_SKIP] at ht ⊢
    exact ht.1
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_SKIP] at ht
    rw [in_traces_Depth_rest]
    rcases ht with rfl | rfl
    · exact ⟨(in_traces_SKIP (t := <>) (M := M1)).2 (Or.inl rfl), by simp⟩
    · exact ⟨(in_traces_SKIP (t := Abs_trace [Tick]) (M := M1)).2 (Or.inr rfl), by simp⟩

/- The Isabelle theorem bundle `cspT_SKIP` is represented by
   `cspT_Parallel_term`, `cspT_Parallel_preterm_l`,
   `cspT_Parallel_preterm_r`, `cspT_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspT_SKIP_Parallel_Ext_choice_SKIP_r`, `cspT_SKIP_Hiding_Id`,
   `cspT_SKIP_Hiding_step`, `cspT_SKIP_Renaming_Id`,
   `cspT_Seq_compo_unit_l`, `cspT_Seq_compo_unit_r`,
   `cspT_SKIP_Seq_compo_step`, and `cspT_SKIP_Depth_rest`. -/

/-
(*********************************************************
                       P [+] SKIP
 *********************************************************)
-/

/- p.141 -/

theorem cspT_Ext_choice_SKIP_resolve
    {P : proc p α} {M : p → domTType α} :
    eqT (P [+] (proc.SKIP : proc p α)) M M ((P [> (proc.SKIP : proc p α))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_Timeout1]
    exact ht
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Timeout1] at ht
    rw [in_traces_Ext_choice]
    exact ht

theorem cspT_Ext_choice_SKIP_resolve_sym
    {P : proc p α} {M : p → domTType α} :
    eqT ((P [> (proc.SKIP : proc p α))) M M (P [+] (proc.SKIP : proc p α)) := by
  exact cspT_sym cspT_Ext_choice_SKIP_resolve

/-
(*********************************************************
                    SKIP ||| P
 *********************************************************)
-/

theorem cspT_Interleave_unit_l
    {P : proc p α} {M : p → domTType α} :
    eqT (((proc.SKIP : proc p α) |[({} : Set α)]| P)) M M P := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Parallel] at hu
    rcases hu with ⟨s, t, hu, hs, ht⟩
    rw [in_traces_SKIP] at hs
    rcases hs with rfl | rfl
    · rcases (par_tr_nil_left.mp hu) with ⟨huEq, _, _⟩
      subst u
      exact ht
    · rcases (par_tr_Tick_left.mp hu) with ⟨huEq, _, _⟩
      subst u
      exact ht
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Parallel]
    by_cases huNo : noTick u
    · refine ⟨<>, u, ?_, (in_traces_SKIP (t := <>) (M := M)).2 (Or.inl rfl), hu⟩
      rw [par_tr_nil_left]
      exact ⟨rfl, by simpa [noTick] using huNo, by simp⟩
    · have huTick : Tick ∈ sett u := by
        by_contra hTick
        apply huNo
        simpa [noTick] using hTick
      refine ⟨Abs_trace [Tick], u, ?_,
        (in_traces_SKIP (t := Abs_trace [Tick]) (M := M)).2 (Or.inr rfl), hu⟩
      rw [par_tr_Tick_left]
      exact ⟨rfl, huTick, by simp⟩

/-
(*********************************************************
                    P ||| SKIP
 *********************************************************)
-/

theorem cspT_Interleave_unit_r
    {P : proc p α} {M : p → domTType α} :
    eqT ((P |[({} : Set α)]| (proc.SKIP : proc p α))) M M P := by
  have h₁ :
      eqT ((P |[({} : Set α)]| (proc.SKIP : proc p α))) M M
        (((proc.SKIP : proc p α) |[({} : Set α)]| P)) :=
    cspT_Parallel_commut
  have h₂ :
      eqT (((proc.SKIP : proc p α) |[({} : Set α)]| P)) M M P :=
    cspT_Interleave_unit_l
  exact cspT_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspT_Interleave_unit` is represented by
   `cspT_Interleave_unit_l` and `cspT_Interleave_unit_r`. -/

end
