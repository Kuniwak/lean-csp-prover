           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005               |
            |                  April 2006  (modified)   |
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

/- T -/

theorem cspT_DIV_Parallel
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.DIV : proc p α) |[X]| proc.DIV)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Parallel] at ht
    rcases ht with ⟨s, u, ht, hs, hu⟩
    rw [in_traces_DIV] at hs hu
    subst s
    subst u
    exact (in_traces_DIV (t := t) (M := M2)).2 ((par_tr_nil_left.mp ht).1)
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Parallel]
    exact ⟨<>, <>, par_tr_nil_nil, (in_traces_DIV (t := <>) (M := M1)).2 rfl,
      (in_traces_DIV (t := <>) (M := M1)).2 rfl⟩

/-
(*********************************************************
                       DIV |[X]| P
 *********************************************************)
-/

theorem cspT_DIV_Parallel_step_l
    {X Y : Set α} {Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.DIV : proc p α) |[X]| proc.Ext_pre_choice Y Qf)) M M
      ((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.DIV : proc p α) |[X]| Qf x))) [+] proc.DIV) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Parallel] at hu
    rcases hu with ⟨s, t, hu, hs, ht⟩
    rw [in_traces_DIV] at hs
    subst s
    rw [in_traces_Ext_pre_choice] at ht
    rcases ht with rfl | ⟨a, ta, rfl, hta, haY⟩
    · rw [in_traces_Ext_choice]
      exact Or.inr ((in_traces_DIV (t := u) (M := M)).2 ((par_tr_nil_left.mp hu).1))
    · rw [in_traces_Ext_choice]
      left
      rw [in_traces_Ext_pre_choice]
      rcases
          (par_tr_nil_Ev_iff (u := u) (t := ta) (X := X) (a := a)).1 hu with
        ⟨haX, v, rfl, hv⟩
      refine Or.inr ⟨a, v, rfl, ?_, ⟨haY, haX⟩⟩
      rw [in_traces_Parallel]
      exact ⟨<>, ta, hv, (in_traces_DIV (t := <>) (M := M)).2 rfl, hta⟩
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Ext_choice] at hu
    rcases hu with hu | hu
    · rw [in_traces_Ext_pre_choice] at hu
      rcases hu with rfl | ⟨a, v, rfl, hv, haYX⟩
      · rw [in_traces_Parallel]
        exact ⟨<>, <>, par_tr_nil_nil, (in_traces_DIV (t := <>) (M := M)).2 rfl,
          (in_traces_Ext_pre_choice (t := <>) (X := Y) (Pf := Qf) (M := M)).2 (Or.inl rfl)⟩
      · rw [in_traces_Parallel] at hv
        rcases hv with ⟨s, t, hv, hs, ht⟩
        rw [in_traces_DIV] at hs
        subst s
        rw [in_traces_Parallel]
        refine ⟨<>, Abs_trace [Ev a] ^^^ t, par_tr_nil_Ev hv haYX.2,
          (in_traces_DIV (t := <>) (M := M)).2 rfl, ?_⟩
        rw [in_traces_Ext_pre_choice]
        exact Or.inr ⟨a, t, rfl, ht, haYX.1⟩
    · rw [in_traces_DIV] at hu
      subst u
      rw [in_traces_Parallel]
      exact ⟨<>, <>, par_tr_nil_nil, (in_traces_DIV (t := <>) (M := M)).2 rfl,
        (in_traces_Ext_pre_choice (t := <>) (X := Y) (Pf := Qf) (M := M)).2 (Or.inl rfl)⟩

/- (*** r ***) -/

theorem cspT_DIV_Parallel_step_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice Y Pf) |[X]| (proc.DIV : proc p α)) M M
      ((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.DIV : proc p α)))) [+] proc.DIV) := by
  have h₁ :
      eqT ((proc.Ext_pre_choice Y Pf) |[X]| (proc.DIV : proc p α)) M M
        (((proc.DIV : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) :=
    cspT_Parallel_commut
  have h₂ :
      eqT
        (((proc.DIV : proc p α) |[X]| proc.Ext_pre_choice Y Pf))
        M M
        ((proc.Ext_pre_choice
            (Y \ X)
            (fun x => ((proc.DIV : proc p α) |[X]| Pf x))) [+] proc.DIV) :=
    cspT_DIV_Parallel_step_l
  have h₃₁ :
      eqT (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.DIV : proc p α) |[X]| Pf x))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.DIV : proc p α)))) := by
    apply cspT_Ext_pre_choice_cong rfl
    intro a ha
    exact cspT_Parallel_commut
  have h₃ :
      eqT
        (((proc.Ext_pre_choice
            (Y \ X)
            (fun x => ((proc.DIV : proc p α) |[X]| Pf x))) [+] proc.DIV))
        M M
        (((proc.Ext_pre_choice
            (Y \ X)
            (fun x => (Pf x |[X]| (proc.DIV : proc p α)))) [+] proc.DIV)) := by
    exact cspT_Ext_choice_cong h₃₁ cspT_reflex_eq_DIV
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_DIV_Parallel_step` is represented by
   `cspT_DIV_Parallel_step_l` and `cspT_DIV_Parallel_step_r`. -/

/-
(*********************************************************
                      DIV and Parallel
 *********************************************************)
-/

theorem cspT_DIV_Parallel_Ext_choice_DIV_l
    {P : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (((P [+] proc.DIV) |[X]| (proc.DIV : proc p α))) M M (P |[X]| (proc.DIV : proc p α)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Parallel] at hu
    rcases hu with ⟨s, t, hu, hs, ht⟩
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Ext_choice] at hs
    rcases hs with hs | hs
    · rw [in_traces_Parallel]
      exact ⟨s, <>, hu, hs, (in_traces_DIV (t := <>) (M := M)).2 rfl⟩
    · rw [in_traces_DIV] at hs
      subst s
      have huNil : u = <> := (par_tr_nil_left.mp hu).1
      subst u
      rw [in_traces_Parallel]
      exact ⟨<>, <>, par_tr_nil_nil, nilt_in_T, (in_traces_DIV (t := <>) (M := M)).2 rfl⟩
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Parallel] at hu
    rcases hu with ⟨s, t, hu, hs, ht⟩
    rw [in_traces_Parallel]
    refine ⟨s, t, hu, ?_, ht⟩
    rw [in_traces_Ext_choice]
    exact Or.inl hs

theorem cspT_DIV_Parallel_Ext_choice_DIV_r
    {P : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (((proc.DIV : proc p α) |[X]| (P [+] proc.DIV))) M M ((proc.DIV : proc p α) |[X]| P) := by
  have h₁ :
      eqT
        (((proc.DIV : proc p α) |[X]| (P [+] proc.DIV)))
        M M
        (((P [+] proc.DIV) |[X]| (proc.DIV : proc p α))) :=
    cspT_Parallel_commut
  have h₂ :
      eqT (((P [+] proc.DIV) |[X]| (proc.DIV : proc p α))) M M (P |[X]| (proc.DIV : proc p α)) :=
    cspT_DIV_Parallel_Ext_choice_DIV_l
  have h₃ : eqT (P |[X]| (proc.DIV : proc p α)) M M (((proc.DIV : proc p α) |[X]| P)) :=
    cspT_Parallel_commut
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_DIV_Parallel_Ext_choice_DIV` is
   represented by `cspT_DIV_Parallel_Ext_choice_DIV_l` and
   `cspT_DIV_Parallel_Ext_choice_DIV_r`. -/

/-
(*********************************************************
                      DIV -- X
 *********************************************************)
-/

theorem cspT_DIV_Hiding_Id
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.Hiding (proc.DIV : proc p α) X) M1 M2 (proc.DIV : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Hiding] at ht
    rcases ht with ⟨s, rfl, hs⟩
    rw [in_traces_DIV] at hs
    subst s
    simp [in_traces_DIV]
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Hiding]
    exact ⟨<>, by simp, (in_traces_DIV (t := <>) (M := M1)).2 rfl⟩

/- (*** div-hide-step ***) -/

theorem cspT_DIV_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] proc.DIV) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Hiding] at ht
    rcases ht with ⟨s, rfl, hs⟩
    rw [in_traces_Ext_choice] at hs
    rcases hs with hs | hs
    · rw [in_traces_Ext_pre_choice] at hs
      rcases hs with rfl | ⟨a, sa, rfl, hsa, haY⟩
      · rw [in_traces_Int_choice, in_traces_Ext_choice]
        simp [in_traces_DIV]
      · by_cases haX : a ∈ X
        · rw [in_traces_Int_choice]
          right
          rw [in_traces_Rep_int_choice_com]
          refine Or.inr ⟨a, ⟨haY, haX⟩, ?_⟩
          rw [in_traces_Hiding]
          exact ⟨sa, hide_tr_in haX, hsa⟩
        · rw [in_traces_Int_choice]
          left
          rw [in_traces_Ext_choice]
          left
          rw [in_traces_Ext_pre_choice]
          refine Or.inr ⟨a, hide_tr sa X, ?_, ?_, ⟨haY, haX⟩⟩
          · exact hide_tr_notin_appt haX
          · rw [in_traces_Hiding]
            exact ⟨sa, rfl, hsa⟩
    · rw [in_traces_DIV] at hs
      subst s
      rw [in_traces_Int_choice, in_traces_Ext_choice]
      simp [in_traces_DIV]
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      rcases ht with ht | ht
      · rw [in_traces_Ext_pre_choice] at ht
        rcases ht with rfl | ⟨a, ta, rfl, hta, haYX⟩
        · rw [in_traces_Hiding]
          refine ⟨<>, by simp, ?_⟩
          rw [in_traces_Ext_choice]
          exact Or.inr <| (in_traces_DIV (t := <>) (M := M)).2 rfl
        · rw [in_traces_Hiding] at hta
          rcases hta with ⟨sa, rfl, hsa⟩
          rw [in_traces_Hiding]
          refine ⟨Abs_trace [Ev a] ^^^ sa, ?_, ?_⟩
          · exact (hide_tr_notin_appt haYX.2).symm
          · rw [in_traces_Ext_choice, in_traces_Ext_pre_choice]
            exact Or.inl <| Or.inr ⟨a, sa, rfl, hsa, haYX.1⟩
      · rw [in_traces_DIV] at ht
        subst t
        rw [in_traces_Hiding]
        refine ⟨<>, by simp, ?_⟩
        rw [in_traces_Ext_choice]
        exact Or.inr <| (in_traces_DIV (t := <>) (M := M)).2 rfl
    · rw [in_traces_Rep_int_choice_com] at ht
      rcases ht with rfl | ⟨a, haYX, hta⟩
      · rw [in_traces_Hiding]
        exact
          ⟨<>,
            by simp,
            (in_traces_Ext_choice (t := <>) (P := proc.Ext_pre_choice Y Pf)
              (Q := (proc.DIV : proc p α)) (M := M)).2 <|
                Or.inr <| (in_traces_DIV (t := <>) (M := M)).2 rfl⟩
      · rw [in_traces_Hiding] at hta
        rcases hta with ⟨sa, rfl, hsa⟩
        rw [in_traces_Hiding]
        refine ⟨Abs_trace [Ev a] ^^^ sa, ?_, ?_⟩
        · exact (hide_tr_in haYX.2).symm
        · rw [in_traces_Ext_choice, in_traces_Ext_pre_choice]
          exact Or.inl <| Or.inr ⟨a, sa, rfl, hsa, haYX.1⟩

/-
(*********************************************************
                      DIV [[r]]
 *********************************************************)
-/

theorem cspT_DIV_Renaming_Id
    {r : Set (α × α)} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.DIV : proc p α)[[r]])) M1 M2 (proc.DIV : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Renaming] at ht
    rcases ht with ⟨s, hs, ht⟩
    rw [in_traces_DIV] at ht
    subst s
    rw [in_traces_DIV]
    exact (ren_tr_nil1 (r := r) (s := t)).1 hs
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Renaming]
    exact ⟨<>, ren_tr_nil, (in_traces_DIV (t := <>) (M := M1)).2 rfl⟩

/-
(*********************************************************
                       DIV ;; P
 *********************************************************)
-/

theorem cspT_DIV_Seq_compo
    {P : proc p α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.DIV : proc p α) ;; P)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo] at hu
    rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hs, ht, hsNo⟩
    · rw [in_traces_DIV] at hs
      subst s
      rw [in_traces_DIV]
      simp
    · have : s ^^^ (Abs_trace [event.Tick] : traceType α) = <> := (in_traces_DIV (t := _)
        (M := M1)).1 hs
      exact False.elim ((event_app_not_nil_right hsNo this))
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Seq_compo]
    exact Or.inl ⟨<>, by simp, (in_traces_DIV (t := <>) (M := M1)).2 rfl⟩

/-
(*********************************************************
               DIV and Sequential composition
 *********************************************************)
-/

set_option maxHeartbeats 1000000 in
-- Nested trace expansions in this sequential-composition proof need extra heartbeats.
theorem cspT_DIV_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α)) ;; Q)) M M
      ((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> (proc.DIV : proc p α)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo] at hu
    rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hs, ht, hsNo⟩
    · rw [in_traces_Timeout1] at hs
      rcases hs with hs | hs
      · rw [in_traces_Ext_pre_choice] at hs
        rcases hs with rfl | ⟨a, sa, rfl, hsa, haX⟩
        · rw [in_traces_Timeout1]
          right
          rw [in_traces_DIV]
          simp
        · have hrm :
            rmTick (Abs_trace [event.Ev a] ^^^ sa) =
              Abs_trace [event.Ev a] ^^^ rmTick sa := by
            exact rmTick_appt_dist (s := Abs_trace [event.Ev a]) (t := sa) (noTick_Ev a)
          have hseq : rmTick sa :t traces (Pf a ;; Q) M := by
            rw [in_traces_Seq_compo]
            exact Or.inl ⟨sa, rfl, hsa⟩
          rw [in_traces_Timeout1]
          left
          rw [in_traces_Ext_pre_choice]
          exact Or.inr ⟨a, rmTick sa, by simp [hrm], hseq, haX⟩
      · rw [in_traces_DIV] at hs
        subst s
        rw [in_traces_Timeout1]
        right
        rw [in_traces_DIV]
        simp
    · rw [in_traces_Timeout1] at hs
      rcases hs with hs | hs
      · rw [in_traces_Ext_pre_choice] at hs
        rcases hs with hs | ⟨a, sa, hEq, hsa, haX⟩
        · have hnil : s = <> := (appt_nil hsNo).mp hs |>.1
          subst s
          simp at hs
        · rcases trace_nil_or_Tick_or_Ev s with rfl | hsTick | ⟨b, sb, rfl⟩
          · have hhd : event.Tick = event.Ev a := by
              simpa [appt_nil_left, hdt_appt] using congrArg hdt hEq
            cases hhd
          · subst s
            exact False.elim (not_noTick_Tick hsNo)
          · have hsbNo : noTick sb := by
              exact (decompo_appt_noTick_only_if (s := Abs_trace [event.Ev b]) (t := sb)
                (Or.inl (noTick_Ev b)) (by simpa using hsNo)).2
            have hAssoc :
                (Abs_trace [event.Ev b] ^^^ sb) ^^^ (Abs_trace [event.Tick] : traceType α) =
                  Abs_trace [event.Ev b] ^^^ (sb ^^^ (Abs_trace [event.Tick] : traceType α)) := by
              exact appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hsbNo)
            have hHead :
                Abs_trace [event.Ev b] ^^^ (sb ^^^ (Abs_trace [event.Tick] : traceType α)) =
                  Abs_trace [event.Ev a] ^^^ sa := by
              calc
                Abs_trace [event.Ev b] ^^^ (sb ^^^ (Abs_trace [event.Tick] : traceType α))
                    =
                      (Abs_trace [event.Ev b] ^^^ sb) ^^^
                        (Abs_trace [event.Tick] : traceType α) := hAssoc.symm
                _ = Abs_trace [event.Ev a] ^^^ sa := hEq
            have hab : b = a ∧ sb ^^^ (Abs_trace [event.Tick] : traceType α) = sa :=
              (appt_same_head.mp hHead)
            rcases hab with ⟨hba, htail⟩
            subst b
            have hseq : (sb ^^^ t) :t traces (Pf a ;; Q) M := by
              rw [in_traces_Seq_compo]
              exact Or.inr ⟨sb, t, rfl, by simpa [htail] using hsa, ht, hsbNo⟩
            have huEq :
                (Abs_trace [event.Ev a] ^^^ sb) ^^^ t =
                  Abs_trace [event.Ev a] ^^^ (sb ^^^ t) := by
              exact appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)
            rw [in_traces_Timeout1]
            left
            rw [in_traces_Ext_pre_choice]
            exact Or.inr ⟨a, sb ^^^ t, huEq, hseq, haX⟩
      · have : s ^^^ (Abs_trace [event.Tick] : traceType α) = <> := (in_traces_DIV (t := _)
          (M := M)).1 hs
        exact False.elim (event_app_not_nil_right hsNo this)
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Timeout1] at hu
    rcases hu with hu | hu
    · rw [in_traces_Ext_pre_choice] at hu
      rcases hu with rfl | ⟨a, v, rfl, hv, haX⟩
      · rw [in_traces_Seq_compo]
        exact
          Or.inl
            ⟨<>,
              by simp,
              (in_traces_Timeout1 (t := <>) (P := proc.Ext_pre_choice X Pf)
                (Q := (proc.DIV : proc p α)) (M := M)).2 <|
                Or.inr <| (in_traces_DIV (t := <>) (M := M)).2 rfl⟩
      · rw [in_traces_Seq_compo] at hv
        rcases hv with ⟨sa, hvEq, hsa⟩ | ⟨sb, t, hvEq, hsTick, ht, hsbNo⟩
        · rw [in_traces_Seq_compo]
          left
          refine ⟨Abs_trace [event.Ev a] ^^^ sa, ?_, ?_⟩
          · cases hvEq
            simp [rmTick_appt_dist (s := Abs_trace [event.Ev a]) (t := sa) (noTick_Ev a)]
          · have htimeout :
                Abs_trace [event.Ev a] ^^^ sa :t
                  traces (((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α))) M := by
              rw [in_traces_Timeout1]
              left
              rw [in_traces_Ext_pre_choice]
              exact Or.inr ⟨a, sa, rfl, hsa, haX⟩
            exact htimeout
        · rw [in_traces_Seq_compo]
          right
          refine ⟨Abs_trace [event.Ev a] ^^^ sb, t, ?_, ?_, ht, ?_⟩
          · calc
              Abs_trace [event.Ev a] ^^^ v = Abs_trace [event.Ev a] ^^^ (sb ^^^ t) := by
                rw [hvEq]
              _ = (Abs_trace [event.Ev a] ^^^ sb) ^^^ t := by
                exact (appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)).symm
          · have htimeout :
                Abs_trace [event.Ev a] ^^^ sb ^^^ (Abs_trace [event.Tick] : traceType α) :t
                  traces (((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α))) M := by
              rw [in_traces_Timeout1]
              left
              rw [in_traces_Ext_pre_choice]
              refine Or.inr ⟨a, sb ^^^ (Abs_trace [event.Tick] : traceType α), rfl, ?_, haX⟩
              simpa using hsTick
            simpa [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)] using htimeout
          · exact decompo_appt_noTick_if (noTick_Ev a) hsbNo
    · rw [in_traces_DIV] at hu
      subst u
      rw [in_traces_Seq_compo]
      exact
        Or.inl
          ⟨<>,
            by simp,
            (in_traces_Timeout1 (t := <>) (P := proc.Ext_pre_choice X Pf)
              (Q := (proc.DIV : proc p α)) (M := M)).2 <|
              Or.inr <| (in_traces_DIV (t := <>) (M := M)).2 rfl⟩

/-
(*********************************************************
                      DIV |. n
 *********************************************************)
-/

theorem cspT_DIV_Depth_rest
    {n : Nat} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (((proc.DIV : proc p α) |. n)) M1 M2 (proc.DIV : proc q α) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Depth_rest] at ht
    exact (in_traces_DIV (t := t) (M := M2)).2 ((in_traces_DIV (t := t) (M := M1)).1 ht.1)
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_DIV] at ht
    subst t
    rw [in_traces_Depth_rest]
    exact ⟨(in_traces_DIV (t := <>) (M := M1)).2 rfl, by simp⟩

/- The Isabelle theorem bundle `cspT_DIV` is represented by
   `cspT_DIV_Parallel`, `cspT_DIV_Parallel_step_l`,
   `cspT_DIV_Parallel_step_r`, `cspT_DIV_Parallel_Ext_choice_DIV_l`,
   `cspT_DIV_Parallel_Ext_choice_DIV_r`, `cspT_DIV_Hiding_Id`,
   `cspT_DIV_Hiding_step`, `cspT_DIV_Renaming_Id`, `cspT_DIV_Seq_compo`,
   `cspT_DIV_Seq_compo_step`, and `cspT_DIV_Depth_rest`. -/

/-
(*********************************************************
                       P [+] DIV
 *********************************************************)
-/

theorem cspT_Ext_choice_DIV_resolve
    {P : proc p α} {M : p → domTType α} :
    eqT (P [+] (proc.DIV : proc p α)) M M (P [> (proc.DIV : proc p α)) := by
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

end
