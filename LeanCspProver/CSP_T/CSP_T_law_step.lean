           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
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

theorem cspT_STOP_step
    {Pf : α → proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.STOP : proc p α) M1 M2 (proc.Ext_pre_choice (∅ : Set α) Pf) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice]
    rw [in_traces_STOP] at ht
    subst t
    exact Or.inl rfl
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_STOP]
    rcases ht with rfl | ⟨a, s, rfl, _, haEmpty⟩
    · rfl
    · simp at haEmpty

/- to avoide producing free variables (Pf) in tactics -/

theorem cspT_STOP_step_DIV
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.STOP : proc p α) M1 M2
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => (proc.DIV : proc q α))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice]
    rw [in_traces_STOP] at ht
    subst t
    exact Or.inl rfl
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_STOP]
    rcases ht with rfl | ⟨a, s, rfl, _, haEmpty⟩
    · rfl
    · simp at haEmpty

/-
(*********************************************************
                    Act_prefix expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Act_prefix_step
    {a : α} {P : proc p α} {M : p → domTType α} :
    eqT (a ~> P) M M (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Act_prefix] at ht
    rw [in_traces_Ext_pre_choice]
    rcases ht with rfl | ⟨s, rfl, hs⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a, s, rfl, hs, by simp⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_Act_prefix]
    rcases ht with rfl | ⟨x, s, rfl, hs, hx⟩
    · exact Or.inl rfl
    · have : x = a := by simpa using hx
      subst x
      exact Or.inr ⟨s, rfl, hs⟩

/-
(*********************************************************
                    Ext choice expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Ext_choice_step
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf)) M M
      (proc.Ext_pre_choice (X ∪ Y) fun x =>
        procIte (x ∈ X ∧ x ∈ Y) (Pf x |~| Qf x)
          (procIte (x ∈ X) (Pf x) (Qf x))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_Ext_pre_choice]
    rcases ht with ht | ht
    · rw [in_traces_Ext_pre_choice] at ht
      rcases ht with rfl | ⟨a, s, rfl, hs, haX⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨a, s, rfl, ?_, Or.inl haX⟩
        by_cases haY : a ∈ Y
        · have hs' : s :t traces (Pf a |~| Qf a) M := by
            rw [in_traces_Int_choice]
            exact Or.inl hs
          simpa [procIte, haX, haY] using hs'
        · simpa [procIte, haX, haY] using hs
    · rw [in_traces_Ext_pre_choice] at ht
      rcases ht with rfl | ⟨a, s, rfl, hs, haY⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨a, s, rfl, ?_, Or.inr haY⟩
        by_cases haX : a ∈ X
        · have hs' : s :t traces (Pf a |~| Qf a) M := by
            rw [in_traces_Int_choice]
            exact Or.inr hs
          simpa [procIte, haX, haY] using hs'
        · simpa [procIte, haX, haY] using hs
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_Ext_choice]
    rcases ht with rfl | ⟨a, s, rfl, hs, haXY⟩
    · left
      rw [in_traces_Ext_pre_choice]
      exact Or.inl rfl
    · rcases haXY with haX | haY
      · by_cases hY : a ∈ Y
        · have hs' : s :t traces (Pf a |~| Qf a) M := by
            simpa [procIte, haX, hY] using hs
          rw [in_traces_Int_choice] at hs'
          rcases hs' with hPf | hQf
          · left
            rw [in_traces_Ext_pre_choice]
            exact Or.inr ⟨a, s, rfl, hPf, haX⟩
          · right
            rw [in_traces_Ext_pre_choice]
            exact Or.inr ⟨a, s, rfl, hQf, hY⟩
        · left
          rw [in_traces_Ext_pre_choice]
          exact Or.inr ⟨a, s, rfl, by simpa [procIte, haX, hY] using hs, haX⟩
      · by_cases hX : a ∈ X
        · have hs' : s :t traces (Pf a |~| Qf a) M := by
            simpa [procIte, hX, haY] using hs
          rw [in_traces_Int_choice] at hs'
          rcases hs' with hPf | hQf
          · left
            rw [in_traces_Ext_pre_choice]
            exact Or.inr ⟨a, s, rfl, hPf, hX⟩
          · right
            rw [in_traces_Ext_pre_choice]
            exact Or.inr ⟨a, s, rfl, hQf, haY⟩
        · right
          rw [in_traces_Ext_pre_choice]
          exact Or.inr ⟨a, s, rfl, by simpa [procIte, hX, haY] using hs, haY⟩

/-
(*********************************************************
                    Parallel expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspT_Parallel_step
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice Y Pf) |[X]| (proc.Ext_pre_choice Z Qf)) M M
      (proc.Ext_pre_choice (((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X))) fun x =>
        procIte (x ∈ X) ((Pf x) |[X]| (Qf x))
          (procIte (x ∈ Y ∧ x ∈ Z)
            (((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
              (proc.Ext_pre_choice Y Pf |[X]| Qf x)))
            (procIte (x ∈ Y)
              (Pf x |[X]| proc.Ext_pre_choice Z Qf)
              (proc.Ext_pre_choice Y Pf |[X]| Qf x))))

/-
(*********************************************************
                      Hide expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspT_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Hiding (proc.Ext_pre_choice Y Pf) X) M M
      (procIte (Y ∩ X = ∅)
        (proc.Ext_pre_choice Y (fun x => proc.Hiding (Pf x) X))
        ((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X))
          [> Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X)))

/-
(*********************************************************
                    Renaming expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Renaming_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[r]]) M M
      (proc.Ext_pre_choice {y | ∃ x, x ∈ X ∧ (x, y) ∈ r} fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ (x, y) ∈ r} (fun x => (Pf x)[[r]])) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Renaming] at ht
    rcases ht with ⟨s, hsRen, hs⟩
    rw [in_traces_Ext_pre_choice] at hs
    rw [in_traces_Ext_pre_choice]
    rcases hs with rfl | ⟨a, sa, rfl, hsa, haX⟩
    · exact Or.inl ((ren_tr_nil1 (r := r) (s := t)).1 hsRen)
    · rcases (ren_tr_decompo_left (a := a) (s := sa) (r := r) (u := t)).1 hsRen with
        ⟨b, ta, htEq, hab, hren⟩
      subst t
      refine Or.inr ⟨b, ta, rfl, ?_, ⟨a, haX, hab⟩⟩
      rw [in_traces_Rep_int_choice_com]
      refine Or.inr ⟨a, ⟨haX, hab⟩, ?_⟩
      rw [in_traces_Renaming]
      exact ⟨sa, hren, hsa⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_Renaming]
    rcases ht with rfl | ⟨y, ta, rfl, hta, hy⟩
    · exact ⟨<>, ren_tr_nil, (in_traces_Ext_pre_choice (t := <>) (X := X) (Pf := Pf) (M := M)).2
        (Or.inl rfl)⟩
    · rw [in_traces_Rep_int_choice_com] at hta
      rcases hta with hta | ⟨x, hx, htx⟩
      · subst ta
        rcases hy with ⟨x, hxX, hxy⟩
        refine ⟨Abs_trace [Ev x], ?_, ?_⟩
        · simpa using (ren_tr_one (a := x) (b := y) (r := r) hxy)
        · rw [in_traces_Ext_pre_choice]
          exact Or.inr ⟨x, <>, by simp, nilt_in_T, hxX⟩
      · rw [in_traces_Renaming] at htx
        rcases htx with ⟨sa, hren, hsa⟩
        refine ⟨Abs_trace [Ev x] ^^^ sa, ?_, ?_⟩
        · exact ren_tr_decompo_left_if hx.2 hren
        · rw [in_traces_Ext_pre_choice]
          exact Or.inr ⟨x, sa, rfl, hsa, hx.1⟩

/-
(*********************************************************
            Sequential composition expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

set_option maxHeartbeats 1000000 in
theorem cspT_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf) ;; Q) M M
      (proc.Ext_pre_choice X (fun x => Pf x ;; Q)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Seq_compo] at hu
    rw [in_traces_Ext_pre_choice]
    rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, huEq, hsTick, ht, hsNo⟩
    · rw [in_traces_Ext_pre_choice] at hs
      rcases hs with rfl | ⟨a, sa, rfl, hsa, haX⟩
      · simpa [rmTick_nil] using (Or.inl rfl : (<> = <> ∨ ∃ a s, <> = Abs_trace [Ev a] ^^^ s ∧ s :t traces (Pf a) M ∧ a ∈ X))
      · have hrm : rmTick (Abs_trace [Ev a] ^^^ sa) = Abs_trace [Ev a] ^^^ rmTick sa := by
          exact rmTick_appt_dist (s := Abs_trace [Ev a]) (t := sa) (noTick_Ev a)
        have hseq : rmTick sa :t traces (Pf a ;; Q) M := by
          rw [in_traces_Seq_compo]
          exact Or.inl ⟨sa, rfl, hsa⟩
        exact Or.inr ⟨a, rmTick sa, by simpa [hrm], hseq, haX⟩
    · rw [in_traces_Ext_pre_choice] at hsTick
      rcases hsTick with hsTick | ⟨a, sa, hEq, hsa, haX⟩
      · exact False.elim (event_app_not_nil_right hsNo hsTick)
      · rcases trace_nil_or_Tick_or_Ev s with rfl | hsTick' | ⟨b, sb, rfl⟩
        · have hhd : Tick = Ev a := by
            simpa [appt_nil_left, hdt_appt] using congrArg hdt hEq
          cases hhd
        · subst s
          exact False.elim (not_noTick_Tick hsNo)
        · have hsbNo : noTick sb := by
            exact (decompo_appt_noTick_only_if (s := Abs_trace [Ev b]) (t := sb)
              (Or.inl (noTick_Ev b)) (by simpa using hsNo)).2
          have hAssoc :
              (Abs_trace [Ev b] ^^^ sb) ^^^ (Abs_trace [Tick] : traceType α) =
                Abs_trace [Ev b] ^^^ (sb ^^^ (Abs_trace [Tick] : traceType α)) := by
            exact appt_assoc (Or.inl (noTick_Ev b)) (Or.inl hsbNo)
          have hHead :
              Abs_trace [Ev b] ^^^ (sb ^^^ (Abs_trace [Tick] : traceType α)) =
                Abs_trace [Ev a] ^^^ sa := by
            calc
              Abs_trace [Ev b] ^^^ (sb ^^^ (Abs_trace [Tick] : traceType α))
                  = (Abs_trace [Ev b] ^^^ sb) ^^^ (Abs_trace [Tick] : traceType α) := hAssoc.symm
              _ = Abs_trace [Ev a] ^^^ sa := hEq
          have hab : b = a ∧ sb ^^^ (Abs_trace [Tick] : traceType α) = sa :=
            (appt_same_head.mp hHead)
          rcases hab with ⟨hba, htail⟩
          subst b
          have hseq : (sb ^^^ t) :t traces (Pf a ;; Q) M := by
            rw [in_traces_Seq_compo]
            exact Or.inr ⟨sb, t, rfl, by simpa [htail] using hsa, ht, hsbNo⟩
          have huEq' : u = Abs_trace [Ev a] ^^^ (sb ^^^ t) := by
            calc
              u = (Abs_trace [Ev a] ^^^ sb) ^^^ t := huEq
              _ = Abs_trace [Ev a] ^^^ (sb ^^^ t) := appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)
          exact Or.inr ⟨a, sb ^^^ t, huEq', hseq, haX⟩
  · rw [subdomT_iff]
    intro u hu
    rw [in_traces_Ext_pre_choice] at hu
    rw [in_traces_Seq_compo]
    rcases hu with rfl | ⟨a, v, rfl, hv, haX⟩
    · exact Or.inl ⟨<>, by simp, (in_traces_Ext_pre_choice (t := <>) (X := X) (Pf := Pf)
          (M := M)).2 (Or.inl rfl)⟩
    · rw [in_traces_Seq_compo] at hv
      rcases hv with ⟨sa, hvEq, hsa⟩ | ⟨sb, t, hvEq, hsTick, ht, hsbNo⟩
      · left
        refine ⟨Abs_trace [Ev a] ^^^ sa, ?_, ?_⟩
        · simpa [rmTick_appt_dist (s := Abs_trace [Ev a]) (t := sa) (noTick_Ev a)] using hvEq
        · rw [in_traces_Ext_pre_choice]
          exact Or.inr ⟨a, sa, rfl, hsa, haX⟩
      · refine Or.inr ⟨Abs_trace [Ev a] ^^^ sb, t, ?_, ?_, ht, ?_⟩
        · calc
            Abs_trace [Ev a] ^^^ v = Abs_trace [Ev a] ^^^ (sb ^^^ t) := by rw [hvEq]
            _ = (Abs_trace [Ev a] ^^^ sb) ^^^ t := by
              exact (appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)).symm
        · rw [in_traces_Ext_pre_choice]
          refine Or.inr ⟨a, sb ^^^ (Abs_trace [Tick] : traceType α),
            appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo), ?_, haX⟩
          simpa [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hsbNo)] using hsTick
        · exact decompo_appt_noTick_if (noTick_Ev a) hsbNo

/-
(*********************************************************
                    Depth_rest expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Depth_rest_step
    {X : Set α} {Pf : α → proc p α} {n : Nat} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf) |. Nat.succ n) M M
      (proc.Ext_pre_choice X (fun x => (Pf x) |. n)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Depth_rest] at ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_Ext_pre_choice]
    rcases ht.1 with rfl | ⟨a, s, rfl, hs, haX⟩
    · exact Or.inl rfl
    · refine Or.inr ⟨a, s, rfl, ?_, haX⟩
      rw [in_traces_Depth_rest]
      refine ⟨hs, ?_⟩
      have hlen : lengtht (Abs_trace [Ev a] ^^^ s) = Nat.succ (lengtht s) :=
        lengtht_app_event_Suc_head
      have hsLen : Nat.succ (lengtht s) ≤ Nat.succ n := by
        simpa [hlen] using ht.2
      exact Nat.succ_le_succ_iff.mp hsLen
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_Depth_rest]
    rcases ht with rfl | ⟨a, s, rfl, hs, haX⟩
    · exact ⟨(in_traces_Ext_pre_choice (t := <>) (X := X) (Pf := Pf) (M := M)).2 (Or.inl rfl), by simp⟩
    · have hs' : s :t traces (Pf a) M ∧ lengtht s ≤ n := by
        rw [in_traces_Depth_rest] at hs
        exact hs
      refine ⟨(in_traces_Ext_pre_choice (t := Abs_trace [Ev a] ^^^ s) (X := X) (Pf := Pf) (M := M)).2
        (Or.inr ⟨a, s, rfl, hs'.1, haX⟩), ?_⟩
      have hlen : lengtht (Abs_trace [Ev a] ^^^ s) = Nat.succ (lengtht s) :=
        lengtht_app_event_Suc_head
      simpa [hlen] using Nat.succ_le_succ hs'.2

/- The Isabelle theorem bundle `cspT_step` is represented by
   `cspT_STOP_step`, `cspT_Act_prefix_step`, `cspT_Ext_choice_step`,
   `cspT_Parallel_step`, `cspT_Hiding_step`, `cspT_Renaming_step`,
   `cspT_Seq_compo_step`, and `cspT_Depth_rest_step`. -/

/- The Isabelle theorem bundle `cspT_light_step` is represented by
   `cspT_STOP_step` and `cspT_Act_prefix_step`. -/

/- The Isabelle theorem bundle `cspT_step_rw` is represented by
   `cspT_STOP_step_DIV`, `cspT_Act_prefix_step`, `cspT_Ext_choice_step`,
   `cspT_Parallel_step`, `cspT_Hiding_step`, `cspT_Renaming_step`,
   `cspT_Seq_compo_step`, and `cspT_Depth_rest_step`. -/

/- The Isabelle theorem bundle `cspT_light_step_rw` is represented by
   `cspT_STOP_step_DIV` and `cspT_Act_prefix_step`. -/

end
