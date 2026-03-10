           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_SKIP
import LeanCspProver.CSP_T.CSP_T_law_ref
import LeanCspProver.CSP_T.CSP_T_law_dist
import LeanCspProver.CSP_T.CSP_T_law_alpha_par
import LeanCspProver.CSP_T.CSP_T_law_step
import LeanCspProver.CSP_T.CSP_T_law_rep_par
import LeanCspProver.CSP_T.CSP_T_law_fix
import LeanCspProver.CSP_T.CSP_T_law_DIV
import LeanCspProver.CSP_T.CSP_T_law_SKIP_DIV
import LeanCspProver.CSP_T.CSP_T_law_step_ext
import LeanCspProver.CSP_T.CSP_T_law_norm

open Function
open SumType

noncomputable section

/-
(*-----------------------------------------------------------*
 |                                                           |
 |                 Ext_choice_Int_choice                     |
 |                                                           |
 |  These rules show the difference between models T and F.  |
 |                                                           |
 *-----------------------------------------------------------*)
-/

theorem cspT_Ext_choice_Int_choice
    {P1 P2 : proc p α} {M : p → domTType α} :
    eqT (P1 [+] P2) M M (P1 |~| P2) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice]
    rw [in_traces_Ext_choice] at ht
    exact ht
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice]
    rw [in_traces_Int_choice] at ht
    exact ht

theorem cspT_Ext_pre_choice_Rep_int_choice [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice X Pf) M M (Int_pre_choice X Pf) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [Int_pre_choice_def, in_traces_Rep_int_choice_com]
    rw [in_traces_Ext_pre_choice] at ht
    rcases ht with rfl | ⟨a, s, rfl, hs, haX⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a, haX, (in_traces_Act_prefix
        (t := Abs_trace [event.Ev a] ^^^ s) (a := a) (P := Pf a) (M := M)).2
        (Or.inr ⟨s, rfl, hs⟩)⟩
  · rw [subdomT_iff]
    intro t ht
    rw [Int_pre_choice_def, in_traces_Rep_int_choice_com] at ht
    rw [in_traces_Ext_pre_choice]
    rcases ht with rfl | ⟨a, haX, ht⟩
    · exact Or.inl rfl
    · rw [in_traces_Act_prefix] at ht
      rcases ht with rfl | ⟨s, rfl, hs⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨a, s, rfl, hs, haX⟩

/- The Isabelle theorem bundle `cspT_Ext_Int` is represented by
   `cspT_Ext_choice_Int_choice` and `cspT_Ext_pre_choice_Rep_int_choice`. -/

/-
(*********************************************************
            SKIP , DIV  and Internal choice
 *********************************************************)
-/

/- (*** |~| ***) -/

open Classical in
theorem cspT_SKIP_DIV_Int_choice
    {P Q : proc p α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : P = (proc.SKIP : proc p α) ∨ P = proc.DIV)
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqT (P |~| Q) M1 M2
      (if (P = (proc.SKIP : proc p α) ∨ Q = proc.SKIP) then (proc.SKIP : proc q α) else proc.DIV) := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · simp
    exact cspT_trans_left_eq cspT_Int_choice_idem cspT_reflex_eq_SKIP
  · simp
    exact cspT_trans_left_eq cspT_Int_choice_unit_r cspT_reflex_eq_SKIP
  · simp
    exact cspT_trans_left_eq cspT_Int_choice_unit_l cspT_reflex_eq_SKIP
  · simp
    exact cspT_trans_left_eq cspT_Int_choice_idem cspT_reflex_eq_DIV

/- (*** !! ***) -/

open Classical in
theorem cspT_SKIP_DIV_Rep_int_choice_sum
    {C : sets_nats α} {Qf : aset_anat α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hQ : ∀ c, c ∈ sumset C → Qf c = (proc.SKIP : proc p α) ∨ Qf c = proc.DIV) :
    eqT (proc.Rep_int_choice C Qf) M1 M2
      (if (∃ c, c ∈ sumset C ∧ Qf c = (proc.SKIP : proc p α)) then (proc.SKIP : proc q α)
       else proc.DIV) := by
  by_cases hSkip : ∃ c, c ∈ sumset C ∧ Qf c = (proc.SKIP : proc p α)
  · simp [hSkip]
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Rep_int_choice_sum] at ht
      rw [in_traces_SKIP]
      rcases ht with rfl | ⟨c, hc, ht⟩
      · exact Or.inl rfl
      · rcases hQ c hc with hSkipC | hDivC
        · rw [hSkipC] at ht
          rw [in_traces_SKIP] at ht
          exact ht
        · rw [hDivC] at ht
          rw [in_traces_DIV] at ht
          exact Or.inl ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_SKIP] at ht
      rw [in_traces_Rep_int_choice_sum]
      rcases ht with rfl | hTick
      · exact Or.inl rfl
      · rcases hSkip with ⟨c, hc, hSkipC⟩
        refine Or.inr ⟨c, hc, ?_⟩
        rw [hSkipC, in_traces_SKIP]
        exact Or.inr hTick
  · simp [hSkip]
    have hDiv : ∀ c, c ∈ sumset C → Qf c = proc.DIV := by
      intro c hc
      rcases hQ c hc with hSkipC | hDivC
      · exact False.elim (hSkip ⟨c, hc, hSkipC⟩)
      · exact hDivC
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Rep_int_choice_sum] at ht
      rw [in_traces_DIV]
      rcases ht with rfl | ⟨c, hc, ht⟩
      · rfl
      · rw [hDiv c hc] at ht
        rw [in_traces_DIV] at ht
        exact ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_DIV] at ht
      rw [in_traces_Rep_int_choice_sum]
      exact Or.inl ht

open Classical in
theorem cspT_SKIP_DIV_Rep_int_choice_nat
    {N : Set Nat} {Qf : Nat → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hQ : ∀ n, n ∈ N → Qf n = (proc.SKIP : proc p α) ∨ Qf n = proc.DIV) :
    eqT (Rep_int_choice_nat N Qf) M1 M2
      (if (∃ n, n ∈ N ∧ Qf n = (proc.SKIP : proc p α)) then (proc.SKIP : proc q α)
       else proc.DIV) := by
  by_cases hSkip : ∃ n, n ∈ N ∧ Qf n = (proc.SKIP : proc p α)
  · simp [hSkip]
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Rep_int_choice_nat] at ht
      rw [in_traces_SKIP]
      rcases ht with rfl | ⟨n, hn, ht⟩
      · exact Or.inl rfl
      · rcases hQ n hn with hSkipN | hDivN
        · rw [hSkipN] at ht
          rw [in_traces_SKIP] at ht
          exact ht
        · rw [hDivN] at ht
          rw [in_traces_DIV] at ht
          exact Or.inl ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_SKIP] at ht
      rw [in_traces_Rep_int_choice_nat]
      rcases ht with rfl | hTick
      · exact Or.inl rfl
      · rcases hSkip with ⟨n, hn, hSkipN⟩
        refine Or.inr ⟨n, hn, ?_⟩
        rw [hSkipN, in_traces_SKIP]
        exact Or.inr hTick
  · simp [hSkip]
    have hDiv : ∀ n, n ∈ N → Qf n = proc.DIV := by
      intro n hn
      rcases hQ n hn with hSkipN | hDivN
      · exact False.elim (hSkip ⟨n, hn, hSkipN⟩)
      · exact hDivN
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Rep_int_choice_nat] at ht
      rw [in_traces_DIV]
      rcases ht with rfl | ⟨n, hn, ht⟩
      · rfl
      · rw [hDiv n hn] at ht
        rw [in_traces_DIV] at ht
        exact ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_DIV] at ht
      rw [in_traces_Rep_int_choice_nat]
      exact Or.inl ht

open Classical in
theorem cspT_SKIP_DIV_Rep_int_choice_set
    {Xs : Set (Set α)} {Qf : Set α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hQ : ∀ X, X ∈ Xs → Qf X = (proc.SKIP : proc p α) ∨ Qf X = proc.DIV) :
    eqT (Rep_int_choice_set Xs Qf) M1 M2
      (if (∃ X, X ∈ Xs ∧ Qf X = (proc.SKIP : proc p α)) then (proc.SKIP : proc q α)
       else proc.DIV) := by
  by_cases hSkip : ∃ X, X ∈ Xs ∧ Qf X = (proc.SKIP : proc p α)
  · simp [hSkip]
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Rep_int_choice_set] at ht
      rw [in_traces_SKIP]
      rcases ht with rfl | ⟨X, hX, ht⟩
      · exact Or.inl rfl
      · rcases hQ X hX with hSkipX | hDivX
        · rw [hSkipX] at ht
          rw [in_traces_SKIP] at ht
          exact ht
        · rw [hDivX] at ht
          rw [in_traces_DIV] at ht
          exact Or.inl ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_SKIP] at ht
      rw [in_traces_Rep_int_choice_set]
      rcases ht with rfl | hTick
      · exact Or.inl rfl
      · rcases hSkip with ⟨X, hX, hSkipX⟩
        refine Or.inr ⟨X, hX, ?_⟩
        rw [hSkipX, in_traces_SKIP]
        exact Or.inr hTick
  · simp [hSkip]
    have hDiv : ∀ X, X ∈ Xs → Qf X = proc.DIV := by
      intro X hX
      rcases hQ X hX with hSkipX | hDivX
      · exact False.elim (hSkip ⟨X, hX, hSkipX⟩)
      · exact hDivX
    rw [cspT_eqT_semantics]
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Rep_int_choice_set] at ht
      rw [in_traces_DIV]
      rcases ht with rfl | ⟨X, hX, ht⟩
      · rfl
      · rw [hDiv X hX] at ht
        rw [in_traces_DIV] at ht
        exact ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_DIV] at ht
      rw [in_traces_Rep_int_choice_set]
      exact Or.inl ht

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Rep_int_choice` is
   represented by `cspT_SKIP_DIV_Rep_int_choice_sum`,
   `cspT_SKIP_DIV_Rep_int_choice_nat`, and
   `cspT_SKIP_DIV_Rep_int_choice_set`. -/
