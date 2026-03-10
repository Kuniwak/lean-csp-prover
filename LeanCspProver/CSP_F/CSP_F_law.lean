           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_SKIP
import LeanCspProver.CSP_F.CSP_F_law_ref
import LeanCspProver.CSP_F.CSP_F_law_dist
import LeanCspProver.CSP_F.CSP_F_law_alpha_par
import LeanCspProver.CSP_F.CSP_F_law_step
import LeanCspProver.CSP_F.CSP_F_law_rep_par
import LeanCspProver.CSP_F.CSP_F_law_fix
import LeanCspProver.CSP_F.CSP_F_law_DIV
import LeanCspProver.CSP_F.CSP_F_law_SKIP_DIV
import LeanCspProver.CSP_F.CSP_F_law_step_ext
import LeanCspProver.CSP_F.CSP_F_law_norm
import LeanCspProver.CSP_T.CSP_T_law

open Function
open SumType

noncomputable section

/-
(*********************************************************
            SKIP , DIV  and Internal choice
 *********************************************************)
-/

/- (*** |~| ***) -/

open Classical in
theorem cspF_SKIP_DIV_Int_choice
    {P Q : proc p α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : P = (proc.SKIP : proc p α) ∨ P = proc.DIV)
    (hQ : Q = (proc.SKIP : proc p α) ∨ Q = proc.DIV) :
    eqF (P |~| Q) M1 M2
      (if (P = (proc.SKIP : proc p α) ∨ Q = proc.SKIP) then (proc.SKIP : proc q α) else proc.DIV) := by
  rcases hP with rfl | rfl <;> rcases hQ with rfl | rfl
  · simp
    exact cspF_trans_left_eq cspF_Int_choice_idem cspF_reflex_eq_SKIP
  · simp
    exact cspF_trans_left_eq cspF_Int_choice_unit_r cspF_reflex_eq_SKIP
  · simp
    exact cspF_trans_left_eq cspF_Int_choice_unit_l cspF_reflex_eq_SKIP
  · simp
    exact cspF_trans_left_eq cspF_Int_choice_idem cspF_reflex_eq_DIV

/- (*** !! ***) -/

open Classical in
theorem cspF_SKIP_DIV_Rep_int_choice_sum
    {C : sets_nats α} {Qf : aset_anat α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hQ : ∀ c, c ∈ sumset C → Qf c = (proc.SKIP : proc p α) ∨ Qf c = proc.DIV) :
    eqF (proc.Rep_int_choice C Qf) M1 M2
      (if (∃ c, c ∈ sumset C ∧ Qf c = (proc.SKIP : proc p α)) then (proc.SKIP : proc q α)
       else proc.DIV) := by
  by_cases hSkip : ∃ c, c ∈ sumset C ∧ Qf c = (proc.SKIP : proc p α)
  · simp [hSkip]
    rw [cspF_cspT_eqF_semantics]
    refine ⟨?_, ?_⟩
    · simpa [hSkip] using
        (cspT_SKIP_DIV_Rep_int_choice_sum
          (M1 := fstF ∘ M1) (M2 := fstF ∘ M2) hQ)
    · apply le_antisymm
      · rw [subsetF_iff]
        intro s X hs
        rw [in_failures_Rep_int_choice_sum] at hs
        rcases hs with ⟨c, hc, hs⟩
        rcases hQ c hc with hSkipC | hDivC
        · rw [hSkipC] at hs
          rw [in_failures_SKIP] at hs ⊢
          exact hs
        · rw [hDivC] at hs
          exact False.elim ((in_failures_DIV (f := ((s, X) : failure α)) (M := M1)) hs)
      · rw [subsetF_iff]
        intro s X hs
        rcases hSkip with ⟨c, hc, hSkipC⟩
        rw [in_failures_Rep_int_choice_sum]
        refine ⟨c, hc, ?_⟩
        rw [hSkipC]
        rw [in_failures_SKIP] at hs ⊢
        exact hs
  · simp [hSkip]
    have hDiv : ∀ c, c ∈ sumset C → Qf c = proc.DIV := by
      intro c hc
      rcases hQ c hc with hSkipC | hDivC
      · exact False.elim (hSkip ⟨c, hc, hSkipC⟩)
      · exact hDivC
    rw [cspF_cspT_eqF_semantics]
    refine ⟨?_, ?_⟩
    · simpa [hSkip] using
        (cspT_SKIP_DIV_Rep_int_choice_sum
          (M1 := fstF ∘ M1) (M2 := fstF ∘ M2) hQ)
    · apply le_antisymm
      · rw [subsetF_iff]
        intro s X hs
        rw [in_failures_Rep_int_choice_sum] at hs
        rcases hs with ⟨c, hc, hs⟩
        rw [hDiv c hc] at hs
        exact False.elim ((in_failures_DIV (f := ((s, X) : failure α)) (M := M1)) hs)
      · rw [subsetF_iff]
        intro s X hs
        exact False.elim ((in_failures_DIV (f := ((s, X) : failure α)) (M := M2)) hs)

open Classical in
theorem cspF_SKIP_DIV_Rep_int_choice_nat
    {N : Set Nat} {Qf : Nat → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hQ : ∀ n, n ∈ N → Qf n = (proc.SKIP : proc p α) ∨ Qf n = proc.DIV) :
    eqF (Rep_int_choice_nat N Qf) M1 M2
      (if (∃ n, n ∈ N ∧ Qf n = (proc.SKIP : proc p α)) then (proc.SKIP : proc q α)
       else proc.DIV) := by
  by_cases hSkip : ∃ n, n ∈ N ∧ Qf n = (proc.SKIP : proc p α)
  · simp [hSkip]
    rw [cspF_cspT_eqF_semantics]
    refine ⟨?_, ?_⟩
    · simpa [hSkip] using
        (cspT_SKIP_DIV_Rep_int_choice_nat
          (M1 := fstF ∘ M1) (M2 := fstF ∘ M2) hQ)
    · apply le_antisymm
      · rw [subsetF_iff]
        intro s X hs
        rw [in_failures_Rep_int_choice_nat] at hs
        rcases hs with ⟨n, hn, hs⟩
        rcases hQ n hn with hSkipN | hDivN
        · rw [hSkipN] at hs
          rw [in_failures_SKIP] at hs ⊢
          exact hs
        · rw [hDivN] at hs
          exact False.elim ((in_failures_DIV (f := ((s, X) : failure α)) (M := M1)) hs)
      · rw [subsetF_iff]
        intro s X hs
        rcases hSkip with ⟨n, hn, hSkipN⟩
        rw [in_failures_Rep_int_choice_nat]
        refine ⟨n, hn, ?_⟩
        rw [hSkipN]
        rw [in_failures_SKIP] at hs ⊢
        exact hs
  · simp [hSkip]
    have hDiv : ∀ n, n ∈ N → Qf n = proc.DIV := by
      intro n hn
      rcases hQ n hn with hSkipN | hDivN
      · exact False.elim (hSkip ⟨n, hn, hSkipN⟩)
      · exact hDivN
    rw [cspF_cspT_eqF_semantics]
    refine ⟨?_, ?_⟩
    · simpa [hSkip] using
        (cspT_SKIP_DIV_Rep_int_choice_nat
          (M1 := fstF ∘ M1) (M2 := fstF ∘ M2) hQ)
    · apply le_antisymm
      · rw [subsetF_iff]
        intro s X hs
        rw [in_failures_Rep_int_choice_nat] at hs
        rcases hs with ⟨n, hn, hs⟩
        rw [hDiv n hn] at hs
        exact False.elim ((in_failures_DIV (f := ((s, X) : failure α)) (M := M1)) hs)
      · rw [subsetF_iff]
        intro s X hs
        exact False.elim ((in_failures_DIV (f := ((s, X) : failure α)) (M := M2)) hs)

open Classical in
theorem cspF_SKIP_DIV_Rep_int_choice_set
    {Xs : Set (Set α)} {Qf : Set α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hQ : ∀ X, X ∈ Xs → Qf X = (proc.SKIP : proc p α) ∨ Qf X = proc.DIV) :
    eqF (Rep_int_choice_set Xs Qf) M1 M2
      (if (∃ X, X ∈ Xs ∧ Qf X = (proc.SKIP : proc p α)) then (proc.SKIP : proc q α)
       else proc.DIV) := by
  by_cases hSkip : ∃ X, X ∈ Xs ∧ Qf X = (proc.SKIP : proc p α)
  · simp [hSkip]
    rw [cspF_cspT_eqF_semantics]
    refine ⟨?_, ?_⟩
    · simpa [hSkip] using
        (cspT_SKIP_DIV_Rep_int_choice_set
          (M1 := fstF ∘ M1) (M2 := fstF ∘ M2) hQ)
    · apply le_antisymm
      · rw [subsetF_iff]
        intro s Y hs
        rw [in_failures_Rep_int_choice_set] at hs
        rcases hs with ⟨X, hX, hs⟩
        rcases hQ X hX with hSkipX | hDivX
        · rw [hSkipX] at hs
          rw [in_failures_SKIP] at hs ⊢
          exact hs
        · rw [hDivX] at hs
          exact False.elim ((in_failures_DIV (f := ((s, Y) : failure α)) (M := M1)) hs)
      · rw [subsetF_iff]
        intro s Y hs
        rcases hSkip with ⟨X, hX, hSkipX⟩
        rw [in_failures_Rep_int_choice_set]
        refine ⟨X, hX, ?_⟩
        rw [hSkipX]
        rw [in_failures_SKIP] at hs ⊢
        exact hs
  · simp [hSkip]
    have hDiv : ∀ X, X ∈ Xs → Qf X = proc.DIV := by
      intro X hX
      rcases hQ X hX with hSkipX | hDivX
      · exact False.elim (hSkip ⟨X, hX, hSkipX⟩)
      · exact hDivX
    rw [cspF_cspT_eqF_semantics]
    refine ⟨?_, ?_⟩
    · simpa [hSkip] using
        (cspT_SKIP_DIV_Rep_int_choice_set
          (M1 := fstF ∘ M1) (M2 := fstF ∘ M2) hQ)
    · apply le_antisymm
      · rw [subsetF_iff]
        intro s Y hs
        rw [in_failures_Rep_int_choice_set] at hs
        rcases hs with ⟨X, hX, hs⟩
        rw [hDiv X hX] at hs
        exact False.elim ((in_failures_DIV (f := ((s, Y) : failure α)) (M := M1)) hs)
      · rw [subsetF_iff]
        intro s Y hs
        exact False.elim ((in_failures_DIV (f := ((s, Y) : failure α)) (M := M2)) hs)

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Rep_int_choice` is
   represented by `cspF_SKIP_DIV_Rep_int_choice_sum`,
   `cspF_SKIP_DIV_Rep_int_choice_nat`, and
   `cspF_SKIP_DIV_Rep_int_choice_set`. -/

end
