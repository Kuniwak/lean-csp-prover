           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_basic

open Function
open SumType

noncomputable section

/-
(*********************************************************
                       ?-div
 *********************************************************)
-/

theorem cspT_input_DIV
    {A : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice A Pf) M M
      ((proc.Ext_pre_choice A (fun a => Pf a [+] (proc.DIV : proc p α))) |~|
        proc.Ext_pre_choice A (fun _ => (proc.DIV : proc p α))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_pre_choice] at ht
    rw [in_traces_Int_choice]
    rcases ht with rfl | ⟨a, s, rfl, hs, haA⟩
    · left
      rw [in_traces_Ext_pre_choice]
      exact Or.inl rfl
    · left
      rw [in_traces_Ext_pre_choice]
      have hs' :
          s :t traces ((Pf a) [+] (proc.DIV : proc p α)) M :=
        (in_traces_Ext_choice (t := s) (P := Pf a) (Q := (proc.DIV : proc p α)) (M := M)).2
          (Or.inl hs)
      exact Or.inr ⟨a, s, rfl, hs', haA⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rw [in_traces_Ext_pre_choice]
    rcases ht with ht | ht
    · rw [in_traces_Ext_pre_choice] at ht
      rcases ht with rfl | ⟨a, s, rfl, hs, haA⟩
      · exact Or.inl rfl
      · rw [in_traces_Ext_choice] at hs
        rcases hs with hs | hs
        · exact Or.inr ⟨a, s, rfl, hs, haA⟩
        · rw [in_traces_DIV] at hs
          subst s
          exact Or.inr ⟨a, <>, rfl, nilt_in_T, haA⟩
    · rw [in_traces_Ext_pre_choice] at ht
      rcases ht with rfl | ⟨a, s, rfl, hs, haA⟩
      · exact Or.inl rfl
      · rw [in_traces_DIV] at hs
        subst s
        exact Or.inr ⟨a, <>, rfl, nilt_in_T, haA⟩

/-
(*********************************************************
                    !set-!set-div
 *********************************************************)
-/

theorem cspT_Rep_int_choice_sum_set_Ext_pre_choice_DIV
    {C : sets_nats α} {Xsf : aset_anat α → Set (Set α)}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT
      (proc.Rep_int_choice C (fun c =>
        Rep_int_choice_set (Xsf c)
          (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α)))))
      M1 M2
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ c, c ∈ sumset C ∧ Xs = Xsf c})
        (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc q α)))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_sum] at ht
    rw [in_traces_Rep_int_choice_set]
    rcases ht with rfl | ⟨c, hc, ht⟩
    · exact Or.inl rfl
    · rw [in_traces_Rep_int_choice_set] at ht
      rcases ht with rfl | ⟨X, hX, htX⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨X, Set.mem_sUnion.mpr ?_, ?_⟩
        · exact ⟨Xsf c, ⟨c, hc, rfl⟩, hX⟩
        · rw [in_traces_Ext_pre_choice] at htX ⊢
          rcases htX with rfl | ⟨a, s, rfl, hs, haX⟩
          · exact Or.inl rfl
          · rw [in_traces_DIV] at hs
            subst s
            exact Or.inr ⟨a, <>, rfl, (in_traces_DIV (t := <>) (M := M2)).2 rfl, haX⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_set] at ht
    rw [in_traces_Rep_int_choice_sum]
    rcases ht with rfl | ⟨X, hX, htX⟩
    · exact Or.inl rfl
    · rcases Set.mem_sUnion.mp hX with ⟨Xs, hXs, hXXs⟩
      rcases hXs with ⟨c, hc, rfl⟩
      refine Or.inr ⟨c, hc, ?_⟩
      rw [in_traces_Rep_int_choice_set]
      refine Or.inr ⟨X, hXXs, ?_⟩
      rw [in_traces_Ext_pre_choice] at htX ⊢
      rcases htX with rfl | ⟨a, s, rfl, hs, haX⟩
      · exact Or.inl rfl
      · rw [in_traces_DIV] at hs
        subst s
        exact Or.inr ⟨a, <>, rfl, (in_traces_DIV (t := <>) (M := M1)).2 rfl, haX⟩

theorem cspT_Rep_int_choice_set_set_Ext_pre_choice_DIV
    {Ys : Set (Set α)} {Xsf : Set α → Set (Set α)}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT
      (Rep_int_choice_set Ys (fun Y =>
        Rep_int_choice_set (Xsf Y)
          (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α)))))
      M1 M2
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ Y, Y ∈ Ys ∧ Xs = Xsf Y})
        (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc q α)))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_set] at ht
    rw [in_traces_Rep_int_choice_set]
    rcases ht with rfl | ⟨Y, hY, ht⟩
    · exact Or.inl rfl
    · rw [in_traces_Rep_int_choice_set] at ht
      rcases ht with rfl | ⟨X, hX, htX⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨X, Set.mem_sUnion.mpr ?_, ?_⟩
        · exact ⟨Xsf Y, ⟨Y, hY, rfl⟩, hX⟩
        · rw [in_traces_Ext_pre_choice] at htX ⊢
          rcases htX with rfl | ⟨a, s, rfl, hs, haX⟩
          · exact Or.inl rfl
          · rw [in_traces_DIV] at hs
            subst s
            exact Or.inr ⟨a, <>, rfl, (in_traces_DIV (t := <>) (M := M2)).2 rfl, haX⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_set] at ht
    rw [in_traces_Rep_int_choice_set]
    rcases ht with rfl | ⟨X, hX, htX⟩
    · exact Or.inl rfl
    · rcases Set.mem_sUnion.mp hX with ⟨Xs, hXs, hXXs⟩
      rcases hXs with ⟨Y, hY, rfl⟩
      refine Or.inr ⟨Y, hY, ?_⟩
      rw [in_traces_Rep_int_choice_set]
      refine Or.inr ⟨X, hXXs, ?_⟩
      rw [in_traces_Ext_pre_choice] at htX ⊢
      rcases htX with rfl | ⟨a, s, rfl, hs, haX⟩
      · exact Or.inl rfl
      · rw [in_traces_DIV] at hs
        subst s
        exact Or.inr ⟨a, <>, rfl, (in_traces_DIV (t := <>) (M := M1)).2 rfl, haX⟩

theorem cspT_Rep_int_choice_nat_set_Ext_pre_choice_DIV
    {N : Set Nat} {Xsf : Nat → Set (Set α)}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT
      (Rep_int_choice_nat N (fun n =>
        Rep_int_choice_set (Xsf n)
          (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α)))))
      M1 M2
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ n, n ∈ N ∧ Xs = Xsf n})
        (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc q α)))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_nat] at ht
    rw [in_traces_Rep_int_choice_set]
    rcases ht with rfl | ⟨n, hn, ht⟩
    · exact Or.inl rfl
    · rw [in_traces_Rep_int_choice_set] at ht
      rcases ht with rfl | ⟨X, hX, htX⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨X, Set.mem_sUnion.mpr ?_, ?_⟩
        · exact ⟨Xsf n, ⟨n, hn, rfl⟩, hX⟩
        · rw [in_traces_Ext_pre_choice] at htX ⊢
          rcases htX with rfl | ⟨a, s, rfl, hs, haX⟩
          · exact Or.inl rfl
          · rw [in_traces_DIV] at hs
            subst s
            exact Or.inr ⟨a, <>, rfl, (in_traces_DIV (t := <>) (M := M2)).2 rfl, haX⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_set] at ht
    rw [in_traces_Rep_int_choice_nat]
    rcases ht with rfl | ⟨X, hX, htX⟩
    · exact Or.inl rfl
    · rcases Set.mem_sUnion.mp hX with ⟨Xs, hXs, hXXs⟩
      rcases hXs with ⟨n, hn, rfl⟩
      refine Or.inr ⟨n, hn, ?_⟩
      rw [in_traces_Rep_int_choice_set]
      refine Or.inr ⟨X, hXXs, ?_⟩
      rw [in_traces_Ext_pre_choice] at htX ⊢
      rcases htX with rfl | ⟨a, s, rfl, hs, haX⟩
      · exact Or.inl rfl
      · rw [in_traces_DIV] at hs
        subst s
        exact Or.inr ⟨a, <>, rfl, (in_traces_DIV (t := <>) (M := M1)).2 rfl, haX⟩

/- The Isabelle theorem bundle `cspT_Rep_int_choice_set_Ext_pre_choice_DIV`
   is represented by `cspT_Rep_int_choice_sum_set_Ext_pre_choice_DIV`,
   `cspT_Rep_int_choice_set_set_Ext_pre_choice_DIV`, and
   `cspT_Rep_int_choice_nat_set_Ext_pre_choice_DIV`. -/

/-
(*********************************************************
                      ?-!set-<=
 *********************************************************)
-/

theorem cspT_input_Rep_int_choice_set_subset
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {Xs Ys : Set (Set α)} {M : p → domTType α}
    (hXY : Xs ⊆ Ys)
    (hYA : ∀ Y, Y ∈ Ys → ∃ X, X ∈ Xs ∧ X ⊆ Y ∧ Y ⊆ A) :
    eqT
      (((proc.Ext_pre_choice A Pf) [+] Q) |~|
        Rep_int_choice_set Xs (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α))))
      M M
      (((proc.Ext_pre_choice A Pf) [+] Q) |~|
        Rep_int_choice_set Ys
          (fun Y => proc.Ext_pre_choice Y (fun _ => (proc.DIV : proc p α)))) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ht
    · rw [in_traces_Rep_int_choice_set] at ht
      rcases ht with rfl | ⟨X, hX, htX⟩
      · right
        rw [in_traces_Rep_int_choice_set]
        exact Or.inl rfl
      · right
        rw [in_traces_Rep_int_choice_set]
        exact Or.inr ⟨X, hXY hX, htX⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht ⊢
    rcases ht with ht | ht
    · exact Or.inl ht
    · rw [in_traces_Rep_int_choice_set] at ht
      rcases ht with rfl | ⟨Y, hY, htY⟩
      · left
        rw [in_traces_Ext_choice, in_traces_Ext_pre_choice]
        exact Or.inl (Or.inl rfl)
      · rcases hYA Y hY with ⟨X, hX, hXY, hYA'⟩
        left
        rw [in_traces_Ext_choice, in_traces_Ext_pre_choice]
        rw [in_traces_Ext_pre_choice] at htY
        rcases htY with rfl | ⟨a, s, rfl, hs, haY⟩
        · exact Or.inl (Or.inl rfl)
        · rw [in_traces_DIV] at hs
          subst s
          exact Or.inl (Or.inr ⟨a, <>, rfl, nilt_in_T, hYA' haY⟩)

/- The Isabelle theorem bundle `cspT_norm` is represented by
   `cspT_input_DIV`, `cspT_Rep_int_choice_sum_set_Ext_pre_choice_DIV`,
   `cspT_Rep_int_choice_set_set_Ext_pre_choice_DIV`,
   `cspT_Rep_int_choice_nat_set_Ext_pre_choice_DIV`, and
   `cspT_input_Rep_int_choice_set_subset`. -/
