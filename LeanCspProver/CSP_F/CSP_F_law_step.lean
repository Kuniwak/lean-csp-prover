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

axiom cspF_Ext_choice_step
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf)) M M
      (proc.Ext_pre_choice (X ∪ Y) fun x =>
        procIte (x ∈ X ∧ x ∈ Y) (Pf x |~| Qf x)
          (procIte (x ∈ X) (Pf x) (Qf x)))

/-
(*********************************************************
                    Parallel expansion
 *********************************************************)
-/

/- set 1 -/

axiom cspF_Parallel_step_set1
    {X Y Z : Set α} {Ya Za : Set (event α)} :
    Ya \ insert Tick (Ev '' X) = Za \ insert Tick (Ev '' X) →
      Ev '' Y ∩ Ya = ∅ → Ev '' Z ∩ Za = ∅ →
        Ev '' (X ∩ Y ∩ Z) ∩ (Ya ∪ Za) = ∅

/- set 2 -/

axiom cspF_Parallel_step_set2
    {X Y Z : Set α} {Ya Za : Set (event α)} :
    Ya \ insert Tick (Ev '' X) = Za \ insert Tick (Ev '' X) →
      Ev '' Y ∩ Ya = ∅ → Ev '' Z ∩ Za = ∅ →
        Ev '' (Y \ X) ∩ (Ya ∪ Za) = ∅

/- set 3 -/

axiom cspF_Parallel_step_set3
    {X Y Z : Set α} {Ya Za : Set (event α)} :
    Ya \ insert Tick (Ev '' X) = Za \ insert Tick (Ev '' X) →
      Ev '' Y ∩ Ya = ∅ → Ev '' Z ∩ Za = ∅ →
        Ev '' (Z \ X) ∩ (Ya ∪ Za) = ∅

/- set 4 -/

axiom cspF_Parallel_step_set4
    {X Y Z : Set α} {Xa : Set (event α)} :
    Ev '' ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) ∩ Xa = ∅ →
      Xa =
        (Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Y)) ∪
          ((Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Z)))

/- set 5 -/

axiom cspF_Parallel_step_set5
    {X Y Z : Set α} {Xa : Set (event α)} :
    Ev '' ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) ∩ Xa = ∅ →
      Ev '' Y ∩ ((Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Y))) = ∅ ∧
        Ev '' Z ∩ ((Xa \ insert Tick (Ev '' X)) ∪ (((Xa ∩ insert Tick (Ev '' X)) \ Ev '' Z))) = ∅

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Parallel_step
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.Ext_pre_choice Z Qf)) M M
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

axiom cspF_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Hiding (proc.Ext_pre_choice Y Pf) X) M M
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

axiom cspF_Renaming_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[r]]) M M
      (proc.Ext_pre_choice {y | ∃ x, x ∈ X ∧ (x, y) ∈ r} fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ (x, y) ∈ r} (fun x => (Pf x)[[r]]))

/-
(*********************************************************
            Sequential composition expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) ;; Q) M M
      (proc.Ext_pre_choice X (fun x => Pf x ;; Q))

/-
(*********************************************************
                    Depth_rest expansion
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Depth_rest_step
    {X : Set α} {Pf : α → proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) |. Nat.succ n) M M
      (proc.Ext_pre_choice X (fun x => (Pf x) |. n))

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
