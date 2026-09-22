           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_nf_def

open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {p : Type u} {α : Type v}

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion` and `Set.sInter`.     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`                 -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there is -/
/-  nothing to disable or re-enable here.                              -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`      -/
/- Isabelle 2017: `split_if --> if_split`                              -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is  -/
/-  nothing to disable or re-enable here.                              -/

/-
(*****************************************************************

         1. full sequentialisation for Rep_int_choice
         2.
         3.

 *****************************************************************)
-/

/- (*============================================================*
 |                                                            |
 |                    Rep_int_choice                          |
 |                                                            |
 *============================================================*) -/

private def fnfF_Rep_int_choice_step_A
    (X : sets_nats α) (Af : aset_anat α → Set α) : Set α :=
  Set.sUnion {A | ∃ x, x ∈ sumset X ∧ A = Af x}

private def fnfF_Rep_int_choice_step_Ys
    (X : sets_nats α) (Ysf : aset_anat α → Set (Set α)) : Set (Set α) :=
  Set.sUnion {Ys | ∃ x, x ∈ sumset X ∧ Ys = Ysf x}

def fnfF_Rep_int_choice_step
    (X : sets_nats α)
    (Af : aset_anat α → Set α)
    (Ysf : aset_anat α → Set (Set α))
    (Pf : α → proc p α)
    (Qf : aset_anat α → proc p α) : proc p α :=
  (((proc.Ext_pre_choice (fnfF_Rep_int_choice_step_A X Af) Pf) [+]
      (if ∃ x, x ∈ sumset X ∧ Qf x = proc.SKIP then proc.SKIP else proc.DIV)) |~|
    Rep_int_choice_set
      (fnfF_set_completion
        (fnfF_Rep_int_choice_step_A X Af)
        (fnfF_Rep_int_choice_step_Ys X Ysf))
      (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))

theorem fnfF_Rep_int_choice_step_def
    (X : sets_nats α)
    (Af : aset_anat α → Set α)
    (Ysf : aset_anat α → Set (Set α))
    (Pf : α → proc p α)
    (Qf : aset_anat α → proc p α) :
    fnfF_Rep_int_choice_step X Af Ysf Pf Qf =
      (((proc.Ext_pre_choice (Set.sUnion {A | ∃ x, x ∈ sumset X ∧ A = Af x}) Pf) [+]
          (if ∃ x, x ∈ sumset X ∧ Qf x = proc.SKIP then proc.SKIP else proc.DIV)) |~|
        Rep_int_choice_set
          (fnfF_set_completion
            (Set.sUnion {A | ∃ x, x ∈ sumset X ∧ A = Af x})
            (Set.sUnion {Ys | ∃ x, x ∈ sumset X ∧ Ys = Ysf x}))
          (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))) :=
  rfl

def fnfF_Rep_int_choice :
    Nat → sets_nats α → (aset_anat α → proc p α) → proc p α
  | 0, _, _ => NDIV
  | Nat.succ n, C, SPf =>
      if _h : ∀ c, c ∈ sumset C → fnfF_proc (SPf c) then
        fnfF_Rep_int_choice_step C
          (fun c => fnfF_A (SPf c))
          (fun c => fnfF_Ys (SPf c))
          (fun a =>
            if a ∈ Set.sUnion {A | ∃ c, c ∈ sumset C ∧ A = fnfF_A (SPf c)} then
              fnfF_Rep_int_choice n
                (sub_sumset C fun c => a ∈ fnfF_A (SPf c))
                (fun c => fnfF_Pf (SPf c) a)
            else
              proc.DIV)
          (fun c => fnfF_Q (SPf c))
      else
        (proc.Rep_int_choice C SPf) |. Nat.succ n

@[simp]
theorem fnfF_Rep_int_choice_zero
    (C : sets_nats α) (SPf : aset_anat α → proc p α) :
    fnfF_Rep_int_choice 0 C SPf = NDIV :=
  rfl

@[simp]
theorem fnfF_Rep_int_choice_succ
    (n : Nat) (C : sets_nats α) (SPf : aset_anat α → proc p α) :
    fnfF_Rep_int_choice (Nat.succ n) C SPf =
      if _h : ∀ c, c ∈ sumset C → fnfF_proc (SPf c) then
        fnfF_Rep_int_choice_step C
          (fun c => fnfF_A (SPf c))
          (fun c => fnfF_Ys (SPf c))
          (fun a =>
            if a ∈ Set.sUnion {A | ∃ c, c ∈ sumset C ∧ A = fnfF_A (SPf c)} then
              fnfF_Rep_int_choice n
                (sub_sumset C fun c => a ∈ fnfF_A (SPf c))
                (fun c => fnfF_Pf (SPf c) a)
            else
              proc.DIV)
          (fun c => fnfF_Q (SPf c))
      else
        (proc.Rep_int_choice C SPf) |. Nat.succ n :=
  by
    simp [fnfF_Rep_int_choice]

/- Lean note:
   Isabelle's syntax/translations for `!! :C ..[n] SPf` and
   `!! c:C ..[n] P` are represented directly by `fnfF_Rep_int_choice`. -/

/- (*===========================================================*
 |                      in fnfF_rest                         |
 *===========================================================*) -/

/-- The union of all `Ysf`-families is below the union of all `Af`-families,
    provided each `Ysf c` is below `Af c`. -/
private theorem step_Ys_Union_subset_A
    {C : sets_nats α} {Af : aset_anat α → Set α} {Ysf : aset_anat α → Set (Set α)}
    (hUn : ∀ c, c ∈ sumset C → Set.sUnion (Ysf c) ⊆ Af c) :
    Set.sUnion (Set.sUnion {Ys | ∃ c, c ∈ sumset C ∧ Ys = Ysf c}) ⊆
      Set.sUnion {A | ∃ c, c ∈ sumset C ∧ A = Af c} := by
  rintro x ⟨Y, ⟨Ys0, ⟨c, hc, rfl⟩, hY⟩, hxY⟩
  exact ⟨Af c, ⟨c, hc, rfl⟩, hUn c hc ⟨Y, hY, hxY⟩⟩

theorem fnfF_Rep_int_choice_in_lm
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → fnfF_proc (SPf c)) →
      fnfF_proc (fnfF_Rep_int_choice n C SPf) := by
  induction n generalizing C SPf with
  | zero =>
      intro _
      exact fnfF_NDIV
  | succ n ih =>
      intro h
      rw [fnfF_Rep_int_choice_succ, dif_pos h]
      unfold fnfF_Rep_int_choice_step fnfF_Rep_int_choice_step_A fnfF_Rep_int_choice_step_Ys
      refine fnfF_proc.fnfF_proc_rule ?_ ?_ fnfF_set_completion_sat_condition ?_ ?_
      · -- a ∈ ⋃₀ {A | ...} : the recursive call is in `fnfF_proc`
        intro a ha
        rw [if_pos ha]
        refine ih ?_
        intro c hc
        rw [sumset_sub_sumset] at hc
        exact fnfF_Pf_A (h c hc.1) hc.2
      · -- a ∉ ⋃₀ {A | ...} : `DIV`
        intro a ha
        rw [if_neg ha]
      · -- ⋃₀ (completion) ⊆ ⋃₀ {A | ...}
        refine fnfF_set_completion_Union_subset ?_
        exact step_Ys_Union_subset_A (fun c hc => fnfF_Union_Ys_A (h c hc))
      · -- the `if`-term is `SKIP` or `DIV`
        by_cases hex : ∃ c, c ∈ sumset C ∧ fnfF_Q (SPf c) = proc.SKIP
        · rw [if_pos hex]
          exact Or.inl rfl
        · rw [if_neg hex]
          exact Or.inr rfl

/- (*------------------------------------*
 |                 in                 |
 *------------------------------------*) -/

theorem fnfF_Rep_int_choice_in
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → fnfF_proc (SPf c)) →
      fnfF_proc (fnfF_Rep_int_choice n C SPf) :=
  fnfF_Rep_int_choice_in_lm

/- (*------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------*) -/
/- (*-----------------------------------------*
 |    convenient lemma for subexpresions   |
 *-----------------------------------------*) -/

theorem fnfF_Rep_int_choice_step_subexp
    [HasPNfun p α] [HasFPmode]
    {C : sets_nats α}
    {Af1 Af2 : aset_anat α → Set α}
    {Ysf1 Ysf2 : aset_anat α → Set (Set α)}
    {Pf1 Pf2 : α → proc p α}
    {Qf1 Qf2 : aset_anat α → proc p α} :
    (∀ a,
        a ∈ Set.sUnion {A | ∃ c, c ∈ sumset C ∧ A = Af2 c} →
          eqFfix (Pf1 a) (Pf2 a)) →
      (∀ c, c ∈ sumset C → Af1 c = Af2 c) →
        (∀ c, c ∈ sumset C → Ysf1 c = Ysf2 c) →
          (∀ c, c ∈ sumset C → Qf1 c = Qf2 c) →
            (∀ c, c ∈ sumset C → Set.sUnion (Ysf2 c) ⊆ Af2 c) →
              eqFfix
                (fnfF_Rep_int_choice_step C Af1 Ysf1 Pf1 Qf1)
                (fnfF_Rep_int_choice_step C Af2 Ysf2 Pf2 Qf2) := by
  intro hP hA hYs hQ _
  have hAset : fnfF_Rep_int_choice_step_A C Af1 = fnfF_Rep_int_choice_step_A C Af2 := by
    unfold fnfF_Rep_int_choice_step_A
    congr 1
    ext A
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, hA c hc⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (hA c hc).symm⟩
  have hYset : fnfF_Rep_int_choice_step_Ys C Ysf1 = fnfF_Rep_int_choice_step_Ys C Ysf2 := by
    unfold fnfF_Rep_int_choice_step_Ys
    congr 1
    ext Ys
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, hYs c hc⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, (hYs c hc).symm⟩
  have hQprop :
      (∃ x, x ∈ sumset C ∧ Qf1 x = proc.SKIP) ↔ (∃ x, x ∈ sumset C ∧ Qf2 x = proc.SKIP) := by
    constructor
    · rintro ⟨x, hx, h⟩
      exact ⟨x, hx, (hQ x hx) ▸ h⟩
    · rintro ⟨x, hx, h⟩
      exact ⟨x, hx, (hQ x hx).symm ▸ h⟩
  unfold fnfF_Rep_int_choice_step
  rw [hAset, hYset]
  simp only [hQprop]
  refine cspF_Int_choice_cong (cspF_Ext_choice_cong ?_ cspF_reflex_eq_P) cspF_reflex_eq_P
  exact cspF_Ext_pre_choice_cong rfl (fun a ha => hP a ha)

/- (*------------------------------------*
 |         one step equality          |
 *------------------------------------*) -/

set_option maxHeartbeats 1000000 in
-- The chain rewrites a replicated internal choice through four distribution
-- laws in a row, each of which carries the whole indexed family along.
theorem cspF_fnfF_Rep_int_choice_one_step
    [HasPNfun p α] [HasFPmode]
    {C : sets_nats α}
    {Af : aset_anat α → Set α}
    {Ysf : aset_anat α → Set (Set α)}
    {Pff : aset_anat α → α → proc p α}
    {Qf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → Set.sUnion (Ysf c) ⊆ Af c) →
      (∀ c, c ∈ sumset C → Qf c = proc.SKIP ∨ Qf c = proc.DIV) →
        eqFfix
          (proc.Rep_int_choice C
            (fun c =>
              (((proc.Ext_pre_choice (Af c) (Pff c)) [+] Qf c) |~|
                Rep_int_choice_set (Ysf c)
                  (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))))
          (fnfF_Rep_int_choice_step C Af Ysf
            (fun a => proc.Rep_int_choice (sub_sumset C fun c => a ∈ Af c) (fun c => Pff c a))
            Qf) := by
  intro hYA hQ
  -- push the internal choice inside
  refine cspF_trans_left_eq (cspF_Rep_int_choice_sum_dist) ?_
  refine cspF_trans_left_eq
    (cspF_Int_choice_cong (cspF_Rep_int_choice_Ext_Dist_sum hQ)
      cspF_Rep_int_choice_sum_set_Ext_pre_choice_DIV) ?_
  -- merge the prefix choices and collapse the terminal part
  refine cspF_trans_left_eq
    (cspF_Int_choice_cong
      (cspF_Ext_choice_cong cspF_Rep_int_choice_sum_input_set
        (cspF_SKIP_DIV_Rep_int_choice_sum hQ))
      cspF_reflex_eq_P) ?_
  -- distribute the merged prefix choice over the terminal part
  refine cspF_trans_left_eq
    (cspF_Int_choice_cong
      (cspF_Rep_int_choice_input_Dist
        (by by_cases h : ∃ c, c ∈ sumset C ∧ Qf c = proc.SKIP
            · rw [if_pos h]; exact Or.inl rfl
            · rw [if_neg h]; exact Or.inr rfl))
      cspF_reflex_eq_P) ?_
  -- the merged prefix set is exactly the one `fnfF_Rep_int_choice_step` uses
  have hUnion : Set.sUnion (Af '' sumset C)
      = Set.sUnion {A | ∃ x, x ∈ sumset C ∧ A = Af x} := by
    congr 1
    ext A
    exact ⟨fun ⟨c, hc, hA⟩ => ⟨c, hc, hA.symm⟩, fun ⟨c, hc, hA⟩ => ⟨c, hc, hA.symm⟩⟩
  unfold fnfF_Rep_int_choice_step
  rw [hUnion]
  -- finally enlarge the refusal sets to the completion
  refine cspF_input_Rep_int_choice_set_subset fnfF_set_completion_subset (fun Y hY => ?_)
  obtain ⟨⟨Y0, hY0, hY0Y⟩, hYsub⟩ := hY
  refine ⟨Y0, hY0, hY0Y, ?_⟩
  intro x hx
  rcases hYsub hx with hA | hYs
  · exact hA
  · exact step_Ys_Union_subset_A hYA hYs

/- (*------------------------------------*
 |              induction             |
 *------------------------------------*) -/

axiom cspF_fnfF_Rep_int_choice_eqF_lm
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    eqFfix ((proc.Rep_int_choice C SPf) |. n) (fnfF_Rep_int_choice n C SPf)

/- (*------------------------------------*
 |                 eqF                |
 *------------------------------------*) -/

theorem cspF_fnfF_Rep_int_choice_eqF
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    eqFfix ((proc.Rep_int_choice C SPf) |. n) (fnfF_Rep_int_choice n C SPf) :=
  cspF_fnfF_Rep_int_choice_eqF_lm

/- (*------------------------*
 |     auxiliary laws     |
 *------------------------*) -/

theorem cspF_fnfF_Rep_int_choice_Depth_rest
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    eqFfix ((fnfF_Rep_int_choice n C SPf) |. n) (fnfF_Rep_int_choice n C SPf) := by
  refine cspF_trans_left_eq
    (cspF_Depth_rest_cong rfl (cspF_sym (cspF_fnfF_Rep_int_choice_eqF
      (n := n) (C := C) (SPf := SPf)))) ?_
  refine cspF_trans_left_eq cspF_Depth_rest_min ?_
  rw [Nat.min_self]
  exact cspF_fnfF_Rep_int_choice_eqF

end
