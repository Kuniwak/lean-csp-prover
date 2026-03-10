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

axiom fnfF_Rep_int_choice_in_lm
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → fnfF_proc (SPf c)) →
      fnfF_proc (fnfF_Rep_int_choice n C SPf)

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

axiom fnfF_Rep_int_choice_step_subexp
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
                (fnfF_Rep_int_choice_step C Af2 Ysf2 Pf2 Qf2)

/- (*------------------------------------*
 |         one step equality          |
 *------------------------------------*) -/

axiom cspF_fnfF_Rep_int_choice_one_step
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
            Qf)

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

axiom cspF_fnfF_Rep_int_choice_Depth_rest
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    eqFfix ((fnfF_Rep_int_choice n C SPf) |. n) (fnfF_Rep_int_choice n C SPf)

end
