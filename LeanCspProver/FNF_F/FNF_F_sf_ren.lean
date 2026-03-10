           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_induct

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

         1. full sequentialization for Renaming (P [[r]])
         2.
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                    Renaming P [[r]]                        |
 |                                                            |
 *============================================================* -/

def Pfun_Renaming (r : Set (α × α)) : proc p α → proc p α :=
  fun P1 => P1 [[r]]

theorem Pfun_Renaming_def
    (r : Set (α × α)) :
    Pfun_Renaming (p := p) (α := α) r =
      (fun P1 => P1 [[r]]) :=
  rfl

def SP_step_Renaming [Inhabited α]
    (r : Set (α × α)) :
    Set α → (α → proc p α) → proc p α →
      (α → proc p α) → proc p α :=
  fun Y1 _Pf1 Q1 SPf =>
    (proc.Ext_pre_choice {y | ∃ x, x ∈ Y1 ∧ (x, y) ∈ r} fun y =>
      fsfF_Rep_int_choice_com {x | x ∈ Y1 ∧ (x, y) ∈ r} SPf) [+] Q1

theorem SP_step_Renaming_def [Inhabited α]
    (r : Set (α × α)) :
    SP_step_Renaming (p := p) (α := α) r =
      (fun Y1 _Pf1 Q1 SPf =>
        (proc.Ext_pre_choice {y | ∃ x, x ∈ Y1 ∧ (x, y) ∈ r} fun y =>
          fsfF_Rep_int_choice_com {x | x ∈ Y1 ∧ (x, y) ∈ r} SPf) [+] Q1) :=
  rfl

def fsfF_Renaming [Inhabited α]
    (P1 : proc p α) (r : Set (α × α)) : proc p α :=
  fsfF_induct1 (Pfun_Renaming r) (SP_step_Renaming r) P1

theorem fsfF_Renaming_def [Inhabited α]
    (P1 : proc p α) (r : Set (α × α)) :
    fsfF_Renaming (p := p) (α := α) P1 r =
      fsfF_induct1 (Pfun_Renaming r) (SP_step_Renaming r) P1 :=
  rfl

notation:84 P " [[" r "]]seq" => fsfF_Renaming P r

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Renaming_in [Inhabited α]
    {P1 : proc p α} {r : Set (α × α)} :
    fsfF_proc P1 →
      fsfF_proc (P1 [[r]]seq) := by
  intro hP1
  rw [fsfF_Renaming_def]
  refine fsfF_induct1_in hP1 ?_
  intro Y1 Pf1 Q1 SPf _hPf1 hSPf hQ1
  refine fsfF_proc.fsfF_proc_ext ?_ hQ1
  intro y hy
  apply fsfF_Rep_int_choice_com_in
  intro x hx
  exact hSPf x hx.1

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fsfF_Renaming_eqF [Inhabited α]
    [HasPNfun p α] [HasFPmode]
    {P1 : proc p α} {r : Set (α × α)} :
    eqFfix (P1 [[r]]) (P1 [[r]]seq) := by
  rw [fsfF_Renaming_def]
  refine cspF_fsfF_induct1_eqF
    (Pfun := Pfun_Renaming r)
    (SP_step := SP_step_Renaming r)
    (P1 := P1) ?_ ?_ ?_
  · intro C1 Rf1 hC1
    simpa [Pfun_Renaming_def] using
      (cspF_Renaming_Dist_sum (C := C1) (Pf := Rf1) (r := r) (M := MF))
  · intro Y1 Pf1 Q1 hQ1
    let Y2 : Set α := {y | ∃ x, x ∈ Y1 ∧ (x, y) ∈ r}
    let RPf : α → proc p α :=
      fun y => Rep_int_choice_com {x | x ∈ Y1 ∧ (x, y) ∈ r} (fun x => (Pf1 x) [[r]])
    let SPf : α → proc p α :=
      fun y => fsfF_Rep_int_choice_com {x | x ∈ Y1 ∧ (x, y) ∈ r} (fun x => (Pf1 x) [[r]])
    have hDist :
        eqFfix ((((proc.Ext_pre_choice Y1 Pf1) [+] Q1) [[r]]))
          ((((proc.Ext_pre_choice Y1 Pf1) [[r]]) [+] (Q1 [[r]]))) := by
      simpa using
        (cspF_Renaming_Ext_dist
          (P1 := proc.Ext_pre_choice Y1 Pf1)
          (P2 := Q1)
          (r := r)
          (M := MF))
    have hStep :
        eqFfix ((((proc.Ext_pre_choice Y1 Pf1) [[r]]) [+] (Q1 [[r]])))
          (((proc.Ext_pre_choice Y2 RPf) [+] (Q1 [[r]]))) := by
      exact cspF_Ext_choice_cong
        (cspF_Renaming_step (X := Y1) (Pf := Pf1) (r := r) (M := MF))
        cspF_reflex_eq_P
    have hRep :
        eqFfix (proc.Ext_pre_choice Y2 RPf) (proc.Ext_pre_choice Y2 SPf) := by
      refine cspF_Ext_pre_choice_cong rfl ?_
      intro y hy
      let Xy : Set α := {x | x ∈ Y1 ∧ (x, y) ∈ r}
      change eqFfix (Rep_int_choice_com Xy (fun x => (Pf1 x) [[r]]))
        (fsfF_Rep_int_choice_com Xy (fun x => (Pf1 x) [[r]]))
      exact cspF_fsfF_Rep_int_choice_com_eqF
    have hStepSeq :
        eqFfix ((proc.Ext_pre_choice Y2 RPf) [+] (Q1 [[r]]))
          ((proc.Ext_pre_choice Y2 SPf) [+] (Q1 [[r]])) := by
      exact cspF_Ext_choice_cong hRep cspF_reflex_eq_P
    have hQ :
        eqFfix ((proc.Ext_pre_choice Y2 SPf) [+] (Q1 [[r]]))
          ((proc.Ext_pre_choice Y2 SPf) [+] Q1) := by
      exact cspF_Ext_choice_cong
        cspF_reflex_eq_P
        (cspF_SKIP_or_DIV_or_STOP_Renaming_Id
          (P := Q1)
          (r := r)
          (M := MF)
          hQ1)
    simpa [Pfun_Renaming_def, SP_step_Renaming_def, Y2, RPf, SPf] using
      (cspF_trans_left_eq hDist
        (cspF_trans_left_eq hStep
          (cspF_trans_left_eq hStepSeq hQ)))
  · intro Y1 Pf1 Q1 SPf SQf hSP
    refine cspF_Ext_choice_cong ?_ cspF_reflex_eq_P
    refine cspF_Ext_pre_choice_cong rfl ?_
    intro y hy
    let Xy : Set α := {x | x ∈ Y1 ∧ (x, y) ∈ r}
    change eqFfix (fsfF_Rep_int_choice_com Xy SPf) (fsfF_Rep_int_choice_com Xy SQf)
    have hRep :
        eqFfix (Rep_int_choice_com Xy SPf) (Rep_int_choice_com Xy SQf) := by
      exact cspF_Rep_int_choice_cong_com rfl (fun x hx => hSP x hx.1)
    exact cspF_trans_left_eq
      (cspF_sym (cspF_fsfF_Rep_int_choice_com_eqF (X := Xy) (SPf := SPf)))
      (cspF_trans_left_eq hRep
        (cspF_fsfF_Rep_int_choice_com_eqF (X := Xy) (SPf := SQf)))

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
