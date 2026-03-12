           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               January 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
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

         1. full sequentialization for Ext_choice
         2. full sequentialization for Timeout
         2.
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                        Ext_choice                          |
 |                                                            |
 *============================================================* -/

def Pfun_Ext_choice : proc p α → proc p α → proc p α :=
  fun P1 P2 => P1 [+] P2

theorem Pfun_Ext_choice_def :
    Pfun_Ext_choice (p := p) (α := α) =
      (fun P1 P2 => P1 [+] P2) :=
  rfl

def SP_step_Ext_choice :
    Set α → (α → proc p α) → proc p α →
      Set α → (α → proc p α) → proc p α →
      (α → proc p α) → (α → proc p α) → (α → proc p α) →
      proc p α :=
  fun A1 Pf1 Q1 A2 Pf2 Q2 _SPf _SPf1 _SPf2 =>
    (proc.Ext_pre_choice (A1 ∪ A2) fun a =>
      if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (Pf1 a) (Pf2 a)
      else if a ∈ A1 then Pf1 a else Pf2 a) [+]
    (if Q1 = proc.STOP then Q2
     else if Q2 = proc.STOP then Q1
     else if (Q1 = proc.SKIP ∨ Q2 = proc.SKIP) then proc.SKIP else proc.DIV)

theorem SP_step_Ext_choice_def :
    SP_step_Ext_choice (p := p) (α := α) =
      (fun A1 Pf1 Q1 A2 Pf2 Q2 _SPf _SPf1 _SPf2 =>
        (proc.Ext_pre_choice (A1 ∪ A2) fun a =>
          if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (Pf1 a) (Pf2 a)
          else if a ∈ A1 then Pf1 a else Pf2 a) [+]
        (if Q1 = proc.STOP then Q2
         else if Q2 = proc.STOP then Q1
         else if (Q1 = proc.SKIP ∨ Q2 = proc.SKIP) then proc.SKIP else proc.DIV)) :=
  rfl

def fsfF_Ext_choice (P1 P2 : proc p α) : proc p α :=
  fsfF_induct2 Pfun_Ext_choice SP_step_Ext_choice P1 P2

theorem fsfF_Ext_choice_def
    (P1 P2 : proc p α) :
    fsfF_Ext_choice (p := p) (α := α) P1 P2 =
      fsfF_induct2 Pfun_Ext_choice SP_step_Ext_choice P1 P2 :=
  rfl

infixl:72 " [+]seq " => fsfF_Ext_choice

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Ext_choice_in
    {P1 P2 : proc p α} :
    fsfF_proc P1 →
      fsfF_proc P2 →
        fsfF_proc (P1 [+]seq P2) := by
  intro hP1 hP2
  rw [fsfF_Ext_choice_def]
  refine fsfF_induct2_in hP1 hP2 ?_
  intro A1 Pf1 Q1 A2 Pf2 Q2 _SPf _SPf1 _SPf2 hPf1 hPf2 _hSPf _hSPf1 _hSPf2 hQ1 hQ2
  refine fsfF_proc.fsfF_proc_ext ?_ ?_
  · intro a ha
    by_cases hBoth : a ∈ A1 ∧ a ∈ A2
    · simpa [hBoth] using fsfF_Int_choice_in (hPf1 a hBoth.1) (hPf2 a hBoth.2)
    · by_cases hA1 : a ∈ A1
      · have hA2 : a ∉ A2 := by
          intro hA2
          exact hBoth ⟨hA1, hA2⟩
        simpa [hA1, hA2] using hPf1 a hA1
      · have hA2 : a ∈ A2 := by
          rcases ha with hA1' | hA2
          · exact False.elim (hA1 hA1')
          · exact hA2
        simpa [hA1, hA2] using hPf2 a hA2
  · rcases hQ1 with rfl | rfl | rfl <;> rcases hQ2 with rfl | rfl | rfl <;>
      simp

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fsfF_Ext_choice_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    eqFfix (P1 [+] P2) (P1 [+]seq P2)

/- *--------------------------------------------------*
 |                                                  |
 |  The equality `cspF_fsfF_Ext_choice_eqF` can be  |
 |  proven by using tactics as follows:             |
 |                                                  |
 *--------------------------------------------------* -/

/- Lean note:
   The original Isabelle file includes a tactic-script proof here. The
   theorem is kept with the same statement, while the proof is introduced
   separately in Lean. -/

/- *============================================================*
 |                                                            |
 |                         Timeout                            |
 |                                                            |
 *============================================================* -/

def fsfF_Timeout
    (P1 P2 : proc p α) : proc p α :=
  (fsfF_Int_choice P1 SSTOP) [+]seq P2

theorem fsfF_Timeout_def
    (P1 P2 : proc p α) :
    fsfF_Timeout (p := p) (α := α) P1 P2 =
      (fsfF_Int_choice P1 SSTOP) [+]seq P2 :=
  rfl

infixl:73 " [>seq " => fsfF_Timeout

/- *------------------------------------*
 |                 in                 |
 *------------------------------------* -/

theorem fsfF_Timeout_in
    {P1 P2 : proc p α} :
    fsfF_proc P1 →
      fsfF_proc P2 →
        fsfF_proc (P1 [>seq P2) := by
  intro hP1 hP2
  rw [fsfF_Timeout_def]
  exact fsfF_Ext_choice_in (fsfF_Int_choice_in hP1 fsfF_SSTOP_in) hP2

/- *------------------------------------*
 |                 eqF                |
 *------------------------------------* -/

theorem cspF_fsfF_Timeout_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    eqFfix (P1 [> P2) (P1 [>seq P2) := by
  have hIntStop : eqFfix (P1 |~| (proc.STOP : proc p α)) (P1 |~| SSTOP) := by
    exact cspF_Int_choice_cong cspF_reflex_eq_P cspF_SSTOP_eqF
  have hIntSeq : eqFfix (P1 |~| SSTOP) (fsfF_Int_choice P1 SSTOP) := by
    exact cspF_fsfF_Int_choice_eqF
  have hInt : eqFfix (P1 |~| (proc.STOP : proc p α)) (fsfF_Int_choice P1 SSTOP) := by
    exact cspF_trans_left_eq hIntStop hIntSeq
  have hExt :
      eqFfix (((P1 |~| (proc.STOP : proc p α)) [+] P2))
        (((fsfF_Int_choice P1 SSTOP) [+]seq P2)) := by
    exact cspF_trans_left_eq
      (cspF_Ext_choice_cong hInt cspF_reflex_eq_P)
      cspF_fsfF_Ext_choice_eqF
  simpa [Timeout_abb, fsfF_Timeout_def] using hExt

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
