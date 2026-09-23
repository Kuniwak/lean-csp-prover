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

/-- Rearranging the two step bodies so the prefix choices and the terminal
    parts can be combined separately. -/
private theorem Ext_choice_regroup
    [HasPNfun p α] [HasFPmode] {X1 Q1 X2 Q2 : proc p α} :
    eqFfix ((X1 [+] Q1) [+] (X2 [+] Q2)) ((X1 [+] X2) [+] (Q1 [+] Q2)) := by
  refine cspF_trans_left_eq (cspF_Ext_choice_assoc_sym (P := X1) (Q := Q1)
    (R := X2 [+] Q2) (M := MF)) ?_
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong cspF_reflex_eq_P
      (cspF_Ext_choice_assoc (P := Q1) (Q := X2) (R := Q2) (M := MF))) ?_
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong cspF_reflex_eq_P
      (cspF_Ext_choice_cong (cspF_Ext_choice_commut (P := Q1) (Q := X2) (M := MF))
        cspF_reflex_eq_P)) ?_
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong cspF_reflex_eq_P
      (cspF_Ext_choice_assoc_sym (P := X2) (Q := Q1) (R := Q2) (M := MF))) ?_
  exact cspF_Ext_choice_assoc (P := X1) (Q := X2) (R := Q1 [+] Q2) (M := MF)

/-- Combining the two terminal parts of a step body. -/
private theorem Ext_choice_term
    [HasPNfun p α] [HasFPmode] {Q1 Q2 : proc p α}
    (hQ1 : Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP)
    (hQ2 : Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) :
    eqFfix (Q1 [+] Q2)
      (if Q1 = proc.STOP then Q2
       else if Q2 = proc.STOP then Q1
       else if (Q1 = proc.SKIP ∨ Q2 = proc.SKIP) then proc.SKIP else proc.DIV) := by
  rcases hQ1 with rfl | rfl | rfl
  · rcases hQ2 with rfl | rfl | rfl
    · simpa using (cspF_Ext_choice_idem (P := (proc.SKIP : proc p α)) (M := MF))
    · simpa using (cspF_SKIP_DIV_Ext_choice1 (p := p) (q := p) (α := α) (M1 := MF) (M2 := MF))
    · simpa using (cspF_Ext_choice_unit_r (P := (proc.SKIP : proc p α)) (M := MF))
  · rcases hQ2 with rfl | rfl | rfl
    · simpa using (cspF_SKIP_DIV_Ext_choice2 (p := p) (q := p) (α := α) (M1 := MF) (M2 := MF))
    · simpa using (cspF_Ext_choice_idem (P := (proc.DIV : proc p α)) (M := MF))
    · simpa using (cspF_Ext_choice_unit_r (P := (proc.DIV : proc p α)) (M := MF))
  · simpa using (cspF_Ext_choice_unit_l (P := Q2) (M := MF))

theorem cspF_fsfF_Ext_choice_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    eqFfix (P1 [+] P2) (P1 [+]seq P2) := by
  rw [fsfF_Ext_choice_def]
  refine cspF_fsfF_induct2_eqF
    (Pfun := Pfun_Ext_choice) (SP_step := SP_step_Ext_choice) ?_ ?_ ?_ ?_
  · intro C1 Rf1 Q hC
    exact cspF_Ext_choice_Dist_sum_l_nonempty hC
  · intro Q C2 Rf2 hC
    exact cspF_Ext_choice_Dist_sum_r_nonempty hC
  · intro A1 Pf1 Q1 A2 Pf2 Q2 hQ1 hQ2
    change eqFfix
      (((proc.Ext_pre_choice A1 Pf1) [+] Q1) [+] ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
      (SP_step_Ext_choice A1 Pf1 Q1 A2 Pf2 Q2 _ _ _)
    refine cspF_trans_left_eq Ext_choice_regroup ?_
    rw [SP_step_Ext_choice_def]
    refine cspF_Ext_choice_cong ?_ (Ext_choice_term hQ1 hQ2)
    refine cspF_trans_left_eq cspF_Ext_choice_step ?_
    refine cspF_Ext_pre_choice_cong rfl (fun a _ => ?_)
    by_cases hBoth : a ∈ A1 ∧ a ∈ A2
    · rw [procIte_pos hBoth, if_pos hBoth]
      exact cspF_fsfF_Int_choice_eqF
    · rw [procIte_neg hBoth, if_neg hBoth]
      by_cases hA1 : a ∈ A1
      · rw [procIte_pos hA1, if_pos hA1]
        exact cspF_reflex_eq_P
      · rw [procIte_neg hA1, if_neg hA1]
        exact cspF_reflex_eq_P
  · intro A1 Pf1 Q1 A2 Pf2 Q2 SPf SQf SPf1 SQf1 SPf2 SQf2 _ _ _
    exact cspF_reflex_eq_P

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
