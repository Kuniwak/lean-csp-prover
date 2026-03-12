           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_ext

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

         1. full sequentialization for Sequential composition (P1 ;; P2)
         2.
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                    Seq_compo P ;; Q                        |
 |                                                            |
 *============================================================* -/

def Pfun_Seq_compo (P2 : proc p α) : proc p α → proc p α :=
  fun P1 => P1 ;; P2

theorem Pfun_Seq_compo_def
    (P2 : proc p α) :
    Pfun_Seq_compo (p := p) (α := α) P2 =
      (fun P1 => P1 ;; P2) :=
  rfl

def SP_step_Seq_compo
    (P2 : proc p α) :
    Set α → (α → proc p α) → proc p α → (α → proc p α) → proc p α :=
  fun Y1 _Pf1 Q1 SPf =>
    if Q1 = proc.SKIP then
      (((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) [>seq P2)
    else if Q1 = proc.DIV then
      (((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) [>seq SDIV)
    else
      ((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP)

theorem SP_step_Seq_compo_def
    (P2 : proc p α) :
    SP_step_Seq_compo (p := p) (α := α) P2 =
      (fun Y1 _Pf1 Q1 SPf =>
        if Q1 = proc.SKIP then
          (((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) [>seq P2)
        else if Q1 = proc.DIV then
          (((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) [>seq SDIV)
        else
          ((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP)) :=
  rfl

def fsfF_Seq_compo
    (P1 P2 : proc p α) : proc p α :=
  fsfF_induct1 (Pfun_Seq_compo P2) (SP_step_Seq_compo P2) P1

theorem fsfF_Seq_compo_def
    (P1 P2 : proc p α) :
    fsfF_Seq_compo (p := p) (α := α) P1 P2 =
      fsfF_induct1 (Pfun_Seq_compo P2) (SP_step_Seq_compo P2) P1 :=
  rfl

infixr:78 " ;;seq " => fsfF_Seq_compo

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Seq_compo_in
    {P1 P2 : proc p α} :
    fsfF_proc P1 →
      fsfF_proc P2 →
        fsfF_proc (P1 ;;seq P2) := by
  intro hP1 hP2
  rw [fsfF_Seq_compo_def]
  refine fsfF_induct1_in hP1 ?_
  intro Y1 Pf1 Q1 SPf _hPf1 hSPf hQ1
  cases hQ1 with
  | inl hQ1 =>
      subst hQ1
      have hStep : fsfF_proc (((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) [>seq P2) := by
        apply fsfF_Timeout_in
        · refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
          intro a ha
          exact hSPf a ha
        · exact hP2
      simpa only [SP_step_Seq_compo_def, if_pos rfl] using hStep
  | inr hQ1 =>
      cases hQ1 with
      | inl hQ1 =>
          subst hQ1
          have hDivNeSkip : (proc.DIV : proc p α) ≠ proc.SKIP := by
            intro h
            cases h
          have hStep : fsfF_proc (((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) [>seq SDIV) := by
            apply fsfF_Timeout_in
            · refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
              intro a ha
              exact hSPf a ha
            · exact fsfF_SDIV_in
          simpa only [SP_step_Seq_compo_def, if_neg hDivNeSkip, if_pos rfl] using hStep
      | inr hQ1 =>
          subst hQ1
          have hStopNeSkip : (proc.STOP : proc p α) ≠ proc.SKIP := by
            intro h
            cases h
          have hStopNeDiv : (proc.STOP : proc p α) ≠ proc.DIV := by
            intro h
            cases h
          have hStep : fsfF_proc ((proc.Ext_pre_choice Y1 SPf) [+] proc.STOP) := by
            refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
            intro a ha
            exact hSPf a ha
          simpa only [SP_step_Seq_compo_def, if_neg hStopNeSkip, if_neg hStopNeDiv] using hStep

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fsfF_Seq_compo_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    eqFfix (P1 ;; P2) (P1 ;;seq P2)

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
