           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_int

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

         1. induction method for full sequentialization
         2.
         3.

 *****************************************************************)
-/

private abbrev FsfFInduct2Pfun (p : Type u) (α : Type v) :=
  proc p α → proc p α → proc p α

private abbrev FsfFInduct2Step (p : Type u) (α : Type v) :=
  Set α → (α → proc p α) → proc p α →
    Set α → (α → proc p α) → proc p α →
    (α → proc p α) →
    (α → proc p α) →
    (α → proc p α) → proc p α

private abbrev FsfFInduct1Pfun (p : Type u) (α : Type v) :=
  proc p α → proc p α

private abbrev FsfFInduct1Step (p : Type u) (α : Type v) :=
  Set α → (α → proc p α) → proc p α →
    (α → proc p α) → proc p α

/- *============================================================*
 |                         Pfun P1 P2                         |
 *============================================================* -/

/- relation -/

axiom fsfF_induct2_rel
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α) :
    proc p α → proc p α → proc p α → Prop

namespace fsfF_induct2_rel

axiom fsfF_induct2_rel_etc_left
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    ¬ fsfF_proc P1 →
      fsfF_induct2_rel Pfun SP_step P1 P2 (Pfun P1 P2)

axiom fsfF_induct2_rel_etc_right
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    ¬ fsfF_proc P2 →
      fsfF_induct2_rel Pfun SP_step P1 P2 (Pfun P1 P2)

axiom fsfF_induct2_rel_step_int_left
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {C1 : sets_nats α}
    {Rf1 SRf : aset_anat α → proc p α}
    {P2 : proc p α} :
    (∀ c, if c ∈ sumset C1
      then fsfF_induct2_rel Pfun SP_step (Rf1 c) P2 (SRf c)
      else SRf c = proc.DIV) →
      sumset C1 ≠ ∅ →
        (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
          fsfF_proc P2 →
            fsfF_induct2_rel Pfun SP_step
              (proc.Rep_int_choice C1 Rf1) P2 (proc.Rep_int_choice C1 SRf)

axiom fsfF_induct2_rel_step_int_right
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 : proc p α}
    {C2 : sets_nats α}
    {Rf2 SRf : aset_anat α → proc p α} :
    (∀ c, if c ∈ sumset C2
      then fsfF_induct2_rel Pfun SP_step P1 (Rf2 c) (SRf c)
      else SRf c = proc.DIV) →
      sumset C2 ≠ ∅ →
        (∀ c, c ∈ sumset C2 → fsfF_proc (Rf2 c)) →
          fsfF_proc P1 →
            (∃ A Pf Q, P1 = (proc.Ext_pre_choice A Pf) [+] Q) →
              fsfF_induct2_rel Pfun SP_step
                P1 (proc.Rep_int_choice C2 Rf2) (proc.Rep_int_choice C2 SRf)

axiom fsfF_induct2_rel_step
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {A1 A2 : Set α}
    {Pf1 Pf2 SPf SPf1 SPf2 : α → proc p α}
    {Q1 Q2 : proc p α} :
    (∀ a, if a ∈ A1 ∧ a ∈ A2
      then fsfF_induct2_rel Pfun SP_step (Pf1 a) (Pf2 a) (SPf a)
      else SPf a = proc.DIV) →
      (∀ a, if a ∈ A1
        then fsfF_induct2_rel Pfun SP_step (Pf1 a) ((proc.Ext_pre_choice A2 Pf2) [+] Q2) (SPf1 a)
        else SPf1 a = proc.DIV) →
        (∀ a, if a ∈ A2
          then fsfF_induct2_rel Pfun SP_step ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Pf2 a) (SPf2 a)
          else SPf2 a = proc.DIV) →
          (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
            (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
              (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
                (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                  fsfF_induct2_rel Pfun SP_step
                    ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
                    ((proc.Ext_pre_choice A2 Pf2) [+] Q2)
                    (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)

end fsfF_induct2_rel

/- function -/

private axiom fsfF_induct2_rel_exists_ax
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α)
    (P1 P2 : proc p α) :
    ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

def fsfF_induct2
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α) :
    proc p α → proc p α → proc p α :=
  fun P1 P2 => Classical.choose (fsfF_induct2_rel_exists_ax Pfun SP_step P1 P2)

theorem fsfF_induct2_def
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α) :
    fsfF_induct2 Pfun SP_step =
      (fun P1 P2 => Classical.choose (fsfF_induct2_rel_exists_ax Pfun SP_step P1 P2)) :=
  rfl

/- uniqueness -/

axiom fsfF_induct2_rel_unique_in_lm
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP1 : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 SP1 →
      ∀ SP2 : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP2 → SP1 = SP2

axiom fsfF_induct2_rel_unique
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP1 SP2 : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 SP1 →
      fsfF_induct2_rel Pfun SP_step P1 P2 SP2 →
        SP1 = SP2

axiom fsfF_induct2_rel_EX1
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α)
    (P1 P2 : proc p α) :
    (∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP) ↔
      ∃! SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

/- fsfF_induct2_rel (iff) -/

axiom fsfF_induct2_rel_etc_left_iff
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    ¬ fsfF_proc P1 →
      (fsfF_induct2_rel Pfun SP_step P1 P2 SP ↔ SP = Pfun P1 P2)

axiom fsfF_induct2_rel_etc_right_iff
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    ¬ fsfF_proc P2 →
      (fsfF_induct2_rel Pfun SP_step P1 P2 SP ↔ SP = Pfun P1 P2)

axiom fsfF_induct2_rel_step_int_left_iff
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {C1 : sets_nats α}
    {Rf1 SRf : aset_anat α → proc p α}
    {P2 SP : proc p α} :
    (∀ c, if c ∈ sumset C1
      then fsfF_induct2_rel Pfun SP_step (Rf1 c) P2 (SRf c)
      else SRf c = proc.DIV) →
      sumset C1 ≠ ∅ →
        (∀ c, fsfF_proc (Rf1 c)) →
          fsfF_proc P2 →
            (fsfF_induct2_rel Pfun SP_step (proc.Rep_int_choice C1 Rf1) P2 SP ↔
              SP = proc.Rep_int_choice C1 SRf)

axiom fsfF_induct2_rel_step_iff
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {A1 A2 : Set α}
    {Pf1 Pf2 SPf SPf1 SPf2 : α → proc p α}
    {Q1 Q2 SP : proc p α} :
    (∀ a, if a ∈ A1 ∧ a ∈ A2
      then fsfF_induct2_rel Pfun SP_step (Pf1 a) (Pf2 a) (SPf a)
      else SPf a = proc.DIV) →
      (∀ a, if a ∈ A1
        then fsfF_induct2_rel Pfun SP_step (Pf1 a) ((proc.Ext_pre_choice A2 Pf2) [+] Q2) (SPf1 a)
        else SPf1 a = proc.DIV) →
        (∀ a, if a ∈ A2
          then fsfF_induct2_rel Pfun SP_step ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Pf2 a) (SPf2 a)
          else SPf2 a = proc.DIV) →
          (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
            (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
              (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
                (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                  (fsfF_induct2_rel Pfun SP_step
                      ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
                      ((proc.Ext_pre_choice A2 Pf2) [+] Q2) SP ↔
                    SP = SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)

/- existence -/

axiom fsfF_induct2_rel_exists_notin1
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    ¬ fsfF_proc P1 →
      ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

axiom fsfF_induct2_rel_exists_notin2
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    ¬ fsfF_proc P2 →
      ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

axiom fsfF_induct2_rel_exists_in_lm1
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α)
    {P2 : proc p α}
    {A : Set α}
    {Pf : α → proc p α}
    {Q : proc p α} :
    fsfF_proc P2 →
      ((∀ a, a ∈ A →
          fsfF_proc (Pf a) ∧
            ∀ P2 : proc p α, ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step (Pf a) P2 SP) ∧
        (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP)) →
          ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step ((proc.Ext_pre_choice A Pf) [+] Q) P2 SP

axiom fsfF_induct2_rel_exists_in_lm
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α)
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ P2 : proc p α, ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

axiom fsfF_induct2_rel_exists_in
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    fsfF_proc P1 →
      ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

axiom fsfF_induct2_rel_exists
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α)
    (P1 P2 : proc p α) :
    ∃ SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

axiom fsfF_induct2_rel_unique_exists
    (Pfun : FsfFInduct2Pfun p α)
    (SP_step : FsfFInduct2Step p α)
    (P1 P2 : proc p α) :
    ∃! SP : proc p α, fsfF_induct2_rel Pfun SP_step P1 P2 SP

/- in fsfF_proc -/

axiom fsfF_induct2_rel_in_lm
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 SP →
      (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
          (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α)
          (SPf SPf1 SPf2 : α → proc p α),
        (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
          (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
            (∀ a, a ∈ A1 ∩ A2 → fsfF_proc (SPf a)) →
              (∀ a, a ∈ A1 → fsfF_proc (SPf1 a)) →
                (∀ a, a ∈ A2 → fsfF_proc (SPf2 a)) →
                  (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
                    (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                      fsfF_proc (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)) →
        (fsfF_proc P1 ∧ fsfF_proc P2) → fsfF_proc SP

axiom fsfF_induct2_rel_in
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 SP →
      fsfF_proc P1 →
        fsfF_proc P2 →
          (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
              (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α)
              (SPf SPf1 SPf2 : α → proc p α),
            (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
              (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
                (∀ a, a ∈ A1 ∩ A2 → fsfF_proc (SPf a)) →
                  (∀ a, a ∈ A1 → fsfF_proc (SPf1 a)) →
                    (∀ a, a ∈ A2 → fsfF_proc (SPf2 a)) →
                      (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
                        (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                          fsfF_proc (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)) →
            fsfF_proc SP

/- syntactical transformation to fsfF -/

axiom cspF_fsfF_induct2_rel_eqF
    [HasPNfun p α] [HasFPmode]
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 SP →
      (∀ (C1 : sets_nats α) (Rf1 : aset_anat α → proc p α) (P2 : proc p α),
        sumset C1 ≠ ∅ →
          eqFfix (Pfun (proc.Rep_int_choice C1 Rf1) P2)
            (proc.Rep_int_choice C1 (fun c => Pfun (Rf1 c) P2))) →
        (∀ (P1 : proc p α) (C2 : sets_nats α) (Rf2 : aset_anat α → proc p α),
          sumset C2 ≠ ∅ →
            eqFfix (Pfun P1 (proc.Rep_int_choice C2 Rf2))
              (proc.Rep_int_choice C2 (fun c => Pfun P1 (Rf2 c)))) →
          (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
              (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α),
            (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
              (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                eqFfix
                  (Pfun ((proc.Ext_pre_choice A1 Pf1) [+] Q1) ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
                  (SP_step A1 Pf1 Q1 A2 Pf2 Q2
                    (fun a => Pfun (Pf1 a) (Pf2 a))
                    (fun a => Pfun (Pf1 a) ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
                    (fun a => Pfun ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Pf2 a)))) →
            (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
                (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α)
                (SPf SQf SPf1 SQf1 SPf2 SQf2 : α → proc p α),
              (∀ a, a ∈ A1 ∩ A2 → eqFfix (SPf a) (SQf a)) →
                (∀ a, a ∈ A1 → eqFfix (SPf1 a) (SQf1 a)) →
                  (∀ a, a ∈ A2 → eqFfix (SPf2 a) (SQf2 a)) →
                    eqFfix
                      (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)
                      (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SQf SQf1 SQf2)) →
              eqFfix (Pfun P1 P2) SP

/- relation --> function -/

axiom fsfF_induct2_in_rel
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 (fsfF_induct2 Pfun SP_step P1 P2)

axiom fsfF_induct2_from_rel
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    fsfF_induct2_rel Pfun SP_step P1 P2 SP ↔
      fsfF_induct2 Pfun SP_step P1 P2 = SP

axiom fsfF_induct2_to_rel
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 SP : proc p α} :
    fsfF_induct2 Pfun SP_step P1 P2 = SP ↔
      fsfF_induct2_rel Pfun SP_step P1 P2 SP

/- function -/

axiom fsfF_induct2_etc
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    ¬ fsfF_proc P1 →
      ¬ fsfF_proc P2 →
        fsfF_induct2 Pfun SP_step P1 P2 = Pfun P1 P2

axiom fsfF_induct2_step_int_left
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {C1 : sets_nats α}
    {Rf1 : aset_anat α → proc p α}
    {P2 : proc p α} :
    sumset C1 ≠ ∅ →
      (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
        fsfF_proc P2 →
          fsfF_induct2 Pfun SP_step (proc.Rep_int_choice C1 Rf1) P2 =
            proc.Rep_int_choice C1
              (fun c =>
                if c ∈ sumset C1
                then fsfF_induct2 Pfun SP_step (Rf1 c) P2
                else proc.DIV)

axiom fsfF_induct2_step_int_right
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 : proc p α}
    {C2 : sets_nats α}
    {Rf2 : aset_anat α → proc p α} :
    sumset C2 ≠ ∅ →
      (∀ c, c ∈ sumset C2 → fsfF_proc (Rf2 c)) →
        fsfF_proc P1 →
          (∃ A Pf Q, P1 = (proc.Ext_pre_choice A Pf) [+] Q) →
            fsfF_induct2 Pfun SP_step P1 (proc.Rep_int_choice C2 Rf2) =
              proc.Rep_int_choice C2
                (fun c =>
                  if c ∈ sumset C2
                  then fsfF_induct2 Pfun SP_step P1 (Rf2 c)
                  else proc.DIV)

axiom fsfF_induct2_step
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {A1 A2 : Set α}
    {Pf1 Pf2 : α → proc p α}
    {Q1 Q2 : proc p α} :
    (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
      (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
        (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
          (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
            fsfF_induct2 Pfun SP_step
              ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
              ((proc.Ext_pre_choice A2 Pf2) [+] Q2) =
              SP_step A1 Pf1 Q1 A2 Pf2 Q2
                (fun a =>
                  if a ∈ A1 ∩ A2
                  then fsfF_induct2 Pfun SP_step (Pf1 a) (Pf2 a)
                  else proc.DIV)
                (fun a =>
                  if a ∈ A1
                  then fsfF_induct2 Pfun SP_step (Pf1 a) ((proc.Ext_pre_choice A2 Pf2) [+] Q2)
                  else proc.DIV)
                (fun a =>
                  if a ∈ A2
                  then fsfF_induct2 Pfun SP_step ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Pf2 a)
                  else proc.DIV)

/- The Isabelle theorem bundle `fsfF_induct2` is represented by
   `fsfF_induct2_etc`, `fsfF_induct2_step_int_left`,
   `fsfF_induct2_step_int_right`, and `fsfF_induct2_step`. -/

/- in fsfF_proc -/

axiom fsfF_induct2_in
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    fsfF_proc P1 →
      fsfF_proc P2 →
        (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
            (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α)
            (SPf SPf1 SPf2 : α → proc p α),
          (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
            (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
              (∀ a, a ∈ A1 ∩ A2 → fsfF_proc (SPf a)) →
                (∀ a, a ∈ A1 → fsfF_proc (SPf1 a)) →
                  (∀ a, a ∈ A2 → fsfF_proc (SPf2 a)) →
                    (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
                      (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                        fsfF_proc (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)) →
            fsfF_proc (fsfF_induct2 Pfun SP_step P1 P2)

/- syntactical transformation to fsfF -/

axiom cspF_fsfF_induct2_eqF
    [HasPNfun p α] [HasFPmode]
    {Pfun : FsfFInduct2Pfun p α}
    {SP_step : FsfFInduct2Step p α}
    {P1 P2 : proc p α} :
    (∀ (C1 : sets_nats α) (Rf1 : aset_anat α → proc p α) (P2 : proc p α),
      sumset C1 ≠ ∅ →
        eqFfix (Pfun (proc.Rep_int_choice C1 Rf1) P2)
          (proc.Rep_int_choice C1 (fun c => Pfun (Rf1 c) P2))) →
      (∀ (P1 : proc p α) (C2 : sets_nats α) (Rf2 : aset_anat α → proc p α),
        sumset C2 ≠ ∅ →
          eqFfix (Pfun P1 (proc.Rep_int_choice C2 Rf2))
            (proc.Rep_int_choice C2 (fun c => Pfun P1 (Rf2 c)))) →
        (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
            (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α),
          (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
            (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
              eqFfix
                (Pfun ((proc.Ext_pre_choice A1 Pf1) [+] Q1) ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
                (SP_step A1 Pf1 Q1 A2 Pf2 Q2
                  (fun a => Pfun (Pf1 a) (Pf2 a))
                  (fun a => Pfun (Pf1 a) ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
                  (fun a => Pfun ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Pf2 a)))) →
          (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
              (A2 : Set α) (Pf2 : α → proc p α) (Q2 : proc p α)
              (SPf SQf SPf1 SQf1 SPf2 SQf2 : α → proc p α),
            (∀ a, a ∈ A1 ∩ A2 → eqFfix (SPf a) (SQf a)) →
              (∀ a, a ∈ A1 → eqFfix (SPf1 a) (SQf1 a)) →
                (∀ a, a ∈ A2 → eqFfix (SPf2 a) (SQf2 a)) →
                  eqFfix
                    (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)
                    (SP_step A1 Pf1 Q1 A2 Pf2 Q2 SQf SQf1 SQf2)) →
            eqFfix (Pfun P1 P2) (fsfF_induct2 Pfun SP_step P1 P2)

/- *===========================================================*
 |               fsfF_induct1 (take one process)             |
 *===========================================================* -/

def fsfF_induct1
    (Pfun : FsfFInduct1Pfun p α)
    (SP_step : FsfFInduct1Step p α) :
    proc p α → proc p α :=
  fun P1 =>
    fsfF_induct2
      (fun P1 _P2 => Pfun P1)
      (fun A1 Pf1 Q1 _A2 _Pf2 _Q2 _SPf SPf1 _SPf2 => SP_step A1 Pf1 Q1 SPf1)
      P1 SDIV

theorem fsfF_induct1_def
    (Pfun : FsfFInduct1Pfun p α)
    (SP_step : FsfFInduct1Step p α) :
    fsfF_induct1 Pfun SP_step =
      (fun P1 =>
        fsfF_induct2
          (fun P1 _P2 => Pfun P1)
          (fun A1 Pf1 Q1 _A2 _Pf2 _Q2 _SPf SPf1 _SPf2 => SP_step A1 Pf1 Q1 SPf1)
          P1 SDIV) :=
  rfl

/- in fsfF_proc -/

axiom fsfF_induct1_in
    {Pfun : FsfFInduct1Pfun p α}
    {SP_step : FsfFInduct1Step p α}
    {P1 : proc p α} :
    fsfF_proc P1 →
      (∀ (A : Set α) (Pf : α → proc p α) (Q : proc p α) (SPf : α → proc p α),
        (∀ a, a ∈ A → fsfF_proc (Pf a)) →
          (∀ a, a ∈ A → fsfF_proc (SPf a)) →
            (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
              fsfF_proc (SP_step A Pf Q SPf)) →
        fsfF_proc (fsfF_induct1 Pfun SP_step P1)

/- syntactical transformation to fsfF -/

axiom cspF_fsfF_induct1_eqF
    [HasPNfun p α] [HasFPmode]
    {Pfun : FsfFInduct1Pfun p α}
    {SP_step : FsfFInduct1Step p α}
    {P1 : proc p α} :
    (∀ (C1 : sets_nats α) (Rf1 : aset_anat α → proc p α),
      sumset C1 ≠ ∅ →
        eqFfix (Pfun (proc.Rep_int_choice C1 Rf1))
          (proc.Rep_int_choice C1 (fun c => Pfun (Rf1 c)))) →
      (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α),
        (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
          eqFfix
            (Pfun ((proc.Ext_pre_choice A1 Pf1) [+] Q1))
            (SP_step A1 Pf1 Q1 (fun a => Pfun (Pf1 a)))) →
        (∀ (A1 : Set α) (Pf1 : α → proc p α) (Q1 : proc p α)
            (SPf SQf : α → proc p α),
          (∀ a, a ∈ A1 → eqFfix (SPf a) (SQf a)) →
            eqFfix (SP_step A1 Pf1 Q1 SPf) (SP_step A1 Pf1 Q1 SQf)) →
          eqFfix (Pfun P1) (fsfF_induct1 Pfun SP_step P1)

end
