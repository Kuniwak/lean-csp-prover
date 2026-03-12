           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |              Februaru 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_def

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

         1. full sequentialization for Depth-restriction (P |. n)
         2.
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                       Depth_rest                           |
 |                                                            |
 *============================================================* -/

/- *============================================================*
 |                         Pfun P1 P2                         |
 *============================================================* -/

/- relation -/

axiom fsfF_Depth_rest_rel : proc p α → Nat → proc p α → Prop

namespace fsfF_Depth_rest_rel

axiom zero
    {P1 : proc p α} :
    fsfF_Depth_rest_rel P1 0 SDIV

axiom etc
    {P1 : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      fsfF_Depth_rest_rel P1 (Nat.succ n) (P1 |. Nat.succ n)

axiom int
    {C1 : sets_nats α}
    {Rf1 SRf : aset_anat α → proc p α}
    {m : Nat} :
    (∀ c, if c ∈ sumset C1
      then fsfF_Depth_rest_rel (Rf1 c) (Nat.succ m) (SRf c)
      else SRf c = proc.DIV) →
      sumset C1 ≠ ∅ →
        (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
          fsfF_Depth_rest_rel
            (proc.Rep_int_choice C1 Rf1)
            (Nat.succ m)
            (proc.Rep_int_choice C1 SRf)

axiom step
    {A1 : Set α}
    {Pf1 SPf : α → proc p α}
    {Q1 : proc p α}
    {n : Nat} :
    (∀ a, if a ∈ A1
      then fsfF_Depth_rest_rel (Pf1 a) n (SPf a)
      else SPf a = proc.DIV) →
      (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
        (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
          fsfF_Depth_rest_rel
            ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
            (Nat.succ n)
            ((proc.Ext_pre_choice A1 SPf) [+] Q1)

end fsfF_Depth_rest_rel

/- function -/

private axiom fsfF_Depth_rest_rel_exists_ax
    (P1 : proc p α)
    (n : Nat) :
    ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP

def fsfF_Depth_rest
    (P1 : proc p α) (n : Nat) : proc p α :=
  Classical.choose (fsfF_Depth_rest_rel_exists_ax P1 n)

theorem fsfF_Depth_rest_def
    (P1 : proc p α) (n : Nat) :
    fsfF_Depth_rest P1 n =
      Classical.choose (fsfF_Depth_rest_rel_exists_ax P1 n) :=
  rfl

/- Lean note:
   Isabelle's syntax/translation for `P |.seq n` is represented directly by
   `fsfF_Depth_rest P n`. -/

/-
(****************************************************************
 |                      uniquness                               |
 ****************************************************************)
-/

axiom fsfF_Depth_rest_rel_unique
    {P1 : proc p α}
    {n : Nat}
    {SP1 SP2 : proc p α} :
    fsfF_Depth_rest_rel P1 n SP1 →
      fsfF_Depth_rest_rel P1 n SP2 →
        SP1 = SP2

lemma fsfF_Depth_rest_rel_unique_in_lm
    {P1 : proc p α}
    {n : Nat}
    {SP1 : proc p α} :
    fsfF_Depth_rest_rel P1 n SP1 →
      ∀ SP2 : proc p α, fsfF_Depth_rest_rel P1 n SP2 → SP1 = SP2 := by
  intro hSP1 SP2 hSP2
  exact fsfF_Depth_rest_rel_unique (P1 := P1) (n := n) hSP1 hSP2

/- *-----------------------*
 |        unique         |
 *-----------------------* -/

lemma fsfF_Depth_rest_rel_EX1
    (P1 : proc p α)
    (n : Nat) :
    (∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP) ↔
      ∃! SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  constructor
  · intro h
    rcases h with ⟨SP, hSP⟩
    exact ⟨SP, hSP, fun SP2 hSP2 =>
      fsfF_Depth_rest_rel_unique
        (P1 := P1)
        (n := n)
        (SP1 := SP2)
        (SP2 := SP)
        hSP2
        hSP⟩
  · intro h
    exact h.exists

/- *------------------------------------------------------------*
 |                   fsfF_Depth_rest_rel (iff)                |
 *------------------------------------------------------------* -/

/- zero -/

axiom fsfF_Depth_rest_rel_zero_iff
    {P1 SP : proc p α} :
    fsfF_Depth_rest_rel P1 0 SP ↔ SP = SDIV

/- etc -/

axiom fsfF_Depth_rest_rel_etc_iff
    {P1 SP : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      (fsfF_Depth_rest_rel P1 (Nat.succ n) SP ↔ SP = P1 |. Nat.succ n)

/- int nat -/

axiom fsfF_Depth_rest_rel_int_iff
    {C1 : sets_nats α}
    {Rf1 SRf : aset_anat α → proc p α}
    {m : Nat}
    {SP : proc p α} :
    (∀ c, if c ∈ sumset C1
      then fsfF_Depth_rest_rel (Rf1 c) (Nat.succ m) (SRf c)
      else SRf c = proc.DIV) →
      sumset C1 ≠ ∅ →
        (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
          (fsfF_Depth_rest_rel
              (proc.Rep_int_choice C1 Rf1)
              (Nat.succ m)
              SP ↔
            SP = proc.Rep_int_choice C1 SRf)

/- step -/

axiom fsfF_Depth_rest_rel_step_iff
    {A1 : Set α}
    {Pf1 SPf : α → proc p α}
    {Q1 SP : proc p α}
    {n : Nat} :
    (∀ a, if a ∈ A1
      then fsfF_Depth_rest_rel (Pf1 a) n (SPf a)
      else SPf a = proc.DIV) →
      (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
        (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
          (fsfF_Depth_rest_rel
              ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
              (Nat.succ n)
              SP ↔
            SP = ((proc.Ext_pre_choice A1 SPf) [+] Q1))

/-
(****************************************************************
 |                      existency                               |
 ****************************************************************)
-/

/- exists -/

lemma fsfF_Depth_rest_rel_exists_zero
    (P1 : proc p α) :
    ∃ SP : proc p α, fsfF_Depth_rest_rel P1 0 SP := by
  exact ⟨SDIV, fsfF_Depth_rest_rel.zero⟩

lemma fsfF_Depth_rest_rel_exists_notin
    {P1 : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  intro hP1
  cases n with
  | zero =>
      exact fsfF_Depth_rest_rel_exists_zero P1
  | succ m =>
      exact ⟨P1 |. Nat.succ m, fsfF_Depth_rest_rel.etc hP1⟩

/- in fsfF_proc -/

lemma fsfF_Depth_rest_rel_exists_in
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ n, ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  intro _hP1 n
  exact fsfF_Depth_rest_rel_exists_ax P1 n

/- *-----------------------*
 |        exists         |
 *-----------------------* -/

lemma fsfF_Depth_rest_rel_exists
    (P1 : proc p α)
    (n : Nat) :
    ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP :=
  fsfF_Depth_rest_rel_exists_ax P1 n

/- *-----------------------*
 |    uniquely exists    |
 *-----------------------* -/

lemma fsfF_Depth_rest_rel_unique_exists
    (P1 : proc p α)
    (n : Nat) :
    ∃! SP : proc p α, fsfF_Depth_rest_rel P1 n SP :=
  (fsfF_Depth_rest_rel_EX1 P1 n).1 (fsfF_Depth_rest_rel_exists P1 n)

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

lemma fsfF_Depth_rest_rel_zero_in
    {P1 SP : proc p α} :
    fsfF_Depth_rest_rel P1 0 SP →
      fsfF_proc SP := by
  intro hSP
  have hEq : SP = SDIV :=
    (fsfF_Depth_rest_rel_zero_iff (P1 := P1) (SP := SP)).1 hSP
  subst SP
  exact fsfF_SDIV_in (p := p) (α := α)

axiom fsfF_Depth_rest_rel_in
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_proc P1 →
      fsfF_Depth_rest_rel P1 n SP →
        fsfF_proc SP

lemma fsfF_Depth_rest_rel_in_lm
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ n SP, fsfF_Depth_rest_rel P1 n SP → fsfF_proc SP := by
  intro hP1 n SP hSP
  exact fsfF_Depth_rest_rel_in (P1 := P1) (n := n) hP1 hSP

/- *------------------------------------*
 |                 in                 |
 *------------------------------------* -/

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fsfF_Depth_rest_rel_eqF_zero
    [HasPNfun p α] [HasFPmode]
    {P1 SP : proc p α} :
    fsfF_Depth_rest_rel P1 0 SP →
      eqFfix (P1 |. 0) SP

axiom cspF_fsfF_Depth_rest_rel_eqF_notin
    [HasPNfun p α] [HasFPmode]
    {P1 SP : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      fsfF_Depth_rest_rel P1 n SP →
        eqFfix (P1 |. n) SP

axiom cspF_fsfF_Depth_rest_rel_eqF_in
    [HasPNfun p α] [HasFPmode]
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ n SP, fsfF_Depth_rest_rel P1 n SP → eqFfix (P1 |. n) SP

lemma cspF_fsfF_Depth_rest_rel_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_Depth_rest_rel P1 n SP →
      eqFfix (P1 |. n) SP := by
  intro hSP
  by_cases hP1 : fsfF_proc P1
  · exact cspF_fsfF_Depth_rest_rel_eqF_in hP1 n SP hSP
  · exact cspF_fsfF_Depth_rest_rel_eqF_notin hP1 hSP

/-
(*************************************************************
                  relation --> function
 *************************************************************)
-/

lemma fsfF_Depth_rest_in_rel
    {P1 : proc p α}
    {n : Nat} :
    fsfF_Depth_rest_rel P1 n (fsfF_Depth_rest P1 n) :=
  Classical.choose_spec (fsfF_Depth_rest_rel_exists_ax P1 n)

lemma fsfF_Depth_rest_from_rel
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_Depth_rest_rel P1 n SP ↔ fsfF_Depth_rest P1 n = SP := by
  constructor
  · intro hSP
    exact fsfF_Depth_rest_rel_unique
      (P1 := P1)
      (n := n)
      fsfF_Depth_rest_in_rel
      hSP
  · intro hSP
    subst hSP
    exact fsfF_Depth_rest_in_rel

lemma fsfF_Depth_rest_to_rel
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_Depth_rest P1 n = SP ↔ fsfF_Depth_rest_rel P1 n SP := by
  constructor
  · intro hSP
    subst hSP
    exact fsfF_Depth_rest_in_rel
  · intro hSP
    exact (fsfF_Depth_rest_from_rel (P1 := P1) (n := n) (SP := SP)).1 hSP

/-
(*************************************************************
                          function
 *************************************************************)
-/

lemma fsfF_Depth_rest_zero
    (P1 : proc p α) :
    fsfF_Depth_rest P1 0 = SDIV := by
  exact (fsfF_Depth_rest_from_rel (P1 := P1) (n := 0) (SP := SDIV)).1
    fsfF_Depth_rest_rel.zero

lemma fsfF_Depth_rest_etc
    {P1 : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      fsfF_Depth_rest P1 (Nat.succ n) = P1 |. Nat.succ n := by
  intro hP1
  exact (fsfF_Depth_rest_from_rel
      (P1 := P1)
      (n := Nat.succ n)
      (SP := P1 |. Nat.succ n)).1
    (fsfF_Depth_rest_rel.etc hP1)

lemma fsfF_Depth_rest_int
    {C1 : sets_nats α}
    {Rf1 : aset_anat α → proc p α}
    {m : Nat} :
    sumset C1 ≠ ∅ →
      (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
        fsfF_Depth_rest (proc.Rep_int_choice C1 Rf1) (Nat.succ m) =
          proc.Rep_int_choice C1
            (fun c =>
              if c ∈ sumset C1
              then fsfF_Depth_rest (Rf1 c) (Nat.succ m)
              else proc.DIV) := by
  intro hC1 hRf1
  apply (fsfF_Depth_rest_from_rel
      (P1 := proc.Rep_int_choice C1 Rf1)
      (n := Nat.succ m)
      (SP := proc.Rep_int_choice C1
        (fun c =>
          if c ∈ sumset C1
          then fsfF_Depth_rest (Rf1 c) (Nat.succ m)
          else proc.DIV))).1
  apply fsfF_Depth_rest_rel.int
  · intro c
    by_cases hc : c ∈ sumset C1
    · simp [hc, fsfF_Depth_rest_in_rel]
    · simp [hc]
  · exact hC1
  · exact hRf1

lemma fsfF_Depth_rest_step
    {A1 : Set α}
    {Pf1 : α → proc p α}
    {Q1 : proc p α}
    {n : Nat} :
    (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
      (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
        fsfF_Depth_rest ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Nat.succ n) =
          ((proc.Ext_pre_choice A1
            (fun a =>
              if a ∈ A1
              then fsfF_Depth_rest (Pf1 a) n
              else proc.DIV)) [+] Q1) := by
  intro hPf1 hQ1
  apply (fsfF_Depth_rest_from_rel
      (P1 := ((proc.Ext_pre_choice A1 Pf1) [+] Q1))
      (n := Nat.succ n)
      (SP := ((proc.Ext_pre_choice A1
        (fun a =>
          if a ∈ A1
          then fsfF_Depth_rest (Pf1 a) n
          else proc.DIV)) [+] Q1))).1
  apply fsfF_Depth_rest_rel.step
  · intro a
    by_cases ha : a ∈ A1
    · simp [ha, fsfF_Depth_rest_in_rel]
    · simp [ha]
  · exact hPf1
  · exact hQ1

/- The Isabelle theorem bundle `fsfF_Depth_rest` is represented by
   `fsfF_Depth_rest_etc`, `fsfF_Depth_rest_int`, and
   `fsfF_Depth_rest_step`. -/

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

lemma fsfF_Depth_rest_in
    {P1 : proc p α}
    {n : Nat} :
    fsfF_proc P1 →
      fsfF_proc (fsfF_Depth_rest P1 n) := by
  intro hP1
  exact fsfF_Depth_rest_rel_in (P1 := P1) (n := n) hP1 fsfF_Depth_rest_in_rel

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

lemma cspF_fsfF_Depth_rest_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 : proc p α}
    {n : Nat} :
    eqFfix (P1 |. n) (fsfF_Depth_rest P1 n) :=
  cspF_fsfF_Depth_rest_rel_eqF fsfF_Depth_rest_in_rel

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
