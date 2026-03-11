           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_nf_int
import LeanCspProver.FNF_F.FNF_F_sf

open fpmode
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

         1. full normalizing
         2.
         3.

 *****************************************************************)
-/

/- (*==================================================================*
 |                          fsfF --> fnfF                           |
 *==================================================================*) -/

axiom fnfF_fsfF_rel : Nat → proc p α → proc p α → Prop

namespace fnfF_fsfF_rel

axiom zero
    {P : proc p α} :
    fnfF_fsfF_rel 0 P NDIV

axiom etc
    {n : Nat} {P : proc p α} :
    ¬ fsfF_proc P →
      fnfF_fsfF_rel (Nat.succ n) P (P |. Nat.succ n)

axiom int
    {n : Nat}
    {C : sets_nats α}
    {SPf NPf : aset_anat α → proc p α} :
    (∀ c, if c ∈ sumset C
      then fnfF_fsfF_rel (Nat.succ n) (SPf c) (NPf c)
      else NPf c = proc.DIV) →
        sumset C ≠ ∅ →
          (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
            fnfF_fsfF_rel
              (Nat.succ n)
              (proc.Rep_int_choice C SPf)
              (fnfF_Rep_int_choice (Nat.succ n) C NPf)

axiom step
    {n : Nat}
    {A : Set α}
    {SPf NPf : α → proc p α}
    {Q : proc p α} :
    (∀ a, if a ∈ A
      then fnfF_fsfF_rel n (SPf a) (NPf a)
      else NPf a = proc.DIV) →
        (∀ a, a ∈ A → fsfF_proc (SPf a)) →
          (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
            fnfF_fsfF_rel
              (Nat.succ n)
              ((proc.Ext_pre_choice A SPf) [+] Q)
              (((proc.Ext_pre_choice A NPf) [+]
                  (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
                Rep_int_choice_set
                  (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
                  (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))

end fnfF_fsfF_rel

/- (*** function ***) -/

private axiom fnfF_fsfF_rel_exists_ax
    (n : Nat) (SP : proc p α) :
    ∃ NP : proc p α, fnfF_fsfF_rel n SP NP

def fnfF_fsfF
    (n : Nat) (SP : proc p α) : proc p α :=
  Classical.choose (fnfF_fsfF_rel_exists_ax n SP)

def fnfF [Inhabited α] [HasPNfun p α] :
    Nat → proc p α → proc p α :=
  fun n P => fnfF_fsfF n (fsfF P)

theorem fnfF_def [Inhabited α] [HasPNfun p α] :
    fnfF (p := p) (α := α) =
      (fun n P => fnfF_fsfF n (fsfF P)) :=
  rfl

def XfnfF [Inhabited α] [HasPNfun p α] :
    proc p α → proc p α :=
  fun P => Rep_int_choice_nat Set.univ (fun n => fnfF n P)

theorem XfnfF_def [Inhabited α] [HasPNfun p α] :
    XfnfF (p := p) (α := α) =
      (fun P => Rep_int_choice_nat Set.univ (fun n => fnfF n P)) :=
  rfl

/- Lean note:
   Isabelle's syntax/translation for `!nat n .. (fnfF n P)` is represented
   directly by `Rep_int_choice_nat Set.univ (fun n => fnfF n P)`. -/

/-
(****************************************************************
 |                      uniquness                               |
 ****************************************************************)
-/

axiom fnfF_fsfF_rel_unique
    {n : Nat} {SP NP1 NP2 : proc p α} :
    fnfF_fsfF_rel n SP NP1 →
      fnfF_fsfF_rel n SP NP2 →
        NP1 = NP2

lemma fnfF_fsfF_rel_unique_in_lm
    {n : Nat} {SP NP1 : proc p α} :
    fnfF_fsfF_rel n SP NP1 →
      ∀ NP2 : proc p α, fnfF_fsfF_rel n SP NP2 → NP1 = NP2 := by
  intro hNP1 NP2 hNP2
  exact fnfF_fsfF_rel_unique (n := n) (SP := SP) hNP1 hNP2

/- *-----------------------*
 |        unique         |
 *-----------------------* -/

theorem fnfF_fsfF_rel_EX1
    (n : Nat) (SP : proc p α) :
    (∃ NP : proc p α, fnfF_fsfF_rel n SP NP) ↔
      ∃! NP : proc p α, fnfF_fsfF_rel n SP NP := by
  constructor
  · intro h
    rcases h with ⟨NP, hNP⟩
    exact ⟨NP, hNP, fun NP2 hNP2 =>
      (fnfF_fsfF_rel_unique (n := n) (SP := SP) (NP1 := NP) (NP2 := NP2) hNP hNP2).symm⟩
  · intro h
    exact h.exists

/- *------------------------------------------------------------*
 |                      fnfF_fsfF_rel (iff)                   |
 *------------------------------------------------------------* -/

/- zero -/

axiom fnfF_fsfF_rel_zero_iff
    {SP NP : proc p α} :
    fnfF_fsfF_rel 0 SP NP ↔ NP = NDIV

/- etc -/

axiom fnfF_fsfF_rel_etc_iff
    {n : Nat} {P NP : proc p α} :
    ¬ fsfF_proc P →
      (fnfF_fsfF_rel (Nat.succ n) P NP ↔ NP = P |. Nat.succ n)

/- int -/

axiom fnfF_fsfF_rel_int_iff
    {n : Nat}
    {C : sets_nats α}
    {SPf NPf : aset_anat α → proc p α}
    {NP : proc p α} :
    (∀ c, if c ∈ sumset C
      then fnfF_fsfF_rel (Nat.succ n) (SPf c) (NPf c)
      else NPf c = proc.DIV) →
        sumset C ≠ ∅ →
          (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
            (fnfF_fsfF_rel (Nat.succ n) (proc.Rep_int_choice C SPf) NP ↔
              NP = fnfF_Rep_int_choice (Nat.succ n) C NPf)

/- step -/

axiom fnfF_fsfF_rel_step_iff
    {n : Nat}
    {A : Set α}
    {SPf NPf : α → proc p α}
    {Q NP : proc p α} :
    (∀ a, if a ∈ A
      then fnfF_fsfF_rel n (SPf a) (NPf a)
      else NPf a = proc.DIV) →
        (∀ a, a ∈ A → fsfF_proc (SPf a)) →
          (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
            (fnfF_fsfF_rel (Nat.succ n) ((proc.Ext_pre_choice A SPf) [+] Q) NP ↔
              NP =
                ((((proc.Ext_pre_choice A NPf) [+]
                    (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
                  Rep_int_choice_set
                    (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
                    (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))))

/-
(****************************************************************
 |                      existency                               |
 ****************************************************************)
-/

/- (*** exists ***) -/

theorem fnfF_fsfF_rel_exists_zero
    (SP : proc p α) :
    ∃ NP : proc p α, fnfF_fsfF_rel 0 SP NP :=
  ⟨NDIV, fnfF_fsfF_rel.zero⟩

theorem fnfF_fsfF_rel_exists_notin
    {n : Nat} {P : proc p α} :
    ¬ fsfF_proc P →
      ∃ NP : proc p α, fnfF_fsfF_rel n P NP := by
  intro hP
  cases n with
  | zero =>
      exact fnfF_fsfF_rel_exists_zero P
  | succ m =>
      exact ⟨P |. Nat.succ m, fnfF_fsfF_rel.etc hP⟩

axiom fnfF_fsfF_rel_exists_in
    {SP : proc p α} :
    fsfF_proc SP →
      ∀ n : Nat, ∃ NP : proc p α, fnfF_fsfF_rel n SP NP

/- *-----------------------*
 |        exists         |
 *-----------------------* -/

theorem fnfF_fsfF_rel_exists
    (n : Nat) (SP : proc p α) :
    ∃ NP : proc p α, fnfF_fsfF_rel n SP NP := by
  by_cases hSP : fsfF_proc SP
  · exact fnfF_fsfF_rel_exists_in hSP n
  · exact fnfF_fsfF_rel_exists_notin hSP

/- *-----------------------*
 |    uniquely exists    |
 *-----------------------* -/

theorem fnfF_fsfF_rel_unique_exists
    (n : Nat) (SP : proc p α) :
    ∃! NP : proc p α, fnfF_fsfF_rel n SP NP :=
  (fnfF_fsfF_rel_EX1 n SP).1 (fnfF_fsfF_rel_exists n SP)

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

axiom fnfF_fsfF_rel_zero_in
    {SP NP : proc p α} :
    fnfF_fsfF_rel 0 SP NP →
      fnfF_proc NP

axiom fnfF_fsfF_rel_in
    {SP NP : proc p α}
    {n : Nat} :
    fsfF_proc SP →
      fnfF_fsfF_rel n SP NP →
        fnfF_proc NP

lemma fnfF_fsfF_rel_in_lm
    {SP : proc p α} :
    fsfF_proc SP →
      ∀ n : Nat, ∀ NP : proc p α, fnfF_fsfF_rel n SP NP → fnfF_proc NP := by
  intro hSP n NP hNP
  exact fnfF_fsfF_rel_in (n := n) (SP := SP) (NP := NP) hSP hNP

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fnfF_fsfF_rel_eqF_zero
    [HasPNfun p α] [HasFPmode]
    {P NP : proc p α} :
    fnfF_fsfF_rel 0 P NP →
      eqFfix (P |. 0) NP

axiom cspF_fnfF_fsfF_rel_eqF_notin
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {P NP : proc p α} :
    ¬ fsfF_proc P →
      fnfF_fsfF_rel n P NP →
        eqFfix (P |. n) NP

axiom cspF_fnfF_fsfF_rel_eqF_in
    [HasPNfun p α] [HasFPmode]
    {SP : proc p α} :
    fsfF_proc SP →
      ∀ n : Nat, ∀ NP : proc p α, fnfF_fsfF_rel n SP NP → eqFfix (SP |. n) NP

theorem cspF_fnfF_fsfF_rel_eqF
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {SP NP : proc p α} :
    fnfF_fsfF_rel n SP NP →
      eqFfix (SP |. n) NP := by
  intro hNP
  by_cases hSP : fsfF_proc SP
  · exact cspF_fnfF_fsfF_rel_eqF_in (SP := SP) hSP n NP hNP
  · exact cspF_fnfF_fsfF_rel_eqF_notin (n := n) (P := SP) (NP := NP) hSP hNP

/-
(*************************************************************
                  relation --> function
 *************************************************************)
-/

theorem fnfF_fsfF_in_rel
    {n : Nat} {SP : proc p α} :
    fnfF_fsfF_rel n SP (fnfF_fsfF n SP) :=
  Classical.choose_spec (fnfF_fsfF_rel_exists_ax n SP)

theorem fnfF_fsfF_from_rel
    {n : Nat} {SP NP : proc p α} :
    fnfF_fsfF_rel n SP NP ↔ fnfF_fsfF n SP = NP := by
  constructor
  · intro hNP
    exact fnfF_fsfF_rel_unique (n := n) (SP := SP)
      (NP1 := fnfF_fsfF n SP) (NP2 := NP) fnfF_fsfF_in_rel hNP
  · intro hNP
    subst hNP
    exact fnfF_fsfF_in_rel

theorem fnfF_fsfF_to_rel
    {n : Nat} {SP NP : proc p α} :
    fnfF_fsfF n SP = NP ↔ fnfF_fsfF_rel n SP NP := by
  constructor
  · intro hNP
    subst hNP
    exact fnfF_fsfF_in_rel (n := n) (SP := SP)
  · intro hNP
    exact (fnfF_fsfF_from_rel (n := n) (SP := SP) (NP := NP)).1 hNP

/-
(*************************************************************
                          function
 *************************************************************)
-/

theorem fnfF_fsfF_zero
    (SP : proc p α) :
    fnfF_fsfF 0 SP = NDIV :=
  (fnfF_fsfF_from_rel (n := 0) (SP := SP) (NP := NDIV)).1 fnfF_fsfF_rel.zero

theorem fnfF_fsfF_etc
    {n : Nat} {P : proc p α} :
    ¬ fsfF_proc P →
      fnfF_fsfF (Nat.succ n) P = P |. Nat.succ n := by
  intro hP
  exact (fnfF_fsfF_from_rel
      (n := Nat.succ n)
      (SP := P)
      (NP := P |. Nat.succ n)).1
    (fnfF_fsfF_rel.etc hP)

axiom fnfF_fsfF_int
    {n : Nat}
    {C : sets_nats α}
    {SPf : aset_anat α → proc p α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
        fnfF_fsfF (Nat.succ n) (proc.Rep_int_choice C SPf) =
          fnfF_Rep_int_choice (Nat.succ n) C
            (fun c =>
              if c ∈ sumset C
              then fnfF_fsfF (Nat.succ n) (SPf c)
              else proc.DIV)

axiom fnfF_fsfF_step
    {n : Nat}
    {A : Set α}
    {SPf : α → proc p α}
    {Q : proc p α} :
    (∀ a, a ∈ A → fsfF_proc (SPf a)) →
      (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
        fnfF_fsfF (Nat.succ n) ((proc.Ext_pre_choice A SPf) [+] Q) =
          (((proc.Ext_pre_choice A
              (fun a =>
                if a ∈ A then fnfF_fsfF n (SPf a) else proc.DIV)) [+]
            (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
            Rep_int_choice_set
              (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
              (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))

/- The Isabelle theorem bundle `fnfF_fsfF` is represented by
   `fnfF_fsfF_etc`, `fnfF_fsfF_int`, and `fnfF_fsfF_step`. -/

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fnfF_fsfF_in
    {n : Nat} {SP : proc p α} :
    fsfF_proc SP →
      fnfF_proc (fnfF_fsfF n SP) := by
  intro hSP
  exact fnfF_fsfF_rel_in (n := n) (SP := SP) (NP := fnfF_fsfF n SP)
    hSP (fnfF_fsfF_in_rel (n := n) (SP := SP))

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fnfF_fsfF_eqF
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {SP : proc p α} :
    eqFfix (SP |. n) (fnfF_fsfF n SP) :=
  cspF_fnfF_fsfF_rel_eqF (n := n) (SP := SP) (NP := fnfF_fsfF n SP)
    (fnfF_fsfF_in_rel (n := n) (SP := SP))

/- *===============================================================*
   theorem --- fnfF P is a (restricted) full normal form ---
 *===============================================================* -/

theorem fnfF_in [Inhabited α] [HasPNfun p α]
    {n : Nat} {P : proc p α} :
    fnfF_proc (fnfF n P) := by
  rw [fnfF_def]
  exact fnfF_fsfF_in (n := n) (SP := fsfF P) (fsfF_in (P := P))

/- *===============================================================*
        theorem --- fnfF P is equal to P based on F ---
 *===============================================================* -/

axiom cspF_fnfF_eqF [Inhabited α] [HasPNfun p α] [HasFPmode]
    {n : Nat} {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix (P |. n) (fnfF n P)

/- *------------------------*
 |     auxiliary laws     |
 *------------------------* -/

axiom cspF_fnfF_eqF_Depth_rest [Inhabited α] [HasPNfun p α] [HasFPmode]
    {n : Nat} {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix ((fnfF n P) |. n) (fnfF n P)

/- *===============================================================*
          theorem --- XfnfF P is a full normal form ---
 *===============================================================* -/

axiom XfnfF_in [Inhabited α] [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      XfnfF P ∈ XfnfF_proc (p := p) (α := α)

/- *===============================================================*
          theorem --- XfnfF P is equal to P based on F ---
 *===============================================================* -/

axiom cspF_XfnfF_eqF [Inhabited α] [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix P (XfnfF P)

/- (****************** to add them again ******************) -/

/- Lean has no direct analogue of Isabelle's local `declare if_split [split]`
   or `declare disj_not1 [simp]` commands. -/

end
