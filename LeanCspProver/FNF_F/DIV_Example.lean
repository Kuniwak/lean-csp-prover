           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F

open Function
open SumType
open fpmode

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DIV_Example

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

         1.
         2.
         3.

 *****************************************************************)
-/

def Count : Nat → proc Nat Nat
  | n => proc.Hiding (n ~> proc.Proc_name (Nat.succ n)) ({n} : Set Nat)

section

local instance : HasPNfun Nat Nat where
  PNfun := Count

local instance : HasFPmode where
  FPmode := CPOmode

axiom ALL_Count_DIV :
    ∀ n m, eqFfix (((fun Qf => Count <<< Qf)^[n]) (fun _ => (proc.DIV : proc Nat Nat)) m) proc.DIV

theorem Count_DIV (n m : Nat) :
    eqFfix (((fun Qf => Count <<< Qf)^[n]) (fun _ => (proc.DIV : proc Nat Nat)) m) proc.DIV :=
  ALL_Count_DIV n m

axiom CountFIX_DIV :
    eqFfix (FIX Count 0)
      (Rep_int_choice_nat Set.univ (fun _ => (proc.DIV : proc Nat Nat)))

/- (*** full normalising ***) -/

axiom CountFIX_DIV_Xnorm :
    eqFfix (FIX Count 0)
      (Rep_int_choice_nat Set.univ (fun _ => (NDIV (p := Nat) (α := Nat))))

/- (*** in extended full normal form ***) -/

axiom DIV_Xnorm_in :
    Rep_int_choice_nat Set.univ (fun _ => (NDIV (p := Nat) (α := Nat))) ∈
      XfnfF_proc (p := Nat) (α := Nat)

/- (*** unwinding test ***) -/

theorem Count_nat_eq (n : Nat) :
    eqFfix (proc.Proc_name n : proc Nat Nat) (FIX Count n) := by
  have hmode :
      FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Count) ∨ FPmode = MIXmode := by
    simp [FPmode]
  simpa [eqFfix] using (cspF_FIX (Pf := Count) (p0 := n) hmode rfl)

theorem CountFIX_DIV_unwinding_test (n : Nat) :
    eqFfix (proc.Proc_name n : proc Nat Nat)
      (proc.Hiding (n ~> proc.Proc_name (Nat.succ n)) ({n} : Set Nat)) := by
  simpa [eqFfix, Count] using
    (cspF_unwind_cpo (Pf := Count) (p0 := n) rfl (Or.inl rfl))

end

/- (****************** to add them again ******************) -/

/-  Lean has no direct analogue of Isabelle's `declare if_split [split]` -/
/-  and `declare disj_not1 [simp]`, so there is nothing to re-enable.   -/

end DIV_Example
