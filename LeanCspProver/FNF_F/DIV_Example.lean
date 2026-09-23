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

theorem ALL_Count_DIV :
    ∀ n m,
      eqFfix (((fun Qf => Count <<< Qf)^[n]) (fun _ => (proc.DIV : proc Nat Nat)) m)
        proc.DIV := by
  intro n
  induction n with
  | zero =>
      intro m
      exact cspF_reflex_eq_P
  | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply']
      change eqFfix
        (proc.Hiding
          ((m : Nat) ~>
            (((fun Qf => Count <<< Qf)^[n]) (fun _ => (proc.DIV : proc Nat Nat)) (Nat.succ m)))
          ({m} : Set Nat))
        proc.DIV
      -- replace the recursive call by DIV using the induction hypothesis
      have h1 : eqFfix
          (proc.Hiding
            ((m : Nat) ~>
              (((fun Qf => Count <<< Qf)^[n])
                (fun _ => (proc.DIV : proc Nat Nat)) (Nat.succ m)))
            ({m} : Set Nat))
          (proc.Hiding ((m : Nat) ~> (proc.DIV : proc Nat Nat)) ({m} : Set Nat)) :=
        cspF_Hiding_cong rfl (cspF_Act_prefix_cong rfl (ih (Nat.succ m)))
      -- m ~> DIV  =F  ? x:{m} -> DIV
      have h2 : eqFfix
          (proc.Hiding ((m : Nat) ~> (proc.DIV : proc Nat Nat)) ({m} : Set Nat))
          (proc.Hiding
            (proc.Ext_pre_choice ({m} : Set Nat) (fun _ => (proc.DIV : proc Nat Nat)))
            ({m} : Set Nat)) :=
        cspF_Hiding_cong rfl cspF_Act_prefix_step
      -- hide the only offered event
      have h3 : eqFfix
          (proc.Hiding
            (proc.Ext_pre_choice ({m} : Set Nat) (fun _ => (proc.DIV : proc Nat Nat)))
            ({m} : Set Nat))
          ((proc.Ext_pre_choice (∅ : Set Nat)
              (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat)))
            [> Rep_int_choice_com ({m} : Set Nat)
                (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat))) := by
        have h := cspF_Hiding_step (X := ({m} : Set Nat)) (Y := ({m} : Set Nat))
          (Pf := fun _ => (proc.DIV : proc Nat Nat)) (M := MF)
        rwa [procIte_neg (by simp), Set.diff_self, Set.inter_self] at h
      -- ? x:∅ -> ...  =F  STOP,  and  STOP [> P  =F  P
      have h4 : eqFfix
          ((proc.Ext_pre_choice (∅ : Set Nat)
              (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat)))
            [> Rep_int_choice_com ({m} : Set Nat)
                (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat)))
          ((proc.STOP : proc Nat Nat)
            [> Rep_int_choice_com ({m} : Set Nat)
                (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat))) :=
        cspF_Timeout_cong (cspF_sym cspF_STOP_step) cspF_reflex_eq_P
      have h5 : eqFfix
          ((proc.STOP : proc Nat Nat)
            [> Rep_int_choice_com ({m} : Set Nat)
                (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat)))
          (Rep_int_choice_com ({m} : Set Nat)
            (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat))) :=
        cspF_STOP_Timeout
      -- collapse the singleton internal choice and hide DIV
      have h6 : eqFfix
          (Rep_int_choice_com ({m} : Set Nat)
            (fun _ => proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat)))
          (proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat)) :=
        cspF_Rep_int_choice_com_unit (by simp)
      have h7 : eqFfix
          (proc.Hiding (proc.DIV : proc Nat Nat) ({m} : Set Nat))
          (proc.DIV : proc Nat Nat) :=
        cspF_DIV_Hiding_Id
      exact cspF_trans_left_eq h1 (cspF_trans_left_eq h2 (cspF_trans_left_eq h3
        (cspF_trans_left_eq h4 (cspF_trans_left_eq h5 (cspF_trans_left_eq h6 h7)))))

theorem Count_DIV (n m : Nat) :
    eqFfix (((fun Qf => Count <<< Qf)^[n]) (fun _ => (proc.DIV : proc Nat Nat)) m) proc.DIV :=
  ALL_Count_DIV n m

private theorem FIX_Count_app :
    FIX Count 0 = Rep_int_choice_nat Set.univ (fun n => FIXn n Count 0) :=
  rfl

theorem CountFIX_DIV :
    eqFfix (FIX Count 0)
      (Rep_int_choice_nat Set.univ (fun _ => (proc.DIV : proc Nat Nat))) := by
  rw [FIX_Count_app]
  exact cspF_Rep_int_choice_cong_nat rfl (fun n _ => ALL_Count_DIV n 0)

/- (*** full normalising ***) -/

theorem CountFIX_DIV_Xnorm :
    eqFfix (FIX Count 0)
      (Rep_int_choice_nat Set.univ (fun _ => (NDIV (p := Nat) (α := Nat)))) :=
  cspF_trans_left_eq CountFIX_DIV
    (cspF_Rep_int_choice_cong_nat rfl (fun _ _ => cspF_NDIV_eqF))

/- (*** in extended full normal form ***) -/

theorem DIV_Xnorm_in :
    Rep_int_choice_nat Set.univ (fun _ => (NDIV (p := Nat) (α := Nat))) ∈
      XfnfF_proc (p := Nat) (α := Nat) := by
  refine ⟨fun _ => NDIV, rfl, ?_, fun _ => fnfF_NDIV⟩
  intro n
  -- (!nat k:univ .. NDIV) |. n  =F  NDIV
  have h1 : eqFfix
      ((Rep_int_choice_nat Set.univ (fun _ => (NDIV : proc Nat Nat))) |. n)
      (Rep_int_choice_nat Set.univ (fun _ => ((NDIV : proc Nat Nat) |. n))) :=
    cspF_Depth_rest_Dist_nat
  have h2 : eqFfix
      (Rep_int_choice_nat Set.univ (fun _ => ((NDIV : proc Nat Nat) |. n)))
      ((NDIV : proc Nat Nat) |. n) :=
    cspF_Rep_int_choice_nat_unit (by simp)
  have h3 : eqFfix ((NDIV : proc Nat Nat) |. n) ((proc.DIV : proc Nat Nat) |. n) :=
    cspF_Depth_rest_cong rfl (cspF_sym cspF_NDIV_eqF)
  have h4 : eqFfix ((proc.DIV : proc Nat Nat) |. n) (proc.DIV : proc Nat Nat) :=
    cspF_DIV_Depth_rest
  have h5 : eqFfix (proc.DIV : proc Nat Nat) (NDIV : proc Nat Nat) :=
    cspF_NDIV_eqF
  exact cspF_sym (cspF_trans_left_eq h1 (cspF_trans_left_eq h2
    (cspF_trans_left_eq h3 (cspF_trans_left_eq h4 h5))))

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
