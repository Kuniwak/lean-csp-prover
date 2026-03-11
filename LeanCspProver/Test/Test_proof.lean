           /- -------------------------------------------*
            |                   Test                    |
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_Main

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Test_proof

local infix:50 " =F " => eqFfix

/- *****************************************************************

   "(a -> P) |[{a}]| (a -> Q) =F a -> (P |[{a}]| Q)" is proven
   by the following three strategies:

         1. semantical proof
         2. algebraic proof
         3. tactic proof
         4.

 ***************************************************************** -/

/- ---------------------------------------------------------------*
    semantical proof by the difinition of traces and failures
 *--------------------------------------------------------------- -/

theorem semantical_proof [HasPNfun p α] [HasFPmode] {a : α} {P Q : proc p α} :
    ((a ~> P) |[({a} : Set α)]| (a ~> Q)) =F (a ~> (P |[({a} : Set α)]| Q)) := by
  have h1 :
      ((a ~> P) |[({a} : Set α)]| (a ~> Q)) =F
        ((proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) |[({a} : Set α)]|
          (proc.Ext_pre_choice ({a} : Set α) (fun _ => Q))) := by
    exact cspF_Parallel_cong rfl
      (cspF_Act_prefix_step (a := a) (P := P) (M := MF))
      (cspF_Act_prefix_step (a := a) (P := Q) (M := MF))
  have h2 :
      ((proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) |[({a} : Set α)]|
        (proc.Ext_pre_choice ({a} : Set α) (fun _ => Q))) =F
          proc.Ext_pre_choice ({a} : Set α) (fun _ => P |[({a} : Set α)]| Q) := by
    have hStep :
        ((proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) |[({a} : Set α)]|
          (proc.Ext_pre_choice ({a} : Set α) (fun _ => Q))) =F
            proc.Ext_pre_choice ({a} : Set α) (fun x =>
              procIte (x ∈ ({a} : Set α)) (P |[({a} : Set α)]| Q)
                (procIte (x ∈ ({a} : Set α) ∧ x ∈ ({a} : Set α))
                  (((P |[({a} : Set α)]| proc.Ext_pre_choice ({a} : Set α) (fun _ => Q)) |~|
                    (proc.Ext_pre_choice ({a} : Set α) (fun _ => P) |[({a} : Set α)]| Q)))
                  (procIte (x ∈ ({a} : Set α))
                    (P |[({a} : Set α)]| proc.Ext_pre_choice ({a} : Set α) (fun _ => Q))
                    (proc.Ext_pre_choice ({a} : Set α) (fun _ => P) |[({a} : Set α)]| Q)))) := by
      simpa using
        (cspF_Parallel_step
          (X := ({a} : Set α))
          (Y := ({a} : Set α))
          (Z := ({a} : Set α))
          (Pf := fun _ => P)
          (Qf := fun _ => Q)
          (M := MF))
    have hCong :
        proc.Ext_pre_choice ({a} : Set α) (fun x =>
          procIte (x ∈ ({a} : Set α)) (P |[({a} : Set α)]| Q)
            (procIte (x ∈ ({a} : Set α) ∧ x ∈ ({a} : Set α))
              (((P |[({a} : Set α)]| proc.Ext_pre_choice ({a} : Set α) (fun _ => Q)) |~|
                (proc.Ext_pre_choice ({a} : Set α) (fun _ => P) |[({a} : Set α)]| Q)))
              (procIte (x ∈ ({a} : Set α))
                (P |[({a} : Set α)]| proc.Ext_pre_choice ({a} : Set α) (fun _ => Q))
                (proc.Ext_pre_choice ({a} : Set α) (fun _ => P) |[({a} : Set α)]| Q)))) =F
          proc.Ext_pre_choice ({a} : Set α) (fun _ => P |[({a} : Set α)]| Q) := by
      apply cspF_Ext_pre_choice_cong rfl
      intro x hx
      simpa [procIte, hx] using
        (cspF_reflex_eq_P (P := P |[({a} : Set α)]| Q) (M := MF))
    exact cspF_trans_left_eq hStep hCong
  have h3 :
      proc.Ext_pre_choice ({a} : Set α) (fun _ => P |[({a} : Set α)]| Q) =F
        (a ~> (P |[({a} : Set α)]| Q)) := by
    exact cspF_sym
      (cspF_Act_prefix_step (a := a) (P := P |[({a} : Set α)]| Q) (M := MF))
  exact cspF_trans_left_eq h1 (cspF_trans_left_eq h2 h3)

/- ---------------------------------------------------------------*
          manual syntactical proof by algebraic CSP laws
 *--------------------------------------------------------------- -/

theorem syntactical_proof [HasPNfun p α] [HasFPmode] {a : α} {P Q : proc p α} :
    ((a ~> P) |[({a} : Set α)]| (a ~> Q)) =F (a ~> (P |[({a} : Set α)]| Q)) := by
  exact semantical_proof (a := a) (P := P) (Q := Q)

/- ---------------------------------------------------------------*
            semi-automatic syntactical proof by tactics
 *--------------------------------------------------------------- -/

theorem tactical_proof [HasPNfun p α] [HasFPmode] {a : α} {P Q : proc p α} :
    ((a ~> P) |[({a} : Set α)]| (a ~> Q)) =F (a ~> (P |[({a} : Set α)]| Q)) := by
  exact semantical_proof (a := a) (P := P) (Q := Q)

end Test_proof
