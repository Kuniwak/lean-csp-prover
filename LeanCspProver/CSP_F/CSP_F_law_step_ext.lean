           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               December 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_step_ext

open Function
open SumType
open event

noncomputable section

/-
(*****************************************************************

         1. step laws
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(*********************************************************
              (P1 [> P2) |[X]| (Q1 [> Q2)
 *********************************************************)
-/

/- The following law in p.288 does not hold.                               -/
/-     (P1 [> P2) |[X]| (Q1 [> Q2)                                         -/
/-  =F (P1 |[X]| Q1) [> ((P2 |[X]| (Q1 [> Q2)) |~| ((P1 [> P2) |[X]| Q2))  -/
/-                                                                         -/
/- a counter example:                                                      -/
/-  P1 = a -> STOP, P2 = STOP, Q1 = STOP, Q2 = b -> STOP, X = {}           -/
/-  where (a ~= b)                                                         -/
/-                                                                         -/
/-  check the following lemmas                                             -/

/- Isabelle's anonymous lemmas are given explicit Lean names below. -/

axiom cspF_Parallel_Timeout_counterexample_notin_failures
    {a b : α} {M : p → domFType α} :
    a ≠ b →
      (Abs_trace [event.Ev a], {event.Ev b}) ~:f
        failures
          ((Timeout (a ~> proc.STOP) proc.STOP) |[({} : Set α)]|
            (Timeout proc.STOP (b ~> proc.STOP)))
          M

axiom cspF_Parallel_Timeout_counterexample_in_failures
    {a b : α} {X : Set α} {M : p → domFType α} :
    (Abs_trace [event.Ev a], {event.Ev b}) :f
      (failures
        (Timeout
          ((a ~> proc.STOP) |[({} : Set α)]| proc.STOP)
          ((proc.STOP |[({} : Set α)]| Timeout proc.STOP (b ~> proc.STOP)) |~|
            ((Timeout (a ~> proc.STOP) proc.STOP) |[X]| (b ~> proc.STOP))))
        M)

/-
(*********************************************************
              (P [> Q) |[X]| (? :Y -> Rf)
 *********************************************************)
-/

/- The following law in p.289 does not hold.                               -/
/-                                                                         -/
/-     (P [> Q) |[X]| (? :Y -> Rf) =F[M,M]                                 -/
/-     (? x:(Y - X) -> ((P [> Q) |[X]| Rf x))                              -/
/-     [+] ((P |[X]| (? :Y -> Rf)) [> (Q |[X]| (? :Y -> Rf)))              -/
/-                                                                         -/
/- a counter example:                                                      -/
/-  P = STOP, Q = b -> STOP, Y = {a}, Rf = (%x. STOP), X = {}              -/
/-  where (a ~= b)                                                         -/
/-                                                                         -/
/-  check the following lemmas                                             -/

axiom cspF_Timeout_Parallel_input_counterexample_notin_failures
    {a b : α} {M : p → domFType α} :
    a ≠ b →
      (Abs_trace [event.Ev a], {event.Ev b}) ~:f
        failures
          ((Timeout proc.STOP (b ~> proc.STOP)) |[({} : Set α)]|
            (proc.Ext_pre_choice ({a} : Set α) (fun _ => proc.STOP)))
          M

axiom cspF_Timeout_Parallel_input_counterexample_in_failures
    {a b : α} {M : p → domFType α} :
    a ≠ b →
      (Abs_trace [event.Ev a], {event.Ev b}) :f
        (failures
          ((proc.Ext_pre_choice (({a} : Set α) \ ({} : Set α))
            (fun _ => (Timeout proc.STOP (b ~> proc.STOP) |[({} : Set α)]| proc.STOP))) [+]
            (Timeout
              (proc.STOP |[({} : Set α)]| proc.Ext_pre_choice ({a} : Set α) (fun _ => proc.STOP))
              ((b ~> proc.STOP) |[({} : Set α)]|
                proc.Ext_pre_choice ({a} : Set α) (fun _ => proc.STOP))))
          M)

/-
(*********************************************************
              Parallel expansion & distribbution
 *********************************************************)
-/

axiom cspF_Parallel_Timeout_split
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P Q : proc p α} {M : p → domFType α} :
    eqF ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]|
      (Timeout (proc.Ext_pre_choice Z Qf) Q)) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q)
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))))
        ((P |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
          ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Q)))

/-
(*********************************************************
            Parallel expansion & distribbution 2
 *********************************************************)
-/

/- (*** left ****) -/

axiom cspF_Parallel_Timeout_input_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| proc.Ext_pre_choice Z Qf) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| proc.Ext_pre_choice Z Qf)
                ((Timeout (proc.Ext_pre_choice Y Pf) P) |[X]| Qf x))))
        (P |[X]| proc.Ext_pre_choice Z Qf))

/- (*** right ****) -/

axiom cspF_Parallel_Timeout_input_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice Y Pf |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) M M
      (Timeout
        (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
          procIte (x ∈ X) (Pf x |[X]| Qf x)
            (procIte (x ∈ Y ∧ x ∈ Z)
              ((Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q) |~|
                (proc.Ext_pre_choice Y Pf |[X]| Qf x))
              (procIte (x ∈ Y)
                (Pf x |[X]| Timeout (proc.Ext_pre_choice Z Qf) Q)
                (proc.Ext_pre_choice Y Pf |[X]| Qf x))))
        (proc.Ext_pre_choice Y Pf |[X]| Q))

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_input` is
   represented by `cspF_Parallel_Timeout_input_l` and
   `cspF_Parallel_Timeout_input_r`. -/

/-
(*** cspF_step_ext ***)
-/

/- The Isabelle theorem bundle `cspF_step_ext` is represented by
   `cspF_Parallel_Timeout_split`, `cspF_Parallel_Timeout_input_l`, and
   `cspF_Parallel_Timeout_input_r`. -/
