           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_norm
import LeanCspProver.CSP_F.CSP_F_simp

open Function
open SumType

noncomputable section

/-
(*********************************************************
                       ?-div
 *********************************************************)
-/

/- Isabelle: `? :A -> Pf =F[M,M] (? :A -> Pf [+] DIV) |~| ? a:A -> DIV`.
   `? :_ -> _` has precedence 80 and binds its body at 80, while `[+]` has
   precedence 72, so `? :A -> Pf [+] DIV` parses as `(? :A -> Pf) [+] DIV`.
   The port originally pushed `[+] DIV` inside the prefix choice; that reading
   is equal in the traces model but *false* in the stable-failures model
   (take `A = {a}`, `Pf = %_. STOP`: `(<Ev a>, {})` is a failure of the
   left-hand side but of neither summand on the right). -/
axiom cspF_input_DIV
    {A : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice A Pf) M M
      (((proc.Ext_pre_choice A Pf) [+] (proc.DIV : proc p α)) |~|
        proc.Ext_pre_choice A (fun _ => (proc.DIV : proc p α)))

/-
(*********************************************************
                    !!-!set-div
 *********************************************************)
-/

theorem cspF_Rep_int_choice_sum_set_Ext_pre_choice_DIV
    {C : sets_nats α} {Xsf : aset_anat α → Set (Set α)}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF
      (proc.Rep_int_choice C (fun c =>
        Rep_int_choice_set (Xsf c)
          (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α)))))
      M1 M2
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ c, c ∈ sumset C ∧ Xs = Xsf c})
        (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc q α)))) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_set_Ext_pre_choice_DIV
    {Ys : Set (Set α)} {Xsf : Set α → Set (Set α)}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF
      (Rep_int_choice_set Ys (fun Y =>
        Rep_int_choice_set (Xsf Y)
          (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α)))))
      M1 M2
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ Y, Y ∈ Ys ∧ Xs = Xsf Y})
        (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc q α)))) := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_set_Ext_pre_choice_DIV
    {N : Set Nat} {Xsf : Nat → Set (Set α)}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF
      (Rep_int_choice_nat N (fun n =>
        Rep_int_choice_set (Xsf n)
          (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α)))))
      M1 M2
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ n, n ∈ N ∧ Xs = Xsf n})
        (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc q α)))) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_set_Ext_pre_choice_DIV`
   is represented by `cspF_Rep_int_choice_sum_set_Ext_pre_choice_DIV`,
   `cspF_Rep_int_choice_set_set_Ext_pre_choice_DIV`, and
   `cspF_Rep_int_choice_nat_set_Ext_pre_choice_DIV`. -/

/-
(*********************************************************
                      ?-!set-<=
 *********************************************************)
-/

theorem cspF_input_Rep_int_choice_set_subset
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {Xs Ys : Set (Set α)} {M : p → domFType α}
    (hXY : Xs ⊆ Ys)
    (hYA : ∀ Y, Y ∈ Ys → ∃ X, X ∈ Xs ∧ X ⊆ Y ∧ Y ⊆ A) :
    eqF
      (((proc.Ext_pre_choice A Pf) [+] Q) |~|
        Rep_int_choice_set Xs (fun X => proc.Ext_pre_choice X (fun _ => (proc.DIV : proc p α))))
      M M
      (((proc.Ext_pre_choice A Pf) [+] Q) |~|
        Rep_int_choice_set Ys
          (fun Y => proc.Ext_pre_choice Y (fun _ => (proc.DIV : proc p α)))) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_norm` is represented by
   `cspF_input_DIV`, `cspF_Rep_int_choice_sum_set_Ext_pre_choice_DIV`,
   `cspF_Rep_int_choice_set_set_Ext_pre_choice_DIV`,
   `cspF_Rep_int_choice_nat_set_Ext_pre_choice_DIV`, and
   `cspF_input_Rep_int_choice_set_subset`. -/
