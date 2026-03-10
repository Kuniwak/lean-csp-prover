           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                January 2006  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_decompo
import LeanCspProver.CSP_T.CSP_T_law_basic

open Function
open SumType

noncomputable section

/-
(*****************************************************************

         1. Commutativity
         2. Associativity
         3. Idempotence
         4. Left Commutativity
         5. IF

 *****************************************************************)
-/

/-
(*********************************************************
                       IF bool
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_IF_split
    {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    eqF (IF b THEN P ELSE Q) M M (if b then P else Q)

axiom cspF_IF_True
    {P Q : proc p α} {M : p → domFType α} :
    eqF (IF True THEN P ELSE Q) M M P

axiom cspF_IF_False
    {P Q : proc p α} {M : p → domFType α} :
    eqF (IF False THEN P ELSE Q) M M Q

/- The Isabelle theorem bundle `cspF_IF` is represented by
   `cspF_IF_True` and `cspF_IF_False`. -/

/- -----------------------------------*
 |           Idempotence             |
 *----------------------------------- -/

axiom cspF_Ext_choice_idem
    {P : proc p α} {M : p → domFType α} :
    eqF (P [+] P) M M P

axiom cspF_Int_choice_idem
    {P : proc p α} {M : p → domFType α} :
    eqF (P |~| P) M M P

/- The Isabelle theorem bundle `cspF_idem` is represented by
   `cspF_Ext_choice_idem` and `cspF_Int_choice_idem`. -/

/- -----------------------------------*
 |          Commutativity            |
 *----------------------------------- -/

/-
(*********************************************************
                      Ext choice
 *********************************************************)
-/

axiom cspF_Ext_choice_commut
    {P Q : proc p α} {M : p → domFType α} :
    eqF (P [+] Q) M M (Q [+] P)

/-
(*********************************************************
                      Int choice
 *********************************************************)
-/

axiom cspF_Int_choice_commut
    {P Q : proc p α} {M : p → domFType α} :
    eqF (P |~| Q) M M (Q |~| P)

/-
(*********************************************************
                      Parallel
 *********************************************************)
-/

axiom cspF_Parallel_commut
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Q) M M (Q |[X]| P)

/- The Isabelle theorem bundle `cspF_commut` is represented by
   `cspF_Ext_choice_commut`, `cspF_Int_choice_commut`, and
   `cspF_Parallel_commut`. -/

/- -----------------------------------*
 |          Associativity            |
 *----------------------------------- -/

axiom cspF_Ext_choice_assoc
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P [+] (Q [+] R)) M M ((P [+] Q) [+] R)

axiom cspF_Ext_choice_assoc_sym
    {P Q R : proc p α} {M : p → domFType α} :
    eqF ((P [+] Q) [+] R) M M (P [+] (Q [+] R))

axiom cspF_Int_choice_assoc
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P |~| (Q |~| R)) M M ((P |~| Q) |~| R)

axiom cspF_Int_choice_assoc_sym
    {P Q R : proc p α} {M : p → domFType α} :
    eqF ((P |~| Q) |~| R) M M (P |~| (Q |~| R))

/- The Isabelle theorem bundle `cspF_assoc` is represented by
   `cspF_Ext_choice_assoc` and `cspF_Int_choice_assoc`. -/

/- The Isabelle theorem bundle `cspF_assoc_sym` is represented by
   `cspF_Ext_choice_assoc_sym` and `cspF_Int_choice_assoc_sym`. -/

/- -----------------------------------*
 |        Left Commutativity         |
 *----------------------------------- -/

axiom cspF_Ext_choice_left_commut
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P [+] (Q [+] R)) M M (Q [+] (P [+] R))

axiom cspF_Int_choice_left_commut
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P |~| (Q |~| R)) M M (Q |~| (P |~| R))

/- The Isabelle theorem bundle `cspF_left_commut` is represented by
   `cspF_Ext_choice_left_commut` and `cspF_Int_choice_left_commut`. -/

/- -----------------------------------*
 |              Unit                 |
 *----------------------------------- -/

/-
(*** STOP [+] P ***)
-/

axiom cspF_Ext_choice_unit_l
    {P : proc p α} {M : p → domFType α} :
    eqF (proc.STOP [+] P) M M P

axiom cspF_Ext_choice_unit_r
    {P : proc p α} {M : p → domFType α} :
    eqF (P [+] proc.STOP) M M P

/- The Isabelle theorem bundle `cspF_Ext_choice_unit` is represented by
   `cspF_Ext_choice_unit_l` and `cspF_Ext_choice_unit_r`. -/

axiom cspF_Int_choice_unit_l
    {P : proc p α} {M : p → domFType α} :
    eqF (proc.DIV |~| P) M M P

axiom cspF_Int_choice_unit_r
    {P : proc p α} {M : p → domFType α} :
    eqF (P |~| proc.DIV) M M P

/- The Isabelle theorem bundle `cspF_Int_choice_unit` is represented by
   `cspF_Int_choice_unit_l` and `cspF_Int_choice_unit_r`. -/

/- The Isabelle theorem bundle `cspF_unit` is represented by
   `cspF_Ext_choice_unit` and `cspF_Int_choice_unit`. -/

/- -----------------------------------*
 |           !!-empty                |
 *----------------------------------- -/

axiom cspF_Rep_int_choice_sum_DIV
    {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C = ∅ → eqF (proc.Rep_int_choice C Pf) M1 M2 (proc.DIV : proc q α)

axiom cspF_Rep_int_choice_nat_DIV
    {Pf : Nat → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_nat (∅ : Set Nat) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspF_Rep_int_choice_set_DIV
    {Pf : Set α → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_set (∅ : Set (Set α)) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspF_Rep_int_choice_com_DIV [Inhabited α]
    {Pf : α → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_com (∅ : Set α) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspF_Rep_int_choice_f_DIV [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Pf : β → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_f f (∅ : Set β) Pf) M1 M2 (proc.DIV : proc q α)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_DIV` is represented by
   `cspF_Rep_int_choice_sum_DIV`, `cspF_Rep_int_choice_nat_DIV`,
   `cspF_Rep_int_choice_set_DIV`, `cspF_Rep_int_choice_com_DIV`, and
   `cspF_Rep_int_choice_f_DIV`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_DIV_sym` is represented by
   `cspF_Rep_int_choice_DIV` together with `cspF_sym`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_empty` is represented by
   `cspF_Rep_int_choice_DIV`. -/

axiom cspF_DIV_top [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    refFfix P proc.DIV

/- -----------------------------------*
 |             !!-unit               |
 *----------------------------------- -/

axiom cspF_Rep_int_choice_sum_unit
    {C : sets_nats α} {P : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ → eqF (proc.Rep_int_choice C (fun _ => P)) M M P

axiom cspF_Rep_int_choice_nat_unit
    {N : Set Nat} {P : proc p α} {M : p → domFType α} :
    N ≠ ∅ → eqF (Rep_int_choice_nat N (fun _ => P)) M M P

axiom cspF_Rep_int_choice_set_unit
    {Xs : Set (Set α)} {P : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (Rep_int_choice_set Xs (fun _ => P)) M M P

axiom cspF_Rep_int_choice_com_unit [Inhabited α]
    {X : Set α} {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF (Rep_int_choice_com X (fun _ => P)) M M P

axiom cspF_Rep_int_choice_f_unit [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF (Rep_int_choice_f f X (fun _ => P)) M M P

/- The Isabelle theorem bundle `cspF_Rep_int_choice_unit` is represented by
   `cspF_Rep_int_choice_sum_unit`, `cspF_Rep_int_choice_nat_unit`,
   `cspF_Rep_int_choice_set_unit`, `cspF_Rep_int_choice_com_unit`, and
   `cspF_Rep_int_choice_f_unit`. -/

/- -----------------------------------*
 |             !!-const              |
 *----------------------------------- -/

/-
(* const *)
-/

axiom cspF_Rep_int_choice_sum_const
    {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {P : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → Pf c = P) →
        eqF (proc.Rep_int_choice C Pf) M M P

axiom cspF_Rep_int_choice_nat_const
    {N : Set Nat} {Pf : Nat → proc p α}
    {P : proc p α} {M : p → domFType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → Pf n = P) →
        eqF (Rep_int_choice_nat N Pf) M M P

axiom cspF_Rep_int_choice_set_const
    {Xs : Set (Set α)} {Pf : Set α → proc p α}
    {P : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → Pf X = P) →
        eqF (Rep_int_choice_set Xs Pf) M M P

axiom cspF_Rep_int_choice_com_const [Inhabited α]
    {X : Set α} {Pf : α → proc p α}
    {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqF (Rep_int_choice_com X Pf) M M P

axiom cspF_Rep_int_choice_f_const [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α}
    {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqF (Rep_int_choice_f f X Pf) M M P

/- The Isabelle theorem bundle `cspF_Rep_int_choice_const` is represented by
   `cspF_Rep_int_choice_sum_const`, `cspF_Rep_int_choice_nat_const`,
   `cspF_Rep_int_choice_set_const`, `cspF_Rep_int_choice_com_const`, and
   `cspF_Rep_int_choice_f_const`. -/

/- -----------------------------------*
 |           |~|-!!-union            |
 *----------------------------------- -/

axiom cspF_Int_Rep_int_choice_sum_union
    {C1 C2 : sets_nats α} {P1f P2f : aset_anat α → proc p α}
    {M : p → domFType α} :
    C1 =type= C2 →
      eqF
        ((proc.Rep_int_choice C1 P1f) |~| (proc.Rep_int_choice C2 P2f)) M M
        (proc.Rep_int_choice (C1 Uns C2) fun c =>
          procIte (c ∈ sumset C1 ∧ c ∈ sumset C2) (P1f c |~| P2f c)
            (procIte (c ∈ sumset C1) (P1f c) (P2f c)))

axiom cspF_Int_Rep_int_choice_nat_union
    {N1 N2 : Set Nat} {P1f P2f : Nat → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_nat N1 P1f) |~| (Rep_int_choice_nat N2 P2f)) M M
      (Rep_int_choice_nat (N1 ∪ N2) fun n =>
        procIte (n ∈ N1 ∧ n ∈ N2) (P1f n |~| P2f n)
          (procIte (n ∈ N1) (P1f n) (P2f n)))

axiom cspF_Int_Rep_int_choice_set_union
    {Xs1 Xs2 : Set (Set α)} {P1f P2f : Set α → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_set Xs1 P1f) |~| (Rep_int_choice_set Xs2 P2f)) M M
      (Rep_int_choice_set (Xs1 ∪ Xs2) fun X =>
        procIte (X ∈ Xs1 ∧ X ∈ Xs2) (P1f X |~| P2f X)
          (procIte (X ∈ Xs1) (P1f X) (P2f X)))

axiom cspF_Int_Rep_int_choice_com_union [Inhabited α]
    {X1 X2 : Set α} {P1f P2f : α → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_com X1 P1f) |~| (Rep_int_choice_com X2 P2f)) M M
      (Rep_int_choice_com (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a)))

axiom cspF_Int_Rep_int_choice_f_union [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {P1f P2f : β → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_f f X1 P1f) |~| (Rep_int_choice_f f X2 P2f)) M M
      (Rep_int_choice_f f (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a)))

/- The Isabelle theorem bundle `cspF_Int_Rep_int_choice_union` is represented by
   `cspF_Int_Rep_int_choice_sum_union`, `cspF_Int_Rep_int_choice_nat_union`,
   `cspF_Int_Rep_int_choice_set_union`, `cspF_Int_Rep_int_choice_com_union`,
   and `cspF_Int_Rep_int_choice_f_union`. -/

/- -----------------------------------*
 |           !!-union-|~|            |
 *----------------------------------- -/

axiom cspF_Rep_int_choice_sum_union_Int
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domFType α} :
    C1 =type= C2 →
      eqF
        (proc.Rep_int_choice (C1 Uns C2) Pf) M M
        ((proc.Rep_int_choice C1 Pf) |~| (proc.Rep_int_choice C2 Pf))

axiom cspF_Rep_int_choice_nat_union_Int
    {N1 N2 : Set Nat} {Pf : Nat → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf))

axiom cspF_Rep_int_choice_set_union_Int
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs1 Pf) |~| (Rep_int_choice_set Xs2 Pf))

axiom cspF_Rep_int_choice_com_union_Int [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf))

axiom cspF_Rep_int_choice_f_union_Int [Inhabited α] [Inhabited β]
    {f : β → α} {X1 X2 : Set β} {Pf : β → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf))

/- The Isabelle theorem bundle `cspF_Rep_int_choice_union_Int` is represented by
   `cspF_Rep_int_choice_sum_union_Int`,
   `cspF_Rep_int_choice_nat_union_Int`,
   `cspF_Rep_int_choice_set_union_Int`,
   `cspF_Rep_int_choice_com_union_Int`, and
   `cspF_Rep_int_choice_f_union_Int`. -/

/-
(*********************************************************
                     Depth_rest
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Depth_rest_Zero
    {P : proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (P |. 0) M1 M2 (proc.DIV : proc q α)

axiom cspF_Depth_rest_min
    {P : proc p α} {n m : Nat} {M : p → domFType α} :
    eqF ((P |. n) |. m) M M (P |. min n m)

axiom cspF_Depth_rest_congE
    {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {S : Prop} :
    eqF P M1 M2 Q →
      ((∀ m, eqF (P |. m) M1 M2 (Q |. m)) → S) →
        S

axiom cspF_Depth_rest_n
    {P : proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((P |. n) |. n) M M (P |. n)

/- (*------------------*
 |     !nat-rest    |
 *------------------*) -/

axiom cspF_nat_Depth_rest_UNIV
    {P : proc p α} {M : p → domFType α} :
    eqF P M M (Rep_int_choice_nat Set.univ fun n => P |. n)

axiom cspF_nat_Depth_rest_lengthset
    {P : proc p α} {M : p → domFType α} :
    eqF P M M (Rep_int_choice_nat (lengthset P (fstF ∘ M)) fun n => P |. n)

/- The Isabelle theorem bundle `cspF_nat_Depth_rest` is represented by
   `cspF_nat_Depth_rest_UNIV` and `cspF_nat_Depth_rest_lengthset`. -/

/- (*------------------*
 |    ?-partial     |
 *------------------*) -/

axiom cspF_Ext_pre_choice_partial
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice X Pf) M M
      (proc.Ext_pre_choice X fun x => procIte (x ∈ X) (Pf x) proc.DIV)

/- (*------------------*
 |   !!-partial     |
 *------------------*) -/

axiom cspF_Rep_int_choice_sum_partial
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C Pf) M M
      (proc.Rep_int_choice C fun c => procIte (c ∈ sumset C) (Pf c) proc.DIV)

axiom cspF_Rep_int_choice_nat_partial
    {N : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N Pf) M M
      (Rep_int_choice_nat N fun n => procIte (n ∈ N) (Pf n) proc.DIV)

axiom cspF_Rep_int_choice_set_partial
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs Pf) M M
      (Rep_int_choice_set Xs fun X => procIte (X ∈ Xs) (Pf X) proc.DIV)

axiom cspF_Rep_int_choice_com_partial [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X Pf) M M
      (Rep_int_choice_com X fun a => procIte (a ∈ X) (Pf a) proc.DIV)

axiom cspF_Rep_int_choice_f_partial [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f X Pf) M M
      (Rep_int_choice_f f X fun a => procIte (a ∈ X) (Pf a) proc.DIV)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_partial` is represented by
   `cspF_Rep_int_choice_sum_partial`,
   `cspF_Rep_int_choice_nat_partial`,
   `cspF_Rep_int_choice_set_partial`,
   `cspF_Rep_int_choice_com_partial`, and
   `cspF_Rep_int_choice_f_partial`. -/

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)
-/

/-
(* --------------------------------------------------- *
       unfold only the first Sending and Receiving
 * --------------------------------------------------- *)
-/

axiom cspF_first_Send_prefix
    {x : Type _} {a : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    eqF (Send_prefix a v P) M M (a v ~> P)

axiom cspF_first_Rec_prefix
    {x : Type _} [Inhabited x] {a : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    eqF (Rec_prefix a X Pf) M M
      (proc.Ext_pre_choice (a '' X) fun x => Pf (Function.invFun a x))

axiom cspF_first_Int_pre_choice [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Int_pre_choice X Pf) M M
      (Rep_int_choice_com X fun x => x ~> Pf x)

axiom cspF_first_Nondet_send_prefix
    {x : Type _} [Inhabited α] [Inhabited x]
    {a : x → α} {X : Set x} {Pf : x → proc p α} {M : p → domFType α} :
    eqF (Nondet_send_prefix a X Pf) M M
      (Int_pre_choice (a '' X) fun x => Pf (Function.invFun a x))

/- The Isabelle theorem bundle `cspF_first_prefix_ss` is represented by
   `cspF_first_Send_prefix`, `cspF_first_Rec_prefix`,
   `cspF_first_Int_pre_choice`, and `cspF_first_Nondet_send_prefix`. -/

/-
(* --------------------------------------------------- *
      Associativity of Sequential composition
 * --------------------------------------------------- *)
-/

axiom cspF_Seq_compo_assoc
    {P Q R : proc p α} {M : p → domFType α} :
    eqF ((P ;; Q) ;; R) M M (P ;; (Q ;; R))

axiom cspF_Seq_compo_assoc_sym
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P ;; (Q ;; R)) M M ((P ;; Q) ;; R)

/-
(* ---------------------------------------------- *
         decompose right internal choice
 * ---------------------------------------------- *)
-/

axiom cspF_Int_choice_eq_right
    {P : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q1 →
      eqF P M1 M2 Q2 →
        eqF P M1 M2 (Q1 |~| Q2)

/- -------- right -------- -/

axiom cspF_Rep_int_choice_sum_eq_right_ALL
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqF P M1 M2 (Qf c)) →
        eqF P M1 M2 (proc.Rep_int_choice C Qf)

axiom cspF_Rep_int_choice_sum_eq_right
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqF P M1 M2 (Qf c)) →
        eqF P M1 M2 (proc.Rep_int_choice C Qf)

axiom cspF_Rep_int_choice_nat_eq_right
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqF P M1 M2 (Qf n)) →
        eqF P M1 M2 (Rep_int_choice_nat N Qf)

axiom cspF_Rep_int_choice_set_eq_right
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqF P M1 M2 (Qf X)) →
        eqF P M1 M2 (Rep_int_choice_set Xs Qf)

axiom cspF_Rep_int_choice_com_eq_right [Inhabited α]
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF P M1 M2 (Qf a)) →
        eqF P M1 M2 (Rep_int_choice_com X Qf)

axiom cspF_Rep_int_choice_f_eq_right [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF P M1 M2 (Qf a)) →
        eqF P M1 M2 (Rep_int_choice_f f X Qf)

/- The Isabelle theorem bundle `cspF_int_eq_right` is represented by
   `cspF_Rep_int_choice_sum_eq_right`, `cspF_Rep_int_choice_nat_eq_right`,
   `cspF_Rep_int_choice_set_eq_right`, `cspF_Rep_int_choice_com_eq_right`,
   `cspF_Rep_int_choice_f_eq_right`, and `cspF_Int_choice_eq_right`. -/

/- -------- left -------- -/

axiom cspF_Int_choice_eq_left
    {P : proc q α} {Q1 Q2 : proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF Q1 M1 M2 P →
      eqF Q2 M1 M2 P →
        eqF (Q1 |~| Q2) M1 M2 P

axiom cspF_Rep_int_choice_sum_eq_left
    {C : sets_nats α} {P : proc q α} {Qf : aset_anat α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqF (Qf c) M1 M2 P) →
        eqF (proc.Rep_int_choice C Qf) M1 M2 P

axiom cspF_Rep_int_choice_nat_eq_left
    {N : Set Nat} {P : proc q α} {Qf : Nat → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqF (Qf n) M1 M2 P) →
        eqF (Rep_int_choice_nat N Qf) M1 M2 P

axiom cspF_Rep_int_choice_set_eq_left
    {Xs : Set (Set α)} {P : proc q α} {Qf : Set α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqF (Qf X) M1 M2 P) →
        eqF (Rep_int_choice_set Xs Qf) M1 M2 P

axiom cspF_Rep_int_choice_com_eq_left [Inhabited α]
    {X : Set α} {P : proc q α} {Qf : α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF (Qf a) M1 M2 P) →
        eqF (Rep_int_choice_com X Qf) M1 M2 P

axiom cspF_Rep_int_choice_f_eq_left [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc q α} {Qf : β → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF (Qf a) M1 M2 P) →
        eqF (Rep_int_choice_f f X Qf) M1 M2 P

/- The Isabelle theorem bundle `cspF_int_eq_left` is represented by
   `cspF_Rep_int_choice_sum_eq_left`, `cspF_Rep_int_choice_nat_eq_left`,
   `cspF_Rep_int_choice_set_eq_left`, `cspF_Rep_int_choice_com_eq_left`,
   `cspF_Rep_int_choice_f_eq_left`, and `cspF_Int_choice_eq_left`. -/

/-
(* ---------------------------------------------- *
      replicated internal choice -> binary ...
 * ---------------------------------------------- *)
-/

/- ---- Un ---- -/

/- nat -/

axiom cspF_Rep_int_choice_nat_Un
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf))

/- set -/

axiom cspF_Rep_int_choice_set_Un
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs2 Pf) |~| (Rep_int_choice_set Xs1 Pf))

/- com -/

axiom cspF_Rep_int_choice_com_Un [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf))

/- f -/

axiom cspF_Rep_int_choice_f_Un [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf))

/- The Isabelle theorem bundle `cspF_Rep_int_choice_Un` is represented by
   `cspF_Rep_int_choice_nat_Un`, `cspF_Rep_int_choice_set_Un`,
   `cspF_Rep_int_choice_com_Un`, and `cspF_Rep_int_choice_f_Un`. -/

/- ---- insert ---- -/

/- nat -/

axiom cspF_Rep_int_choice_nat_insert
    {m : Nat} {N : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat (insert m N) Pf) M M
      (Pf m |~| Rep_int_choice_nat N Pf)

/- set -/

axiom cspF_Rep_int_choice_set_insert
    {Y : Set α} {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set (insert Y Xs) Pf) M M
      (Pf Y |~| Rep_int_choice_set Xs Pf)

/- com -/

axiom cspF_Rep_int_choice_com_insert [Inhabited α]
    {a : α} {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_com X Pf)

/- f -/

axiom cspF_Rep_int_choice_f_insert [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {a : β} {X : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_f f X Pf)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_insert` is represented by
   `cspF_Rep_int_choice_nat_insert`, `cspF_Rep_int_choice_set_insert`,
   `cspF_Rep_int_choice_com_insert`, and `cspF_Rep_int_choice_f_insert`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_sepa` is represented by
   `cspF_Rep_int_choice_insert` and `cspF_Rep_int_choice_Un`. -/

/-
(* ---------------------------------------------- *
       simplify replicated internal choice
 * ---------------------------------------------- *)
-/

axiom cspF_Rep_int_choice_com_map_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com (f '' X) Pf) M M
      (Rep_int_choice_f f X fun x => Pf (f x))

axiom cspF_Rep_int_choice_f_map_f [Inhabited α] [Inhabited β] [Inhabited γ]
    {f : β → α} {g : γ → β} (hf : Injective f) (hg : Injective g)
    {X : Set γ} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f (g '' X) Pf) M M
      (Rep_int_choice_f (f ∘ g) X fun x => Pf (g x))

/- The Isabelle theorem bundle `cspF_Rep_int_choice_f_map` is represented by
   `cspF_Rep_int_choice_com_map_f` and `cspF_Rep_int_choice_f_map_f`. -/

end
