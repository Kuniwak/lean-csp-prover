           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_decompo

open Function
open SumType

noncomputable section

open Classical in
noncomputable def procIte (b : Prop) (P Q : proc p α) : proc p α :=
  if b then P else Q

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
                          top
 *********************************************************)
-/

axiom cspT_STOP_top [HasPNfun p α] [HasFPmode] {P : proc p α} :
    refTfix P (proc.STOP : proc p α)

axiom cspT_DIV_top [HasPNfun p α] [HasFPmode] {P : proc p α} :
    refTfix P (proc.DIV : proc p α)

/-
(*********************************************************
                       IF bool
 *********************************************************)
-/

axiom cspT_IF_split {b : Bool} {P Q : proc p α} {M : p → domTType α} :
    eqT (IF b THEN P ELSE Q) M M (if b then P else Q)

axiom cspT_IF_True {P Q : proc p α} {M : p → domTType α} :
    eqT (IF True THEN P ELSE Q) M M P

axiom cspT_IF_False {P Q : proc p α} {M : p → domTType α} :
    eqT (IF False THEN P ELSE Q) M M Q

/-
(*********************************************************
                      basic laws
 *********************************************************)
-/

axiom cspT_Ext_choice_idem {P : proc p α} {M : p → domTType α} :
    eqT (P [+] P) M M P

axiom cspT_Int_choice_idem {P : proc p α} {M : p → domTType α} :
    eqT (P |~| P) M M P

axiom cspT_Ext_choice_commut {P Q : proc p α} {M : p → domTType α} :
    eqT (P [+] Q) M M (Q [+] P)

axiom cspT_Int_choice_commut {P Q : proc p α} {M : p → domTType α} :
    eqT (P |~| Q) M M (Q |~| P)

axiom cspT_Parallel_commut {P Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| Q) M M (Q |[X]| P)

axiom cspT_Ext_choice_assoc {P Q R : proc p α} {M : p → domTType α} :
    eqT (P [+] (Q [+] R)) M M ((P [+] Q) [+] R)

axiom cspT_Ext_choice_assoc_sym {P Q R : proc p α} {M : p → domTType α} :
    eqT ((P [+] Q) [+] R) M M (P [+] (Q [+] R))

axiom cspT_Int_choice_assoc {P Q R : proc p α} {M : p → domTType α} :
    eqT (P |~| (Q |~| R)) M M ((P |~| Q) |~| R)

axiom cspT_Int_choice_assoc_sym {P Q R : proc p α} {M : p → domTType α} :
    eqT ((P |~| Q) |~| R) M M (P |~| (Q |~| R))

axiom cspT_Ext_choice_left_commut {P Q R : proc p α} {M : p → domTType α} :
    eqT (P [+] (Q [+] R)) M M (Q [+] (P [+] R))

axiom cspT_Int_choice_left_commut {P Q R : proc p α} {M : p → domTType α} :
    eqT (P |~| (Q |~| R)) M M (Q |~| (P |~| R))

axiom cspT_Ext_choice_unit_l {P : proc p α} {M : p → domTType α} :
    eqT (proc.STOP [+] P) M M P

axiom cspT_Ext_choice_unit_r {P : proc p α} {M : p → domTType α} :
    eqT (P [+] proc.STOP) M M P

axiom cspT_Int_choice_unit_l {P : proc p α} {M : p → domTType α} :
    eqT (proc.DIV |~| P) M M P

axiom cspT_Int_choice_unit_r {P : proc p α} {M : p → domTType α} :
    eqT (P |~| proc.DIV) M M P

/-
(*********************************************************
                    Rep_int_choice
 *********************************************************)
-/

axiom cspT_Rep_int_choice_sum_DIV {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C = ∅ → eqT (proc.Rep_int_choice C Pf) M1 M2 (proc.DIV : proc q α)

axiom cspT_Rep_int_choice_nat_DIV {Pf : Nat → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_nat (∅ : Set Nat) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspT_Rep_int_choice_set_DIV {Pf : Set α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_set (∅ : Set (Set α)) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspT_Rep_int_choice_com_DIV [Inhabited α] {Pf : α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_com (∅ : Set α) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspT_Rep_int_choice_f_DIV [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Pf : β → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_f f (∅ : Set β) Pf) M1 M2 (proc.DIV : proc q α)

axiom cspT_Rep_int_choice_sum_unit {C : sets_nats α} {P : proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ → eqT (proc.Rep_int_choice C (fun _ => P)) M M P

axiom cspT_Rep_int_choice_nat_unit {N : Set Nat} {P : proc p α} {M : p → domTType α} :
    N ≠ ∅ → eqT (Rep_int_choice_nat N (fun _ => P)) M M P

axiom cspT_Rep_int_choice_set_unit {Xs : Set (Set α)} {P : proc p α} {M : p → domTType α} :
    Xs ≠ ∅ → eqT (Rep_int_choice_set Xs (fun _ => P)) M M P

axiom cspT_Rep_int_choice_com_unit [Inhabited α] {X : Set α} {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ → eqT (Rep_int_choice_com X (fun _ => P)) M M P

axiom cspT_Rep_int_choice_f_unit [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ → eqT (Rep_int_choice_f f X (fun _ => P)) M M P

axiom cspT_Rep_int_choice_sum_const {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {P : proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → Pf c = P) →
        eqT (proc.Rep_int_choice C Pf) M M P

axiom cspT_Rep_int_choice_nat_const {N : Set Nat} {Pf : Nat → proc p α}
    {P : proc p α} {M : p → domTType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → Pf n = P) →
        eqT (Rep_int_choice_nat N Pf) M M P

axiom cspT_Rep_int_choice_set_const {Xs : Set (Set α)} {Pf : Set α → proc p α}
    {P : proc p α} {M : p → domTType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → Pf X = P) →
        eqT (Rep_int_choice_set Xs Pf) M M P

axiom cspT_Rep_int_choice_com_const [Inhabited α] {X : Set α} {Pf : α → proc p α}
    {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqT (Rep_int_choice_com X Pf) M M P

axiom cspT_Rep_int_choice_f_const [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α}
    {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqT (Rep_int_choice_f f X Pf) M M P

axiom cspT_Int_Rep_int_choice_sum_union
    {C1 C2 : sets_nats α} {P1f P2f : aset_anat α → proc p α} {M : p → domTType α} :
    C1 =type= C2 →
      eqT
        ((proc.Rep_int_choice C1 P1f) |~| (proc.Rep_int_choice C2 P2f)) M M
        (proc.Rep_int_choice (C1 Uns C2) fun c =>
          procIte (c ∈ sumset C1 ∧ c ∈ sumset C2) (P1f c |~| P2f c)
            (procIte (c ∈ sumset C1) (P1f c) (P2f c)))

axiom cspT_Int_Rep_int_choice_nat_union
    {N1 N2 : Set Nat} {P1f P2f : Nat → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_nat N1 P1f) |~| (Rep_int_choice_nat N2 P2f)) M M
      (Rep_int_choice_nat (N1 ∪ N2) fun n =>
        procIte (n ∈ N1 ∧ n ∈ N2) (P1f n |~| P2f n)
          (procIte (n ∈ N1) (P1f n) (P2f n)))

axiom cspT_Int_Rep_int_choice_set_union
    {Xs1 Xs2 : Set (Set α)} {P1f P2f : Set α → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_set Xs1 P1f) |~| (Rep_int_choice_set Xs2 P2f)) M M
      (Rep_int_choice_set (Xs1 ∪ Xs2) fun X =>
        procIte (X ∈ Xs1 ∧ X ∈ Xs2) (P1f X |~| P2f X)
          (procIte (X ∈ Xs1) (P1f X) (P2f X)))

axiom cspT_Int_Rep_int_choice_com_union [Inhabited α]
    {X1 X2 : Set α} {P1f P2f : α → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_com X1 P1f) |~| (Rep_int_choice_com X2 P2f)) M M
      (Rep_int_choice_com (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a)))

axiom cspT_Int_Rep_int_choice_f_union [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {P1f P2f : β → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_f f X1 P1f) |~| (Rep_int_choice_f f X2 P2f)) M M
      (Rep_int_choice_f f (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a)))

axiom cspT_Rep_int_choice_sum_union_Int {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    C1 =type= C2 →
      eqT
        (proc.Rep_int_choice (C1 Uns C2) Pf) M M
        ((proc.Rep_int_choice C1 Pf) |~| (proc.Rep_int_choice C2 Pf))

axiom cspT_Rep_int_choice_nat_union_Int {N1 N2 : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf))

axiom cspT_Rep_int_choice_set_union_Int
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs1 Pf) |~| (Rep_int_choice_set Xs2 Pf))

axiom cspT_Rep_int_choice_com_union_Int [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf))

axiom cspT_Rep_int_choice_f_union_Int [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf))

/-
(*********************************************************
                     Depth_rest
 *********************************************************)
-/

axiom cspT_Depth_rest_Zero {P : proc p α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (P |. 0) M1 M2 (proc.DIV : proc q α)

axiom cspT_Depth_rest_min {P : proc p α} {n m : Nat} {M : p → domTType α} :
    eqT ((P |. n) |. m) M M (P |. min n m)

axiom cspT_Depth_rest_congE {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {S : Prop} :
    eqT P M1 M2 Q →
      ((∀ m, eqT (P |. m) M1 M2 (Q |. m)) → S) →
        S

axiom cspT_nat_Depth_rest_UNIV {P : proc p α} {M : p → domTType α} :
    eqT P M M (Rep_int_choice_nat Set.univ fun n => P |. n)

axiom cspT_nat_Depth_rest_lengthset {P : proc p α} {M : p → domTType α} :
    eqT P M M (Rep_int_choice_nat (lengthset P M) fun n => P |. n)

/-
(*********************************************************
                       partial
 *********************************************************)
-/

axiom cspT_Ext_pre_choice_partial {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice X Pf) M M
      (proc.Ext_pre_choice X fun x => procIte (x ∈ X) (Pf x) proc.DIV)

axiom cspT_Rep_int_choice_sum_partial {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice C Pf) M M
      (proc.Rep_int_choice C fun c => procIte (c ∈ sumset C) (Pf c) proc.DIV)

axiom cspT_Rep_int_choice_nat_partial {N : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N Pf) M M
      (Rep_int_choice_nat N fun n => procIte (n ∈ N) (Pf n) proc.DIV)

axiom cspT_Rep_int_choice_set_partial
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs Pf) M M
      (Rep_int_choice_set Xs fun X => procIte (X ∈ Xs) (Pf X) proc.DIV)

axiom cspT_Rep_int_choice_com_partial [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com X Pf) M M
      (Rep_int_choice_com X fun a => procIte (a ∈ X) (Pf a) proc.DIV)

axiom cspT_Rep_int_choice_f_partial [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f X Pf) M M
      (Rep_int_choice_f f X fun a => procIte (a ∈ X) (Pf a) proc.DIV)

axiom cspT_Rep_int_choice_sum_set {Xs : Set (Set α)} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice (type1 Xs) Pf) M M
      (Rep_int_choice_set Xs fun X => Pf (type1 X))

axiom cspT_Rep_int_choice_sum_nat {N : Set Nat} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice (type2 N) Pf) M M
      (Rep_int_choice_nat N fun n => Pf (type2 n))

axiom cspT_Rep_int_choice_sum {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice C Pf) M M
      (procIte (type1check C)
        (Rep_int_choice_set (open1 C) fun X => Pf (type1 X))
        (Rep_int_choice_nat (open2 C) fun n => Pf (type2 n)))

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)
-/

axiom cspT_first_Send_prefix {x : Type _} {a : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    eqT (Send_prefix a v P) M M (a v ~> P)

axiom cspT_first_Rec_prefix {x : Type _} [Inhabited x] {a : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    eqT (Rec_prefix a X Pf) M M
      (proc.Ext_pre_choice (a '' X) fun x => Pf (Function.invFun a x))

axiom cspT_first_Int_pre_choice [Inhabited α] {X : Set α} {Pf : α → proc p α}
    {M : p → domTType α} :
    eqT (Int_pre_choice X Pf) M M
      (Rep_int_choice_com X fun x => x ~> Pf x)

axiom cspT_first_Nondet_send_prefix {x : Type _} [Inhabited α] [Inhabited x]
    {a : x → α} {X : Set x} {Pf : x → proc p α} {M : p → domTType α} :
    eqT (Nondet_send_prefix a X Pf) M M
      (Int_pre_choice (a '' X) fun x => Pf (Function.invFun a x))

axiom cspT_Seq_compo_assoc {P Q R : proc p α} {M : p → domTType α} :
    eqT ((P ;; Q) ;; R) M M (P ;; (Q ;; R))

axiom cspT_Int_choice_eq_right {P : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT P M1 M2 Q1 →
      eqT P M1 M2 Q2 →
        eqT P M1 M2 (Q1 |~| Q2)

axiom cspT_Rep_int_choice_sum_eq_right_ALL
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqT P M1 M2 (Qf c)) →
        eqT P M1 M2 (proc.Rep_int_choice C Qf)

axiom cspT_Rep_int_choice_sum_eq_right
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqT P M1 M2 (Qf c)) →
        eqT P M1 M2 (proc.Rep_int_choice C Qf)

axiom cspT_Rep_int_choice_nat_eq_right
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqT P M1 M2 (Qf n)) →
        eqT P M1 M2 (Rep_int_choice_nat N Qf)

axiom cspT_Rep_int_choice_set_eq_right
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqT P M1 M2 (Qf X)) →
        eqT P M1 M2 (Rep_int_choice_set Xs Qf)

axiom cspT_Rep_int_choice_com_eq_right [Inhabited α]
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT P M1 M2 (Qf a)) →
        eqT P M1 M2 (Rep_int_choice_com X Qf)

axiom cspT_Rep_int_choice_f_eq_right [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT P M1 M2 (Qf a)) →
        eqT P M1 M2 (Rep_int_choice_f f X Qf)

axiom cspT_Int_choice_eq_left {P : proc q α} {Q1 Q2 : proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT Q1 M1 M2 P →
      eqT Q2 M1 M2 P →
        eqT (Q1 |~| Q2) M1 M2 P

axiom cspT_Rep_int_choice_sum_eq_left
    {C : sets_nats α} {P : proc q α} {Qf : aset_anat α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqT (Qf c) M1 M2 P) →
        eqT (proc.Rep_int_choice C Qf) M1 M2 P

axiom cspT_Rep_int_choice_nat_eq_left
    {N : Set Nat} {P : proc q α} {Qf : Nat → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqT (Qf n) M1 M2 P) →
        eqT (Rep_int_choice_nat N Qf) M1 M2 P

axiom cspT_Rep_int_choice_set_eq_left
    {Xs : Set (Set α)} {P : proc q α} {Qf : Set α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqT (Qf X) M1 M2 P) →
        eqT (Rep_int_choice_set Xs Qf) M1 M2 P

axiom cspT_Rep_int_choice_com_eq_left [Inhabited α]
    {X : Set α} {P : proc q α} {Qf : α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT (Qf a) M1 M2 P) →
        eqT (Rep_int_choice_com X Qf) M1 M2 P

axiom cspT_Rep_int_choice_f_eq_left [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc q α} {Qf : β → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT (Qf a) M1 M2 P) →
        eqT (Rep_int_choice_f f X Qf) M1 M2 P

axiom cspT_Rep_int_choice_nat_Un {N1 N2 : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf))

axiom cspT_Rep_int_choice_set_Un
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs2 Pf) |~| (Rep_int_choice_set Xs1 Pf))

axiom cspT_Rep_int_choice_com_Un [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf))

axiom cspT_Rep_int_choice_f_Un [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf))

axiom cspT_Rep_int_choice_nat_insert {m : Nat} {N : Set Nat} {Pf : Nat → proc p α}
    {M : p → domTType α} :
    eqT (Rep_int_choice_nat (insert m N) Pf) M M
      (Pf m |~| Rep_int_choice_nat N Pf)

axiom cspT_Rep_int_choice_set_insert
    {Y : Set α} {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set (insert Y Xs) Pf) M M
      (Pf Y |~| Rep_int_choice_set Xs Pf)

axiom cspT_Rep_int_choice_com_insert [Inhabited α]
    {a : α} {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_com X Pf)

axiom cspT_Rep_int_choice_f_insert [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {a : β} {X : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_f f X Pf)

axiom cspT_Rep_int_choice_com_map_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com (f '' X) Pf) M M
      (Rep_int_choice_f f X fun x => Pf (f x))

axiom cspT_Rep_int_choice_f_map_f [Inhabited α] [Inhabited β] [Inhabited γ]
    {f : β → α} {g : γ → β} (hf : Injective f) (hg : Injective g)
    {X : Set γ} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f (g '' X) Pf) M M
      (Rep_int_choice_f (f ∘ g) X fun x => Pf (g x))
