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
import LeanCspProver.CSP_F.CSP_F_simp

open Function
open SumType

noncomputable section

open Classical in
@[csp_F] theorem in_failures_procIte {s : traceType α} {X : Set (event α)} {b : Prop}
    {P Q : proc p α} {M : p → domFType α} :
    ((s, X) :f failures (procIte b P Q) M) ↔
      (if b then (s, X) :f failures P M else (s, X) :f failures Q M) := by
  unfold procIte; split_ifs <;> rfl

/-- Congruence for `procIte`; the `eqF` counterpart of `cspT_procIte_cong`
    (see `CSP_T_law_basic`), used by the algebraic resolve proofs in
    `CSP_F_law_aux`. -/
theorem cspF_procIte_cong
    {b : Prop} {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (procIte b P1 P2) M1 M2 (procIte b Q1 Q2) := by
  unfold procIte
  split_ifs <;> assumption

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

theorem cspF_IF_split
    {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    eqF (IF b THEN P ELSE Q) M M (if b then P else Q) := by
  cspF_auto

theorem cspF_IF_True
    {P Q : proc p α} {M : p → domFType α} :
    eqF (IF True THEN P ELSE Q) M M P := by
  cspF_auto

theorem cspF_IF_False
    {P Q : proc p α} {M : p → domFType α} :
    eqF (IF False THEN P ELSE Q) M M Q := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_IF` is represented by
   `cspF_IF_True` and `cspF_IF_False`. -/

/- -----------------------------------*
 |           Idempotence             |
 *----------------------------------- -/

theorem cspF_Ext_choice_idem
    {P : proc p α} {M : p → domFType α} :
    eqF (P [+] P) M M P := by
  cspF_auto

theorem cspF_Int_choice_idem
    {P : proc p α} {M : p → domFType α} :
    eqF (P |~| P) M M P := by
  cspF_auto

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

theorem cspF_Ext_choice_commut
    {P Q : proc p α} {M : p → domFType α} :
    eqF (P [+] Q) M M (Q [+] P) := by
  cspF_auto

/-
(*********************************************************
                      Int choice
 *********************************************************)
-/

theorem cspF_Int_choice_commut
    {P Q : proc p α} {M : p → domFType α} :
    eqF (P |~| Q) M M (Q |~| P) := by
  cspF_auto

/-
(*********************************************************
                      Parallel
 *********************************************************)
-/

theorem cspF_Parallel_commut
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Q) M M (Q |[X]| P) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_commut` is represented by
   `cspF_Ext_choice_commut`, `cspF_Int_choice_commut`, and
   `cspF_Parallel_commut`. -/

/- -----------------------------------*
 |          Associativity            |
 *----------------------------------- -/

theorem cspF_Ext_choice_assoc
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P [+] (Q [+] R)) M M ((P [+] Q) [+] R) := by
  cspF_auto

theorem cspF_Ext_choice_assoc_sym
    {P Q R : proc p α} {M : p → domFType α} :
    eqF ((P [+] Q) [+] R) M M (P [+] (Q [+] R)) := by
  cspF_auto

theorem cspF_Int_choice_assoc
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P |~| (Q |~| R)) M M ((P |~| Q) |~| R) := by
  cspF_auto

theorem cspF_Int_choice_assoc_sym
    {P Q R : proc p α} {M : p → domFType α} :
    eqF ((P |~| Q) |~| R) M M (P |~| (Q |~| R)) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_assoc` is represented by
   `cspF_Ext_choice_assoc` and `cspF_Int_choice_assoc`. -/

/- The Isabelle theorem bundle `cspF_assoc_sym` is represented by
   `cspF_Ext_choice_assoc_sym` and `cspF_Int_choice_assoc_sym`. -/

/- -----------------------------------*
 |        Left Commutativity         |
 *----------------------------------- -/

theorem cspF_Ext_choice_left_commut
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P [+] (Q [+] R)) M M (Q [+] (P [+] R)) := by
  cspF_auto

theorem cspF_Int_choice_left_commut
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P |~| (Q |~| R)) M M (Q |~| (P |~| R)) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_left_commut` is represented by
   `cspF_Ext_choice_left_commut` and `cspF_Int_choice_left_commut`. -/

/- -----------------------------------*
 |              Unit                 |
 *----------------------------------- -/

/-
(*** STOP [+] P ***)
-/

theorem cspF_Ext_choice_unit_l
    {P : proc p α} {M : p → domFType α} :
    eqF (proc.STOP [+] P) M M P := by
  cspF_auto

theorem cspF_Ext_choice_unit_r
    {P : proc p α} {M : p → domFType α} :
    eqF (P [+] proc.STOP) M M P := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Ext_choice_unit` is represented by
   `cspF_Ext_choice_unit_l` and `cspF_Ext_choice_unit_r`. -/

theorem cspF_Int_choice_unit_l
    {P : proc p α} {M : p → domFType α} :
    eqF (proc.DIV |~| P) M M P := by
  cspF_auto

theorem cspF_Int_choice_unit_r
    {P : proc p α} {M : p → domFType α} :
    eqF (P |~| proc.DIV) M M P := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Int_choice_unit` is represented by
   `cspF_Int_choice_unit_l` and `cspF_Int_choice_unit_r`. -/

/- The Isabelle theorem bundle `cspF_unit` is represented by
   `cspF_Ext_choice_unit` and `cspF_Int_choice_unit`. -/

/- -----------------------------------*
 |           !!-empty                |
 *----------------------------------- -/

theorem cspF_Rep_int_choice_sum_DIV
    {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C = ∅ → eqF (proc.Rep_int_choice C Pf) M1 M2 (proc.DIV : proc q α) := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_DIV
    {Pf : Nat → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_nat (∅ : Set Nat) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_DIV
    {Pf : Set α → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_set (∅ : Set (Set α)) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspF_auto

theorem cspF_Rep_int_choice_com_DIV
    {Pf : α → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_com (∅ : Set α) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspF_auto

theorem cspF_Rep_int_choice_f_DIV [Inhabited β]
    {f : β → α} (hf : Injective f) {Pf : β → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (Rep_int_choice_f f (∅ : Set β) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_DIV` is represented by
   `cspF_Rep_int_choice_sum_DIV`, `cspF_Rep_int_choice_nat_DIV`,
   `cspF_Rep_int_choice_set_DIV`, `cspF_Rep_int_choice_com_DIV`, and
   `cspF_Rep_int_choice_f_DIV`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_DIV_sym` is represented by
   `cspF_Rep_int_choice_DIV` together with `cspF_sym`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_empty` is represented by
   `cspF_Rep_int_choice_DIV`. -/

theorem cspF_DIV_top [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    refFfix P proc.DIV := by
  rw [show refFfix P (proc.DIV : proc p α) = refF P MF MF proc.DIV from rfl, cspF_refF_iff]
  constructor
  · intro t ht
    rw [in_traces_DIV] at ht; subst ht; exact nilt_in_T
  · intro s X h
    exact absurd h in_failures_DIV

/- -----------------------------------*
 |             !!-unit               |
 *----------------------------------- -/

theorem cspF_Rep_int_choice_sum_unit
    {C : sets_nats α} {P : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ → eqF (proc.Rep_int_choice C (fun _ => P)) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_unit
    {N : Set Nat} {P : proc p α} {M : p → domFType α} :
    N ≠ ∅ → eqF (Rep_int_choice_nat N (fun _ => P)) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_set_unit
    {Xs : Set (Set α)} {P : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (Rep_int_choice_set Xs (fun _ => P)) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_com_unit
    {X : Set α} {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF (Rep_int_choice_com X (fun _ => P)) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_f_unit [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF (Rep_int_choice_f f X (fun _ => P)) M M P := by
  -- `in_failures_Rep_int_choice_f` needs `Injective f`; go through the `_com` form
  rw [Rep_int_choice_f_def]
  cspF_auto

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

theorem cspF_Rep_int_choice_sum_const
    {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {P : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → Pf c = P) →
        eqF (proc.Rep_int_choice C Pf) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_const
    {N : Set Nat} {Pf : Nat → proc p α}
    {P : proc p α} {M : p → domFType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → Pf n = P) →
        eqF (Rep_int_choice_nat N Pf) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_set_const
    {Xs : Set (Set α)} {Pf : Set α → proc p α}
    {P : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → Pf X = P) →
        eqF (Rep_int_choice_set Xs Pf) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_com_const
    {X : Set α} {Pf : α → proc p α}
    {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqF (Rep_int_choice_com X Pf) M M P := by
  cspF_auto

theorem cspF_Rep_int_choice_f_const [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α}
    {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqF (Rep_int_choice_f f X Pf) M M P := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_const` is represented by
   `cspF_Rep_int_choice_sum_const`, `cspF_Rep_int_choice_nat_const`,
   `cspF_Rep_int_choice_set_const`, `cspF_Rep_int_choice_com_const`, and
   `cspF_Rep_int_choice_f_const`. -/

/- -----------------------------------*
 |           |~|-!!-union            |
 *----------------------------------- -/

theorem cspF_Int_Rep_int_choice_sum_union
    {C1 C2 : sets_nats α} {P1f P2f : aset_anat α → proc p α}
    {M : p → domFType α} :
    C1 =type= C2 →
      eqF
        ((proc.Rep_int_choice C1 P1f) |~| (proc.Rep_int_choice C2 P2f)) M M
        (proc.Rep_int_choice (C1 Uns C2) fun c =>
          procIte (c ∈ sumset C1 ∧ c ∈ sumset C2) (P1f c |~| P2f c)
            (procIte (c ∈ sumset C1) (P1f c) (P2f c))) := by
  cspF_auto

theorem cspF_Int_Rep_int_choice_nat_union
    {N1 N2 : Set Nat} {P1f P2f : Nat → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_nat N1 P1f) |~| (Rep_int_choice_nat N2 P2f)) M M
      (Rep_int_choice_nat (N1 ∪ N2) fun n =>
        procIte (n ∈ N1 ∧ n ∈ N2) (P1f n |~| P2f n)
          (procIte (n ∈ N1) (P1f n) (P2f n))) := by
  cspF_auto

theorem cspF_Int_Rep_int_choice_set_union
    {Xs1 Xs2 : Set (Set α)} {P1f P2f : Set α → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_set Xs1 P1f) |~| (Rep_int_choice_set Xs2 P2f)) M M
      (Rep_int_choice_set (Xs1 ∪ Xs2) fun X =>
        procIte (X ∈ Xs1 ∧ X ∈ Xs2) (P1f X |~| P2f X)
          (procIte (X ∈ Xs1) (P1f X) (P2f X))) := by
  cspF_auto

theorem cspF_Int_Rep_int_choice_com_union
    {X1 X2 : Set α} {P1f P2f : α → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_com X1 P1f) |~| (Rep_int_choice_com X2 P2f)) M M
      (Rep_int_choice_com (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a))) := by
  cspF_auto

theorem cspF_Int_Rep_int_choice_f_union [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {P1f P2f : β → proc p α}
    {M : p → domFType α} :
    eqF
      ((Rep_int_choice_f f X1 P1f) |~| (Rep_int_choice_f f X2 P2f)) M M
      (Rep_int_choice_f f (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a))) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Int_Rep_int_choice_union` is represented by
   `cspF_Int_Rep_int_choice_sum_union`, `cspF_Int_Rep_int_choice_nat_union`,
   `cspF_Int_Rep_int_choice_set_union`, `cspF_Int_Rep_int_choice_com_union`,
   and `cspF_Int_Rep_int_choice_f_union`. -/

/- -----------------------------------*
 |           !!-union-|~|            |
 *----------------------------------- -/

theorem cspF_Rep_int_choice_sum_union_Int
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domFType α} :
    C1 =type= C2 →
      eqF
        (proc.Rep_int_choice (C1 Uns C2) Pf) M M
        ((proc.Rep_int_choice C1 Pf) |~| (proc.Rep_int_choice C2 Pf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_union_Int
    {N1 N2 : Set Nat} {Pf : Nat → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_union_Int
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs1 Pf) |~| (Rep_int_choice_set Xs2 Pf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_com_union_Int
    {X1 X2 : Set α} {Pf : α → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_f_union_Int [Inhabited β]
    {f : β → α} {X1 X2 : Set β} {Pf : β → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf)) := by
  -- `in_failures_Rep_int_choice_f` needs `Injective f`; go through the `_com` form
  simp only [Rep_int_choice_f_def, Set.image_union]
  cspF_auto

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

theorem cspF_Depth_rest_Zero
    {P : proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (P |. 0) M1 M2 (proc.DIV : proc q α) := by
  cspF_auto

theorem cspF_Depth_rest_min
    {P : proc p α} {n m : Nat} {M : p → domFType α} :
    eqF ((P |. n) |. m) M M (P |. min n m) := by
  cspF_auto

theorem cspF_Depth_rest_congE
    {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {S : Prop} :
    eqF P M1 M2 Q →
      ((∀ m, eqF (P |. m) M1 M2 (Q |. m)) → S) →
        S := by
  cspF_auto

theorem cspF_Depth_rest_n
    {P : proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((P |. n) |. n) M M (P |. n) := by
  cspF_auto

/- (*------------------*
 |     !nat-rest    |
 *------------------*) -/

theorem cspF_nat_Depth_rest_UNIV
    {P : proc p α} {M : p → domFType α} :
    eqF P M M (Rep_int_choice_nat Set.univ fun n => P |. n) := by
  apply cspF_eqF_of_eqT cspT_nat_Depth_rest_UNIV
  intro s X
  simp only [in_failures_Rep_int_choice_nat, in_failures_Depth_rest, Prod.mk.injEq,
    Set.mem_univ, true_and, tickTrace_eq]
  constructor
  · intro h
    exact ⟨lengtht s + 1, s, X, ⟨rfl, rfl⟩, h, Or.inl (Nat.lt_succ_self _)⟩
  · rintro ⟨n, t', X', ⟨rfl, rfl⟩, h, -⟩
    exact h

theorem cspF_nat_Depth_rest_lengthset
    {P : proc p α} {M : p → domFType α} :
    eqF P M M (Rep_int_choice_nat (lengthset P (fstF ∘ M)) fun n => P |. n) := by
  apply cspF_eqF_of_eqT cspT_nat_Depth_rest_lengthset
  intro s X
  simp only [in_failures_Rep_int_choice_nat, in_failures_Depth_rest, Prod.mk.injEq,
    mem_lengthset, tickTrace_eq]
  constructor
  · intro h
    by_cases hs : noTick s
    · exact ⟨lengtht s + 1, ⟨s, failures_T2 h, Or.inr ⟨rfl, hs⟩⟩,
        s, X, ⟨rfl, rfl⟩, h, Or.inl (Nat.lt_succ_self _)⟩
    · have hne : s ≠ <> := fun hnil => hs (hnil ▸ noTick_nil)
      exact ⟨lengtht s, ⟨s, failures_T2 h, Or.inl rfl⟩,
        s, X, ⟨rfl, rfl⟩, h,
        Or.inr ⟨rfl, butlastt s, Tick_decompo hs, noTick_butlast hne⟩⟩
  · rintro ⟨n, -, t', X', ⟨rfl, rfl⟩, h, -⟩
    exact h

/- The Isabelle theorem bundle `cspF_nat_Depth_rest` is represented by
   `cspF_nat_Depth_rest_UNIV` and `cspF_nat_Depth_rest_lengthset`. -/

/- (*------------------*
 |    ?-partial     |
 *------------------*) -/

theorem cspF_Ext_pre_choice_partial
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice X Pf) M M
      (proc.Ext_pre_choice X fun x => procIte (x ∈ X) (Pf x) proc.DIV) := by
  cspF_auto

/- (*------------------*
 |   !!-partial     |
 *------------------*) -/

theorem cspF_Rep_int_choice_sum_partial
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C Pf) M M
      (proc.Rep_int_choice C fun c => procIte (c ∈ sumset C) (Pf c) proc.DIV) := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_partial
    {N : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N Pf) M M
      (Rep_int_choice_nat N fun n => procIte (n ∈ N) (Pf n) proc.DIV) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_partial
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs Pf) M M
      (Rep_int_choice_set Xs fun X => procIte (X ∈ Xs) (Pf X) proc.DIV) := by
  cspF_auto

theorem cspF_Rep_int_choice_com_partial
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X Pf) M M
      (Rep_int_choice_com X fun a => procIte (a ∈ X) (Pf a) proc.DIV) := by
  cspF_auto

theorem cspF_Rep_int_choice_f_partial [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f X Pf) M M
      (Rep_int_choice_f f X fun a => procIte (a ∈ X) (Pf a) proc.DIV) := by
  cspF_auto

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

theorem cspF_first_Send_prefix
    {x : Type _} {a : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    eqF (Send_prefix a v P) M M (a v ~> P) := by
  cspF_auto

theorem cspF_first_Rec_prefix
    {x : Type _} [Inhabited x] {a : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    eqF (Rec_prefix a X Pf) M M
      (proc.Ext_pre_choice (a '' X) fun x => Pf (Function.invFun a x)) :=
  -- definitionally equal (`Rec_prefix_def` is `rfl`)
  cspF_reflex_eq_P

theorem cspF_first_Int_pre_choice
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Int_pre_choice X Pf) M M
      (Rep_int_choice_com X fun x => x ~> Pf x) := by
  cspF_auto

theorem cspF_first_Nondet_send_prefix
    {x : Type _} [Inhabited x]
    {a : x → α} {X : Set x} {Pf : x → proc p α} {M : p → domFType α} :
    eqF (Nondet_send_prefix a X Pf) M M
      (Int_pre_choice (a '' X) fun x => Pf (Function.invFun a x)) :=
  -- definitionally equal (`Nondet_send_prefix_def` is `rfl`)
  cspF_reflex_eq_P

/- The Isabelle theorem bundle `cspF_first_prefix_ss` is represented by
   `cspF_first_Send_prefix`, `cspF_first_Rec_prefix`,
   `cspF_first_Int_pre_choice`, and `cspF_first_Nondet_send_prefix`. -/

/-
(* --------------------------------------------------- *
      Associativity of Sequential composition
 * --------------------------------------------------- *)
-/

theorem cspF_Seq_compo_assoc
    {P Q R : proc p α} {M : p → domFType α} :
    eqF ((P ;; Q) ;; R) M M (P ;; (Q ;; R)) := by
  apply cspF_eqF_of_eqT cspT_Seq_compo_assoc
  intro w X
  simp only [in_failures_Seq_compo, in_traces_Seq_compo, Prod.mk.injEq]
  constructor
  · rintro (⟨t, X', ⟨heq, rfl⟩, hA, hnot⟩ | ⟨s, u, X', ⟨heq, rfl⟩, hA, hR, hno⟩)
    · subst heq
      rcases hA with ⟨t2, X2, ⟨heq2, rfl⟩, hP, _⟩ |
        ⟨s, u, X2, ⟨heq2, rfl⟩, hP, hQ, hno⟩
      · subst heq2
        exact Or.inl ⟨w, X, ⟨rfl, rfl⟩,
          by simpa [Set.union_assoc, Set.union_self] using hP, hnot⟩
      · subst heq2
        have hnu : noTick u := (decompo_appt_noTick_only_if (Or.inl hno) hnot).2
        exact Or.inr ⟨s, u, X, ⟨rfl, rfl⟩, hP,
          Or.inl ⟨u, X, ⟨rfl, rfl⟩, hQ, hnu⟩, hno⟩
    · subst heq
      rcases hA with ⟨w', hw, hPw⟩ | ⟨s2, u2, hEq, hP2, hQ2, hno2⟩
      · exfalso
        have hTick : noTick (s ^^^ (Abs_trace [event.Tick] : traceType α)) := by
          rw [hw]; exact noTick_rmTick
        exact not_noTick_Tick
          ((decompo_appt_noTick_only_if (Or.inl hno) hTick).2)
      · rcases (appt_decompo (Or.inl hno) (Or.inl hno2)).mp hEq with
          ⟨v, hv1, hv2, hv3⟩ | ⟨v, hv1, hv2, hv3⟩
        · rcases (appt_decompo_one_sym (a := event.Tick)
              (hv3.imp id And.right)).mp hv2 with ⟨hv, hu2⟩ | ⟨hv, hu2⟩
          · exfalso
            subst hv
            rw [← hv1] at hno2
            exact not_noTick_Tick
              ((decompo_appt_noTick_only_if (Or.inl hno) hno2).2)
          · subst hv hu2
            rw [appt_nil_right] at hv1
            subst hv1
            exact Or.inr ⟨s, u, X, ⟨rfl, rfl⟩, hP2,
              Or.inr ⟨<>, u, X, ⟨(appt_nil_left).symm, rfl⟩,
                by simpa [appt_nil_left] using hQ2, hR, noTick_nil⟩, hno⟩
        · have hvno : noTick v := by
            rcases hv3 with h | ⟨_, h⟩
            · exact h
            · exact absurd h (one_neq_nil (a := event.Tick))
          subst hv1
          exact Or.inr ⟨s2, v ^^^ u, X,
            ⟨appt_assoc (Or.inl hno2) (Or.inl hvno), rfl⟩, hP2,
            Or.inr ⟨v, u, X, ⟨rfl, rfl⟩, by rw [hv2]; exact hQ2, hR, hvno⟩,
            hno2⟩
  · rintro (⟨t, X', ⟨heq, rfl⟩, hP, hnot⟩ | ⟨s, u, X', ⟨heq, rfl⟩, hP, hB, hno⟩)
    · subst heq
      exact Or.inl ⟨w, X, ⟨rfl, rfl⟩,
        Or.inl ⟨w, X ∪ {event.Tick}, ⟨rfl, rfl⟩,
          by simpa [Set.union_assoc, Set.union_self] using hP, hnot⟩, hnot⟩
    · subst heq
      rcases hB with ⟨t2, X2, ⟨hequ, rfl⟩, hQ, hnot2⟩ |
        ⟨s2, u2, X2, ⟨hequ, rfl⟩, hQ2, hR2, hno2⟩
      · subst hequ
        exact Or.inl ⟨s ^^^ u, X, ⟨rfl, rfl⟩,
          Or.inr ⟨s, u, X ∪ {event.Tick}, ⟨rfl, rfl⟩, hP, hQ, hno⟩,
          decompo_appt_noTick_if hno hnot2⟩
      · subst hequ
        refine Or.inr ⟨s ^^^ s2, u2, X,
          ⟨(appt_assoc (Or.inl hno) (Or.inl hno2)).symm, rfl⟩,
          ?_, hR2, decompo_appt_noTick_if hno hno2⟩
        rw [appt_assoc (Or.inl hno) (Or.inl hno2)]
        exact Or.inr ⟨s, s2 ^^^ (Abs_trace [event.Tick] : traceType α), rfl, hP, hQ2, hno⟩

theorem cspF_Seq_compo_assoc_sym
    {P Q R : proc p α} {M : p → domFType α} :
    eqF (P ;; (Q ;; R)) M M ((P ;; Q) ;; R) :=
  cspF_sym cspF_Seq_compo_assoc

/-
(* ---------------------------------------------- *
         decompose right internal choice
 * ---------------------------------------------- *)
-/

theorem cspF_Int_choice_eq_right
    {P : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q1 →
      eqF P M1 M2 Q2 →
        eqF P M1 M2 (Q1 |~| Q2) := by
  cspF_auto

/- -------- right -------- -/

theorem cspF_Rep_int_choice_sum_eq_right_ALL
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqF P M1 M2 (Qf c)) →
        eqF P M1 M2 (proc.Rep_int_choice C Qf) := by
  cspF_auto

theorem cspF_Rep_int_choice_sum_eq_right
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqF P M1 M2 (Qf c)) →
        eqF P M1 M2 (proc.Rep_int_choice C Qf) := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_eq_right
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqF P M1 M2 (Qf n)) →
        eqF P M1 M2 (Rep_int_choice_nat N Qf) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_eq_right
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqF P M1 M2 (Qf X)) →
        eqF P M1 M2 (Rep_int_choice_set Xs Qf) := by
  cspF_auto

theorem cspF_Rep_int_choice_com_eq_right
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF P M1 M2 (Qf a)) →
        eqF P M1 M2 (Rep_int_choice_com X Qf) := by
  cspF_auto

theorem cspF_Rep_int_choice_f_eq_right [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF P M1 M2 (Qf a)) →
        eqF P M1 M2 (Rep_int_choice_f f X Qf) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_int_eq_right` is represented by
   `cspF_Rep_int_choice_sum_eq_right`, `cspF_Rep_int_choice_nat_eq_right`,
   `cspF_Rep_int_choice_set_eq_right`, `cspF_Rep_int_choice_com_eq_right`,
   `cspF_Rep_int_choice_f_eq_right`, and `cspF_Int_choice_eq_right`. -/

/- -------- left -------- -/

theorem cspF_Int_choice_eq_left
    {P : proc q α} {Q1 Q2 : proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF Q1 M1 M2 P →
      eqF Q2 M1 M2 P →
        eqF (Q1 |~| Q2) M1 M2 P := by
  cspF_auto

theorem cspF_Rep_int_choice_sum_eq_left
    {C : sets_nats α} {P : proc q α} {Qf : aset_anat α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqF (Qf c) M1 M2 P) →
        eqF (proc.Rep_int_choice C Qf) M1 M2 P := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_eq_left
    {N : Set Nat} {P : proc q α} {Qf : Nat → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqF (Qf n) M1 M2 P) →
        eqF (Rep_int_choice_nat N Qf) M1 M2 P := by
  cspF_auto

theorem cspF_Rep_int_choice_set_eq_left
    {Xs : Set (Set α)} {P : proc q α} {Qf : Set α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqF (Qf X) M1 M2 P) →
        eqF (Rep_int_choice_set Xs Qf) M1 M2 P := by
  cspF_auto

theorem cspF_Rep_int_choice_com_eq_left
    {X : Set α} {P : proc q α} {Qf : α → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF (Qf a) M1 M2 P) →
        eqF (Rep_int_choice_com X Qf) M1 M2 P := by
  cspF_auto

theorem cspF_Rep_int_choice_f_eq_left [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc q α} {Qf : β → proc p α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqF (Qf a) M1 M2 P) →
        eqF (Rep_int_choice_f f X Qf) M1 M2 P := by
  cspF_auto

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

theorem cspF_Rep_int_choice_nat_Un
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf)) := by
  cspF_auto

/- set -/

theorem cspF_Rep_int_choice_set_Un
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs2 Pf) |~| (Rep_int_choice_set Xs1 Pf)) := by
  cspF_auto

/- com -/

theorem cspF_Rep_int_choice_com_Un
    {X1 X2 : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf)) := by
  cspF_auto

/- f -/

theorem cspF_Rep_int_choice_f_Un [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf)) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_Un` is represented by
   `cspF_Rep_int_choice_nat_Un`, `cspF_Rep_int_choice_set_Un`,
   `cspF_Rep_int_choice_com_Un`, and `cspF_Rep_int_choice_f_Un`. -/

/- ---- insert ---- -/

/- nat -/

theorem cspF_Rep_int_choice_nat_insert
    {m : Nat} {N : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat (insert m N) Pf) M M
      (Pf m |~| Rep_int_choice_nat N Pf) := by
  cspF_auto

/- set -/

theorem cspF_Rep_int_choice_set_insert
    {Y : Set α} {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set (insert Y Xs) Pf) M M
      (Pf Y |~| Rep_int_choice_set Xs Pf) := by
  cspF_auto

/- com -/

theorem cspF_Rep_int_choice_com_insert
    {a : α} {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_com X Pf) := by
  cspF_auto

/- f -/

theorem cspF_Rep_int_choice_f_insert [Inhabited β]
    {f : β → α} (hf : Injective f) {a : β} {X : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_f f X Pf) := by
  cspF_auto

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

theorem cspF_Rep_int_choice_com_map_f [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com (f '' X) Pf) M M
      (Rep_int_choice_f f X fun x => Pf (f x)) := by
  cspF_auto

theorem cspF_Rep_int_choice_f_map_f [Inhabited β] [Inhabited γ]
    {f : β → α} {g : γ → β} (hf : Injective f) (hg : Injective g)
    {X : Set γ} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f (g '' X) Pf) M M
      (Rep_int_choice_f (f ∘ g) X fun x => Pf (g x)) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_f_map` is represented by
   `cspF_Rep_int_choice_com_map_f` and `cspF_Rep_int_choice_f_map_f`. -/

end
