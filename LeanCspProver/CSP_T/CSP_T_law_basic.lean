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
import LeanCspProver.CSP_T.CSP_T_simp

open Function
open SumType

noncomputable section

open Classical in
noncomputable def procIte (b : Prop) (P Q : proc p α) : proc p α :=
  if b then P else Q

open Classical in
@[csp_T] theorem in_traces_procIte {t : traceType α} {b : Prop} {P Q : proc p α}
    {M : p → domTType α} :
    (t :t traces (procIte b P Q) M) ↔ (if b then t :t traces P M else t :t traces Q M) := by
  unfold procIte; split_ifs <;> rfl

open Classical in
/-- Reduce `procIte` under a proof of the condition (plain equality). -/
theorem procIte_pos {b : Prop} (hb : b) (P Q : proc p α) : procIte b P Q = P := by
  unfold procIte; exact if_pos hb

open Classical in
/-- Reduce `procIte` under a refutation of the condition (plain equality). -/
theorem procIte_neg {b : Prop} (hb : ¬b) (P Q : proc p α) : procIte b P Q = Q := by
  unfold procIte; exact if_neg hb

/-- Congruence for `procIte` (the `Prop`-conditional counterpart of
    `cspT_IF_cong`); used by the algebraic resolve proofs in
    `CSP_T_law_aux`. -/
theorem cspT_procIte_cong
    {b : Prop} {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (procIte b P1 P2) M1 M2 (procIte b Q1 Q2) := by
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
                          top
 *********************************************************)
-/

theorem cspT_STOP_top [HasPNfun p α] [HasFPmode] {P : proc p α} :
    refTfix P (proc.STOP : proc p α) := by
  change refT P MT MT (proc.STOP : proc p α)
  rw [cspT_refT_semantics, subdomT_iff]; intro t ht
  rw [in_traces_STOP] at ht; subst ht; exact nilt_in_T

theorem cspT_DIV_top [HasPNfun p α] [HasFPmode] {P : proc p α} :
    refTfix P (proc.DIV : proc p α) := by
  change refT P MT MT (proc.DIV : proc p α)
  rw [cspT_refT_semantics, subdomT_iff]; intro t ht
  rw [in_traces_DIV] at ht; subst ht; exact nilt_in_T

/-
(*********************************************************
                       IF bool
 *********************************************************)
-/

theorem cspT_IF_split {b : Bool} {P Q : proc p α} {M : p → domTType α} :
    eqT (IF b THEN P ELSE Q) M M (if b then P else Q) := by
  rw [cspT_eqT_semantics]; apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht; cases b <;> simpa [in_traces_IF] using ht

theorem cspT_IF_True {P Q : proc p α} {M : p → domTType α} :
    eqT (IF True THEN P ELSE Q) M M P := by
  rw [cspT_eqT_semantics]; apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht; simpa [in_traces_IF] using ht

theorem cspT_IF_False {P Q : proc p α} {M : p → domTType α} :
    eqT (IF False THEN P ELSE Q) M M Q := by
  rw [cspT_eqT_semantics]; apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht; simpa [in_traces_IF] using ht

/-
(*********************************************************
                      basic laws
 *********************************************************)
-/

theorem cspT_Ext_choice_idem {P : proc p α} {M : p → domTType α} :
    eqT (P [+] P) M M P := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice] at ht ⊢; tauto

theorem cspT_Int_choice_idem {P : proc p α} {M : p → domTType α} :
    eqT (P |~| P) M M P := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Ext_choice_commut {P Q : proc p α} {M : p → domTType α} :
    eqT (P [+] Q) M M (Q [+] P) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice] at ht ⊢; tauto

theorem cspT_Int_choice_commut {P Q : proc p α} {M : p → domTType α} :
    eqT (P |~| Q) M M (Q |~| P) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Parallel_commut {P Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| Q) M M (Q |[X]| P) := by
  cspT_auto

theorem cspT_Ext_choice_assoc {P Q R : proc p α} {M : p → domTType α} :
    eqT (P [+] (Q [+] R)) M M ((P [+] Q) [+] R) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice] at ht ⊢; tauto

theorem cspT_Ext_choice_assoc_sym {P Q R : proc p α} {M : p → domTType α} :
    eqT ((P [+] Q) [+] R) M M (P [+] (Q [+] R)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice] at ht ⊢; tauto

theorem cspT_Int_choice_assoc {P Q R : proc p α} {M : p → domTType α} :
    eqT (P |~| (Q |~| R)) M M ((P |~| Q) |~| R) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Int_choice_assoc_sym {P Q R : proc p α} {M : p → domTType α} :
    eqT ((P |~| Q) |~| R) M M (P |~| (Q |~| R)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Ext_choice_left_commut {P Q R : proc p α} {M : p → domTType α} :
    eqT (P [+] (Q [+] R)) M M (Q [+] (P [+] R)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice] at ht ⊢; tauto

theorem cspT_Int_choice_left_commut {P Q R : proc p α} {M : p → domTType α} :
    eqT (P |~| (Q |~| R)) M M (Q |~| (P |~| R)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Ext_choice_unit_l {P : proc p α} {M : p → domTType α} :
    eqT (proc.STOP [+] P) M M P := by
  rw [cspT_eqT_semantics]; apply le_antisymm
  · rw [subdomT_iff]; intro t ht
    rw [in_traces_Ext_choice, in_traces_STOP] at ht
    rcases ht with rfl | h
    · exact nilt_in_T
    · exact h
  · rw [subdomT_iff]; intro t ht; rw [in_traces_Ext_choice]; exact Or.inr ht

theorem cspT_Ext_choice_unit_r {P : proc p α} {M : p → domTType α} :
    eqT (P [+] proc.STOP) M M P := by
  rw [cspT_eqT_semantics]; apply le_antisymm
  · rw [subdomT_iff]; intro t ht
    rw [in_traces_Ext_choice, in_traces_STOP] at ht
    rcases ht with h | rfl
    · exact h
    · exact nilt_in_T
  · rw [subdomT_iff]; intro t ht; rw [in_traces_Ext_choice]; exact Or.inl ht

theorem cspT_Int_choice_unit_l {P : proc p α} {M : p → domTType α} :
    eqT (proc.DIV |~| P) M M P := by
  rw [cspT_eqT_semantics]; apply le_antisymm
  · rw [subdomT_iff]; intro t ht
    rw [in_traces_Int_choice, in_traces_DIV] at ht
    rcases ht with rfl | h
    · exact nilt_in_T
    · exact h
  · rw [subdomT_iff]; intro t ht; rw [in_traces_Int_choice]; exact Or.inr ht

theorem cspT_Int_choice_unit_r {P : proc p α} {M : p → domTType α} :
    eqT (P |~| proc.DIV) M M P := by
  rw [cspT_eqT_semantics]; apply le_antisymm
  · rw [subdomT_iff]; intro t ht
    rw [in_traces_Int_choice, in_traces_DIV] at ht
    rcases ht with h | rfl
    · exact h
    · exact nilt_in_T
  · rw [subdomT_iff]; intro t ht; rw [in_traces_Int_choice]; exact Or.inl ht

/-
(*********************************************************
                    Rep_int_choice
 *********************************************************)
-/

theorem cspT_Rep_int_choice_sum_DIV {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C = ∅ → eqT (proc.Rep_int_choice C Pf) M1 M2 (proc.DIV : proc q α) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_DIV {Pf : Nat → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_nat (∅ : Set Nat) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_DIV {Pf : Set α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_set (∅ : Set (Set α)) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_DIV {Pf : α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_com (∅ : Set α) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_DIV [Inhabited β]
    {f : β → α} (hf : Injective f) {Pf : β → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (Rep_int_choice_f f (∅ : Set β) Pf) M1 M2 (proc.DIV : proc q α) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_unit {C : sets_nats α} {P : proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ → eqT (proc.Rep_int_choice C (fun _ => P)) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_unit {N : Set Nat} {P : proc p α} {M : p → domTType α} :
    N ≠ ∅ → eqT (Rep_int_choice_nat N (fun _ => P)) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_set_unit {Xs : Set (Set α)} {P : proc p α} {M : p → domTType α} :
    Xs ≠ ∅ → eqT (Rep_int_choice_set Xs (fun _ => P)) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_com_unit {X : Set α} {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ → eqT (Rep_int_choice_com X (fun _ => P)) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_f_unit [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ → eqT (Rep_int_choice_f f X (fun _ => P)) M M P := by
  -- `in_traces_Rep_int_choice_f` needs `Injective f`; go through the `_com` form
  rw [Rep_int_choice_f_def]
  cspT_auto

theorem cspT_Rep_int_choice_sum_const {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {P : proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → Pf c = P) →
        eqT (proc.Rep_int_choice C Pf) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_const {N : Set Nat} {Pf : Nat → proc p α}
    {P : proc p α} {M : p → domTType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → Pf n = P) →
        eqT (Rep_int_choice_nat N Pf) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_set_const {Xs : Set (Set α)} {Pf : Set α → proc p α}
    {P : proc p α} {M : p → domTType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → Pf X = P) →
        eqT (Rep_int_choice_set Xs Pf) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_com_const {X : Set α} {Pf : α → proc p α}
    {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqT (Rep_int_choice_com X Pf) M M P := by
  cspT_auto

theorem cspT_Rep_int_choice_f_const [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α}
    {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → Pf a = P) →
        eqT (Rep_int_choice_f f X Pf) M M P := by
  cspT_auto

theorem cspT_Int_Rep_int_choice_sum_union
    {C1 C2 : sets_nats α} {P1f P2f : aset_anat α → proc p α} {M : p → domTType α} :
    C1 =type= C2 →
      eqT
        ((proc.Rep_int_choice C1 P1f) |~| (proc.Rep_int_choice C2 P2f)) M M
        (proc.Rep_int_choice (C1 Uns C2) fun c =>
          procIte (c ∈ sumset C1 ∧ c ∈ sumset C2) (P1f c |~| P2f c)
            (procIte (c ∈ sumset C1) (P1f c) (P2f c))) := by
  cspT_auto

theorem cspT_Int_Rep_int_choice_nat_union
    {N1 N2 : Set Nat} {P1f P2f : Nat → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_nat N1 P1f) |~| (Rep_int_choice_nat N2 P2f)) M M
      (Rep_int_choice_nat (N1 ∪ N2) fun n =>
        procIte (n ∈ N1 ∧ n ∈ N2) (P1f n |~| P2f n)
          (procIte (n ∈ N1) (P1f n) (P2f n))) := by
  cspT_auto

theorem cspT_Int_Rep_int_choice_set_union
    {Xs1 Xs2 : Set (Set α)} {P1f P2f : Set α → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_set Xs1 P1f) |~| (Rep_int_choice_set Xs2 P2f)) M M
      (Rep_int_choice_set (Xs1 ∪ Xs2) fun X =>
        procIte (X ∈ Xs1 ∧ X ∈ Xs2) (P1f X |~| P2f X)
          (procIte (X ∈ Xs1) (P1f X) (P2f X))) := by
  cspT_auto

theorem cspT_Int_Rep_int_choice_com_union
    {X1 X2 : Set α} {P1f P2f : α → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_com X1 P1f) |~| (Rep_int_choice_com X2 P2f)) M M
      (Rep_int_choice_com (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a))) := by
  cspT_auto

theorem cspT_Int_Rep_int_choice_f_union [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {P1f P2f : β → proc p α} {M : p → domTType α} :
    eqT
      ((Rep_int_choice_f f X1 P1f) |~| (Rep_int_choice_f f X2 P2f)) M M
      (Rep_int_choice_f f (X1 ∪ X2) fun a =>
        procIte (a ∈ X1 ∧ a ∈ X2) (P1f a |~| P2f a)
          (procIte (a ∈ X1) (P1f a) (P2f a))) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_union_Int {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    C1 =type= C2 →
      eqT
        (proc.Rep_int_choice (C1 Uns C2) Pf) M M
        ((proc.Rep_int_choice C1 Pf) |~| (proc.Rep_int_choice C2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_union_Int
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_union_Int
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs1 Pf) |~| (Rep_int_choice_set Xs2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_union_Int
    {X1 X2 : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_union_Int [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT
      (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf)) := by
  cspT_auto

/-
(*********************************************************
                     Depth_rest
 *********************************************************)
-/

theorem cspT_Depth_rest_Zero {P : proc p α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (P |. 0) M1 M2 (proc.DIV : proc q α) := by
  cspT_auto

theorem cspT_Depth_rest_min {P : proc p α} {n m : Nat} {M : p → domTType α} :
    eqT ((P |. n) |. m) M M (P |. min n m) := by
  cspT_auto

theorem cspT_Depth_rest_congE {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {S : Prop} :
    eqT P M1 M2 Q →
      ((∀ m, eqT (P |. m) M1 M2 (Q |. m)) → S) →
        S := by
  cspT_auto

theorem cspT_nat_Depth_rest_UNIV {P : proc p α} {M : p → domTType α} :
    eqT P M M (Rep_int_choice_nat Set.univ fun n => P |. n) := by
  simp only [cspT_eqT_iff] at *
  intro t
  cspT_simp
  constructor
  · intro h
    rcases eq_or_ne t <> with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr ⟨lengtht t, trivial, h, le_refl _⟩
  · rintro (rfl | ⟨n, -, h, -⟩)
    · exact nilt_in_T
    · exact h

theorem cspT_nat_Depth_rest_lengthset {P : proc p α} {M : p → domTType α} :
    eqT P M M (Rep_int_choice_nat (lengthset P M) fun n => P |. n) := by
  simp only [cspT_eqT_iff] at *
  intro t
  cspT_simp
  constructor
  · intro h
    exact Or.inr ⟨lengtht t, ⟨t, h, Or.inl rfl⟩, h, le_refl _⟩
  · rintro (rfl | ⟨n, -, h, -⟩)
    · exact nilt_in_T
    · exact h

/-
(*********************************************************
                       partial
 *********************************************************)
-/

theorem cspT_Ext_pre_choice_partial {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice X Pf) M M
      (proc.Ext_pre_choice X fun x => procIte (x ∈ X) (Pf x) proc.DIV) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_partial {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice C Pf) M M
      (proc.Rep_int_choice C fun c => procIte (c ∈ sumset C) (Pf c) proc.DIV) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_partial {N : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N Pf) M M
      (Rep_int_choice_nat N fun n => procIte (n ∈ N) (Pf n) proc.DIV) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_partial
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs Pf) M M
      (Rep_int_choice_set Xs fun X => procIte (X ∈ Xs) (Pf X) proc.DIV) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_partial
    {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com X Pf) M M
      (Rep_int_choice_com X fun a => procIte (a ∈ X) (Pf a) proc.DIV) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_partial [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f X Pf) M M
      (Rep_int_choice_f f X fun a => procIte (a ∈ X) (Pf a) proc.DIV) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_set {Xs : Set (Set α)} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice (type1 Xs) Pf) M M
      (Rep_int_choice_set Xs fun X => Pf (type1 X)) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_nat {N : Set Nat} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice (type2 N) Pf) M M
      (Rep_int_choice_nat N fun n => Pf (type2 n)) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum {C : sets_nats α} {Pf : aset_anat α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice C Pf) M M
      (procIte (type1check C)
        (Rep_int_choice_set (open1 C) fun X => Pf (type1 X))
        (Rep_int_choice_nat (open2 C) fun n => Pf (type2 n))) := by
  cases C <;> cspT_auto

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)
-/

theorem cspT_first_Send_prefix {x : Type _} {a : x → α} {v : x} {P : proc p α}
    {M : p → domTType α} :
    eqT (Send_prefix a v P) M M (a v ~> P) := by
  cspT_auto

theorem cspT_first_Rec_prefix {x : Type _} [Inhabited x] {a : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    eqT (Rec_prefix a X Pf) M M
      (proc.Ext_pre_choice (a '' X) fun x => Pf (Function.invFun a x)) := by
  cspT_auto

theorem cspT_first_Int_pre_choice {X : Set α} {Pf : α → proc p α}
    {M : p → domTType α} :
    eqT (Int_pre_choice X Pf) M M
      (Rep_int_choice_com X fun x => x ~> Pf x) := by
  cspT_auto

theorem cspT_first_Nondet_send_prefix {x : Type _} [Inhabited x]
    {a : x → α} {X : Set x} {Pf : x → proc p α} {M : p → domTType α} :
    eqT (Nondet_send_prefix a X Pf) M M
      (Int_pre_choice (a '' X) fun x => Pf (Function.invFun a x)) := by
  cspT_auto

theorem cspT_Seq_compo_assoc {P Q R : proc p α} {M : p → domTType α} :
    eqT ((P ;; Q) ;; R) M M (P ;; (Q ;; R)) := by
  cspT_ext
  simp only [in_traces_Seq_compo]
  constructor
  · rintro (⟨s, rfl, (⟨s', rfl, hP⟩ | ⟨s1, u1, rfl, hP, hQ, hno1⟩)⟩ |
            ⟨s, u, rfl, hA, hR, hno⟩)
    · exact Or.inl ⟨s', rmTick_idem, hP⟩
    · exact Or.inr ⟨s1, rmTick u1, rmTick_appt_dist hno1,
        hP, Or.inl ⟨u1, rfl, hQ⟩, hno1⟩
    · rcases hA with ⟨w, hw, hPw⟩ | ⟨s2, u2, hEq, hP2, hQ2, hno2⟩
      · exfalso
        have hTick : noTick (s ^^^ (Abs_trace [event.Tick] : traceType α)) := by
          rw [hw]; exact noTick_rmTick
        exact not_noTick_Tick
          ((decompo_appt_noTick_only_if (Or.inl hno) hTick).2)
      · rcases (appt_decompo (Or.inl hno) (Or.inl hno2)).mp hEq with
          ⟨v, hv1, hv2, hv3⟩ | ⟨v, hv1, hv2, hv3⟩
        · -- Abs_trace [Tick] = v ^^^ u2
          rcases (appt_decompo_one_sym (a := event.Tick)
              (hv3.imp id And.right)).mp hv2 with ⟨hv, hu2⟩ | ⟨hv, hu2⟩
          · -- v = <Tick> : then s2 = s ^^^ <Tick>, contradicting noTick s2
            exfalso
            subst hv
            rw [← hv1] at hno2
            exact not_noTick_Tick
              ((decompo_appt_noTick_only_if (Or.inl hno) hno2).2)
          · -- v = <>, u2 = <Tick>
            subst hv hu2
            rw [appt_nil_right] at hv1
            subst hv1
            exact Or.inr ⟨s, u, rfl, hP2,
              Or.inr ⟨<>, u, (appt_nil_left).symm, by simpa [appt_nil_left] using hQ2,
                hR, noTick_nil⟩, hno⟩
        · -- s = s2 ^^^ v, u2 = v ^^^ <Tick>
          have hvno : noTick v := by
            rcases hv3 with h | ⟨_, h⟩
            · exact h
            · exact absurd h (one_neq_nil (a := event.Tick))
          subst hv1
          exact Or.inr ⟨s2, v ^^^ u,
            appt_assoc (Or.inl hno2) (Or.inl hvno), hP2,
            Or.inr ⟨v, u, rfl, by rw [hv2]; exact hQ2, hR, hvno⟩,
            hno2⟩
  · rintro (⟨s, rfl, hP⟩ |
            ⟨s, u, rfl, hP, (⟨w, rfl, hQw⟩ | ⟨s2, u2, rfl, hQ2, hR2, hno2⟩), hno⟩)
    · exact Or.inl ⟨rmTick s, rmTick_idem.symm, Or.inl ⟨s, rfl, hP⟩⟩
    · exact Or.inl ⟨s ^^^ w, (rmTick_appt_dist hno).symm,
        Or.inr ⟨s, w, rfl, hP, hQw, hno⟩⟩
    · refine Or.inr ⟨s ^^^ s2, u2,
        (appt_assoc (Or.inl hno) (Or.inl hno2)).symm,
        ?_, hR2, decompo_appt_noTick_if hno hno2⟩
      rw [appt_assoc (Or.inl hno) (Or.inl hno2)]
      exact Or.inr ⟨s, s2 ^^^ (Abs_trace [event.Tick] : traceType α), rfl, hP, hQ2, hno⟩

theorem cspT_Int_choice_eq_right {P : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT P M1 M2 Q1 →
      eqT P M1 M2 Q2 →
        eqT P M1 M2 (Q1 |~| Q2) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_eq_right_ALL
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqT P M1 M2 (Qf c)) →
        eqT P M1 M2 (proc.Rep_int_choice C Qf) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_eq_right
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqT P M1 M2 (Qf c)) →
        eqT P M1 M2 (proc.Rep_int_choice C Qf) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_eq_right
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqT P M1 M2 (Qf n)) →
        eqT P M1 M2 (Rep_int_choice_nat N Qf) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_eq_right
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqT P M1 M2 (Qf X)) →
        eqT P M1 M2 (Rep_int_choice_set Xs Qf) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_eq_right
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT P M1 M2 (Qf a)) →
        eqT P M1 M2 (Rep_int_choice_com X Qf) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_eq_right [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT P M1 M2 (Qf a)) →
        eqT P M1 M2 (Rep_int_choice_f f X Qf) := by
  cspT_auto

theorem cspT_Int_choice_eq_left {P : proc q α} {Q1 Q2 : proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT Q1 M1 M2 P →
      eqT Q2 M1 M2 P →
        eqT (Q1 |~| Q2) M1 M2 P := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_eq_left
    {C : sets_nats α} {P : proc q α} {Qf : aset_anat α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → eqT (Qf c) M1 M2 P) →
        eqT (proc.Rep_int_choice C Qf) M1 M2 P := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_eq_left
    {N : Set Nat} {P : proc q α} {Qf : Nat → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    N ≠ ∅ →
      (∀ n, n ∈ N → eqT (Qf n) M1 M2 P) →
        eqT (Rep_int_choice_nat N Qf) M1 M2 P := by
  cspT_auto

theorem cspT_Rep_int_choice_set_eq_left
    {Xs : Set (Set α)} {P : proc q α} {Qf : Set α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    Xs ≠ ∅ →
      (∀ X, X ∈ Xs → eqT (Qf X) M1 M2 P) →
        eqT (Rep_int_choice_set Xs Qf) M1 M2 P := by
  cspT_auto

theorem cspT_Rep_int_choice_com_eq_left
    {X : Set α} {P : proc q α} {Qf : α → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT (Qf a) M1 M2 P) →
        eqT (Rep_int_choice_com X Qf) M1 M2 P := by
  cspT_auto

theorem cspT_Rep_int_choice_f_eq_left [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {P : proc q α} {Qf : β → proc p α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      (∀ a, a ∈ X → eqT (Qf a) M1 M2 P) →
        eqT (Rep_int_choice_f f X Qf) M1 M2 P := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_Un {N1 N2 : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat (N1 ∪ N2) Pf) M M
      ((Rep_int_choice_nat N1 Pf) |~| (Rep_int_choice_nat N2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_Un
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set (Xs1 ∪ Xs2) Pf) M M
      ((Rep_int_choice_set Xs2 Pf) |~| (Rep_int_choice_set Xs1 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_Un
    {X1 X2 : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_com X1 Pf) |~| (Rep_int_choice_com X2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_Un [Inhabited β]
    {f : β → α} (hf : Injective f) {X1 X2 : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f (X1 ∪ X2) Pf) M M
      ((Rep_int_choice_f f X1 Pf) |~| (Rep_int_choice_f f X2 Pf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_insert {m : Nat} {N : Set Nat} {Pf : Nat → proc p α}
    {M : p → domTType α} :
    eqT (Rep_int_choice_nat (insert m N) Pf) M M
      (Pf m |~| Rep_int_choice_nat N Pf) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_insert
    {Y : Set α} {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set (insert Y Xs) Pf) M M
      (Pf Y |~| Rep_int_choice_set Xs Pf) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_insert
    {a : α} {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_com X Pf) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_insert [Inhabited β]
    {f : β → α} (hf : Injective f) {a : β} {X : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f (insert a X) Pf) M M
      (Pf a |~| Rep_int_choice_f f X Pf) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_map_f [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com (f '' X) Pf) M M
      (Rep_int_choice_f f X fun x => Pf (f x)) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_map_f [Inhabited β] [Inhabited γ]
    {f : β → α} {g : γ → β} (hf : Injective f) (hg : Injective g)
    {X : Set γ} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f (g '' X) Pf) M M
      (Rep_int_choice_f (f ∘ g) X fun x => Pf (g x)) := by
  cspT_auto
