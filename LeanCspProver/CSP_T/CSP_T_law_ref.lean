           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_basic

open Function
open SumType

noncomputable section

/-
(*****************************************************************

         1. rules for refinement

 *****************************************************************)
-/

/- -------------------------------------------------------*
 |            refinement and equality                    |
 *------------------------------------------------------- -/

theorem cspT_ref_eq_iff {P Q : proc p α} {M : p → domTType α} :
    refT P M M Q ↔ eqT P M M (Q |~| P) := by
  rw [cspT_refT_semantics, cspT_eqT_semantics]
  constructor
  · intro hPQ
    apply le_antisymm
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Int_choice]
      exact Or.inr ht
    · rw [subdomT_iff]
      intro t ht
      rw [in_traces_Int_choice] at ht
      rcases ht with ht | ht
      · exact hPQ ht
      · exact ht
  · intro hEq
    rw [subdomT_iff]
    intro t ht
    have ht' : t :t traces (Q |~| P) M := by
      rw [in_traces_Int_choice]
      exact Or.inl ht
    simpa [hEq] using ht'

/- -------------------------------------------------------*
 |             simp STOP [+]                             |
 *------------------------------------------------------- -/

theorem cspT_Ent_choice_left1_ref {P Q : proc p α} {M : p → domTType α} :
    refT (P [+] Q) M M P := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Ext_choice]
  exact Or.inl ht

theorem cspT_Ent_choice_left2_ref {P Q : proc p α} {M : p → domTType α} :
    refT (P [+] Q) M M Q := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Ext_choice]
  exact Or.inr ht

/- The Isabelle theorem bundle `cspT_Ent_choice_left_ref` is represented by
   `cspT_Ent_choice_left1_ref` and `cspT_Ent_choice_left2_ref`. -/

/- -------------------------------------------------------*
 |              decompose Internal choice                |
 *------------------------------------------------------- -/

/- (*** or <= ***) -/                                   /- unsafe -/

theorem cspT_Int_choice_left1
    {P1 P2 : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : refT P1 M1 M2 Q) :
    refT (P1 |~| P2) M1 M2 Q := by
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Int_choice]
  exact Or.inl (hPQ t ht)

theorem cspT_Int_choice_left2
    {P1 P2 : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : refT P2 M1 M2 Q) :
    refT (P1 |~| P2) M1 M2 Q := by
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Int_choice]
  exact Or.inr (hPQ t ht)

/- (*** <= and ***) -/                                    /- safe -/

theorem cspT_Int_choice_right
    {P : proc p α} {Q1 Q2 : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hP1 : refT P M1 M2 Q1) (hP2 : refT P M1 M2 Q2) :
    refT P M1 M2 (Q1 |~| Q2) := by
  rw [cspT_refT_semantics, subdomT_iff] at hP1 hP2 ⊢
  intro t ht
  rw [in_traces_Int_choice] at ht
  rcases ht with ht | ht
  · exact hP1 t ht
  · exact hP2 t ht

/- -------------------------------------------------------*
 |        decompose Replicated internal choice           |
 *------------------------------------------------------- -/

/- (*** EX <= ***) -/                                     /- unsafe -/

theorem cspT_Rep_int_choice_sum_left
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∃ c, c ∈ sumset C ∧ refT (Pf c) M1 M2 Q) :
    refT (proc.Rep_int_choice C Pf) M1 M2 Q := by
  rcases hPQ with ⟨c, hc, hPQ⟩
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Rep_int_choice_sum]
  exact Or.inr ⟨c, hc, hPQ t ht⟩

theorem cspT_Rep_int_choice_sum_left_x
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc q α}
    {c : aset_anat α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hc : c ∈ sumset C) (hPQ : refT (Pf c) M1 M2 Q) :
    refT (proc.Rep_int_choice C Pf) M1 M2 Q := by
  exact cspT_Rep_int_choice_sum_left ⟨c, hc, hPQ⟩

theorem cspT_Rep_int_choice_nat_left
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∃ n, n ∈ N ∧ refT (Pf n) M1 M2 Q) :
    refT (Rep_int_choice_nat N Pf) M1 M2 Q := by
  rcases hPQ with ⟨n, hn, hPQ⟩
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Rep_int_choice_nat]
  exact Or.inr ⟨n, hn, hPQ t ht⟩

theorem cspT_Rep_int_choice_nat_left_x
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc q α}
    {n : Nat} {M1 : p → domTType α} {M2 : q → domTType α}
    (hn : n ∈ N) (hPQ : refT (Pf n) M1 M2 Q) :
    refT (Rep_int_choice_nat N Pf) M1 M2 Q := by
  exact cspT_Rep_int_choice_nat_left ⟨n, hn, hPQ⟩

theorem cspT_Rep_int_choice_set_left
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∃ X, X ∈ Xs ∧ refT (Pf X) M1 M2 Q) :
    refT (Rep_int_choice_set Xs Pf) M1 M2 Q := by
  rcases hPQ with ⟨X, hX, hPQ⟩
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Rep_int_choice_set]
  exact Or.inr ⟨X, hX, hPQ t ht⟩

theorem cspT_Rep_int_choice_set_left_x
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc q α}
    {X : Set α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : X ∈ Xs) (hPQ : refT (Pf X) M1 M2 Q) :
    refT (Rep_int_choice_set Xs Pf) M1 M2 Q := by
  exact cspT_Rep_int_choice_set_left ⟨X, hX, hPQ⟩

theorem cspT_Rep_int_choice_com_left [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∃ a, a ∈ X ∧ refT (Pf a) M1 M2 Q) :
    refT (Rep_int_choice_com X Pf) M1 M2 Q := by
  rcases hPQ with ⟨a, ha, hPQ⟩
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Rep_int_choice_com]
  exact Or.inr ⟨a, ha, hPQ t ht⟩

theorem cspT_Rep_int_choice_com_left_x [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc q α}
    {a : α} {M1 : p → domTType α} {M2 : q → domTType α}
    (ha : a ∈ X) (hPQ : refT (Pf a) M1 M2 Q) :
    refT (Rep_int_choice_com X Pf) M1 M2 Q := by
  exact cspT_Rep_int_choice_com_left ⟨a, ha, hPQ⟩

theorem cspT_Rep_int_choice_f_left [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {Pf : β → proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hPQ : ∃ a, a ∈ X ∧ refT (Pf a) M1 M2 Q) :
    refT (Rep_int_choice_f f X Pf) M1 M2 Q := by
  rcases hPQ with ⟨a, ha, hPQ⟩
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Rep_int_choice_f hf]
  exact Or.inr ⟨a, ha, hPQ t ht⟩

theorem cspT_Rep_int_choice_f_left_x [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {Pf : β → proc p α} {Q : proc q α}
    {a : β} {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (ha : a ∈ X) (hPQ : refT (Pf a) M1 M2 Q) :
    refT (Rep_int_choice_f f X Pf) M1 M2 Q := by
  exact cspT_Rep_int_choice_f_left hf ⟨a, ha, hPQ⟩

/- The Isabelle theorem bundle `cspT_Rep_int_choice_left` is represented by
   `cspT_Rep_int_choice_sum_left`, `cspT_Rep_int_choice_nat_left`,
   `cspT_Rep_int_choice_set_left`, `cspT_Rep_int_choice_com_left`, and
   `cspT_Rep_int_choice_f_left`. -/

/- The Isabelle theorem bundle `cspT_Rep_int_choice_left_x` is represented
   by `cspT_Rep_int_choice_sum_left_x`, `cspT_Rep_int_choice_nat_left_x`,
   `cspT_Rep_int_choice_set_left_x`, `cspT_Rep_int_choice_com_left_x`, and
   `cspT_Rep_int_choice_f_left_x`. -/

/- (*** <= ALL ***) -/                                   /- safe -/

theorem cspT_Rep_int_choice_sum_right
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ c, c ∈ sumset C → refT P M1 M2 (Qf c)) :
    refT P M1 M2 (proc.Rep_int_choice C Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_sum] at ht
  rcases ht with rfl | ⟨c, hc, ht⟩
  · exact nilt_in_T
  · have hPc : refT P M1 M2 (Qf c) := hPQ c hc
    rw [cspT_refT_semantics, subdomT_iff] at hPc
    exact hPc t ht

theorem cspT_Rep_int_choice_nat_right
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ n, n ∈ N → refT P M1 M2 (Qf n)) :
    refT P M1 M2 (Rep_int_choice_nat N Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_nat] at ht
  rcases ht with rfl | ⟨n, hn, ht⟩
  · exact nilt_in_T
  · have hPn : refT P M1 M2 (Qf n) := hPQ n hn
    rw [cspT_refT_semantics, subdomT_iff] at hPn
    exact hPn t ht

theorem cspT_Rep_int_choice_set_right
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ X, X ∈ Xs → refT P M1 M2 (Qf X)) :
    refT P M1 M2 (Rep_int_choice_set Xs Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_set] at ht
  rcases ht with rfl | ⟨X, hX, ht⟩
  · exact nilt_in_T
  · have hPX : refT P M1 M2 (Qf X) := hPQ X hX
    rw [cspT_refT_semantics, subdomT_iff] at hPX
    exact hPX t ht

theorem cspT_Rep_int_choice_com_right [Inhabited α]
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ a, a ∈ X → refT P M1 M2 (Qf a)) :
    refT P M1 M2 (Rep_int_choice_com X Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_com] at ht
  rcases ht with rfl | ⟨a, ha, ht⟩
  · exact nilt_in_T
  · have hPa : refT P M1 M2 (Qf a) := hPQ a ha
    rw [cspT_refT_semantics, subdomT_iff] at hPa
    exact hPa t ht

theorem cspT_Rep_int_choice_f_right [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hPQ : ∀ a, a ∈ X → refT P M1 M2 (Qf a)) :
    refT P M1 M2 (Rep_int_choice_f f X Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_f hf] at ht
  rcases ht with rfl | ⟨a, ha, ht⟩
  · exact nilt_in_T
  · have hPa : refT P M1 M2 (Qf a) := hPQ a ha
    rw [cspT_refT_semantics, subdomT_iff] at hPa
    exact hPa t ht

/- The Isabelle theorem bundle `cspT_Rep_int_choice_right` is represented
   by `cspT_Rep_int_choice_sum_right`, `cspT_Rep_int_choice_nat_right`,
   `cspT_Rep_int_choice_set_right`, `cspT_Rep_int_choice_com_right`, and
   `cspT_Rep_int_choice_f_right`. -/

/- 1,2,3,f E -/

theorem cspT_Rep_int_choice_sum_rightE
    {C : sets_nats α} {P : proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {R : Prop}
    (hPQ : refT P M1 M2 (proc.Rep_int_choice C Qf))
    (hR : (∀ c, c ∈ sumset C → refT P M1 M2 (Qf c)) → R) :
    R := by
  apply hR
  intro c hc
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  exact hPQ t ((in_traces_Rep_int_choice_sum (t := t) (C := C) (Pf := Qf) (M := M2)).2
    (Or.inr ⟨c, hc, ht⟩))

theorem cspT_Rep_int_choice_nat_rightE
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {R : Prop}
    (hPQ : refT P M1 M2 (Rep_int_choice_nat N Qf))
    (hR : (∀ n, n ∈ N → refT P M1 M2 (Qf n)) → R) :
    R := by
  apply hR
  intro n hn
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  exact hPQ t ((in_traces_Rep_int_choice_nat (t := t) (N := N) (Pf := Qf) (M := M2)).2
    (Or.inr ⟨n, hn, ht⟩))

theorem cspT_Rep_int_choice_set_rightE
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {R : Prop}
    (hPQ : refT P M1 M2 (Rep_int_choice_set Xs Qf))
    (hR : (∀ X, X ∈ Xs → refT P M1 M2 (Qf X)) → R) :
    R := by
  apply hR
  intro X hX
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  exact hPQ t ((in_traces_Rep_int_choice_set (t := t) (Xs := Xs) (Pf := Qf) (M := M2)).2
    (Or.inr ⟨X, hX, ht⟩))

theorem cspT_Rep_int_choice_com_rightE [Inhabited α]
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {R : Prop}
    (hPQ : refT P M1 M2 (Rep_int_choice_com X Qf))
    (hR : (∀ a, a ∈ X → refT P M1 M2 (Qf a)) → R) :
    R := by
  apply hR
  intro a ha
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  exact hPQ t ((in_traces_Rep_int_choice_com (t := t) (X := X) (Pf := Qf) (M := M2)).2
    (Or.inr ⟨a, ha, ht⟩))

theorem cspT_Rep_int_choice_f_rightE [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {R : Prop}
    (hPQ : refT P M1 M2 (Rep_int_choice_f f X Qf)) (hf : Injective f)
    (hR : (∀ a, a ∈ X → refT P M1 M2 (Qf a)) → R) :
    R := by
  apply hR
  intro a ha
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  exact hPQ t ((in_traces_Rep_int_choice_f hf (t := t) (X := X) (Pf := Qf) (M := M2)).2
    (Or.inr ⟨a, ha, ht⟩))

/- The Isabelle theorem bundle `cspT_Rep_int_choice_rightE` is represented
   by `cspT_Rep_int_choice_sum_rightE`, `cspT_Rep_int_choice_nat_rightE`,
   `cspT_Rep_int_choice_set_rightE`, `cspT_Rep_int_choice_com_rightE`, and
   `cspT_Rep_int_choice_f_rightE`. -/

/- -------------------------------------------------------*
 |             decomposition with subset                 |
 *------------------------------------------------------- -/

/- (*** Rep_int_choice ***) -/                                  /- unsafe -/

theorem cspT_Rep_int_choice_sum_subset
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hC : sumset C2 ⊆ sumset C1)
    (hPQ : ∀ c, c ∈ sumset C2 → refT (Pf c) M1 M2 (Qf c)) :
    refT (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_sum] at ht
  rw [in_traces_Rep_int_choice_sum]
  rcases ht with rfl | ⟨c, hc, ht⟩
  · exact Or.inl rfl
  · have hPc : refT (Pf c) M1 M2 (Qf c) := hPQ c hc
    rw [cspT_refT_semantics, subdomT_iff] at hPc
    exact Or.inr ⟨c, hC hc, hPc t ht⟩

theorem cspT_Rep_int_choice_nat_subset
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hN : N2 ⊆ N1)
    (hPQ : ∀ n, n ∈ N2 → refT (Pf n) M1 M2 (Qf n)) :
    refT (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_nat] at ht
  rw [in_traces_Rep_int_choice_nat]
  rcases ht with rfl | ⟨n, hn, ht⟩
  · exact Or.inl rfl
  · have hPn : refT (Pf n) M1 M2 (Qf n) := hPQ n hn
    rw [cspT_refT_semantics, subdomT_iff] at hPn
    exact Or.inr ⟨n, hN hn, hPn t ht⟩

theorem cspT_Rep_int_choice_set_subset
    {Xs Ys : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : Ys ⊆ Xs)
    (hPQ : ∀ X, X ∈ Ys → refT (Pf X) M1 M2 (Qf X)) :
    refT (Rep_int_choice_set Xs Pf) M1 M2 (Rep_int_choice_set Ys Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_set] at ht
  rw [in_traces_Rep_int_choice_set]
  rcases ht with rfl | ⟨X, hY, ht⟩
  · exact Or.inl rfl
  · have hPX : refT (Pf X) M1 M2 (Qf X) := hPQ X hY
    rw [cspT_refT_semantics, subdomT_iff] at hPX
    exact Or.inr ⟨X, hX hY, hPX t ht⟩

theorem cspT_Rep_int_choice_com_subset [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : Y ⊆ X)
    (hPQ : ∀ a, a ∈ Y → refT (Pf a) M1 M2 (Qf a)) :
    refT (Rep_int_choice_com X Pf) M1 M2 (Rep_int_choice_com Y Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_com] at ht
  rw [in_traces_Rep_int_choice_com]
  rcases ht with rfl | ⟨a, ha, ht⟩
  · exact Or.inl rfl
  · have hPa : refT (Pf a) M1 M2 (Qf a) := hPQ a ha
    rw [cspT_refT_semantics, subdomT_iff] at hPa
    exact Or.inr ⟨a, hXY ha, hPa t ht⟩

theorem cspT_Rep_int_choice_f_subset [Inhabited α] [Inhabited β]
    {f : β → α} {X Y : Set β} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hXY : Y ⊆ X)
    (hPQ : ∀ a, a ∈ Y → refT (Pf a) M1 M2 (Qf a)) :
    refT (Rep_int_choice_f f X Pf) M1 M2 (Rep_int_choice_f f Y Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_f hf] at ht
  rw [in_traces_Rep_int_choice_f hf]
  rcases ht with rfl | ⟨a, ha, ht⟩
  · exact Or.inl rfl
  · have hPa : refT (Pf a) M1 M2 (Qf a) := hPQ a ha
    rw [cspT_refT_semantics, subdomT_iff] at hPa
    exact Or.inr ⟨a, hXY ha, hPa t ht⟩

/- The Isabelle theorem bundle `cspT_Rep_int_choice_subset` is represented
   by `cspT_Rep_int_choice_sum_subset`, `cspT_Rep_int_choice_nat_subset`,
   `cspT_Rep_int_choice_set_subset`, `cspT_Rep_int_choice_com_subset`, and
   `cspT_Rep_int_choice_f_subset`. -/

/- (*** ! x:X .. and ? -> ***) -/

theorem cspT_Int_Ext_pre_choice_subset [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (_hY : Y ≠ ∅) (hYX : Y ⊆ X)
    (hPQ : ∀ a, a ∈ Y → refT (Pf a) M1 M2 (Qf a)) :
    refT (Int_pre_choice X Pf) M1 M2 (proc.Ext_pre_choice Y Qf) := by
  rw [Int_pre_choice_def]
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Ext_pre_choice] at ht
  rw [in_traces_Rep_int_choice_com]
  rcases ht with rfl | ⟨a, s, rfl, hs, haY⟩
  · exact Or.inl rfl
  · have hQa : refT (Pf a) M1 M2 (Qf a) := hPQ a haY
    rw [cspT_refT_semantics, subdomT_iff] at hQa
    have hs' : s :t traces (Pf a) M1 := hQa s hs
    exact Or.inr ⟨a, hYX haY, (in_traces_Act_prefix (t := Abs_trace [event.Ev a] ^^^ s)
      (a := a) (P := Pf a) (M := M1)).2 (Or.inr ⟨s, rfl, hs'⟩)⟩

/- The Isabelle theorem bundle `cspT_decompo_subset` is represented by
   `cspT_Rep_int_choice_subset` and `cspT_Int_Ext_pre_choice_subset`. -/

/- -------------------------------------------------------*
 |               decompose external choice               |
 *------------------------------------------------------- -/

theorem cspT_Ext_choice_right
    {P : proc p α} {Q1 Q2 : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hP1 : refT P M1 M2 Q1) (hP2 : refT P M1 M2 Q2) :
    refT P M1 M2 (Q1 [+] Q2) := by
  rw [cspT_refT_semantics, subdomT_iff] at hP1 hP2 ⊢
  intro t ht
  rw [in_traces_Ext_choice] at ht
  rcases ht with ht | ht
  · exact hP1 t ht
  · exact hP2 t ht
