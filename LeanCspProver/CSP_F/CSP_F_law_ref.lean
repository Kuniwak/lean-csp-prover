           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_ref

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

theorem cspF_ref_eq_iff {P Q : proc p α} {M : p → domFType α} :
    refF P M M Q ↔ eqF P M M (Q |~| P) := by
  rw [cspF_cspT_refF_semantics, cspF_cspT_eqF_semantics, cspT_ref_eq_iff]
  constructor
  · rintro ⟨hT, hF⟩
    refine ⟨hT, ?_⟩
    apply le_antisymm
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_Int_choice]
      exact Or.inr hs
    · rw [subsetF_iff]
      intro s X hs
      rw [in_failures_Int_choice] at hs
      exact hs.elim (fun hsQ => hF hsQ) id
  · rintro ⟨hT, hEq⟩
    refine ⟨hT, ?_⟩
    rw [subsetF_iff]
    intro s X hs
    have hs' : (s, X) :f failures (Q |~| P) M := by
      rw [in_failures_Int_choice]
      exact Or.inl hs
    simpa [hEq] using hs'

/- -------------------------------------------------------*
 |              decompose Internal choice                |
 *------------------------------------------------------- -/

/- (*** or <= ***) -/                                   /- unsafe -/

theorem cspF_Int_choice_left1
    {P1 P2 : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : refF P1 M1 M2 Q) :
    refF (P1 |~| P2) M1 M2 Q := by
  rcases (cspF_cspT_refF_semantics.mp hPQ) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Int_choice_left1 hT, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Int_choice]
  exact Or.inl (hF hs)

theorem cspF_Int_choice_left2
    {P1 P2 : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : refF P2 M1 M2 Q) :
    refF (P1 |~| P2) M1 M2 Q := by
  rcases (cspF_cspT_refF_semantics.mp hPQ) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Int_choice_left2 hT, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Int_choice]
  exact Or.inr (hF hs)

/- (*** <= and ***) -/                                    /- safe -/

theorem cspF_Int_choice_right
    {P : proc p α} {Q1 Q2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hP1 : refF P M1 M2 Q1) (hP2 : refF P M1 M2 Q2) :
    refF P M1 M2 (Q1 |~| Q2) := by
  rcases (cspF_cspT_refF_semantics.mp hP1) with ⟨hT1, hF1⟩
  rcases (cspF_cspT_refF_semantics.mp hP2) with ⟨hT2, hF2⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Int_choice_right hT1 hT2, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Int_choice] at hs
  exact hs.elim (fun hs1 => hF1 hs1) (fun hs2 => hF2 hs2)

/- -------------------------------------------------------*
 |        decompose Replicated internal choice           |
 *------------------------------------------------------- -/

/- (*** EX <= ***) -/                                     /- unsafe -/

theorem cspF_Rep_int_choice_nat_left
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∃ n, n ∈ N ∧ refF (Pf n) M1 M2 Q) :
    refF (Rep_int_choice_nat N Pf) M1 M2 Q := by
  rcases hPQ with ⟨n, hn, hRef⟩
  rcases (cspF_cspT_refF_semantics.mp hRef) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_nat_left ⟨n, hn, hT⟩, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Rep_int_choice_nat]
  exact ⟨n, hn, hF hs⟩

theorem cspF_Rep_int_choice_nat_left_x
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc q α}
    {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α}
    (hn : n ∈ N) (hPQ : refF (Pf n) M1 M2 Q) :
    refF (Rep_int_choice_nat N Pf) M1 M2 Q := by
  exact cspF_Rep_int_choice_nat_left ⟨n, hn, hPQ⟩

theorem cspF_Rep_int_choice_set_left
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∃ X, X ∈ Xs ∧ refF (Pf X) M1 M2 Q) :
    refF (Rep_int_choice_set Xs Pf) M1 M2 Q := by
  rcases hPQ with ⟨X, hX, hRef⟩
  rcases (cspF_cspT_refF_semantics.mp hRef) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_set_left ⟨X, hX, hT⟩, ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  rw [in_failures_Rep_int_choice_set]
  exact ⟨X, hX, hF hs⟩

theorem cspF_Rep_int_choice_set_left_x
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc q α}
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : X ∈ Xs) (hPQ : refF (Pf X) M1 M2 Q) :
    refF (Rep_int_choice_set Xs Pf) M1 M2 Q := by
  exact cspF_Rep_int_choice_set_left ⟨X, hX, hPQ⟩

theorem cspF_Rep_int_choice_com_left [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∃ a, a ∈ X ∧ refF (Pf a) M1 M2 Q) :
    refF (Rep_int_choice_com X Pf) M1 M2 Q := by
  rcases hPQ with ⟨a, ha, hRef⟩
  rcases (cspF_cspT_refF_semantics.mp hRef) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_com_left ⟨a, ha, hT⟩, ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  rw [in_failures_Rep_int_choice_com]
  exact ⟨a, ha, hF hs⟩

theorem cspF_Rep_int_choice_com_left_x [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc q α}
    {a : α} {M1 : p → domFType α} {M2 : q → domFType α}
    (ha : a ∈ X) (hPQ : refF (Pf a) M1 M2 Q) :
    refF (Rep_int_choice_com X Pf) M1 M2 Q := by
  exact cspF_Rep_int_choice_com_left ⟨a, ha, hPQ⟩

theorem cspF_Rep_int_choice_f_left [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {Pf : β → proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hPQ : ∃ a, a ∈ X ∧ refF (Pf a) M1 M2 Q) :
    refF (Rep_int_choice_f f X Pf) M1 M2 Q := by
  rcases hPQ with ⟨a, ha, hRef⟩
  rcases (cspF_cspT_refF_semantics.mp hRef) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_f_left hf ⟨a, ha, hT⟩, ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  rw [in_failures_Rep_int_choice_f hf]
  exact ⟨a, ha, hF hs⟩

theorem cspF_Rep_int_choice_f_left_x [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {Pf : β → proc p α} {Q : proc q α}
    {a : β} {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (ha : a ∈ X) (hPQ : refF (Pf a) M1 M2 Q) :
    refF (Rep_int_choice_f f X Pf) M1 M2 Q := by
  exact cspF_Rep_int_choice_f_left hf ⟨a, ha, hPQ⟩

/- The Isabelle theorem bundle `cspF_Rep_int_choice_left` is represented by
   `cspF_Rep_int_choice_nat_left`, `cspF_Rep_int_choice_set_left`,
   `cspF_Rep_int_choice_com_left`, and `cspF_Rep_int_choice_f_left`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_left_x` is represented
   by `cspF_Rep_int_choice_nat_left_x`, `cspF_Rep_int_choice_set_left_x`,
   `cspF_Rep_int_choice_com_left_x`, and `cspF_Rep_int_choice_f_left_x`. -/

/- (*** <= ALL ***) -/                                   /- safe -/

theorem cspF_Rep_int_choice_nat_right
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ n, n ∈ N → refF P M1 M2 (Qf n)) :
    refF P M1 M2 (Rep_int_choice_nat N Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_nat_right
    intro n hn
    exact (cspF_cspT_refF_semantics.mp (hPQ n hn)).1
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Rep_int_choice_nat] at hs
    rcases hs with ⟨n, hn, hs⟩
    exact (cspF_cspT_refF_semantics.mp (hPQ n hn)).2 hs

theorem cspF_Rep_int_choice_set_right
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ X, X ∈ Xs → refF P M1 M2 (Qf X)) :
    refF P M1 M2 (Rep_int_choice_set Xs Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_set_right
    intro X hX
    exact (cspF_cspT_refF_semantics.mp (hPQ X hX)).1
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Rep_int_choice_set] at hs
    rcases hs with ⟨X, hX, hs⟩
    exact (cspF_cspT_refF_semantics.mp (hPQ X hX)).2 hs

theorem cspF_Rep_int_choice_com_right [Inhabited α]
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ a, a ∈ X → refF P M1 M2 (Qf a)) :
    refF P M1 M2 (Rep_int_choice_com X Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_com_right
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).1
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Rep_int_choice_com] at hs
    rcases hs with ⟨a, ha, hs⟩
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).2 hs

theorem cspF_Rep_int_choice_f_right [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hPQ : ∀ a, a ∈ X → refF P M1 M2 (Qf a)) :
    refF P M1 M2 (Rep_int_choice_f f X Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_f_right hf
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).1
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Rep_int_choice_f hf] at hs
    rcases hs with ⟨a, ha, hs⟩
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).2 hs

/- The Isabelle theorem bundle `cspF_Rep_int_choice_right` is represented by
   `cspF_Rep_int_choice_nat_right`, `cspF_Rep_int_choice_set_right`,
   `cspF_Rep_int_choice_com_right`, and `cspF_Rep_int_choice_f_right`. -/

/- 1,2,3,f E -/

theorem cspF_Rep_int_choice_nat_rightE
    {N : Set Nat} {P : proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {R : Prop}
    (hPQ : refF P M1 M2 (Rep_int_choice_nat N Qf))
    (hR : (∀ n, n ∈ N → refF P M1 M2 (Qf n)) → R) :
    R := by
  apply hR
  intro n hn
  rcases (cspF_cspT_refF_semantics.mp hPQ) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_nat_rightE hT (fun hAll => hAll n hn), ?_⟩
  rw [subsetF_iff]
  intro s X hs
  exact hF <| (in_failures_Rep_int_choice_nat
    (f := ((s, X) : failure α)) (N := N) (Pf := Qf) (M := M2)).2 ⟨n, hn, hs⟩

theorem cspF_Rep_int_choice_set_rightE
    {Xs : Set (Set α)} {P : proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {R : Prop}
    (hPQ : refF P M1 M2 (Rep_int_choice_set Xs Qf))
    (hR : (∀ X, X ∈ Xs → refF P M1 M2 (Qf X)) → R) :
    R := by
  apply hR
  intro X hX
  rcases (cspF_cspT_refF_semantics.mp hPQ) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_set_rightE hT (fun hAll => hAll X hX), ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  exact hF <| (in_failures_Rep_int_choice_set
    (f := ((s, Y) : failure α)) (Xs := Xs) (Pf := Qf) (M := M2)).2 ⟨X, hX, hs⟩

theorem cspF_Rep_int_choice_com_rightE [Inhabited α]
    {X : Set α} {P : proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {R : Prop}
    (hPQ : refF P M1 M2 (Rep_int_choice_com X Qf))
    (hR : (∀ a, a ∈ X → refF P M1 M2 (Qf a)) → R) :
    R := by
  apply hR
  intro a ha
  rcases (cspF_cspT_refF_semantics.mp hPQ) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_com_rightE hT (fun hAll => hAll a ha), ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  exact hF <| (in_failures_Rep_int_choice_com
    (f := ((s, Y) : failure α)) (X := X) (Pf := Qf) (M := M2)).2 ⟨a, ha, hs⟩

theorem cspF_Rep_int_choice_f_rightE [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {R : Prop}
    (hPQ : refF P M1 M2 (Rep_int_choice_f f X Qf)) (hf : Injective f)
    (hR : (∀ a, a ∈ X → refF P M1 M2 (Qf a)) → R) :
    R := by
  apply hR
  intro a ha
  rcases (cspF_cspT_refF_semantics.mp hPQ) with ⟨hT, hF⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_f_rightE hT hf (fun hAll => hAll a ha), ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  exact hF <| (in_failures_Rep_int_choice_f
    (f := ((s, Y) : failure α)) hf (X := X) (Pf := Qf) (M := M2)).2 ⟨a, ha, hs⟩

/- The Isabelle theorem bundle `cspF_Rep_int_choice_rightE` is represented by
   `cspF_Rep_int_choice_nat_rightE`, `cspF_Rep_int_choice_set_rightE`,
   `cspF_Rep_int_choice_com_rightE`, and `cspF_Rep_int_choice_f_rightE`. -/

/- -------------------------------------------------------*
 |             decomposition with subset                 |
 *------------------------------------------------------- -/

theorem cspF_Rep_int_choice_nat_subset
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hN : N2 ⊆ N1) (hPQ : ∀ n, n ∈ N2 → refF (Pf n) M1 M2 (Qf n)) :
    refF (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_nat_subset hN
    intro n hn
    exact (cspF_cspT_refF_semantics.mp (hPQ n hn)).1
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Rep_int_choice_nat] at hs
    rw [in_failures_Rep_int_choice_nat]
    rcases hs with ⟨n, hn, hs⟩
    exact ⟨n, hN hn, (cspF_cspT_refF_semantics.mp (hPQ n hn)).2 hs⟩

theorem cspF_Rep_int_choice_set_subset
    {Xs Ys : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : Ys ⊆ Xs) (hPQ : ∀ X, X ∈ Ys → refF (Pf X) M1 M2 (Qf X)) :
    refF (Rep_int_choice_set Xs Pf) M1 M2 (Rep_int_choice_set Ys Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_set_subset hX
    intro X hY
    exact (cspF_cspT_refF_semantics.mp (hPQ X hY)).1
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Rep_int_choice_set] at hs
    rw [in_failures_Rep_int_choice_set]
    rcases hs with ⟨X, hY, hs⟩
    exact ⟨X, hX hY, (cspF_cspT_refF_semantics.mp (hPQ X hY)).2 hs⟩

theorem cspF_Rep_int_choice_com_subset [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hYX : Y ⊆ X) (hPQ : ∀ a, a ∈ Y → refF (Pf a) M1 M2 (Qf a)) :
    refF (Rep_int_choice_com X Pf) M1 M2 (Rep_int_choice_com Y Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_com_subset hYX
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).1
  · rw [subsetF_iff]
    intro s Z hs
    rw [in_failures_Rep_int_choice_com] at hs
    rw [in_failures_Rep_int_choice_com]
    rcases hs with ⟨a, ha, hs⟩
    exact ⟨a, hYX ha, (cspF_cspT_refF_semantics.mp (hPQ a ha)).2 hs⟩

theorem cspF_Rep_int_choice_f_subset [Inhabited α] [Inhabited β]
    {f : β → α} {X Y : Set β} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hYX : Y ⊆ X) (hPQ : ∀ a, a ∈ Y → refF (Pf a) M1 M2 (Qf a)) :
    refF (Rep_int_choice_f f X Pf) M1 M2 (Rep_int_choice_f f Y Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_f_subset hf hYX
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).1
  · rw [subsetF_iff]
    intro s Z hs
    rw [in_failures_Rep_int_choice_f hf] at hs
    rw [in_failures_Rep_int_choice_f hf]
    rcases hs with ⟨a, ha, hs⟩
    exact ⟨a, hYX ha, (cspF_cspT_refF_semantics.mp (hPQ a ha)).2 hs⟩

/- The Isabelle theorem bundle `cspF_Rep_int_choice_subset` is represented
   by `cspF_Rep_int_choice_nat_subset`, `cspF_Rep_int_choice_set_subset`,
   `cspF_Rep_int_choice_com_subset`, and `cspF_Rep_int_choice_f_subset`. -/

/- (*** ! x:X .. and ? -> ***) -/

theorem cspF_Int_Ext_pre_choice_subset [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hY : Y ≠ ∅) (hYX : Y ⊆ X) (hPQ : ∀ a, a ∈ Y → refF (Pf a) M1 M2 (Qf a)) :
    refF (Int_pre_choice X Pf) M1 M2 (proc.Ext_pre_choice Y Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Int_Ext_pre_choice_subset hY hYX
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).1
  · rw [subsetF_iff]
    intro s Z hs
    rw [in_failures_Ext_pre_choice] at hs
    rw [Int_pre_choice_def, in_failures_Rep_int_choice_com]
    rcases hs with hs | hs
    · rcases hs with ⟨Z', hEq, hEmpty⟩
      rcases Prod.mk.inj hEq with ⟨hsEq, hZEq⟩
      subst hsEq
      subst hZEq
      rcases Set.nonempty_iff_ne_empty.mpr hY with ⟨a, haY⟩
      refine ⟨a, hYX haY, ?_⟩
      rw [in_failures_Act_prefix]
      refine Or.inl ⟨Z, rfl, ?_⟩
      intro hEv
      have : event.Ev a ∈ (event.Ev '' Y) ∩ Z := ⟨⟨a, haY, rfl⟩, hEv⟩
      simp [hEmpty] at this
    · rcases hs with ⟨a, t, Z', hEq, htY, haY⟩
      rcases Prod.mk.inj hEq with ⟨hsEq, hZEq⟩
      subst hsEq
      subst hZEq
      refine ⟨a, hYX haY, ?_⟩
      rw [in_failures_Act_prefix]
      refine Or.inr ⟨t, Z, rfl, (cspF_cspT_refF_semantics.mp (hPQ a haY)).2 htY⟩

/- The Isabelle theorem bundle `cspF_decompo_subset` is represented by
   `cspF_Rep_int_choice_subset` and `cspF_Int_Ext_pre_choice_subset`. -/

/- -------------------------------------------------------*
 |               decompose external choice               |
 *------------------------------------------------------- -/

theorem cspF_Ext_choice_right
    {P : proc p α} {Q1 Q2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hP1 : refF P M1 M2 Q1) (hP2 : refF P M1 M2 Q2) :
    refF P M1 M2 (Q1 [+] Q2) := by
  rcases (cspF_cspT_refF_semantics.mp hP1) with ⟨hT1, hF1⟩
  rcases (cspF_cspT_refF_semantics.mp hP2) with ⟨hT2, hF2⟩
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Ext_choice_right hT1 hT2, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Ext_choice] at hs
  rcases hs with hs | hs | hs
  · exact hF1 hs.2.1
  · rcases hs with ⟨_, _, hsQ, _⟩
    rcases hsQ with hsQ | hsQ
    · exact hF1 hsQ
    · exact hF2 hsQ
  · rcases hs with ⟨X', hEq, hTick, hX'⟩
    rcases Prod.mk.inj hEq with ⟨hsEq, hXEq⟩
    subst hsEq
    subst hXEq
    have hTickP : (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M1) := by
      rcases hTick with hTick | hTick
      · exact hT1 hTick
      · exact hT2 hTick
    exact proc_F2_F4 (P := P) (M := M1) (s := <>) (X := X)
      (by simpa using hTickP) noTick_nil hX'
