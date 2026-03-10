           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_law_decompo

open Function
open SumType

noncomputable section

/-
(*------------------------------------------------*
 |                                                |
 |      laws for monotonicity and congruence      |
 |                                                |
 *------------------------------------------------*)
-/

/-
(*********************************************************
                        Act_prefix mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Act_prefix_mono
    {a b : α} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hab : a = b) (hPQ : refF P M1 M2 Q) :
    refF (a ~> P) M1 M2 (b ~> Q) := by
  subst b
  rw [cspF_cspT_refF_semantics] at hPQ ⊢
  refine ⟨cspT_Act_prefix_mono rfl hPQ.1, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Act_prefix] at hs ⊢
  rcases hs with ⟨Y, hEq, hNot⟩ | ⟨t, Y, hEq, htY⟩
  · exact Or.inl ⟨Y, hEq, hNot⟩
  · exact Or.inr ⟨t, Y, hEq, hPQ.2 htY⟩

theorem cspF_Act_prefix_cong
    {a b : α} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hab : a = b) (hPQ : eqF P M1 M2 Q) :
    eqF (a ~> P) M1 M2 (b ~> Q) := by
  rw [cspF_eq_ref_iff] at hPQ ⊢
  exact ⟨cspF_Act_prefix_mono hab hPQ.1, cspF_Act_prefix_mono hab.symm hPQ.2⟩

/-
(*********************************************************
                   Ext_pre_choice mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Ext_pre_choice_mono
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hPQ : ∀ a, a ∈ Y → refF (Pf a) M1 M2 (Qf a)) :
    refF (proc.Ext_pre_choice X Pf) M1 M2 (proc.Ext_pre_choice Y Qf) := by
  subst Y
  have hT : ∀ a, a ∈ X → refT (Pf a) (fstF ∘ M1) (fstF ∘ M2) (Qf a) := by
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).1
  have hF : ∀ a, a ∈ X → failures (Qf a) M2 <= failures (Pf a) M1 := by
    intro a ha
    exact (cspF_cspT_refF_semantics.mp (hPQ a ha)).2
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Ext_pre_choice_mono rfl hT, ?_⟩
  rw [subsetF_iff]
  intro s Z hs
  rw [in_failures_Ext_pre_choice] at hs ⊢
  rcases hs with ⟨Y, hEq, hEmpty⟩ | ⟨a, t, Y, hEq, htY, haX⟩
  · exact Or.inl ⟨Y, hEq, hEmpty⟩
  · exact Or.inr ⟨a, t, Y, hEq, hF a haX htY, haX⟩

theorem cspF_Ext_pre_choice_cong
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hPQ : ∀ a, a ∈ Y → eqF (Pf a) M1 M2 (Qf a)) :
    eqF (proc.Ext_pre_choice X Pf) M1 M2 (proc.Ext_pre_choice Y Qf) := by
  subst Y
  have hPQ' : ∀ a, a ∈ X → refF (Pf a) M1 M2 (Qf a) ∧ refF (Qf a) M2 M1 (Pf a) := by
    intro a ha
    exact cspF_eq_ref_iff.mp (hPQ a ha)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Ext_pre_choice_mono rfl (fun a ha => (hPQ' a ha).1)
  · exact cspF_Ext_pre_choice_mono rfl (fun a ha => (hPQ' a ha).2)

/-
(*********************************************************
                      Ext choice mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Ext_choice_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (P1 [+] P2) M1 M2 (Q1 [+] Q2) := by
  rw [cspF_cspT_refF_semantics] at hP hQ ⊢
  refine ⟨cspT_Ext_choice_mono hP.1 hQ.1, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Ext_choice] at hs ⊢
  rcases hs with hs | hs
  · rcases hs with ⟨⟨Y, hEq⟩, hs1, hs2⟩
    exact Or.inl ⟨⟨Y, hEq⟩, hP.2 hs1, hQ.2 hs2⟩
  · rcases hs with hs | hs
    · rcases hs with ⟨t, ⟨Y, hEq⟩, hs12, htNe⟩
      refine Or.inr <| Or.inl ?_
      refine ⟨t, ⟨Y, hEq⟩, ?_, htNe⟩
      rcases hs12 with hs1 | hs2
      · exact Or.inl (hP.2 hs1)
      · exact Or.inr (hQ.2 hs2)
    · rcases hs with ⟨Y, hEq, hTick, hSub⟩
      have hPRef := hP.1
      have hQRef := hQ.1
      have hPTr : traces Q1 (fstF ∘ M2) <= traces P1 (fstF ∘ M1) := by
        rwa [cspT_refT_semantics] at hPRef
      have hQTr : traces Q2 (fstF ∘ M2) <= traces P2 (fstF ∘ M1) := by
        rwa [cspT_refT_semantics] at hQRef
      refine Or.inr <| Or.inr ?_
      refine ⟨Y, hEq, ?_, hSub⟩
      rcases hTick with hTick | hTick
      · exact Or.inl (hPTr hTick)
      · exact Or.inr (hQTr hTick)

theorem cspF_Ext_choice_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (P1 [+] P2) M1 M2 (Q1 [+] Q2) := by
  rw [cspF_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspF_Ext_choice_mono hP.1 hQ.1, cspF_Ext_choice_mono hP.2 hQ.2⟩

/-
(*********************************************************
                      Int choice mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Int_choice_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (P1 |~| P2) M1 M2 (Q1 |~| Q2) := by
  rw [cspF_cspT_refF_semantics] at hP hQ ⊢
  refine ⟨cspT_Int_choice_mono hP.1 hQ.1, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Int_choice] at hs ⊢
  rcases hs with hs | hs
  · exact Or.inl (hP.2 hs)
  · exact Or.inr (hQ.2 hs)

theorem cspF_Int_choice_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (P1 |~| P2) M1 M2 (Q1 |~| Q2) := by
  rw [cspF_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspF_Int_choice_mono hP.1 hQ.1, cspF_Int_choice_mono hP.2 hQ.2⟩

/-
(*********************************************************
               replicated internal choice
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/- (****** mono ******) -/

theorem cspF_Rep_int_choice_mono_sum
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hC : C1 = C2) (hPQ : ∀ c, c ∈ sumset C1 → refF (Pf c) M1 M2 (Qf c)) :
    refF (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  subst C2
  have hT : ∀ c, c ∈ sumset C1 → refT (Pf c) (fstF ∘ M1) (fstF ∘ M2) (Qf c) := by
    intro c hc
    exact (cspF_cspT_refF_semantics.mp (hPQ c hc)).1
  have hF : ∀ c, c ∈ sumset C1 → failures (Qf c) M2 <= failures (Pf c) M1 := by
    intro c hc
    exact (cspF_cspT_refF_semantics.mp (hPQ c hc)).2
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_mono_sum rfl hT, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Rep_int_choice_sum] at hs ⊢
  rcases hs with ⟨c, hc, hs⟩
  exact ⟨c, hc, hF c hc hs⟩

theorem cspF_Rep_int_choice_mono_nat
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hN : N1 = N2) (hPQ : ∀ n, n ∈ N1 → refF (Pf n) M1 M2 (Qf n)) :
    refF (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  subst N2
  have hT : ∀ n, n ∈ N1 → refT (Pf n) (fstF ∘ M1) (fstF ∘ M2) (Qf n) := by
    intro n hn
    exact (cspF_cspT_refF_semantics.mp (hPQ n hn)).1
  have hF : ∀ n, n ∈ N1 → failures (Qf n) M2 <= failures (Pf n) M1 := by
    intro n hn
    exact (cspF_cspT_refF_semantics.mp (hPQ n hn)).2
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_mono_nat rfl hT, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Rep_int_choice_nat] at hs ⊢
  rcases hs with ⟨n, hn, hs⟩
  exact ⟨n, hn, hF n hn hs⟩

theorem cspF_Rep_int_choice_mono_set
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : Xs1 = Xs2) (hPQ : ∀ X, X ∈ Xs1 → refF (Pf X) M1 M2 (Qf X)) :
    refF (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  subst Xs2
  have hT : ∀ X, X ∈ Xs1 → refT (Pf X) (fstF ∘ M1) (fstF ∘ M2) (Qf X) := by
    intro X hX
    exact (cspF_cspT_refF_semantics.mp (hPQ X hX)).1
  have hF : ∀ X, X ∈ Xs1 → failures (Qf X) M2 <= failures (Pf X) M1 := by
    intro X hX
    exact (cspF_cspT_refF_semantics.mp (hPQ X hX)).2
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_mono_set rfl hT, ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  rw [in_failures_Rep_int_choice_set] at hs ⊢
  rcases hs with ⟨X, hX, hs⟩
  exact ⟨X, hX, hF X hX hs⟩

theorem cspF_Rep_int_choice_mono_com [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → refF (Pf x) M1 M2 (Qf x)) :
    refF (Rep_int_choice_com X1 Pf) M1 M2 (Rep_int_choice_com X2 Qf) := by
  subst X2
  have hT : ∀ x, x ∈ X1 → refT (Pf x) (fstF ∘ M1) (fstF ∘ M2) (Qf x) := by
    intro x hx
    exact (cspF_cspT_refF_semantics.mp (hPQ x hx)).1
  have hF : ∀ x, x ∈ X1 → failures (Qf x) M2 <= failures (Pf x) M1 := by
    intro x hx
    exact (cspF_cspT_refF_semantics.mp (hPQ x hx)).2
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_mono_com rfl hT, ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  rw [in_failures_Rep_int_choice_com] at hs ⊢
  rcases hs with ⟨x, hx, hs⟩
  exact ⟨x, hx, hF x hx hs⟩

theorem cspF_Rep_int_choice_mono_f [Inhabited α] [Inhabited β]
    {f : β → α} {X1 X2 : Set β} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → refF (Pf x) M1 M2 (Qf x)) :
    refF (Rep_int_choice_f f X1 Pf) M1 M2 (Rep_int_choice_f f X2 Qf) := by
  subst X2
  have hT : ∀ x, x ∈ X1 → refT (Pf x) (fstF ∘ M1) (fstF ∘ M2) (Qf x) := by
    intro x hx
    exact (cspF_cspT_refF_semantics.mp (hPQ x hx)).1
  have hF : ∀ x, x ∈ X1 → failures (Qf x) M2 <= failures (Pf x) M1 := by
    intro x hx
    exact (cspF_cspT_refF_semantics.mp (hPQ x hx)).2
  rw [cspF_cspT_refF_semantics]
  refine ⟨cspT_Rep_int_choice_mono_f hf rfl hT, ?_⟩
  rw [subsetF_iff]
  intro s Y hs
  rw [in_failures_Rep_int_choice_f hf] at hs ⊢
  rcases hs with ⟨x, hx, hs⟩
  exact ⟨x, hx, hF x hx hs⟩

/- The Isabelle theorem bundle `cspF_Rep_int_choice_mono` is represented by
   `cspF_Rep_int_choice_mono_sum`, `cspF_Rep_int_choice_mono_nat`,
   `cspF_Rep_int_choice_mono_set`, `cspF_Rep_int_choice_mono_com`,
   and `cspF_Rep_int_choice_mono_f`. -/

/- (****** cong ******) -/

theorem cspF_Rep_int_choice_cong_sum
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hC : C1 = C2) (hPQ : ∀ c, c ∈ sumset C1 → eqF (Pf c) M1 M2 (Qf c)) :
    eqF (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  subst C2
  have hPQ' : ∀ c, c ∈ sumset C1 → refF (Pf c) M1 M2 (Qf c) ∧ refF (Qf c) M2 M1 (Pf c) := by
    intro c hc
    exact cspF_eq_ref_iff.mp (hPQ c hc)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Rep_int_choice_mono_sum rfl (fun c hc => (hPQ' c hc).1)
  · exact cspF_Rep_int_choice_mono_sum rfl (fun c hc => (hPQ' c hc).2)

theorem cspF_Rep_int_choice_cong_nat
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hN : N1 = N2) (hPQ : ∀ n, n ∈ N1 → eqF (Pf n) M1 M2 (Qf n)) :
    eqF (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  subst N2
  have hPQ' : ∀ n, n ∈ N1 → refF (Pf n) M1 M2 (Qf n) ∧ refF (Qf n) M2 M1 (Pf n) := by
    intro n hn
    exact cspF_eq_ref_iff.mp (hPQ n hn)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Rep_int_choice_mono_nat rfl (fun n hn => (hPQ' n hn).1)
  · exact cspF_Rep_int_choice_mono_nat rfl (fun n hn => (hPQ' n hn).2)

theorem cspF_Rep_int_choice_cong_set
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : Xs1 = Xs2) (hPQ : ∀ X, X ∈ Xs1 → eqF (Pf X) M1 M2 (Qf X)) :
    eqF (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  subst Xs2
  have hPQ' : ∀ X, X ∈ Xs1 → refF (Pf X) M1 M2 (Qf X) ∧ refF (Qf X) M2 M1 (Pf X) := by
    intro X hX
    exact cspF_eq_ref_iff.mp (hPQ X hX)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Rep_int_choice_mono_set rfl (fun X hX => (hPQ' X hX).1)
  · exact cspF_Rep_int_choice_mono_set rfl (fun X hX => (hPQ' X hX).2)

theorem cspF_Rep_int_choice_cong_com [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Rep_int_choice_com X1 Pf) M1 M2 (Rep_int_choice_com X2 Qf) := by
  subst X2
  have hPQ' : ∀ x, x ∈ X1 → refF (Pf x) M1 M2 (Qf x) ∧ refF (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspF_eq_ref_iff.mp (hPQ x hx)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Rep_int_choice_mono_com rfl (fun x hx => (hPQ' x hx).1)
  · exact cspF_Rep_int_choice_mono_com rfl (fun x hx => (hPQ' x hx).2)

theorem cspF_Rep_int_choice_cong_f [Inhabited α] [Inhabited β]
    {f : β → α} {X1 X2 : Set β} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Rep_int_choice_f f X1 Pf) M1 M2 (Rep_int_choice_f f X2 Qf) := by
  subst X2
  have hPQ' : ∀ x, x ∈ X1 → refF (Pf x) M1 M2 (Qf x) ∧ refF (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspF_eq_ref_iff.mp (hPQ x hx)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Rep_int_choice_mono_f hf rfl (fun x hx => (hPQ' x hx).1)
  · exact cspF_Rep_int_choice_mono_f hf rfl (fun x hx => (hPQ' x hx).2)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_cong` is represented by
   `cspF_Rep_int_choice_cong_sum`, `cspF_Rep_int_choice_cong_nat`,
   `cspF_Rep_int_choice_cong_set`, `cspF_Rep_int_choice_cong_com`,
   and `cspF_Rep_int_choice_cong_f`. -/

/-
(*********************************************************
                   IF mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_IF_mono
    {b1 b2 : Bool} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hb : b1 = b2) (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (IF b1 THEN P1 ELSE P2) M1 M2 (IF b2 THEN Q1 ELSE Q2) := by
  subst b2
  cases b1 with
  | false =>
      simpa [cspF_cspT_refF_semantics, failures] using hQ
  | true =>
      simpa [cspF_cspT_refF_semantics, failures] using hP

theorem cspF_IF_cong
    {b1 b2 : Bool} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hb : b1 = b2) (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (IF b1 THEN P1 ELSE P2) M1 M2 (IF b2 THEN Q1 ELSE Q2) := by
  rw [cspF_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspF_IF_mono hb hP.1 hQ.1, cspF_IF_mono hb.symm hP.2 hQ.2⟩

/-
(*********************************************************
                     Parallel mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Parallel_mono
    {X Y : Set α} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (P1 |[X]| P2) M1 M2 (Q1 |[Y]| Q2) := by
  subst Y
  rw [cspF_cspT_refF_semantics] at hP hQ ⊢
  refine ⟨cspT_Parallel_mono rfl hP.1 hQ.1, ?_⟩
  rw [subsetF_iff]
  intro u X hs
  rw [in_failures_Parallel] at hs ⊢
  rcases hs with ⟨t, Y, Z, hEq, hYZ, s, r, hu, hsY, hrZ⟩
  exact ⟨t, Y, Z, hEq, hYZ, s, r, hu, hP.2 hsY, hQ.2 hrZ⟩

theorem cspF_Parallel_cong
    {X Y : Set α} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (P1 |[X]| P2) M1 M2 (Q1 |[Y]| Q2) := by
  rw [cspF_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspF_Parallel_mono hXY hP.1 hQ.1, cspF_Parallel_mono hXY.symm hP.2 hQ.2⟩

/-
(*********************************************************
                        Hiding mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Hiding_mono
    {X Y : Set α} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hPQ : refF P M1 M2 Q) :
    refF (proc.Hiding P X) M1 M2 (proc.Hiding Q Y) := by
  subst Y
  rw [cspF_cspT_refF_semantics] at hPQ ⊢
  refine ⟨cspT_Hiding_mono rfl hPQ.1, ?_⟩
  rw [subsetF_iff]
  intro t Z hs
  rw [in_failures_Hiding] at hs ⊢
  rcases hs with ⟨s, Y, hEq, hsY⟩
  exact ⟨s, Y, hEq, hPQ.2 hsY⟩

theorem cspF_Hiding_cong
    {X Y : Set α} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hPQ : eqF P M1 M2 Q) :
    eqF (proc.Hiding P X) M1 M2 (proc.Hiding Q Y) := by
  rw [cspF_eq_ref_iff] at hPQ ⊢
  exact ⟨cspF_Hiding_mono hXY hPQ.1, cspF_Hiding_mono hXY.symm hPQ.2⟩

/-
(*********************************************************
                        Renaming mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Renaming_mono
    {r1 r2 : Set (α × α)} {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hr : r1 = r2) (hPQ : refF P M1 M2 Q) :
    refF (P[[r1]]) M1 M2 (Q[[r2]]) := by
  subst r2
  rw [cspF_cspT_refF_semantics] at hPQ ⊢
  refine ⟨cspT_Renaming_mono rfl hPQ.1, ?_⟩
  rw [subsetF_iff]
  intro t X hs
  rw [in_failures_Renaming] at hs ⊢
  rcases hs with ⟨s, u, Y, hEq, hRen, hsY⟩
  exact ⟨s, u, Y, hEq, hRen, hPQ.2 hsY⟩

theorem cspF_Renaming_cong
    {r1 r2 : Set (α × α)} {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hr : r1 = r2) (hPQ : eqF P M1 M2 Q) :
    eqF (P[[r1]]) M1 M2 (Q[[r2]]) := by
  rw [cspF_eq_ref_iff] at hPQ ⊢
  exact ⟨cspF_Renaming_mono hr hPQ.1, cspF_Renaming_mono hr.symm hPQ.2⟩

/-
(*********************************************************
               Sequential composition mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Seq_compo_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  rw [cspF_cspT_refF_semantics] at hP hQ ⊢
  refine ⟨cspT_Seq_compo_mono hP.1 hQ.1, ?_⟩
  rw [subsetF_iff]
  intro u X hs
  rw [in_failures_Seq_compo] at hs ⊢
  rcases hs with hs | hs
  · rcases hs with ⟨t, Y, hEq, htY, htNo⟩
    exact Or.inl ⟨t, Y, hEq, hP.2 htY, htNo⟩
  · rcases hs with ⟨s, t, Y, hEq, hTick, htY, hsNo⟩
    have hPRef := hP.1
    have hPTr : traces Q1 (fstF ∘ M2) <= traces P1 (fstF ∘ M1) := by
      rwa [cspT_refT_semantics] at hPRef
    exact Or.inr ⟨s, t, Y, hEq, hPTr hTick, hQ.2 htY, hsNo⟩

theorem cspF_Seq_compo_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  rw [cspF_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspF_Seq_compo_mono hP.1 hQ.1, cspF_Seq_compo_mono hP.2 hQ.2⟩

/-
(*********************************************************
                       Depth_rest mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Depth_rest_mono
    {n1 n2 : Nat} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hn : n1 = n2) (hPQ : refF P M1 M2 Q) :
    refF (P |. n1) M1 M2 (Q |. n2) := by
  subst n2
  rw [cspF_cspT_refF_semantics] at hPQ ⊢
  refine ⟨cspT_Depth_rest_mono rfl hPQ.1, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  rw [in_failures_Depth_rest] at hs ⊢
  rcases hs with ⟨t, Y, hEq, htY, hRest⟩
  exact ⟨t, Y, hEq, hPQ.2 htY, hRest⟩

theorem cspF_Depth_rest_cong
    {n1 n2 : Nat} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hn : n1 = n2) (hPQ : eqF P M1 M2 Q) :
    eqF (P |. n1) M1 M2 (Q |. n2) := by
  rw [cspF_eq_ref_iff] at hPQ ⊢
  exact ⟨cspF_Depth_rest_mono hn hPQ.1, cspF_Depth_rest_mono hn.symm hPQ.2⟩

/-
(*********************************************************
                        Timeout mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_Timeout_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : refF P1 M1 M2 Q1) (hQ : refF P2 M1 M2 Q2) :
    refF (P1 [> P2) M1 M2 (Q1 [> Q2) := by
  simpa using
    (cspF_Ext_choice_mono (cspF_Int_choice_mono hP cspF_reflex_ref_STOP) hQ)

theorem cspF_Timeout_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hP : eqF P1 M1 M2 Q1) (hQ : eqF P2 M1 M2 Q2) :
    eqF (P1 [> P2) M1 M2 (Q1 [> Q2) := by
  simpa using
    (cspF_Ext_choice_cong (cspF_Int_choice_cong hP cspF_reflex_eq_STOP) hQ)

/- The Isabelle theorem bundle `cspF_free_mono` is represented by
   `cspF_Ext_choice_mono`, `cspF_Int_choice_mono`, `cspF_Parallel_mono`,
   `cspF_Hiding_mono`, `cspF_Renaming_mono`, `cspF_Seq_compo_mono`,
   and `cspF_Depth_rest_mono`. -/

/- The Isabelle theorem bundle `cspF_mono` is represented by
   `cspF_free_mono`, `cspF_Act_prefix_mono`, `cspF_Ext_pre_choice_mono`,
   `cspF_Rep_int_choice_mono`, and `cspF_IF_mono`. -/

/- The Isabelle theorem bundle `cspF_free_cong` is represented by
   `cspF_Ext_choice_cong`, `cspF_Int_choice_cong`, `cspF_Parallel_cong`,
   `cspF_Hiding_cong`, `cspF_Renaming_cong`, `cspF_Seq_compo_cong`,
   and `cspF_Depth_rest_cong`. -/

/- The Isabelle theorem bundle `cspF_cong` is represented by
   `cspF_free_cong`, `cspF_Act_prefix_cong`, `cspF_Ext_pre_choice_cong`,
   `cspF_Rep_int_choice_cong`, and `cspF_IF_cong`. -/

/- The Isabelle theorem bundle `cspF_free_decompo` is represented by
   `cspF_free_mono` and `cspF_free_cong`. -/

/- The Isabelle theorem bundle `cspF_decompo` is represented by
   `cspF_mono` and `cspF_cong`. -/

/- The Isabelle theorem bundle `cspF_rm_head_mono` is represented by
   `cspF_Act_prefix_mono` and `cspF_Ext_pre_choice_mono`. -/

/- The Isabelle theorem bundle `cspF_rm_head_cong` is represented by
   `cspF_Act_prefix_cong` and `cspF_Ext_pre_choice_cong`. -/

/- The Isabelle theorem bundle `cspF_rm_head` is represented by
   `cspF_rm_head_mono` and `cspF_rm_head_cong`. -/

/-
(*-------------------------------------------------------*
 |            decomposition with ALL and EX              |
 *-------------------------------------------------------*)
-/

/- (*** Rep_int_choice ***) -/

theorem cspF_Rep_int_choice_sum_decompo_ALL_EX_ref
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ c2, c2 ∈ sumset C2 → ∃ c1, c1 ∈ sumset C1 ∧ refF (Pf c1) M1 M2 (Qf c2)) :
    refF (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_sum_decompo_ALL_EX_ref
    intro c2 hc2
    rcases hPQ c2 hc2 with ⟨c1, hc1, hRef⟩
    exact ⟨c1, hc1, (cspF_cspT_refF_semantics.mp hRef).1⟩
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Rep_int_choice_sum] at hs ⊢
    rcases hs with ⟨c2, hc2, hs⟩
    rcases hPQ c2 hc2 with ⟨c1, hc1, hRef⟩
    exact ⟨c1, hc1, (cspF_cspT_refF_semantics.mp hRef).2 hs⟩

theorem cspF_Rep_int_choice_nat_decompo_ALL_EX_ref
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ n2, n2 ∈ N2 → ∃ n1, n1 ∈ N1 ∧ refF (Pf n1) M1 M2 (Qf n2)) :
    refF (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_nat_decompo_ALL_EX_ref
    intro n2 hn2
    rcases hPQ n2 hn2 with ⟨n1, hn1, hRef⟩
    exact ⟨n1, hn1, (cspF_cspT_refF_semantics.mp hRef).1⟩
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Rep_int_choice_nat] at hs ⊢
    rcases hs with ⟨n2, hn2, hs⟩
    rcases hPQ n2 hn2 with ⟨n1, hn1, hRef⟩
    exact ⟨n1, hn1, (cspF_cspT_refF_semantics.mp hRef).2 hs⟩

theorem cspF_Rep_int_choice_set_decompo_ALL_EX_ref
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ X2, X2 ∈ Xs2 → ∃ X1, X1 ∈ Xs1 ∧ refF (Pf X1) M1 M2 (Qf X2)) :
    refF (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  rw [cspF_cspT_refF_semantics]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_set_decompo_ALL_EX_ref
    intro X2 hX2
    rcases hPQ X2 hX2 with ⟨X1, hX1, hRef⟩
    exact ⟨X1, hX1, (cspF_cspT_refF_semantics.mp hRef).1⟩
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Rep_int_choice_set] at hs ⊢
    rcases hs with ⟨X2, hX2, hs⟩
    rcases hPQ X2 hX2 with ⟨X1, hX1, hRef⟩
    exact ⟨X1, hX1, (cspF_cspT_refF_semantics.mp hRef).2 hs⟩

/- The Isabelle theorem bundle `cspF_Rep_int_choice_decompo_ALL_EX_ref`
   is represented by `cspF_Rep_int_choice_sum_decompo_ALL_EX_ref`,
   `cspF_Rep_int_choice_nat_decompo_ALL_EX_ref`, and
   `cspF_Rep_int_choice_set_decompo_ALL_EX_ref`. -/

theorem cspF_Rep_int_choice_sum_decompo_ALL_EX_eq
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (h12 : ∀ c1, c1 ∈ sumset C1 → ∃ c2, c2 ∈ sumset C2 ∧ eqF (Pf c1) M1 M2 (Qf c2))
    (h21 : ∀ c2, c2 ∈ sumset C2 → ∃ c1, c1 ∈ sumset C1 ∧ eqF (Pf c1) M1 M2 (Qf c2)) :
    eqF (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · apply cspF_Rep_int_choice_sum_decompo_ALL_EX_ref
    intro c2 hc2
    rcases h21 c2 hc2 with ⟨c1, hc1, hEq⟩
    exact ⟨c1, hc1, cspF_eq_ref hEq⟩
  · apply cspF_Rep_int_choice_sum_decompo_ALL_EX_ref
    intro c1 hc1
    rcases h12 c1 hc1 with ⟨c2, hc2, hEq⟩
    exact ⟨c2, hc2, cspF_eq_ref (cspF_sym hEq)⟩

theorem cspF_Rep_int_choice_nat_decompo_ALL_EX_eq
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (h12 : ∀ n1, n1 ∈ N1 → ∃ n2, n2 ∈ N2 ∧ eqF (Pf n1) M1 M2 (Qf n2))
    (h21 : ∀ n2, n2 ∈ N2 → ∃ n1, n1 ∈ N1 ∧ eqF (Pf n1) M1 M2 (Qf n2)) :
    eqF (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · apply cspF_Rep_int_choice_nat_decompo_ALL_EX_ref
    intro n2 hn2
    rcases h21 n2 hn2 with ⟨n1, hn1, hEq⟩
    exact ⟨n1, hn1, cspF_eq_ref hEq⟩
  · apply cspF_Rep_int_choice_nat_decompo_ALL_EX_ref
    intro n1 hn1
    rcases h12 n1 hn1 with ⟨n2, hn2, hEq⟩
    exact ⟨n2, hn2, cspF_eq_ref (cspF_sym hEq)⟩

theorem cspF_Rep_int_choice_set_decompo_ALL_EX_eq
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (h12 : ∀ X1, X1 ∈ Xs1 → ∃ X2, X2 ∈ Xs2 ∧ eqF (Pf X1) M1 M2 (Qf X2))
    (h21 : ∀ X2, X2 ∈ Xs2 → ∃ X1, X1 ∈ Xs1 ∧ eqF (Pf X1) M1 M2 (Qf X2)) :
    eqF (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · apply cspF_Rep_int_choice_set_decompo_ALL_EX_ref
    intro X2 hX2
    rcases h21 X2 hX2 with ⟨X1, hX1, hEq⟩
    exact ⟨X1, hX1, cspF_eq_ref hEq⟩
  · apply cspF_Rep_int_choice_set_decompo_ALL_EX_ref
    intro X1 hX1
    rcases h12 X1 hX1 with ⟨X2, hX2, hEq⟩
    exact ⟨X2, hX2, cspF_eq_ref (cspF_sym hEq)⟩

/- The Isabelle theorem bundle `cspF_Rep_int_choice_decompo_ALL_EX_eq`
   is represented by `cspF_Rep_int_choice_sum_decompo_ALL_EX_eq`,
   `cspF_Rep_int_choice_nat_decompo_ALL_EX_eq`, and
   `cspF_Rep_int_choice_set_decompo_ALL_EX_eq`. -/

/- The Isabelle theorem bundle `cspF_Rep_int_choice_decompo_ALL_EX`
   is represented by `cspF_Rep_int_choice_decompo_ALL_EX_ref` and
   `cspF_Rep_int_choice_decompo_ALL_EX_eq`. -/

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)
-/

/-
(*********************************************************
                        Act_prefix mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/- (** mono **) -/

theorem cspF_Send_prefix_mono
    {x : Type _} {a b : x → α} {v : x} {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hab : a = b) (hPQ : refF P M1 M2 Q) :
    refF (Send_prefix a v P) M1 M2 (Send_prefix b v Q) := by
  subst b
  simpa [Send_prefix_def] using
    (cspF_Act_prefix_mono (a := a v) (b := a v) (P := P) (Q := Q) (M1 := M1) (M2 := M2) rfl hPQ)

theorem cspF_Rec_prefix_mono
    {x : Type _} [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → refF (Pf x) M1 M2 (Qf x)) :
    refF (Rec_prefix a X Pf) M1 M2 (Rec_prefix b Y Qf) := by
  subst b
  subst Y
  apply cspF_Ext_pre_choice_mono rfl
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Rec_prefix_def, Function.leftInverse_invFun ha x] using hPQ x hx

theorem cspF_Int_pre_choice_mono [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hPQ : ∀ x, x ∈ Y → refF (Pf x) M1 M2 (Qf x)) :
    refF (Int_pre_choice X Pf) M1 M2 (Int_pre_choice Y Qf) := by
  subst Y
  simpa [Int_pre_choice_def] using
    (cspF_Rep_int_choice_mono_com (X1 := X) (X2 := X)
      (Pf := fun x => x ~> Pf x) (Qf := fun x => x ~> Qf x) (M1 := M1) (M2 := M2) rfl
      (by
        intro x hx
        exact cspF_Act_prefix_mono rfl (hPQ x hx)))

theorem cspF_Nondet_send_prefix_mono
    {x : Type _} [Inhabited α] [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → refF (Pf x) M1 M2 (Qf x)) :
    refF (Nondet_send_prefix a X Pf) M1 M2 (Nondet_send_prefix b Y Qf) := by
  subst b
  subst Y
  apply cspF_Int_pre_choice_mono rfl
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Nondet_send_prefix_def, Int_pre_choice_def,
    Function.leftInverse_invFun ha x] using hPQ x hx

/- (** cong **) -/

theorem cspF_Send_prefix_cong
    {x : Type _} {a b : x → α} {v : x} {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hab : a = b) (hPQ : eqF P M1 M2 Q) :
    eqF (Send_prefix a v P) M1 M2 (Send_prefix b v Q) := by
  subst b
  simpa [Send_prefix_def] using
    (cspF_Act_prefix_cong (a := a v) (b := a v) (P := P) (Q := Q) (M1 := M1) (M2 := M2) rfl hPQ)

theorem cspF_Rec_prefix_cong
    {x : Type _} [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Rec_prefix a X Pf) M1 M2 (Rec_prefix b Y Qf) := by
  subst b
  subst Y
  have hPQ' : ∀ x, x ∈ X → refF (Pf x) M1 M2 (Qf x) ∧ refF (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspF_eq_ref_iff.mp (hPQ x hx)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Rec_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).1)
  · exact cspF_Rec_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).2)

theorem cspF_Int_pre_choice_cong [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hXY : X = Y) (hPQ : ∀ x, x ∈ Y → eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Int_pre_choice X Pf) M1 M2 (Int_pre_choice Y Qf) := by
  subst Y
  have hPQ' : ∀ x, x ∈ X → refF (Pf x) M1 M2 (Qf x) ∧ refF (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspF_eq_ref_iff.mp (hPQ x hx)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Int_pre_choice_mono rfl (fun x hx => (hPQ' x hx).1)
  · exact cspF_Int_pre_choice_mono rfl (fun x hx => (hPQ' x hx).2)

theorem cspF_Nondet_send_prefix_cong
    {x : Type _} [Inhabited α] [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Nondet_send_prefix a X Pf) M1 M2 (Nondet_send_prefix b Y Qf) := by
  subst b
  subst Y
  have hPQ' : ∀ x, x ∈ X → refF (Pf x) M1 M2 (Qf x) ∧ refF (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspF_eq_ref_iff.mp (hPQ x hx)
  rw [cspF_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspF_Nondet_send_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).1)
  · exact cspF_Nondet_send_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).2)

/- The Isabelle theorem bundle `cspF_prefix_ss_mono` is represented by
   `cspF_Send_prefix_mono`, `cspF_Rec_prefix_mono`,
   `cspF_Int_pre_choice_mono`, and `cspF_Nondet_send_prefix_mono`. -/

/- The Isabelle theorem bundle `cspF_prefx_ss_cong` is represented by
   `cspF_Send_prefix_cong`, `cspF_Rec_prefix_cong`,
   `cspF_Int_pre_choice_cong`, and `cspF_Nondet_send_prefix_cong`. -/

/- The Isabelle theorem bundle `cspF_mono_ss` is represented by
   `cspF_mono` and `cspF_prefix_ss_mono`. -/

/- The Isabelle theorem bundle `cspF_cong_ss` is represented by
   `cspF_cong` and `cspF_prefx_ss_cong`. -/

/- The Isabelle theorem bundle `cspF_decompo_ss` is represented by
   `cspF_mono_ss` and `cspF_cong_ss`. -/

/-
(*********************************************************
             Rep_internal_choice for UNIV
              this is useful for tactic
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/- (* mono_UNIV *) -/

theorem cspF_Rep_int_choice_mono_UNIV_nat
    {Pf : Nat → proc p α} {Qf : Nat → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ n, refF (Pf n) M1 M2 (Qf n)) :
    refF (Rep_int_choice_nat Set.univ Pf) M1 M2 (Rep_int_choice_nat Set.univ Qf) := by
  exact cspF_Rep_int_choice_mono_nat rfl (fun n _ => hPQ n)

theorem cspF_Rep_int_choice_mono_UNIV_set
    {Pf : Set α → proc p α} {Qf : Set α → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ X, refF (Pf X) M1 M2 (Qf X)) :
    refF (Rep_int_choice_set Set.univ Pf) M1 M2 (Rep_int_choice_set Set.univ Qf) := by
  exact cspF_Rep_int_choice_mono_set rfl (fun X _ => hPQ X)

theorem cspF_Rep_int_choice_mono_UNIV_com [Inhabited α]
    {Pf : α → proc p α} {Qf : α → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ x, refF (Pf x) M1 M2 (Qf x)) :
    refF (Rep_int_choice_com Set.univ Pf) M1 M2 (Rep_int_choice_com Set.univ Qf) := by
  exact cspF_Rep_int_choice_mono_com rfl (fun x _ => hPQ x)

theorem cspF_Rep_int_choice_mono_UNIV_f [Inhabited α] [Inhabited β]
    {f : β → α} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hPQ : ∀ x, refF (Pf x) M1 M2 (Qf x)) :
    refF (Rep_int_choice_f f Set.univ Pf) M1 M2 (Rep_int_choice_f f Set.univ Qf) := by
  exact cspF_Rep_int_choice_mono_f hf rfl (fun x _ => hPQ x)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_mono_UNIV` is represented
   by `cspF_Rep_int_choice_mono_UNIV_nat`,
   `cspF_Rep_int_choice_mono_UNIV_set`,
   `cspF_Rep_int_choice_mono_UNIV_com`, and
   `cspF_Rep_int_choice_mono_UNIV_f`. -/

/- (* cong *) -/

theorem cspF_Rep_int_choice_cong_UNIV_nat
    {Pf : Nat → proc p α} {Qf : Nat → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ n, eqF (Pf n) M1 M2 (Qf n)) :
    eqF (Rep_int_choice_nat Set.univ Pf) M1 M2 (Rep_int_choice_nat Set.univ Qf) := by
  exact cspF_Rep_int_choice_cong_nat rfl (fun n _ => hPQ n)

theorem cspF_Rep_int_choice_cong_UNIV_set
    {Pf : Set α → proc p α} {Qf : Set α → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ X, eqF (Pf X) M1 M2 (Qf X)) :
    eqF (Rep_int_choice_set Set.univ Pf) M1 M2 (Rep_int_choice_set Set.univ Qf) := by
  exact cspF_Rep_int_choice_cong_set rfl (fun X _ => hPQ X)

theorem cspF_Rep_int_choice_cong_UNIV_com [Inhabited α]
    {Pf : α → proc p α} {Qf : α → proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hPQ : ∀ x, eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Rep_int_choice_com Set.univ Pf) M1 M2 (Rep_int_choice_com Set.univ Qf) := by
  exact cspF_Rep_int_choice_cong_com rfl (fun x _ => hPQ x)

theorem cspF_Rep_int_choice_cong_UNIV_f [Inhabited α] [Inhabited β]
    {f : β → α} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (hPQ : ∀ x, eqF (Pf x) M1 M2 (Qf x)) :
    eqF (Rep_int_choice_f f Set.univ Pf) M1 M2 (Rep_int_choice_f f Set.univ Qf) := by
  exact cspF_Rep_int_choice_cong_f hf rfl (fun x _ => hPQ x)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_cong_UNIV` is represented
   by `cspF_Rep_int_choice_cong_UNIV_nat`,
   `cspF_Rep_int_choice_cong_UNIV_set`,
   `cspF_Rep_int_choice_cong_UNIV_com`, and
   `cspF_Rep_int_choice_cong_UNIV_f`. -/

end
