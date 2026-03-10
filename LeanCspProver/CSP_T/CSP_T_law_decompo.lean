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

import LeanCspProver.CSP_T.CSP_T_traces

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

theorem cspT_Act_prefix_mono
    {a b : α} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hab : a = b) (hPQ : refT P M1 M2 Q) :
    refT (a ~> P) M1 M2 (b ~> Q) := by
  subst b
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Act_prefix] at ht ⊢
  rcases ht with rfl | ⟨s, rfl, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨s, rfl, hPQ s hs⟩

theorem cspT_Act_prefix_cong
    {a b : α} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hab : a = b) (hPQ : eqT P M1 M2 Q) :
    eqT (a ~> P) M1 M2 (b ~> Q) := by
  rw [cspT_eq_ref_iff] at hPQ ⊢
  exact ⟨cspT_Act_prefix_mono hab hPQ.1, cspT_Act_prefix_mono hab.symm hPQ.2⟩

/-
(*********************************************************
                   Ext_pre_choice mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Ext_pre_choice_mono
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hPQ : ∀ a, a ∈ Y → refT (Pf a) M1 M2 (Qf a)) :
    refT (proc.Ext_pre_choice X Pf) M1 M2 (proc.Ext_pre_choice Y Qf) := by
  subst Y
  have hPQ' : ∀ a, a ∈ X → ∀ t, t :t traces (Qf a) M2 → t :t traces (Pf a) M1 := by
    intro a ha t ht
    have h := hPQ a ha
    rw [cspT_refT_semantics, subdomT_iff] at h
    exact h t ht
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Ext_pre_choice] at ht ⊢
  rcases ht with rfl | ⟨a, s, rfl, hs, haX⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, s, rfl, hPQ' a haX s hs, haX⟩

theorem cspT_Ext_pre_choice_cong
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hPQ : ∀ a, a ∈ Y → eqT (Pf a) M1 M2 (Qf a)) :
    eqT (proc.Ext_pre_choice X Pf) M1 M2 (proc.Ext_pre_choice Y Qf) := by
  subst Y
  have hPQ' : ∀ a, a ∈ X → refT (Pf a) M1 M2 (Qf a) ∧ refT (Qf a) M2 M1 (Pf a) := by
    intro a ha
    exact cspT_eq_ref_iff.mp (hPQ a ha)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Ext_pre_choice_mono rfl (fun a ha => (hPQ' a ha).1)
  · exact cspT_Ext_pre_choice_mono rfl (fun a ha => (hPQ' a ha).2)

/-
(*********************************************************
                      Ext choice mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Ext_choice_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (P1 [+] P2) M1 M2 (Q1 [+] Q2) := by
  rw [cspT_refT_semantics, subdomT_iff] at hP hQ ⊢
  intro t ht
  rw [in_traces_Ext_choice] at ht ⊢
  exact ht.elim (fun h => Or.inl (hP t h)) (fun h => Or.inr (hQ t h))

theorem cspT_Ext_choice_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (P1 [+] P2) M1 M2 (Q1 [+] Q2) := by
  rw [cspT_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspT_Ext_choice_mono hP.1 hQ.1, cspT_Ext_choice_mono hP.2 hQ.2⟩

/-
(*********************************************************
                      Int choice mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Int_choice_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (P1 |~| P2) M1 M2 (Q1 |~| Q2) := by
  rw [cspT_refT_semantics, subdomT_iff] at hP hQ ⊢
  intro t ht
  rw [in_traces_Int_choice] at ht ⊢
  exact ht.elim (fun h => Or.inl (hP t h)) (fun h => Or.inr (hQ t h))

theorem cspT_Int_choice_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (P1 |~| P2) M1 M2 (Q1 |~| Q2) := by
  rw [cspT_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspT_Int_choice_mono hP.1 hQ.1, cspT_Int_choice_mono hP.2 hQ.2⟩

/-
(*********************************************************
               replicated internal choice
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

/- (****** mono ******) -/

theorem cspT_Rep_int_choice_mono_sum
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hC : C1 = C2) (hPQ : ∀ c, c ∈ sumset C1 → refT (Pf c) M1 M2 (Qf c)) :
    refT (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  subst C2
  have hPQ' : ∀ c, c ∈ sumset C1 → ∀ t, t :t traces (Qf c) M2 → t :t traces (Pf c) M1 := by
    intro c hc t ht
    have h := hPQ c hc
    rw [cspT_refT_semantics, subdomT_iff] at h
    exact h t ht
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_sum] at ht ⊢
  rcases ht with rfl | ⟨c, hc, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨c, hc, hPQ' c hc t hs⟩

theorem cspT_Rep_int_choice_mono_nat
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hN : N1 = N2) (hPQ : ∀ n, n ∈ N1 → refT (Pf n) M1 M2 (Qf n)) :
    refT (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  subst N2
  have hPQ' : ∀ n, n ∈ N1 → ∀ t, t :t traces (Qf n) M2 → t :t traces (Pf n) M1 := by
    intro n hn t ht
    have h := hPQ n hn
    rw [cspT_refT_semantics, subdomT_iff] at h
    exact h t ht
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_nat] at ht ⊢
  rcases ht with rfl | ⟨n, hn, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨n, hn, hPQ' n hn t hs⟩

theorem cspT_Rep_int_choice_mono_set
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : Xs1 = Xs2) (hPQ : ∀ X, X ∈ Xs1 → refT (Pf X) M1 M2 (Qf X)) :
    refT (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  subst Xs2
  have hPQ' : ∀ X, X ∈ Xs1 → ∀ t, t :t traces (Qf X) M2 → t :t traces (Pf X) M1 := by
    intro X hX t ht
    have h := hPQ X hX
    rw [cspT_refT_semantics, subdomT_iff] at h
    exact h t ht
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_set] at ht ⊢
  rcases ht with rfl | ⟨X, hX, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨X, hX, hPQ' X hX t hs⟩

theorem cspT_Rep_int_choice_mono_com [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → refT (Pf x) M1 M2 (Qf x)) :
    refT (Rep_int_choice_com X1 Pf) M1 M2 (Rep_int_choice_com X2 Qf) := by
  subst X2
  have hPQ' : ∀ x, x ∈ X1 → ∀ t, t :t traces (Qf x) M2 → t :t traces (Pf x) M1 := by
    intro x hx t ht
    have h := hPQ x hx
    rw [cspT_refT_semantics, subdomT_iff] at h
    exact h t ht
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_com] at ht ⊢
  rcases ht with rfl | ⟨x, hx, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, hx, hPQ' x hx t hs⟩

theorem cspT_Rep_int_choice_mono_f [Inhabited α] [Inhabited β]
    {f : β → α} {X1 X2 : Set β} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → refT (Pf x) M1 M2 (Qf x)) :
    refT (Rep_int_choice_f f X1 Pf) M1 M2 (Rep_int_choice_f f X2 Qf) := by
  subst X2
  have hPQ' : ∀ x, x ∈ X1 → ∀ t, t :t traces (Qf x) M2 → t :t traces (Pf x) M1 := by
    intro x hx t ht
    have h := hPQ x hx
    rw [cspT_refT_semantics, subdomT_iff] at h
    exact h t ht
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_f hf] at ht ⊢
  rcases ht with rfl | ⟨x, hx, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨x, hx, hPQ' x hx t hs⟩

/- The Isabelle theorem bundle `cspT_Rep_int_choice_mono` is represented by
   `cspT_Rep_int_choice_mono_sum`, `cspT_Rep_int_choice_mono_set`,
   `cspT_Rep_int_choice_mono_nat`, `cspT_Rep_int_choice_mono_com`,
   and `cspT_Rep_int_choice_mono_f`. -/

/- (****** cong ******) -/

theorem cspT_Rep_int_choice_cong_sum
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hC : C1 = C2) (hPQ : ∀ c, c ∈ sumset C1 → eqT (Pf c) M1 M2 (Qf c)) :
    eqT (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  subst C2
  have hPQ' : ∀ c, c ∈ sumset C1 → refT (Pf c) M1 M2 (Qf c) ∧ refT (Qf c) M2 M1 (Pf c) := by
    intro c hc
    exact cspT_eq_ref_iff.mp (hPQ c hc)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Rep_int_choice_mono_sum rfl (fun c hc => (hPQ' c hc).1)
  · exact cspT_Rep_int_choice_mono_sum rfl (fun c hc => (hPQ' c hc).2)

theorem cspT_Rep_int_choice_cong_nat
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hN : N1 = N2) (hPQ : ∀ n, n ∈ N1 → eqT (Pf n) M1 M2 (Qf n)) :
    eqT (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  subst N2
  have hPQ' : ∀ n, n ∈ N1 → refT (Pf n) M1 M2 (Qf n) ∧ refT (Qf n) M2 M1 (Pf n) := by
    intro n hn
    exact cspT_eq_ref_iff.mp (hPQ n hn)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Rep_int_choice_mono_nat rfl (fun n hn => (hPQ' n hn).1)
  · exact cspT_Rep_int_choice_mono_nat rfl (fun n hn => (hPQ' n hn).2)

theorem cspT_Rep_int_choice_cong_set
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : Xs1 = Xs2) (hPQ : ∀ X, X ∈ Xs1 → eqT (Pf X) M1 M2 (Qf X)) :
    eqT (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  subst Xs2
  have hPQ' : ∀ X, X ∈ Xs1 → refT (Pf X) M1 M2 (Qf X) ∧ refT (Qf X) M2 M1 (Pf X) := by
    intro X hX
    exact cspT_eq_ref_iff.mp (hPQ X hX)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Rep_int_choice_mono_set rfl (fun X hX => (hPQ' X hX).1)
  · exact cspT_Rep_int_choice_mono_set rfl (fun X hX => (hPQ' X hX).2)

theorem cspT_Rep_int_choice_cong_com [Inhabited α]
    {X1 X2 : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Rep_int_choice_com X1 Pf) M1 M2 (Rep_int_choice_com X2 Qf) := by
  subst X2
  have hPQ' : ∀ x, x ∈ X1 → refT (Pf x) M1 M2 (Qf x) ∧ refT (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspT_eq_ref_iff.mp (hPQ x hx)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Rep_int_choice_mono_com rfl (fun x hx => (hPQ' x hx).1)
  · exact cspT_Rep_int_choice_mono_com rfl (fun x hx => (hPQ' x hx).2)

theorem cspT_Rep_int_choice_cong_f [Inhabited α] [Inhabited β]
    {f : β → α} {X1 X2 : Set β} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hX : X1 = X2) (hPQ : ∀ x, x ∈ X1 → eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Rep_int_choice_f f X1 Pf) M1 M2 (Rep_int_choice_f f X2 Qf) := by
  subst X2
  have hPQ' : ∀ x, x ∈ X1 → refT (Pf x) M1 M2 (Qf x) ∧ refT (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspT_eq_ref_iff.mp (hPQ x hx)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Rep_int_choice_mono_f hf rfl (fun x hx => (hPQ' x hx).1)
  · exact cspT_Rep_int_choice_mono_f hf rfl (fun x hx => (hPQ' x hx).2)

/- The Isabelle theorem bundle `cspT_Rep_int_choice_cong` is represented by
   `cspT_Rep_int_choice_cong_sum`, `cspT_Rep_int_choice_cong_set`,
   `cspT_Rep_int_choice_cong_nat`, `cspT_Rep_int_choice_cong_com`,
   and `cspT_Rep_int_choice_cong_f`. -/

/-
(*********************************************************
                   IF mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_IF_mono
    {b1 b2 : Bool} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hb : b1 = b2) (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (IF b1 THEN P1 ELSE P2) M1 M2 (IF b2 THEN Q1 ELSE Q2) := by
  subst b2
  cases b1 with
  | false =>
      simpa [cspT_refT_semantics, traces] using hQ
  | true =>
      simpa [cspT_refT_semantics, traces] using hP

theorem cspT_IF_cong
    {b1 b2 : Bool} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hb : b1 = b2) (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (IF b1 THEN P1 ELSE P2) M1 M2 (IF b2 THEN Q1 ELSE Q2) := by
  rw [cspT_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspT_IF_mono hb hP.1 hQ.1, cspT_IF_mono hb.symm hP.2 hQ.2⟩

/-
(*********************************************************
                     Parallel mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Parallel_mono
    {X Y : Set α} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (P1 |[X]| P2) M1 M2 (Q1 |[Y]| Q2) := by
  subst Y
  rw [cspT_refT_semantics, subdomT_iff] at hP hQ ⊢
  intro u hu
  rw [in_traces_Parallel] at hu ⊢
  rcases hu with ⟨s, t, hu, hs, ht⟩
  exact ⟨s, t, hu, hP s hs, hQ t ht⟩

theorem cspT_Parallel_cong
    {X Y : Set α} {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (P1 |[X]| P2) M1 M2 (Q1 |[Y]| Q2) := by
  rw [cspT_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspT_Parallel_mono hXY hP.1 hQ.1, cspT_Parallel_mono hXY.symm hP.2 hQ.2⟩

/-
(*********************************************************
                        Hiding mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Hiding_mono
    {X Y : Set α} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hPQ : refT P M1 M2 Q) :
    refT (proc.Hiding P X) M1 M2 (proc.Hiding Q Y) := by
  subst Y
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Hiding] at ht ⊢
  rcases ht with ⟨s, rfl, hs⟩
  exact ⟨s, rfl, hPQ s hs⟩

theorem cspT_Hiding_cong
    {X Y : Set α} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hPQ : eqT P M1 M2 Q) :
    eqT (proc.Hiding P X) M1 M2 (proc.Hiding Q Y) := by
  rw [cspT_eq_ref_iff] at hPQ ⊢
  exact ⟨cspT_Hiding_mono hXY hPQ.1, cspT_Hiding_mono hXY.symm hPQ.2⟩

/-
(*********************************************************
                        Renaming mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Renaming_mono
    {r1 r2 : Set (α × α)} {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hr : r1 = r2) (hPQ : refT P M1 M2 Q) :
    refT (P[[r1]]) M1 M2 (Q[[r2]]) := by
  subst r2
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Renaming] at ht ⊢
  rcases ht with ⟨s, hs, htQ⟩
  exact ⟨s, hs, hPQ s htQ⟩

theorem cspT_Renaming_cong
    {r1 r2 : Set (α × α)} {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hr : r1 = r2) (hPQ : eqT P M1 M2 Q) :
    eqT (P[[r1]]) M1 M2 (Q[[r2]]) := by
  rw [cspT_eq_ref_iff] at hPQ ⊢
  exact ⟨cspT_Renaming_mono hr hPQ.1, cspT_Renaming_mono hr.symm hPQ.2⟩

/-
(*********************************************************
               Sequential composition mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Seq_compo_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  rw [cspT_refT_semantics, subdomT_iff] at hP hQ ⊢
  intro u hu
  rw [in_traces_Seq_compo] at hu ⊢
  rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hs, ht, hnt⟩
  · exact Or.inl ⟨s, rfl, hP s hs⟩
  · exact Or.inr ⟨s, t, rfl, hP _ hs, hQ _ ht, hnt⟩

theorem cspT_Seq_compo_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  rw [cspT_eq_ref_iff] at hP hQ ⊢
  exact ⟨cspT_Seq_compo_mono hP.1 hQ.1, cspT_Seq_compo_mono hP.2 hQ.2⟩

/-
(*********************************************************
                        Depth_rest mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Depth_rest_mono
    {n1 n2 : Nat} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hn : n1 = n2) (hPQ : refT P M1 M2 Q) :
    refT (P |. n1) M1 M2 (Q |. n2) := by
  subst n2
  rw [cspT_refT_semantics, subdomT_iff] at hPQ ⊢
  intro t ht
  rw [in_traces_Depth_rest] at ht ⊢
  exact ⟨hPQ t ht.1, ht.2⟩

theorem cspT_Depth_rest_cong
    {n1 n2 : Nat} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hn : n1 = n2) (hPQ : eqT P M1 M2 Q) :
    eqT (P |. n1) M1 M2 (Q |. n2) := by
  rw [cspT_eq_ref_iff] at hPQ ⊢
  exact ⟨cspT_Depth_rest_mono hn hPQ.1, cspT_Depth_rest_mono hn.symm hPQ.2⟩

/-
(*********************************************************
                        Timeout mono
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspT_Timeout_mono
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : refT P1 M1 M2 Q1) (hQ : refT P2 M1 M2 Q2) :
    refT (P1 [> P2) M1 M2 (Q1 [> Q2) := by
  simpa using
    (cspT_Ext_choice_mono (cspT_Int_choice_mono hP cspT_reflex_ref_STOP) hQ)

theorem cspT_Timeout_cong
    {P1 : proc p α} {P2 : proc p α} {Q1 : proc q α} {Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hP : eqT P1 M1 M2 Q1) (hQ : eqT P2 M1 M2 Q2) :
    eqT (P1 [> P2) M1 M2 (Q1 [> Q2) := by
  simpa using
    (cspT_Ext_choice_cong (cspT_Int_choice_cong hP cspT_reflex_eq_STOP) hQ)

/- The Isabelle theorem bundle `cspT_free_mono` is represented by
   `cspT_Ext_choice_mono`, `cspT_Int_choice_mono`, `cspT_Parallel_mono`,
   `cspT_Hiding_mono`, `cspT_Renaming_mono`, `cspT_Seq_compo_mono`,
   and `cspT_Depth_rest_mono`. -/

/- The Isabelle theorem bundle `cspT_mono` is represented by
   `cspT_free_mono`, `cspT_Act_prefix_mono`, `cspT_Ext_pre_choice_mono`,
   `cspT_Rep_int_choice_mono`, and `cspT_IF_mono`. -/

/- The Isabelle theorem bundle `cspT_free_cong` is represented by
   `cspT_Ext_choice_cong`, `cspT_Int_choice_cong`, `cspT_Parallel_cong`,
   `cspT_Hiding_cong`, `cspT_Renaming_cong`, `cspT_Seq_compo_cong`,
   and `cspT_Depth_rest_cong`. -/

/- The Isabelle theorem bundle `cspT_cong` is represented by
   `cspT_free_cong`, `cspT_Act_prefix_cong`, `cspT_Ext_pre_choice_cong`,
   `cspT_Rep_int_choice_cong`, and `cspT_IF_cong`. -/

/- The Isabelle theorem bundle `cspT_free_decompo` is represented by
   `cspT_free_mono` and `cspT_free_cong`. -/

/- The Isabelle theorem bundle `cspT_decompo` is represented by
   `cspT_mono` and `cspT_cong`. -/

/- The Isabelle theorem bundle `cspT_rm_head_mono` is represented by
   `cspT_Act_prefix_mono` and `cspT_Ext_pre_choice_mono`. -/

/- The Isabelle theorem bundle `cspT_rm_head_cong` is represented by
   `cspT_Act_prefix_cong` and `cspT_Ext_pre_choice_cong`. -/

/- The Isabelle theorem bundle `cspT_rm_head` is represented by
   `cspT_rm_head_mono` and `cspT_rm_head_cong`. -/

/-
(*-------------------------------------------------------*
 |            decomposition with ALL and EX              |
 *-------------------------------------------------------*)
-/

/- (*** Rep_int_choice ***) -/

theorem cspT_Rep_int_choice_sum_decompo_ALL_EX_ref
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ c2, c2 ∈ sumset C2 → ∃ c1, c1 ∈ sumset C1 ∧ refT (Pf c1) M1 M2 (Qf c2)) :
    refT (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_sum] at ht ⊢
  rcases ht with rfl | ⟨c2, hc2, htQ⟩
  · exact Or.inl rfl
  · rcases hPQ c2 hc2 with ⟨c1, hc1, hRef⟩
    rw [cspT_refT_semantics, subdomT_iff] at hRef
    exact Or.inr ⟨c1, hc1, hRef t htQ⟩

theorem cspT_Rep_int_choice_nat_decompo_ALL_EX_ref
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ n2, n2 ∈ N2 → ∃ n1, n1 ∈ N1 ∧ refT (Pf n1) M1 M2 (Qf n2)) :
    refT (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_nat] at ht ⊢
  rcases ht with rfl | ⟨n2, hn2, htQ⟩
  · exact Or.inl rfl
  · rcases hPQ n2 hn2 with ⟨n1, hn1, hRef⟩
    rw [cspT_refT_semantics, subdomT_iff] at hRef
    exact Or.inr ⟨n1, hn1, hRef t htQ⟩

theorem cspT_Rep_int_choice_set_decompo_ALL_EX_ref
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ X2, X2 ∈ Xs2 → ∃ X1, X1 ∈ Xs1 ∧ refT (Pf X1) M1 M2 (Qf X2)) :
    refT (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  rw [cspT_refT_semantics, subdomT_iff]
  intro t ht
  rw [in_traces_Rep_int_choice_set] at ht ⊢
  rcases ht with rfl | ⟨X2, hX2, htQ⟩
  · exact Or.inl rfl
  · rcases hPQ X2 hX2 with ⟨X1, hX1, hRef⟩
    rw [cspT_refT_semantics, subdomT_iff] at hRef
    exact Or.inr ⟨X1, hX1, hRef t htQ⟩

/- The Isabelle theorem bundle `cspT_Rep_int_choice_decompo_ALL_EX_ref`
   is represented by `cspT_Rep_int_choice_sum_decompo_ALL_EX_ref`,
   `cspT_Rep_int_choice_nat_decompo_ALL_EX_ref`, and
   `cspT_Rep_int_choice_set_decompo_ALL_EX_ref`. -/

theorem cspT_Rep_int_choice_sum_decompo_ALL_EX_eq
    {C1 C2 : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (h12 : ∀ c1, c1 ∈ sumset C1 → ∃ c2, c2 ∈ sumset C2 ∧ eqT (Pf c1) M1 M2 (Qf c2))
    (h21 : ∀ c2, c2 ∈ sumset C2 → ∃ c1, c1 ∈ sumset C1 ∧ eqT (Pf c1) M1 M2 (Qf c2)) :
    eqT (proc.Rep_int_choice C1 Pf) M1 M2 (proc.Rep_int_choice C2 Qf) := by
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_sum_decompo_ALL_EX_ref
    intro c2 hc2
    rcases h21 c2 hc2 with ⟨c1, hc1, hEq⟩
    exact ⟨c1, hc1, cspT_eq_ref hEq⟩
  · apply cspT_Rep_int_choice_sum_decompo_ALL_EX_ref
    intro c1 hc1
    rcases h12 c1 hc1 with ⟨c2, hc2, hEq⟩
    exact ⟨c2, hc2, cspT_eq_ref (cspT_sym hEq)⟩

theorem cspT_Rep_int_choice_nat_decompo_ALL_EX_eq
    {N1 N2 : Set Nat} {Pf : Nat → proc p α} {Qf : Nat → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (h12 : ∀ n1, n1 ∈ N1 → ∃ n2, n2 ∈ N2 ∧ eqT (Pf n1) M1 M2 (Qf n2))
    (h21 : ∀ n2, n2 ∈ N2 → ∃ n1, n1 ∈ N1 ∧ eqT (Pf n1) M1 M2 (Qf n2)) :
    eqT (Rep_int_choice_nat N1 Pf) M1 M2 (Rep_int_choice_nat N2 Qf) := by
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_nat_decompo_ALL_EX_ref
    intro n2 hn2
    rcases h21 n2 hn2 with ⟨n1, hn1, hEq⟩
    exact ⟨n1, hn1, cspT_eq_ref hEq⟩
  · apply cspT_Rep_int_choice_nat_decompo_ALL_EX_ref
    intro n1 hn1
    rcases h12 n1 hn1 with ⟨n2, hn2, hEq⟩
    exact ⟨n2, hn2, cspT_eq_ref (cspT_sym hEq)⟩

theorem cspT_Rep_int_choice_set_decompo_ALL_EX_eq
    {Xs1 Xs2 : Set (Set α)} {Pf : Set α → proc p α} {Qf : Set α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (h12 : ∀ X1, X1 ∈ Xs1 → ∃ X2, X2 ∈ Xs2 ∧ eqT (Pf X1) M1 M2 (Qf X2))
    (h21 : ∀ X2, X2 ∈ Xs2 → ∃ X1, X1 ∈ Xs1 ∧ eqT (Pf X1) M1 M2 (Qf X2)) :
    eqT (Rep_int_choice_set Xs1 Pf) M1 M2 (Rep_int_choice_set Xs2 Qf) := by
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · apply cspT_Rep_int_choice_set_decompo_ALL_EX_ref
    intro X2 hX2
    rcases h21 X2 hX2 with ⟨X1, hX1, hEq⟩
    exact ⟨X1, hX1, cspT_eq_ref hEq⟩
  · apply cspT_Rep_int_choice_set_decompo_ALL_EX_ref
    intro X1 hX1
    rcases h12 X1 hX1 with ⟨X2, hX2, hEq⟩
    exact ⟨X2, hX2, cspT_eq_ref (cspT_sym hEq)⟩

/- The Isabelle theorem bundle `cspT_Rep_int_choice_decompo_ALL_EX_eq`
   is represented by `cspT_Rep_int_choice_sum_decompo_ALL_EX_eq`,
   `cspT_Rep_int_choice_nat_decompo_ALL_EX_eq`, and
   `cspT_Rep_int_choice_set_decompo_ALL_EX_eq`. -/

/- The Isabelle theorem bundle `cspT_Rep_int_choice_decompo_ALL_EX`
   is represented by `cspT_Rep_int_choice_decompo_ALL_EX_ref` and
   `cspT_Rep_int_choice_decompo_ALL_EX_eq`. -/

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

theorem cspT_Send_prefix_mono
    {x : Type _} {a b : x → α} {v : x} {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hab : a = b) (hPQ : refT P M1 M2 Q) :
    refT (Send_prefix a v P) M1 M2 (Send_prefix b v Q) := by
  subst b
  simpa [Send_prefix_def] using
    (cspT_Act_prefix_mono (a := a v) (b := a v) (P := P) (Q := Q) (M1 := M1) (M2 := M2) rfl hPQ)

theorem cspT_Rec_prefix_mono
    {x : Type _} [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → refT (Pf x) M1 M2 (Qf x)) :
    refT (Rec_prefix a X Pf) M1 M2 (Rec_prefix b Y Qf) := by
  subst b
  subst Y
  apply cspT_Ext_pre_choice_mono rfl
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Rec_prefix_def, Function.leftInverse_invFun ha x] using hPQ x hx

theorem cspT_Int_pre_choice_mono [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hPQ : ∀ x, x ∈ Y → refT (Pf x) M1 M2 (Qf x)) :
    refT (Int_pre_choice X Pf) M1 M2 (Int_pre_choice Y Qf) := by
  subst Y
  simpa [Int_pre_choice_def] using
    (cspT_Rep_int_choice_mono_com (X1 := X) (X2 := X)
      (Pf := fun x => x ~> Pf x) (Qf := fun x => x ~> Qf x) (M1 := M1) (M2 := M2) rfl
      (by
        intro x hx
        exact cspT_Act_prefix_mono rfl (hPQ x hx)))

theorem cspT_Nondet_send_prefix_mono
    {x : Type _} [Inhabited α] [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → refT (Pf x) M1 M2 (Qf x)) :
    refT (Nondet_send_prefix a X Pf) M1 M2 (Nondet_send_prefix b Y Qf) := by
  subst b
  subst Y
  apply cspT_Int_pre_choice_mono rfl
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Nondet_send_prefix_def, Int_pre_choice_def,
    Function.leftInverse_invFun ha x] using hPQ x hx

/- (** cong **) -/

theorem cspT_Send_prefix_cong
    {x : Type _} {a b : x → α} {v : x} {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hab : a = b) (hPQ : eqT P M1 M2 Q) :
    eqT (Send_prefix a v P) M1 M2 (Send_prefix b v Q) := by
  subst b
  simpa [Send_prefix_def] using
    (cspT_Act_prefix_cong (a := a v) (b := a v) (P := P) (Q := Q) (M1 := M1) (M2 := M2) rfl hPQ)

theorem cspT_Rec_prefix_cong
    {x : Type _} [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Rec_prefix a X Pf) M1 M2 (Rec_prefix b Y Qf) := by
  subst b
  subst Y
  have hPQ' : ∀ x, x ∈ X → refT (Pf x) M1 M2 (Qf x) ∧ refT (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspT_eq_ref_iff.mp (hPQ x hx)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Rec_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).1)
  · exact cspT_Rec_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).2)

theorem cspT_Int_pre_choice_cong [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hXY : X = Y) (hPQ : ∀ x, x ∈ Y → eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Int_pre_choice X Pf) M1 M2 (Int_pre_choice Y Qf) := by
  subst Y
  have hPQ' : ∀ x, x ∈ X → refT (Pf x) M1 M2 (Qf x) ∧ refT (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspT_eq_ref_iff.mp (hPQ x hx)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Int_pre_choice_mono rfl (fun x hx => (hPQ' x hx).1)
  · exact cspT_Int_pre_choice_mono rfl (fun x hx => (hPQ' x hx).2)

theorem cspT_Nondet_send_prefix_cong
    {x : Type _} [Inhabited α] [Inhabited x] {a b : x → α} {X Y : Set x}
    {Pf : x → proc p α} {Qf : x → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (ha : Injective a) (hab : a = b) (hXY : X = Y)
    (hPQ : ∀ x, x ∈ Y → eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Nondet_send_prefix a X Pf) M1 M2 (Nondet_send_prefix b Y Qf) := by
  subst b
  subst Y
  have hPQ' : ∀ x, x ∈ X → refT (Pf x) M1 M2 (Qf x) ∧ refT (Qf x) M2 M1 (Pf x) := by
    intro x hx
    exact cspT_eq_ref_iff.mp (hPQ x hx)
  rw [cspT_eq_ref_iff]
  refine ⟨?_, ?_⟩
  · exact cspT_Nondet_send_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).1)
  · exact cspT_Nondet_send_prefix_mono ha rfl rfl (fun x hx => (hPQ' x hx).2)

/- The Isabelle theorem bundle `cspT_prefix_ss_mono` is represented by
   `cspT_Send_prefix_mono`, `cspT_Rec_prefix_mono`,
   `cspT_Int_pre_choice_mono`, and `cspT_Nondet_send_prefix_mono`. -/

/- The Isabelle theorem bundle `cspT_prefx_ss_cong` is represented by
   `cspT_Send_prefix_cong`, `cspT_Rec_prefix_cong`,
   `cspT_Int_pre_choice_cong`, and `cspT_Nondet_send_prefix_cong`. -/

/- The Isabelle theorem bundle `cspT_mono_ss` is represented by
   `cspT_mono` and `cspT_prefix_ss_mono`. -/

/- The Isabelle theorem bundle `cspT_cong_ss` is represented by
   `cspT_cong` and `cspT_prefx_ss_cong`. -/

/- The Isabelle theorem bundle `cspT_decompo_ss` is represented by
   `cspT_mono_ss` and `cspT_cong_ss`. -/

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

theorem cspT_Rep_int_choice_mono_UNIV_nat
    {Pf : Nat → proc p α} {Qf : Nat → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ n, refT (Pf n) M1 M2 (Qf n)) :
    refT (Rep_int_choice_nat Set.univ Pf) M1 M2 (Rep_int_choice_nat Set.univ Qf) := by
  exact cspT_Rep_int_choice_mono_nat rfl (fun n _ => hPQ n)

theorem cspT_Rep_int_choice_mono_UNIV_set
    {Pf : Set α → proc p α} {Qf : Set α → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ X, refT (Pf X) M1 M2 (Qf X)) :
    refT (Rep_int_choice_set Set.univ Pf) M1 M2 (Rep_int_choice_set Set.univ Qf) := by
  exact cspT_Rep_int_choice_mono_set rfl (fun X _ => hPQ X)

theorem cspT_Rep_int_choice_mono_UNIV_com [Inhabited α]
    {Pf : α → proc p α} {Qf : α → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ x, refT (Pf x) M1 M2 (Qf x)) :
    refT (Rep_int_choice_com Set.univ Pf) M1 M2 (Rep_int_choice_com Set.univ Qf) := by
  exact cspT_Rep_int_choice_mono_com rfl (fun x _ => hPQ x)

theorem cspT_Rep_int_choice_mono_UNIV_f [Inhabited α] [Inhabited β]
    {f : β → α} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hPQ : ∀ x, refT (Pf x) M1 M2 (Qf x)) :
    refT (Rep_int_choice_f f Set.univ Pf) M1 M2 (Rep_int_choice_f f Set.univ Qf) := by
  exact cspT_Rep_int_choice_mono_f hf rfl (fun x _ => hPQ x)

/- The Isabelle theorem bundle `cspT_Rep_int_choice_mono_UNIV` is represented
   by `cspT_Rep_int_choice_mono_UNIV_nat`,
   `cspT_Rep_int_choice_mono_UNIV_set`,
   `cspT_Rep_int_choice_mono_UNIV_com`, and
   `cspT_Rep_int_choice_mono_UNIV_f`. -/

/- (* cong *) -/

theorem cspT_Rep_int_choice_cong_UNIV_nat
    {Pf : Nat → proc p α} {Qf : Nat → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ n, eqT (Pf n) M1 M2 (Qf n)) :
    eqT (Rep_int_choice_nat Set.univ Pf) M1 M2 (Rep_int_choice_nat Set.univ Qf) := by
  exact cspT_Rep_int_choice_cong_nat rfl (fun n _ => hPQ n)

theorem cspT_Rep_int_choice_cong_UNIV_set
    {Pf : Set α → proc p α} {Qf : Set α → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ X, eqT (Pf X) M1 M2 (Qf X)) :
    eqT (Rep_int_choice_set Set.univ Pf) M1 M2 (Rep_int_choice_set Set.univ Qf) := by
  exact cspT_Rep_int_choice_cong_set rfl (fun X _ => hPQ X)

theorem cspT_Rep_int_choice_cong_UNIV_com [Inhabited α]
    {Pf : α → proc p α} {Qf : α → proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (hPQ : ∀ x, eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Rep_int_choice_com Set.univ Pf) M1 M2 (Rep_int_choice_com Set.univ Qf) := by
  exact cspT_Rep_int_choice_cong_com rfl (fun x _ => hPQ x)

theorem cspT_Rep_int_choice_cong_UNIV_f [Inhabited α] [Inhabited β]
    {f : β → α} {Pf : β → proc p α} {Qf : β → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (hf : Injective f) (hPQ : ∀ x, eqT (Pf x) M1 M2 (Qf x)) :
    eqT (Rep_int_choice_f f Set.univ Pf) M1 M2 (Rep_int_choice_f f Set.univ Qf) := by
  exact cspT_Rep_int_choice_cong_f hf rfl (fun x _ => hPQ x)

/- The Isabelle theorem bundle `cspT_Rep_int_choice_cong_UNIV` is represented
   by `cspT_Rep_int_choice_cong_UNIV_nat`,
   `cspT_Rep_int_choice_cong_UNIV_set`,
   `cspT_Rep_int_choice_cong_UNIV_com`, and
   `cspT_Rep_int_choice_cong_UNIV_f`. -/

end
