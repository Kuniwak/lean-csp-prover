           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                October 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_aux

open Function
open SumType

noncomputable section

/-
(*------------------------*
         |~| --> !!
 *------------------------*)
-/

theorem cspT_Int_choice_to_Rep
    {P Q : proc p α} {M : p → domTType α} :
    eqT (P |~| Q) M M
      (Rep_int_choice_nat ({0, 1} : Set Nat) fun n => IF n = 0 THEN P ELSE Q) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rw [in_traces_Rep_int_choice_nat]
    rcases ht with hP | hQ
    · refine Or.inr ⟨0, by simp, ?_⟩
      simpa [in_traces_IF]
        using hP
    · refine Or.inr ⟨1, by simp, ?_⟩
      simpa [in_traces_IF]
        using hQ
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Rep_int_choice_nat] at ht
    rw [in_traces_Int_choice]
    rcases ht with rfl | ⟨n, hn, ht⟩
    · exact Or.inl nilt_in_T
    · have hn' : n = 0 ∨ n = 1 := by
        simpa using hn
      rcases hn' with rfl | rfl
      · exact Or.inl (by simpa [in_traces_IF] using ht)
      · exact Or.inr (by simpa [in_traces_IF] using ht)

/- (*** cspT_Rep_int_choice_set_input ***)
-/

theorem cspT_Rep_int_choice_sum_set_input
    {C : sets_nats α} {Xsf : aset_anat α → Set (Set α)} {Pff : aset_anat α → α → proc p α}
    {M : p → domTType α} :
    eqT
      (proc.Rep_int_choice C fun c =>
        Rep_int_choice_set (Xsf c) fun X => proc.Ext_pre_choice X (Pff c))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ c, c ∈ sumset C ∧ Xs = Xsf c}) fun X =>
        proc.Ext_pre_choice X fun a =>
          proc.Rep_int_choice (sub_sumset C fun c => ∃ X, X ∈ Xsf c ∧ a ∈ X) fun c =>
            Pff c a) := by
  cspT_auto_step_dist

/- (*** cspT_Rep_int_choice_set_input ***)
-/

theorem cspT_Rep_int_choice_set_input
    {N : Set Nat} {Xsf : Nat → Set (Set α)} {Pff : Nat → α → proc p α}
    {M : p → domTType α} :
    eqT
      (Rep_int_choice_nat N fun n =>
        Rep_int_choice_set (Xsf n) fun X => proc.Ext_pre_choice X (Pff n))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ n, n ∈ N ∧ Xs = Xsf n}) fun X =>
        proc.Ext_pre_choice X fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ ∃ X, X ∈ Xsf n ∧ a ∈ X} fun n =>
            Pff n a) := by
  cspT_auto_step_dist

/- (*** cspT_Rep_int_choice_set_set_DIV ***)
-/

theorem cspT_Rep_int_choice_set_set_DIV
    {Xs Ys : Set (Set α)} {M : p → domTType α} :
    Xs ≠ ∅ →
      Ys ≠ ∅ →
      eqT
        (Rep_int_choice_set Xs fun X =>
          Rep_int_choice_set Ys fun Y =>
            proc.Ext_pre_choice (X ∪ Y) fun _ => (proc.DIV : proc p α))
        M M
        (Rep_int_choice_set {Z | ∃ X, X ∈ Xs ∧ ∃ Y, Y ∈ Ys ∧ Z = X ∪ Y} fun Z =>
          proc.Ext_pre_choice Z fun _ => (proc.DIV : proc p α)) := by
  cspT_auto_step_dist

/-
(*********************************************************
               (P [+] SKIP) |~| (Q [+] SKIP)
 *********************************************************)

(* p.289 *)
-/

theorem cspT_Int_choice_Ext_choice_SKIP
    {P Q : proc p α} {M : p → domTType α} :
    eqT ((P [+] proc.SKIP) |~| (Q [+] proc.SKIP)) M M (P [+] Q [+] proc.SKIP) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        Or.inr
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr h))
        Or.inr
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_Int_choice]
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        (fun h => Or.inr (by rw [in_traces_Ext_choice]; exact Or.inl h))
    · exact Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr ht)

/-
(*********************************************************
               (P [+] DIV) |~| (Q [+] DIV)
 *********************************************************)
-/

theorem cspT_Int_choice_Ext_choice_DIV
    {P Q : proc p α} {M : p → domTType α} :
    eqT ((P [+] proc.DIV) |~| (Q [+] proc.DIV)) M M (P [+] Q [+] proc.DIV) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        Or.inr
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr h))
        Or.inr
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_Int_choice]
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        (fun h => Or.inr (by rw [in_traces_Ext_choice]; exact Or.inl h))
    · exact Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr ht)

/-
(*********************************************************
             (P [+] SKIP) |~| (Q [+] DIV)
 *********************************************************)
-/

theorem cspT_Int_choice_Ext_choice_SKIP_DIV
    {P Q : proc p α} {M : p → domTType α} :
    eqT ((P [+] proc.SKIP) |~| (Q [+] proc.DIV)) M M (P [+] Q [+] proc.SKIP) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        Or.inr
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr h))
        (fun h => by
          rw [in_traces_DIV] at h
          subst t
          exact Or.inr nilt_in_T)
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_Int_choice]
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        (fun h => Or.inr (by rw [in_traces_Ext_choice]; exact Or.inl h))
    · exact Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr ht)

/-
(*********************************************************
             (P [+] DIV) |~| (Q [+] SKIP)
 *********************************************************)
-/

theorem cspT_Int_choice_Ext_choice_DIV_SKIP
    {P Q : proc p α} {M : p → domTType α} :
    eqT ((P [+] proc.DIV) |~| (Q [+] proc.SKIP)) M M (P [+] Q [+] proc.SKIP) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        (fun h => by
          rw [in_traces_DIV] at h
          subst t
          exact Or.inr nilt_in_T)
    · rw [in_traces_Ext_choice] at ht
      rw [in_traces_Ext_choice]
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inr h))
        Or.inr
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Ext_choice] at ht
    rw [in_traces_Int_choice]
    rcases ht with ht | ht
    · rw [in_traces_Ext_choice] at ht
      exact ht.elim
        (fun h => Or.inl (by rw [in_traces_Ext_choice]; exact Or.inl h))
        (fun h => Or.inr (by rw [in_traces_Ext_choice]; exact Or.inl h))
    · exact Or.inr (by rw [in_traces_Ext_choice]; exact Or.inr ht)

/-
(*********************************************************
         (P [+] SKIP or DIV) |~| (Q [+] DIV or SKIP)
 *********************************************************)
-/

theorem cspT_Int_choice_Ext_choice_SKIP_or_DIV
    {P1 P2 Q1 Q2 : proc p α} {M : p → domTType α}
    (hP2 : P2 = proc.SKIP ∨ P2 = proc.DIV)
    (hQ2 : Q2 = proc.SKIP ∨ Q2 = proc.DIV) :
    eqT ((P1 [+] P2) |~| (Q1 [+] Q2)) M M (P1 [+] Q1 [+] (P2 |~| Q2)) := by
  rcases hP2 with rfl | rfl <;> rcases hQ2 with rfl | rfl
  · have hTail : eqT (proc.SKIP : proc p α) M M (proc.SKIP |~| proc.SKIP) := by
      exact cspT_sym (cspT_trans_left_eq cspT_Int_choice_idem cspT_reflex_eq_SKIP)
    exact cspT_trans_left_eq
      cspT_Int_choice_Ext_choice_SKIP
      (cspT_Ext_choice_cong cspT_reflex_eq_P hTail)
  · have hTail : eqT (proc.SKIP : proc p α) M M (proc.SKIP |~| proc.DIV) := by
      exact cspT_sym cspT_Int_choice_unit_r
    exact cspT_trans_left_eq
      cspT_Int_choice_Ext_choice_SKIP_DIV
      (cspT_Ext_choice_cong cspT_reflex_eq_P hTail)
  · have hTail : eqT (proc.SKIP : proc p α) M M (proc.DIV |~| proc.SKIP) := by
      exact cspT_sym cspT_Int_choice_unit_l
    exact cspT_trans_left_eq
      cspT_Int_choice_Ext_choice_DIV_SKIP
      (cspT_Ext_choice_cong cspT_reflex_eq_P hTail)
  · have hTail : eqT (proc.DIV : proc p α) M M (proc.DIV |~| proc.DIV) := by
      exact cspT_sym (cspT_trans_left_eq cspT_Int_choice_idem cspT_reflex_eq_DIV)
    exact cspT_trans_left_eq
      cspT_Int_choice_Ext_choice_DIV
      (cspT_Ext_choice_cong cspT_reflex_eq_P hTail)

/-
(*********************************************************
                    (P [+] DIV) |~| P
 *********************************************************)
-/

theorem cspT_Ext_choice_DIV_Int_choice_Id
    {P : proc p α} {M : p → domTType α} :
    eqT ((P [+] proc.DIV) |~| P) M M P := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice] at ht
    rcases ht with hLeft | hRight
    · rw [in_traces_Ext_choice] at hLeft
      exact hLeft.elim (fun h => h) fun h => by
        rw [in_traces_DIV] at h
        subst t
        exact nilt_in_T
    · exact hRight
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Int_choice]
    exact Or.inr ht

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 |                    (renaming)                       |
 * =================================================== *)
-/

theorem cspT_Ext_pre_choice_Renaming_fun_step
    {X : Set α} {Pf : α → proc p α} {f : α → α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[fun_to_rel f]]) M M
      (proc.Ext_pre_choice (f '' X) fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ y = f x} fun x =>
          (Pf x)[[fun_to_rel f]]) := by
  refine cspT_rw_left_eq cspT_Renaming_step ?_
  have hS : {y | ∃ x, x ∈ X ∧ (x, y) ∈ fun_to_rel f} = f '' X := by
    ext y
    simp [Set.mem_image, eq_comm]
  refine cspT_Ext_pre_choice_cong hS fun a ha => ?_
  have hT : {x | x ∈ X ∧ (x, a) ∈ fun_to_rel f} = {x | x ∈ X ∧ a = f x} := by
    ext x
    simp
  rw [hT]
  exact cspT_reflex_eq_P

theorem cspT_Act_prefix_Renaming_fun_step
    {a : α} {P : proc p α} {f : α → α} {M : p → domTType α} :
    eqT (((a ~> P)[[fun_to_rel f]]) ) M M (f a ~> P[[fun_to_rel f]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Renaming_fun_step` is represented by
   `cspT_Ext_pre_choice_Renaming_fun_step` and
   `cspT_Act_prefix_Renaming_fun_step`. -/

theorem cspT_Act_prefix_Renaming1_event1_step_in
    {a b : α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[a <--> b]]) ) M M (b ~> P[[a <--> b]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming1_event2_step_in
    {a b : α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[b <--> a]]) ) M M (b ~> P[[b <--> a]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming1_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domTType α} :
    a ≠ c →
      b ≠ c →
      eqT (((c ~> P)[[a <--> b]]) ) M M (c ~> P[[a <--> b]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming1_event_step` is
   represented by `cspT_Act_prefix_Renaming1_event1_step_in`,
   `cspT_Act_prefix_Renaming1_event2_step_in`, and
   `cspT_Act_prefix_Renaming1_event_step_notin`. -/

theorem cspT_Act_prefix_Renaming2_set_event_step_in
    {a b : α} {A : Set α} {P : proc p α} {M : p → domTType α} :
    a ∈ A →
      eqT (((a ~> P)[[A <<- b]]) ) M M (b ~> P[[A <<- b]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming2_set_event_step_notin
    {b c : α} {A : Set α} {P : proc p α} {M : p → domTType α} :
    c ∉ A →
      eqT (((c ~> P)[[A <<- b]]) ) M M (c ~> P[[A <<- b]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming2_set_event_step
    {a b : α} {A : Set α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[A <<- b]]) ) M M
      (procIte (a ∈ A) (b ~> P[[A <<- b]]) (a ~> P[[A <<- b]])) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming2_set_event_steps` is
   represented by `cspT_Act_prefix_Renaming2_set_event_step_in` and
   `cspT_Act_prefix_Renaming2_set_event_step_notin`. -/

theorem cspT_Act_prefix_Renaming2_event_step_in
    {a b : α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[a <-- b]]) ) M M (b ~> P[[a <-- b]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming2_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domTType α} :
    c ≠ a →
      eqT (((c ~> P)[[a <-- b]]) ) M M (c ~> P[[a <-- b]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming2_event_step` is
   represented by `cspT_Act_prefix_Renaming2_event_step_in` and
   `cspT_Act_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming_event_step` is
   represented by `cspT_Act_prefix_Renaming1_event_step` and
   `cspT_Act_prefix_Renaming2_event_step`. -/

theorem cspT_Act_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((((f v) ~> P)[[f <==> g]]) ) M M (g v ~> P[[f <==> g]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((((f v) ~> P)[[g <==> f]]) ) M M (g v ~> P[[g <==> f]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α} {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqT ((((h v) ~> P)[[f <==> g]]) ) M M ((h v) ~> P[[f <==> g]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming1_channel_step` is
   represented by `cspT_Act_prefix_Renaming1_channel1_step_in`,
   `cspT_Act_prefix_Renaming1_channel2_step_in`, and
   `cspT_Act_prefix_Renaming1_channel_step_notin`. -/

theorem cspT_Act_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((((f v) ~> P)[[f <== g]]) ) M M (g v ~> P[[f <== g]]) := by
  cspT_auto_step_dist

theorem cspT_Act_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f : x → α} {g : x → α} {h : y → α} {v : y}
    {P : proc p α} {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqT ((((h v) ~> P)[[f <== g]]) ) M M ((h v) ~> P[[f <== g]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming2_channel_step` is
   represented by `cspT_Act_prefix_Renaming2_channel_step_in` and
   `cspT_Act_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming_channel_step` is
   represented by `cspT_Act_prefix_Renaming1_channel_step` and
   `cspT_Act_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming_step` is represented
   by `cspT_Act_prefix_Renaming_fun_step`,
   `cspT_Act_prefix_Renaming_event_step`, and
   `cspT_Act_prefix_Renaming_channel_step`. -/

theorem cspT_Ext_pre_choice_Renaming1_event1_step
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])) := by
  cspT_auto_step_dist

theorem cspT_Ext_pre_choice_Renaming1_event2_step
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    a = b →
      eqT ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
        ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
          (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
          (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])) := by
  cspT_auto_step_dist

theorem cspT_Ext_pre_choice_Renaming1_event_step
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])) := by
  cspT_auto_step_dist

theorem cspT_Ext_pre_choice_Renaming2_set_event_step_in
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domTType α} :
    X ∩ A ≠ ∅ →
      eqT ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]]) := by
  intro hXA
  obtain ⟨c, hcX, hcA⟩ : ∃ c, c ∈ X ∧ c ∈ A := by
    by_contra hcon
    exact hXA (Set.eq_empty_iff_forall_notMem.mpr fun c hc => hcon ⟨c, hc.1, hc.2⟩)
  rw [cspT_eqT_iff]
  intro t
  rw [in_traces_Renaming, in_traces_Ext_choice, in_traces_Act_prefix,
    in_traces_Ext_pre_choice (X := X \ A)]
  constructor
  · rintro ⟨s, hren, hs⟩
    rw [in_traces_Ext_pre_choice] at hs
    rcases hs with rfl | ⟨x, sx, rfl, hsx, hxX⟩
    · exact Or.inl (Or.inl (ren_tr_nil1.mp hren))
    · obtain ⟨b, tb, rfl, hab, hren'⟩ := ren_tr_decompo_left.mp hren
      rw [mem_Renaming2_event] at hab
      by_cases hxA : x ∈ A
      · have hba : b = a := by rw [hab]; simp [Renaming2_event_fun, hxA]
        subst hba
        refine Or.inl (Or.inr ⟨tb, rfl, ?_⟩)
        rw [in_traces_Rep_int_choice_com]
        exact Or.inr ⟨x, ⟨hxX, hxA⟩, in_traces_Renaming.mpr ⟨sx, hren', hsx⟩⟩
      · have hbx : b = x := by rw [hab]; simp [Renaming2_event_fun, hxA]
        subst hbx
        exact Or.inr (Or.inr ⟨b, tb, rfl,
          in_traces_Renaming.mpr ⟨sx, hren', hsx⟩, ⟨hxX, hxA⟩⟩)
  · have hnil : (<> : traceType α) :t traces ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M := by
      exact in_traces_Renaming.mpr ⟨<>, ren_tr_nil,
        in_traces_Ext_pre_choice.mpr (Or.inl rfl)⟩
    rintro ((rfl | ⟨tb, rfl, hQ⟩) | (rfl | ⟨x, tb, rfl, hR, hx⟩))
    · exact in_traces_Renaming.mp hnil
    · rw [in_traces_Rep_int_choice_com] at hQ
      rcases hQ with rfl | ⟨x, ⟨hxX, hxA⟩, hR⟩
      · refine ⟨Abs_trace [event.Ev c] ^^^ <>, ?_, in_traces_Ext_pre_choice.mpr
          (Or.inr ⟨c, <>, rfl, nilt_in_T, hcX⟩)⟩
        refine ren_tr_decompo_left_if ?_ ren_tr_nil
        rw [mem_Renaming2_event]
        simp [Renaming2_event_fun, hcA]
      · obtain ⟨sx, hren', hsx⟩ := in_traces_Renaming.mp hR
        refine ⟨Abs_trace [event.Ev x] ^^^ sx, ?_,
          in_traces_Ext_pre_choice.mpr (Or.inr ⟨x, sx, rfl, hsx, hxX⟩)⟩
        refine ren_tr_decompo_left_if ?_ hren'
        rw [mem_Renaming2_event]
        simp [Renaming2_event_fun, hxA]
    · exact in_traces_Renaming.mp hnil
    · obtain ⟨sx, hren', hsx⟩ := in_traces_Renaming.mp hR
      refine ⟨Abs_trace [event.Ev x] ^^^ sx, ?_,
        in_traces_Ext_pre_choice.mpr (Or.inr ⟨x, sx, rfl, hsx, hx.1⟩)⟩
      refine ren_tr_decompo_left_if ?_ hren'
      rw [mem_Renaming2_event]
      simp [Renaming2_event_fun, hx.2]

theorem cspT_Ext_pre_choice_Renaming2_set_event_step_notin
    {X A : Set α} {Pf : α → proc p α} {b : α} {M : p → domTType α} :
    X ∩ A = ∅ →
      eqT ((proc.Ext_pre_choice X Pf)[[A <<- b]]) M M
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- b]]) := by
  cspT_auto_step_dist

theorem cspT_Ext_pre_choice_Renaming2_set_event_step
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
      (procIte (X ∩ A ≠ ∅)
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- a]])) := by
  by_cases h : X ∩ A ≠ ∅
  · rw [procIte_pos h]
    exact cspT_Ext_pre_choice_Renaming2_set_event_step_in h
  · rw [procIte_neg h]
    exact cspT_Ext_pre_choice_Renaming2_set_event_step_notin (by simpa using h)

theorem cspT_Ext_pre_choice_Renaming2_event_step
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[a <-- b]]) M M
      (procIte (a ∈ X)
        ((b ~> (Pf a)[[a <-- b]]) [+]
          proc.Ext_pre_choice (X \ ({a} : Set α)) fun x => (Pf x)[[a <-- b]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[a <-- b]])) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Ext_pre_choice_Renaming_event_step` is
   represented by `cspT_Ext_pre_choice_Renaming1_event_step`,
   `cspT_Ext_pre_choice_Renaming2_set_event_step`, and
   `cspT_Ext_pre_choice_Renaming2_event_step`. -/

theorem cspT_Send_prefix_Renaming1_event1_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Send_prefix f v P)[[a <--> f v]]) M M (a ~> P[[a <--> f v]]) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming1_event2_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Send_prefix f v P)[[f v <--> a]]) M M (a ~> P[[f v <--> a]]) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming1_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domTType α} :
    a ≠ f v →
      b ≠ f v →
      eqT ((Send_prefix f v P)[[a <--> b]]) M M
        (Send_prefix f v (P[[a <--> b]])) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming1_event_step` is
   represented by `cspT_Send_prefix_Renaming1_event1_step_in`,
   `cspT_Send_prefix_Renaming1_event2_step_in`, and
   `cspT_Send_prefix_Renaming1_event_step_notin`. -/

theorem cspT_Send_prefix_Renaming2_set_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domTType α} :
    f v ∈ A →
      eqT ((Send_prefix f v P)[[A <<- a]]) M M (a ~> P[[A <<- a]]) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming2_set_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {b : α}
    {M : p → domTType α} :
    f v ∉ A →
      eqT ((Send_prefix f v P)[[A <<- b]]) M M
        (Send_prefix f v (P[[A <<- b]])) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming2_set_event_step
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domTType α} :
    eqT ((Send_prefix f v P)[[A <<- a]]) M M
      (procIte (f v ∈ A) (a ~> P[[A <<- a]]) (Send_prefix f v (P[[A <<- a]]))) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming2_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domTType α} :
    eqT ((Send_prefix f v P)[[f v <-- a]]) M M (a ~> P[[f v <-- a]]) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming2_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domTType α} :
    a ≠ f v →
      eqT ((Send_prefix f v P)[[a <-- b]]) M M
        (Send_prefix f v (P[[a <-- b]])) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming2_event_step` is
   represented by `cspT_Send_prefix_Renaming2_event_step_in` and
   `cspT_Send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming_event_step` is
   represented by `cspT_Send_prefix_Renaming1_event_step` and
   `cspT_Send_prefix_Renaming2_event_step`. -/

theorem cspT_Send_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((Send_prefix f v P)[[f <==> g]]) M M (Send_prefix g v (P[[f <==> g]])) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((Send_prefix f v P)[[g <==> f]]) M M (Send_prefix g v (P[[g <==> f]])) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqT ((Send_prefix h v P)[[f <==> g]]) M M
        (Send_prefix h v (P[[f <==> g]])) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming1_channel_step` is
   represented by `cspT_Send_prefix_Renaming1_channel1_step_in`,
   `cspT_Send_prefix_Renaming1_channel2_step_in`, and
   `cspT_Send_prefix_Renaming1_channel_step_notin`. -/

theorem cspT_Send_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((Send_prefix f v P)[[f <== g]]) M M (Send_prefix g v (P[[f <== g]])) := by
  cspT_auto_step_dist

theorem cspT_Send_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqT ((Send_prefix h v P)[[f <== g]]) M M
        (Send_prefix h v (P[[f <== g]])) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming2_channel_step` is
   represented by `cspT_Send_prefix_Renaming2_channel_step_in` and
   `cspT_Send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming_channel_step` is
   represented by `cspT_Send_prefix_Renaming1_channel_step` and
   `cspT_Send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming_step` is
   represented by `cspT_Send_prefix_Renaming_event_step` and
   `cspT_Send_prefix_Renaming_channel_step`. -/

theorem cspT_Rec_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqT ((Rec_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]]) := by
  cspT_auto_step_dist

theorem cspT_Rec_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqT ((Rec_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]]) := by
  cspT_auto_step_dist

theorem cspT_Rec_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      ((∀ x, x ∈ X → b ≠ f x) ∨ b ∉ f '' X) →
      eqT ((Rec_prefix f X Pf)[[a <--> b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <--> b]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming1_event_step` is
   represented by `cspT_Rec_prefix_Renaming1_event1_step_in`,
   `cspT_Rec_prefix_Renaming1_event2_step_in`, and
   `cspT_Rec_prefix_Renaming1_event_step_notin`. -/

theorem cspT_Rec_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqT ((Rec_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
          Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]]) := by
  intro _ hex
  have h1 : f '' {y | y ∈ X ∧ f y ∈ A} = (f '' X) ∩ A := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzX, hzA⟩, rfl⟩
      exact ⟨⟨z, hzX, rfl⟩, hzA⟩
    · rintro ⟨⟨z, hzX, rfl⟩, hyA⟩
      exact ⟨z, ⟨hzX, hyA⟩, rfl⟩
  have h2 : f '' (X \ {y | y ∈ X ∧ f y ∈ A}) = (f '' X) \ A := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzX, hz⟩, rfl⟩
      exact ⟨⟨z, hzX, rfl⟩, fun hA => hz ⟨hzX, hA⟩⟩
    · rintro ⟨⟨z, hzX, rfl⟩, hyA⟩
      exact ⟨z, ⟨hzX, fun hz => hyA hz.2⟩, rfl⟩
  have hne : (f '' X) ∩ A ≠ ∅ := by
    obtain ⟨z, hzX, hzA⟩ := hex
    intro hEq
    exact Set.eq_empty_iff_forall_notMem.mp hEq (f z) ⟨⟨z, hzX, rfl⟩, hzA⟩
  rw [Rec_prefix_def, Rec_prefix_def, Rep_int_choice_f_def, h1, h2]
  exact cspT_Ext_pre_choice_Renaming2_set_event_step_in hne

theorem cspT_Rec_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {A : Set α} {b : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqT ((Rec_prefix f X Pf)[[A <<- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[A <<- b]]) := by
  cspT_auto_step_dist

theorem cspT_Rec_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Rec_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
            Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Rec_prefix f X fun x => (Pf x)[[A <<- a]])) := by
  intro hinj
  by_cases hex : ∃ x, x ∈ X ∧ f x ∈ A
  · rw [procIte_pos hex]
    exact cspT_Rec_prefix_Renaming2_set_event_step_in hinj hex
  · rw [procIte_neg hex]
    refine cspT_Rec_prefix_Renaming2_set_event_step_notin (Or.inl ?_)
    intro z hzX hzA
    exact hex ⟨z, hzX, hzA⟩

theorem cspT_Rec_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      eqT ((Rec_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]]) := by
  cspT_auto_step_dist

theorem cspT_Rec_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      eqT ((Rec_prefix f X Pf)[[a <-- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <-- b]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming2_event_step` is
   represented by `cspT_Rec_prefix_Renaming2_event_step_in` and
   `cspT_Rec_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming_event_step` is
   represented by `cspT_Rec_prefix_Renaming1_event_step` and
   `cspT_Rec_prefix_Renaming2_event_step`. -/

theorem cspT_Rec_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix f X Pf)[[f <==> g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <==> g]]) := by
  cspT_auto_step_dist

theorem cspT_Rec_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix f X Pf)[[g <==> f]]) M M
        (Rec_prefix g X fun x => (Pf x)[[g <==> f]]) := by
  cspT_auto_step_dist

/- The Isabelle lemmas `Renaming_channel_fun_h` and
   `Renaming_channel_fun_map_h` are already represented in
   `LeanCspProver.CSP.Infra_ren`. -/

theorem cspT_Rec_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domTType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix h X Pf)[[f <==> g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <==> g]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming1_channel_step` is
   represented by `cspT_Rec_prefix_Renaming1_channel1_step_in`,
   `cspT_Rec_prefix_Renaming1_channel2_step_in`, and
   `cspT_Rec_prefix_Renaming1_channel_step_notin`. -/

theorem cspT_Rec_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix f X Pf)[[f <== g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <== g]]) := by
  cspT_auto_step_dist

theorem cspT_Rec_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domTType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix h X Pf)[[f <== g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <== g]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming2_channel_step` is
   represented by `cspT_Rec_prefix_Renaming2_channel_step_in` and
   `cspT_Rec_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming_channel_step` is
   represented by `cspT_Rec_prefix_Renaming1_channel_step` and
   `cspT_Rec_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming_step` is represented
   by `cspT_Rec_prefix_Renaming_event_step` and
   `cspT_Rec_prefix_Renaming_channel_step`. -/

theorem cspT_Nondet_send_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqT ((Nondet_send_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqT ((Nondet_send_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domTType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      ((∀ x, b ≠ f x) ∨ b ∉ Set.range f) →
      eqT ((Nondet_send_prefix f X Pf)[[a <--> b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <--> b]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming1_event_step`
   is represented by `cspT_Nondet_send_prefix_Renaming1_event1_step_in`,
   `cspT_Nondet_send_prefix_Renaming1_event2_step_in`, and
   `cspT_Nondet_send_prefix_Renaming1_event_step_notin`. -/

/-- The `Int_pre_choice` counterpart of
    `cspT_Ext_pre_choice_Renaming2_set_event_step_in`; this is what
    `cspT_Nondet_send_prefix_Renaming2_set_event_step_in` unfolds to. -/
private theorem Int_pre_choice_Renaming2_set_event_in
    {Y A : Set α} {Qf : α → proc p α} {a : α} {M : p → domTType α} :
    Y ∩ A ≠ ∅ →
      eqT ((Int_pre_choice Y Qf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_com (Y ∩ A) fun y => (Qf y)[[A <<- a]]) |~|
          Rep_int_choice_com (Y \ A) fun y => y ~> (Qf y)[[A <<- a]]) := by
  intro hYA
  obtain ⟨c, hcY, hcA⟩ : ∃ c, c ∈ Y ∧ c ∈ A := by
    by_contra hcon
    exact hYA (Set.eq_empty_iff_forall_notMem.mpr fun z hz => hcon ⟨z, hz.1, hz.2⟩)
  rw [Int_pre_choice_def, cspT_eqT_iff]
  intro t
  rw [in_traces_Renaming, in_traces_Int_choice, in_traces_Act_prefix,
    in_traces_Rep_int_choice_com (X := Y \ A)]
  constructor
  · rintro ⟨s, hren, hs⟩
    rw [in_traces_Rep_int_choice_com] at hs
    rcases hs with rfl | ⟨y, hyY, hs⟩
    · exact Or.inl (Or.inl (ren_tr_nil1.mp hren))
    · rw [in_traces_Act_prefix] at hs
      rcases hs with rfl | ⟨u, rfl, hu⟩
      · exact Or.inl (Or.inl (ren_tr_nil1.mp hren))
      · obtain ⟨b, tb, rfl, hab, hren'⟩ := ren_tr_decompo_left.mp hren
        rw [mem_Renaming2_event] at hab
        by_cases hyA : y ∈ A
        · have hba : b = a := by rw [hab]; simp [Renaming2_event_fun, hyA]
          subst hba
          refine Or.inl (Or.inr ⟨tb, rfl, ?_⟩)
          rw [in_traces_Rep_int_choice_com]
          exact Or.inr ⟨y, ⟨hyY, hyA⟩, in_traces_Renaming.mpr ⟨u, hren', hu⟩⟩
        · have hby : b = y := by rw [hab]; simp [Renaming2_event_fun, hyA]
          subst hby
          refine Or.inr (Or.inr ⟨b, ⟨hyY, hyA⟩, ?_⟩)
          rw [in_traces_Act_prefix]
          exact Or.inr ⟨tb, rfl, in_traces_Renaming.mpr ⟨u, hren', hu⟩⟩
  · have hnil : ∃ s, ren_tr s (Renaming2_event A a) (<> : traceType α) ∧
        s :t traces (Rep_int_choice_com Y fun y => y ~> Qf y) M :=
      ⟨<>, ren_tr_nil, in_traces_Rep_int_choice_com.mpr (Or.inl rfl)⟩
    rintro ((rfl | ⟨tb, rfl, hQ⟩) | (rfl | ⟨y, ⟨hyY, hyA⟩, hR⟩))
    · exact hnil
    · rw [in_traces_Rep_int_choice_com] at hQ
      rcases hQ with rfl | ⟨y, ⟨hyY, hyA⟩, hR⟩
      · refine ⟨Abs_trace [event.Ev c] ^^^ <>, ?_,
          in_traces_Rep_int_choice_com.mpr (Or.inr ⟨c, hcY, ?_⟩)⟩
        · refine ren_tr_decompo_left_if ?_ ren_tr_nil
          rw [mem_Renaming2_event]
          simp [Renaming2_event_fun, hcA]
        · exact in_traces_Act_prefix.mpr (Or.inr ⟨<>, rfl, nilt_in_T⟩)
      · obtain ⟨u, hren', hu⟩ := in_traces_Renaming.mp hR
        refine ⟨Abs_trace [event.Ev y] ^^^ u, ?_,
          in_traces_Rep_int_choice_com.mpr (Or.inr ⟨y, hyY, ?_⟩)⟩
        · refine ren_tr_decompo_left_if ?_ hren'
          rw [mem_Renaming2_event]
          simp [Renaming2_event_fun, hyA]
        · exact in_traces_Act_prefix.mpr (Or.inr ⟨u, rfl, hu⟩)
    · exact hnil
    · rw [in_traces_Act_prefix] at hR
      rcases hR with rfl | ⟨tb, rfl, hR⟩
      · exact hnil
      · obtain ⟨u, hren', hu⟩ := in_traces_Renaming.mp hR
        refine ⟨Abs_trace [event.Ev y] ^^^ u, ?_,
          in_traces_Rep_int_choice_com.mpr (Or.inr ⟨y, hyY, ?_⟩)⟩
        · refine ren_tr_decompo_left_if ?_ hren'
          rw [mem_Renaming2_event]
          simp [Renaming2_event_fun, hyA]
        · exact in_traces_Act_prefix.mpr (Or.inr ⟨u, rfl, hu⟩)

theorem cspT_Nondet_send_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqT ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
          Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]]) := by
  intro _ hex
  have h1 : f '' {y | y ∈ X ∧ f y ∈ A} = (f '' X) ∩ A := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzX, hzA⟩, rfl⟩
      exact ⟨⟨z, hzX, rfl⟩, hzA⟩
    · rintro ⟨⟨z, hzX, rfl⟩, hyA⟩
      exact ⟨z, ⟨hzX, hyA⟩, rfl⟩
  have h2 : f '' (X \ {y | y ∈ X ∧ f y ∈ A}) = (f '' X) \ A := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzX, hz⟩, rfl⟩
      exact ⟨⟨z, hzX, rfl⟩, fun hA => hz ⟨hzX, hA⟩⟩
    · rintro ⟨⟨z, hzX, rfl⟩, hyA⟩
      exact ⟨z, ⟨hzX, fun hz => hyA hz.2⟩, rfl⟩
  have hne : (f '' X) ∩ A ≠ ∅ := by
    obtain ⟨z, hzX, hzA⟩ := hex
    intro hEq
    exact Set.eq_empty_iff_forall_notMem.mp hEq (f z) ⟨⟨z, hzX, rfl⟩, hzA⟩
  rw [Nondet_send_prefix_def, Nondet_send_prefix_def, Rep_int_choice_f_def, h1, h2,
    Int_pre_choice_def]
  exact Int_pre_choice_Renaming2_set_event_in hne

theorem cspT_Nondet_send_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqT ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
            Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]])) := by
  intro hinj
  by_cases hex : ∃ x, x ∈ X ∧ f x ∈ A
  · rw [procIte_pos hex]
    exact cspT_Nondet_send_prefix_Renaming2_set_event_step_in hinj hex
  · rw [procIte_neg hex]
    refine cspT_Nondet_send_prefix_Renaming2_set_event_step_notin (Or.inl ?_)
    intro z hzX hzA
    exact hex ⟨z, hzX, hzA⟩

theorem cspT_Nondet_send_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqT ((Nondet_send_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domTType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      eqT ((Nondet_send_prefix f X Pf)[[a <-- b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <-- b]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming2_event_step`
   is represented by `cspT_Nondet_send_prefix_Renaming2_event_step_in` and
   `cspT_Nondet_send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming_event_step`
   is represented by `cspT_Nondet_send_prefix_Renaming1_event_step` and
   `cspT_Nondet_send_prefix_Renaming2_event_step`. -/

theorem cspT_Nondet_send_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Nondet_send_prefix f X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <==> g]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Nondet_send_prefix f X Pf)[[g <==> f]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[g <==> f]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domTType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      eqT ((Nondet_send_prefix h X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <==> g]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle
   `cspT_Nondet_send_prefix_Renaming1_channel_step` is represented by
   `cspT_Nondet_send_prefix_Renaming1_channel1_step_in`,
   `cspT_Nondet_send_prefix_Renaming1_channel2_step_in`, and
   `cspT_Nondet_send_prefix_Renaming1_channel_step_notin`. -/

theorem cspT_Nondet_send_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Nondet_send_prefix f X Pf)[[f <== g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <== g]]) := by
  cspT_auto_step_dist

theorem cspT_Nondet_send_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domTType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      eqT ((Nondet_send_prefix h X Pf)[[f <== g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <== g]]) := by
  cspT_auto_step_dist

/- The Isabelle theorem bundle
   `cspT_Nondet_send_prefix_Renaming2_channel_step` is represented by
   `cspT_Nondet_send_prefix_Renaming2_channel_step_in` and
   `cspT_Nondet_send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming_channel_step`
   is represented by `cspT_Nondet_send_prefix_Renaming1_channel_step` and
   `cspT_Nondet_send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming_step` is
   represented by `cspT_Nondet_send_prefix_Renaming_event_step` and
   `cspT_Nondet_send_prefix_Renaming_channel_step`. -/

/- The Isabelle theorem bundle `cspT_prefix_Renaming_in_step` is represented
   by the `..._step_in` theorems in this file. -/

/- The Isabelle theorem bundle `cspT_prefix_Renaming_notin_step` is
   represented by the `..._step_notin` theorems together with
   `cspT_Act_prefix_Renaming2_set_event_step`,
   `cspT_Send_prefix_Renaming2_set_event_step`,
   `cspT_Rec_prefix_Renaming2_set_event_step`,
   `cspT_Nondet_send_prefix_Renaming2_set_event_step`, and
   `cspT_Ext_pre_choice_Renaming_event_step`. -/
