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

axiom cspT_Rep_int_choice_sum_set_input
    {C : sets_nats α} {Xsf : aset_anat α → Set (Set α)} {Pff : aset_anat α → α → proc p α}
    {M : p → domTType α} :
    eqT
      (proc.Rep_int_choice C fun c =>
        Rep_int_choice_set (Xsf c) fun X => proc.Ext_pre_choice X (Pff c))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ c, c ∈ sumset C ∧ Xs = Xsf c}) fun X =>
        proc.Ext_pre_choice X fun a =>
          proc.Rep_int_choice (sub_sumset C fun c => ∃ X, X ∈ Xsf c ∧ a ∈ X) fun c =>
            Pff c a)

/- (*** cspT_Rep_int_choice_set_input ***)
-/

axiom cspT_Rep_int_choice_set_input
    {N : Set Nat} {Xsf : Nat → Set (Set α)} {Pff : Nat → α → proc p α}
    {M : p → domTType α} :
    eqT
      (Rep_int_choice_nat N fun n =>
        Rep_int_choice_set (Xsf n) fun X => proc.Ext_pre_choice X (Pff n))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ n, n ∈ N ∧ Xs = Xsf n}) fun X =>
        proc.Ext_pre_choice X fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ ∃ X, X ∈ Xsf n ∧ a ∈ X} fun n =>
            Pff n a)

/- (*** cspT_Rep_int_choice_set_set_DIV ***)
-/

axiom cspT_Rep_int_choice_set_set_DIV
    {Xs Ys : Set (Set α)} {M : p → domTType α} :
    Xs ≠ ∅ →
      Ys ≠ ∅ →
      eqT
        (Rep_int_choice_set Xs fun X =>
          Rep_int_choice_set Ys fun Y =>
            proc.Ext_pre_choice (X ∪ Y) fun _ => (proc.DIV : proc p α))
        M M
        (Rep_int_choice_set {Z | ∃ X, X ∈ Xs ∧ ∃ Y, Y ∈ Ys ∧ Z = X ∪ Y} fun Z =>
          proc.Ext_pre_choice Z fun _ => (proc.DIV : proc p α))

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

axiom cspT_Ext_pre_choice_Renaming_fun_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {f : α → α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[fun_to_rel f]]) M M
      (proc.Ext_pre_choice (f '' X) fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ y = f x} fun x =>
          (Pf x)[[fun_to_rel f]])

axiom cspT_Act_prefix_Renaming_fun_step
    {a : α} {P : proc p α} {f : α → α} {M : p → domTType α} :
    eqT (((a ~> P)[[fun_to_rel f]]) ) M M (f a ~> P[[fun_to_rel f]])

/- The Isabelle theorem bundle `cspT_Renaming_fun_step` is represented by
   `cspT_Ext_pre_choice_Renaming_fun_step` and
   `cspT_Act_prefix_Renaming_fun_step`. -/

axiom cspT_Act_prefix_Renaming1_event1_step_in
    {a b : α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[a <--> b]]) ) M M (b ~> P[[a <--> b]])

axiom cspT_Act_prefix_Renaming1_event2_step_in
    {a b : α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[b <--> a]]) ) M M (b ~> P[[b <--> a]])

axiom cspT_Act_prefix_Renaming1_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domTType α} :
    a ≠ c →
      b ≠ c →
      eqT (((c ~> P)[[a <--> b]]) ) M M (c ~> P[[a <--> b]])

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming1_event_step` is
   represented by `cspT_Act_prefix_Renaming1_event1_step_in`,
   `cspT_Act_prefix_Renaming1_event2_step_in`, and
   `cspT_Act_prefix_Renaming1_event_step_notin`. -/

axiom cspT_Act_prefix_Renaming2_set_event_step_in
    {a b : α} {A : Set α} {P : proc p α} {M : p → domTType α} :
    a ∈ A →
      eqT (((a ~> P)[[A <<- b]]) ) M M (b ~> P[[A <<- b]])

axiom cspT_Act_prefix_Renaming2_set_event_step_notin
    {b c : α} {A : Set α} {P : proc p α} {M : p → domTType α} :
    c ∉ A →
      eqT (((c ~> P)[[A <<- b]]) ) M M (c ~> P[[A <<- b]])

axiom cspT_Act_prefix_Renaming2_set_event_step
    {a b : α} {A : Set α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[A <<- b]]) ) M M
      (procIte (a ∈ A) (b ~> P[[A <<- b]]) (a ~> P[[A <<- b]]))

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming2_set_event_steps` is
   represented by `cspT_Act_prefix_Renaming2_set_event_step_in` and
   `cspT_Act_prefix_Renaming2_set_event_step_notin`. -/

axiom cspT_Act_prefix_Renaming2_event_step_in
    {a b : α} {P : proc p α} {M : p → domTType α} :
    eqT (((a ~> P)[[a <-- b]]) ) M M (b ~> P[[a <-- b]])

axiom cspT_Act_prefix_Renaming2_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domTType α} :
    c ≠ a →
      eqT (((c ~> P)[[a <-- b]]) ) M M (c ~> P[[a <-- b]])

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming2_event_step` is
   represented by `cspT_Act_prefix_Renaming2_event_step_in` and
   `cspT_Act_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming_event_step` is
   represented by `cspT_Act_prefix_Renaming1_event_step` and
   `cspT_Act_prefix_Renaming2_event_step`. -/

axiom cspT_Act_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((((f v) ~> P)[[f <==> g]]) ) M M (g v ~> P[[f <==> g]])

axiom cspT_Act_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((((f v) ~> P)[[g <==> f]]) ) M M (g v ~> P[[g <==> f]])

axiom cspT_Act_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α} {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqT ((((h v) ~> P)[[f <==> g]]) ) M M ((h v) ~> P[[f <==> g]])

/- The Isabelle theorem bundle `cspT_Act_prefix_Renaming1_channel_step` is
   represented by `cspT_Act_prefix_Renaming1_channel1_step_in`,
   `cspT_Act_prefix_Renaming1_channel2_step_in`, and
   `cspT_Act_prefix_Renaming1_channel_step_notin`. -/

axiom cspT_Act_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((((f v) ~> P)[[f <== g]]) ) M M (g v ~> P[[f <== g]])

axiom cspT_Act_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f : x → α} {g : x → α} {h : y → α} {v : y}
    {P : proc p α} {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqT ((((h v) ~> P)[[f <== g]]) ) M M ((h v) ~> P[[f <== g]])

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

axiom cspT_Ext_pre_choice_Renaming1_event1_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]]))

axiom cspT_Ext_pre_choice_Renaming1_event2_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    a = b →
      eqT ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
        ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
          (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
          (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]]))

axiom cspT_Ext_pre_choice_Renaming1_event_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]]))

axiom cspT_Ext_pre_choice_Renaming2_set_event_step_in [Inhabited α]
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domTType α} :
    X ∩ A ≠ ∅ →
      eqT ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]])

axiom cspT_Ext_pre_choice_Renaming2_set_event_step_notin
    {X A : Set α} {Pf : α → proc p α} {b : α} {M : p → domTType α} :
    X ∩ A = ∅ →
      eqT ((proc.Ext_pre_choice X Pf)[[A <<- b]]) M M
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- b]])

axiom cspT_Ext_pre_choice_Renaming2_set_event_step [Inhabited α]
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
      (procIte (X ∩ A ≠ ∅)
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- a]]))

axiom cspT_Ext_pre_choice_Renaming2_event_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf)[[a <-- b]]) M M
      (procIte (a ∈ X)
        ((b ~> (Pf a)[[a <-- b]]) [+]
          proc.Ext_pre_choice (X \ ({a} : Set α)) fun x => (Pf x)[[a <-- b]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[a <-- b]]))

/- The Isabelle theorem bundle `cspT_Ext_pre_choice_Renaming_event_step` is
   represented by `cspT_Ext_pre_choice_Renaming1_event_step`,
   `cspT_Ext_pre_choice_Renaming2_set_event_step`, and
   `cspT_Ext_pre_choice_Renaming2_event_step`. -/

axiom cspT_Send_prefix_Renaming1_event1_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Send_prefix f v P)[[a <--> f v]]) M M (a ~> P[[a <--> f v]])

axiom cspT_Send_prefix_Renaming1_event2_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Send_prefix f v P)[[f v <--> a]]) M M (a ~> P[[f v <--> a]])

axiom cspT_Send_prefix_Renaming1_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domTType α} :
    a ≠ f v →
      b ≠ f v →
      eqT ((Send_prefix f v P)[[a <--> b]]) M M
        (Send_prefix f v (P[[a <--> b]]))

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming1_event_step` is
   represented by `cspT_Send_prefix_Renaming1_event1_step_in`,
   `cspT_Send_prefix_Renaming1_event2_step_in`, and
   `cspT_Send_prefix_Renaming1_event_step_notin`. -/

axiom cspT_Send_prefix_Renaming2_set_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domTType α} :
    f v ∈ A →
      eqT ((Send_prefix f v P)[[A <<- a]]) M M (a ~> P[[A <<- a]])

axiom cspT_Send_prefix_Renaming2_set_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {b : α}
    {M : p → domTType α} :
    f v ∉ A →
      eqT ((Send_prefix f v P)[[A <<- b]]) M M
        (Send_prefix f v (P[[A <<- b]]))

axiom cspT_Send_prefix_Renaming2_set_event_step
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domTType α} :
    eqT ((Send_prefix f v P)[[A <<- a]]) M M
      (procIte (f v ∈ A) (a ~> P[[A <<- a]]) (Send_prefix f v (P[[A <<- a]])))

axiom cspT_Send_prefix_Renaming2_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domTType α} :
    eqT ((Send_prefix f v P)[[f v <-- a]]) M M (a ~> P[[f v <-- a]])

axiom cspT_Send_prefix_Renaming2_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domTType α} :
    a ≠ f v →
      eqT ((Send_prefix f v P)[[a <-- b]]) M M
        (Send_prefix f v (P[[a <-- b]]))

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming2_event_step` is
   represented by `cspT_Send_prefix_Renaming2_event_step_in` and
   `cspT_Send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming_event_step` is
   represented by `cspT_Send_prefix_Renaming1_event_step` and
   `cspT_Send_prefix_Renaming2_event_step`. -/

axiom cspT_Send_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((Send_prefix f v P)[[f <==> g]]) M M (Send_prefix g v (P[[f <==> g]]))

axiom cspT_Send_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((Send_prefix f v P)[[g <==> f]]) M M (Send_prefix g v (P[[g <==> f]]))

axiom cspT_Send_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqT ((Send_prefix h v P)[[f <==> g]]) M M
        (Send_prefix h v (P[[f <==> g]]))

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming1_channel_step` is
   represented by `cspT_Send_prefix_Renaming1_channel1_step_in`,
   `cspT_Send_prefix_Renaming1_channel2_step_in`, and
   `cspT_Send_prefix_Renaming1_channel_step_notin`. -/

axiom cspT_Send_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domTType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqT ((Send_prefix f v P)[[f <== g]]) M M (Send_prefix g v (P[[f <== g]]))

axiom cspT_Send_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domTType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqT ((Send_prefix h v P)[[f <== g]]) M M
        (Send_prefix h v (P[[f <== g]]))

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming2_channel_step` is
   represented by `cspT_Send_prefix_Renaming2_channel_step_in` and
   `cspT_Send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming_channel_step` is
   represented by `cspT_Send_prefix_Renaming1_channel_step` and
   `cspT_Send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspT_Send_prefix_Renaming_step` is
   represented by `cspT_Send_prefix_Renaming_event_step` and
   `cspT_Send_prefix_Renaming_channel_step`. -/

axiom cspT_Rec_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqT ((Rec_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]])

axiom cspT_Rec_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqT ((Rec_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]])

axiom cspT_Rec_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      ((∀ x, x ∈ X → b ≠ f x) ∨ b ∉ f '' X) →
      eqT ((Rec_prefix f X Pf)[[a <--> b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <--> b]])

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming1_event_step` is
   represented by `cspT_Rec_prefix_Renaming1_event1_step_in`,
   `cspT_Rec_prefix_Renaming1_event2_step_in`, and
   `cspT_Rec_prefix_Renaming1_event_step_notin`. -/

axiom cspT_Rec_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqT ((Rec_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
          Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])

axiom cspT_Rec_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {A : Set α} {b : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqT ((Rec_prefix f X Pf)[[A <<- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[A <<- b]])

axiom cspT_Rec_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Rec_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
            Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Rec_prefix f X fun x => (Pf x)[[A <<- a]]))

axiom cspT_Rec_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      eqT ((Rec_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]])

axiom cspT_Rec_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      eqT ((Rec_prefix f X Pf)[[a <-- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <-- b]])

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming2_event_step` is
   represented by `cspT_Rec_prefix_Renaming2_event_step_in` and
   `cspT_Rec_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming_event_step` is
   represented by `cspT_Rec_prefix_Renaming1_event_step` and
   `cspT_Rec_prefix_Renaming2_event_step`. -/

axiom cspT_Rec_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix f X Pf)[[f <==> g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <==> g]])

axiom cspT_Rec_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix f X Pf)[[g <==> f]]) M M
        (Rec_prefix g X fun x => (Pf x)[[g <==> f]])

/- The Isabelle lemmas `Renaming_channel_fun_h` and
   `Renaming_channel_fun_map_h` are already represented in
   `LeanCspProver.CSP.Infra_ren`. -/

axiom cspT_Rec_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domTType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix h X Pf)[[f <==> g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <==> g]])

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming1_channel_step` is
   represented by `cspT_Rec_prefix_Renaming1_channel1_step_in`,
   `cspT_Rec_prefix_Renaming1_channel2_step_in`, and
   `cspT_Rec_prefix_Renaming1_channel_step_notin`. -/

axiom cspT_Rec_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix f X Pf)[[f <== g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <== g]])

axiom cspT_Rec_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domTType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqT ((Rec_prefix h X Pf)[[f <== g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <== g]])

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming2_channel_step` is
   represented by `cspT_Rec_prefix_Renaming2_channel_step_in` and
   `cspT_Rec_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming_channel_step` is
   represented by `cspT_Rec_prefix_Renaming1_channel_step` and
   `cspT_Rec_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspT_Rec_prefix_Renaming_step` is represented
   by `cspT_Rec_prefix_Renaming_event_step` and
   `cspT_Rec_prefix_Renaming_channel_step`. -/

axiom cspT_Nondet_send_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqT ((Nondet_send_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]])

axiom cspT_Nondet_send_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqT ((Nondet_send_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]])

axiom cspT_Nondet_send_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domTType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      ((∀ x, b ≠ f x) ∨ b ∉ Set.range f) →
      eqT ((Nondet_send_prefix f X Pf)[[a <--> b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <--> b]])

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming1_event_step`
   is represented by `cspT_Nondet_send_prefix_Renaming1_event1_step_in`,
   `cspT_Nondet_send_prefix_Renaming1_event2_step_in`, and
   `cspT_Nondet_send_prefix_Renaming1_event_step_notin`. -/

axiom cspT_Nondet_send_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqT ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
          Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])

axiom cspT_Nondet_send_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqT ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]])

axiom cspT_Nondet_send_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domTType α} :
    Injective f →
      eqT ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
            Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]]))

axiom cspT_Nondet_send_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domTType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqT ((Nondet_send_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]])

axiom cspT_Nondet_send_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domTType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      eqT ((Nondet_send_prefix f X Pf)[[a <-- b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <-- b]])

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming2_event_step`
   is represented by `cspT_Nondet_send_prefix_Renaming2_event_step_in` and
   `cspT_Nondet_send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspT_Nondet_send_prefix_Renaming_event_step`
   is represented by `cspT_Nondet_send_prefix_Renaming1_event_step` and
   `cspT_Nondet_send_prefix_Renaming2_event_step`. -/

axiom cspT_Nondet_send_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Nondet_send_prefix f X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <==> g]])

axiom cspT_Nondet_send_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Nondet_send_prefix f X Pf)[[g <==> f]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[g <==> f]])

axiom cspT_Nondet_send_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited α] [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domTType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      eqT ((Nondet_send_prefix h X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <==> g]])

/- The Isabelle theorem bundle
   `cspT_Nondet_send_prefix_Renaming1_channel_step` is represented by
   `cspT_Nondet_send_prefix_Renaming1_channel1_step_in`,
   `cspT_Nondet_send_prefix_Renaming1_channel2_step_in`, and
   `cspT_Nondet_send_prefix_Renaming1_channel_step_notin`. -/

axiom cspT_Nondet_send_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domTType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqT ((Nondet_send_prefix f X Pf)[[f <== g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <== g]])

axiom cspT_Nondet_send_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited α] [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domTType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      eqT ((Nondet_send_prefix h X Pf)[[f <== g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <== g]])

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
