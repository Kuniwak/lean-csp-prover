           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                October 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_aux
import LeanCspProver.CSP_T.CSP_T_law_etc

open Function
open SumType

noncomputable section

/-
(*------------------------*
         |~| --> !!
 *------------------------*)
-/

theorem cspF_Int_choice_to_Rep
    {P Q : proc p α} {M : p → domFType α} :
    eqF (P |~| Q) M M
      (Rep_int_choice_nat ({0, 1} : Set Nat) fun n => IF n = 0 THEN P ELSE Q) := by
  cspF_auto_step_dist

/- (*** cspF_Rep_int_choice_set_input ***) -/

theorem cspF_Rep_int_choice_sum_set_input
    {C : sets_nats α} {Xsf : aset_anat α → Set (Set α)} {Pff : aset_anat α → α → proc p α}
    {M : p → domFType α} :
    eqF
      (proc.Rep_int_choice C fun c =>
        Rep_int_choice_set (Xsf c) fun X => proc.Ext_pre_choice X (Pff c))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ c, c ∈ sumset C ∧ Xs = Xsf c}) fun X =>
        proc.Ext_pre_choice X fun a =>
          proc.Rep_int_choice (sub_sumset C fun c => ∃ X, X ∈ Xsf c ∧ a ∈ X) fun c =>
            Pff c a) := by
  cspF_auto_step_dist

/- (*** cspF_Rep_int_choice_set_input ***) -/

theorem cspF_Rep_int_choice_set_input
    {N : Set Nat} {Xsf : Nat → Set (Set α)} {Pff : Nat → α → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_nat N fun n =>
        Rep_int_choice_set (Xsf n) fun X => proc.Ext_pre_choice X (Pff n))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ n, n ∈ N ∧ Xs = Xsf n}) fun X =>
        proc.Ext_pre_choice X fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ ∃ X, X ∈ Xsf n ∧ a ∈ X} fun n =>
            Pff n a) := by
  cspF_auto_step_dist

/- (*** cspF_Rep_int_choice_set_set_DIV ***) -/

theorem cspF_Rep_int_choice_set_set_DIV
    {Xs Ys : Set (Set α)} {M : p → domFType α} :
    Xs ≠ ∅ →
      Ys ≠ ∅ →
      eqF
        (Rep_int_choice_set Xs fun X =>
          Rep_int_choice_set Ys fun Y =>
            proc.Ext_pre_choice (X ∪ Y) fun _ => (proc.DIV : proc p α))
        M M
        (Rep_int_choice_set {Z | ∃ X, X ∈ Xs ∧ ∃ Y, Y ∈ Ys ∧ Z = X ∪ Y} fun Z =>
          proc.Ext_pre_choice Z fun _ => (proc.DIV : proc p α)) := by
  cspF_auto_step_dist

/-
(*********************************************************
               (P [+] SKIP) |~| (Q [+] SKIP)
 *********************************************************)

(* p.289 *)
-/

theorem cspF_Int_choice_Ext_choice_SKIP
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.SKIP) |~| (Q [+] proc.SKIP)) M M (P [+] Q [+] proc.SKIP) := by
  cspF_auto_step_dist

/-
(*********************************************************
               (P [+] DIV) |~| (Q [+] DIV)
 *********************************************************)
-/

theorem cspF_Int_choice_Ext_choice_DIV
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.DIV) |~| (Q [+] proc.DIV)) M M (P [+] Q [+] proc.DIV) := by
  cspF_auto_step_dist

/-
(*********************************************************
             (P [+] SKIP) |~| (Q [+] DIV)
 *********************************************************)
-/

theorem cspF_Int_choice_Ext_choice_SKIP_DIV
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.SKIP) |~| (Q [+] proc.DIV)) M M (P [+] Q [+] proc.SKIP) := by
  cspF_auto_step_dist

/-
(*********************************************************
             (P [+] DIV) |~| (Q [+] SKIP)
 *********************************************************)
-/

theorem cspF_Int_choice_Ext_choice_DIV_SKIP
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.DIV) |~| (Q [+] proc.SKIP)) M M (P [+] Q [+] proc.SKIP) := by
  cspF_auto_step_dist

/-
(*********************************************************
         (P [+] SKIP or DIV) |~| (Q [+] DIV or SKIP)
 *********************************************************)
-/

theorem cspF_Int_choice_Ext_choice_SKIP_or_DIV
    {P1 P2 Q1 Q2 : proc p α} {M : p → domFType α} :
    (P2 = proc.SKIP ∨ P2 = proc.DIV) →
      (Q2 = proc.SKIP ∨ Q2 = proc.DIV) →
      eqF ((P1 [+] P2) |~| (Q1 [+] Q2)) M M (P1 [+] Q1 [+] (P2 |~| Q2)) := by
  rintro (rfl | rfl) (rfl | rfl) <;> cspF_auto_step_dist

/-
(*********************************************************
                    (P [+] DIV) |~| P
 *********************************************************)
-/

theorem cspF_Ext_choice_DIV_Int_choice_Id
    {P : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.DIV) |~| P) M M P := by
  cspF_auto_step_dist

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 |                    (renaming)                       |
 * =================================================== *)
-/

/-! ### Helpers for the renaming step laws -/

/-- Failures of `P [+] Q` when neither side can terminate. -/
private theorem in_failures_Ext_choice_noTick {P Q : proc p α} {u : traceType α}
    {W : Set (event α)} {M : p → domFType α}
    (hP : ¬ ((Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M)))
    (hQ : ¬ ((Abs_trace [event.Tick] : traceType α) :t traces Q (fstF ∘ M))) :
    ((u, W) :f failures (P [+] Q) M) ↔
      ((u = <> ∧ (u, W) :f failures P M ∧ (u, W) :f failures Q M) ∨
        (u ≠ <> ∧ ((u, W) :f failures P M ∨ (u, W) :f failures Q M))) := by
  rw [in_failures_Ext_choice]
  constructor
  · rintro (⟨⟨V, hEq⟩, hp, hq⟩ | ⟨v, ⟨V, hEq⟩, hor, hne⟩ | ⟨V, hEq, hTk, -⟩)
    · exact Or.inl ⟨(Prod.mk.inj hEq).1, hp, hq⟩
    · exact Or.inr ⟨fun h => hne ((Prod.mk.inj hEq).1.symm.trans h), hor⟩
    · rcases hTk with h | h
      · exact absurd h hP
      · exact absurd h hQ
  · rintro (⟨rfl, hp, hq⟩ | ⟨hne, hor⟩)
    · exact Or.inl ⟨⟨W, rfl⟩, hp, hq⟩
    · exact Or.inr (Or.inl ⟨u, ⟨W, rfl⟩, hor, hne⟩)

private theorem Tick_notin_traces_Act_prefix {c : α} {P : proc p α} {M : p → domTType α} :
    ¬ ((Abs_trace [event.Tick] : traceType α) :t traces (c ~> P) M) := by
  intro h
  rw [in_traces_Act_prefix] at h
  rcases h with h | ⟨w, hw, -⟩
  · simp at h
  · have hhd := congrArg hdt hw
    simp [hdt_appt] at hhd

private theorem Tick_notin_traces_STOP {M : p → domTType α} :
    ¬ ((Abs_trace [event.Tick] : traceType α) :t traces (proc.STOP : proc p α) M) := by
  intro h
  rw [in_traces_STOP] at h
  simp at h

private theorem in_failures_procIte_Act_prefix {c : α} {P : proc p α} {C : Prop}
    {v : traceType α} {V : Set (event α)} {M : p → domFType α} :
    ((v, V) :f failures (procIte C (c ~> P) proc.STOP) M) ↔
      ((v = <> ∧ (C → (event.Ev c : event α) ∉ V)) ∨
        (C ∧ ∃ t', v = Abs_trace [event.Ev c] ^^^ t' ∧ (t', V) :f failures P M)) := by
  by_cases hC : C
  · rw [procIte_pos hC, in_failures_Act_prefix]
    constructor
    · rintro (⟨V1, hE1, hb⟩ | ⟨s1, V1, hE1, hf⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
        exact Or.inl ⟨rfl, fun _ => hb⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
        exact Or.inr ⟨hC, s1, rfl, hf⟩
    · rintro (⟨rfl, hb⟩ | ⟨-, t', rfl, hf⟩)
      · exact Or.inl ⟨V, rfl, hb hC⟩
      · exact Or.inr ⟨t', V, rfl, hf⟩
  · rw [procIte_neg hC, in_failures_STOP]
    constructor
    · rintro ⟨V1, hE1⟩
      obtain ⟨rfl, -⟩ := Prod.mk.inj hE1
      exact Or.inl ⟨rfl, fun h => absurd h hC⟩
    · rintro (⟨rfl, -⟩ | ⟨hC', -⟩)
      · exact ⟨V, rfl⟩
      · exact absurd hC' hC

private theorem Tick_notin_traces_procIte {c : α} {P : proc p α} {C : Prop}
    {M : p → domTType α} :
    ¬ ((Abs_trace [event.Tick] : traceType α) :t traces (procIte C (c ~> P) proc.STOP) M) := by
  by_cases hC : C
  · rw [procIte_pos hC]
    exact Tick_notin_traces_Act_prefix
  · rw [procIte_neg hC]
    exact Tick_notin_traces_STOP

private theorem ren_inv_disjoint_iff {X : Set α} {r : Set (α × α)} {W : Set (event α)} :
    event.Ev '' X ∩ ren_inv r W = ∅ ↔
      ∀ x, x ∈ X → ∀ b, (x, b) ∈ r → (event.Ev b : event α) ∉ W := by
  constructor
  · intro hX x hxX b hxb hbW
    have hm : (event.Ev x : event α) ∈ event.Ev '' X ∩ ren_inv r W :=
      ⟨⟨x, hxX, rfl⟩, ren_inv_mem_Ev.mpr ⟨b, hxb, hbW⟩⟩
    rw [hX] at hm
    exact hm
  · intro hX
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨⟨x, hxX, rfl⟩, he⟩
    obtain ⟨b, hxb, hbW⟩ := ren_inv_mem_Ev.mp he
    exact hX x hxX b hxb hbW

private theorem Renaming2_pair {A : Set α} {a x : α} (hxA : x ∈ A) :
    ((x, a) ∈ (Renaming2_event A a : Set (α × α))) := by
  rw [mem_Renaming2_event]
  simp [Renaming2_event_fun, hxA]

private theorem Renaming2_pair' {A : Set α} {a x : α} (hxA : x ∉ A) :
    ((x, x) ∈ (Renaming2_event A a : Set (α × α))) := by
  rw [mem_Renaming2_event]
  simp [Renaming2_event_fun, hxA]

/-- Renaming by a function that is the identity on the index set commutes with
    `? :Y -> Qf`. -/
private theorem Renaming_fun_Ext_pre_choice_id
    {Y : Set α} {Qf : α → proc p α} {g : α → α} {M : p → domFType α}
    (hg : ∀ y, y ∈ Y → g y = y) :
    eqF ((proc.Ext_pre_choice Y Qf)[[fun_to_rel g]]) M M
      (proc.Ext_pre_choice Y fun y => (Qf y)[[fun_to_rel g]]) := by
  rw [cspF_eqF_iff]
  constructor
  · intro t
    rw [in_traces_Renaming, in_traces_Ext_pre_choice (X := Y)]
    constructor
    · rintro ⟨s, hren, hs⟩
      rw [in_traces_Ext_pre_choice] at hs
      rcases hs with rfl | ⟨y, sy, rfl, hsy, hyY⟩
      · exact Or.inl (ren_tr_nil1.mp hren)
      · obtain ⟨b, tb, rfl, hyb, hren'⟩ := ren_tr_decompo_left.mp hren
        rw [mem_fun_to_rel, hg y hyY] at hyb
        subst hyb
        exact Or.inr ⟨b, tb, rfl, in_traces_Renaming.mpr ⟨sy, hren', hsy⟩, hyY⟩
    · rintro (rfl | ⟨y, tb, rfl, ht, hyY⟩)
      · exact ⟨<>, ren_tr_nil, in_traces_Ext_pre_choice.mpr (Or.inl rfl)⟩
      · obtain ⟨sy, hren', hsy⟩ := in_traces_Renaming.mp ht
        refine ⟨Abs_trace [event.Ev y] ^^^ sy, ren_tr_decompo_left_if ?_ hren',
          in_traces_Ext_pre_choice.mpr (Or.inr ⟨y, sy, rfl, hsy, hyY⟩)⟩
        rw [mem_fun_to_rel, hg y hyY]
  · intro u W
    rw [in_failures_Renaming_Ext_pre_choice, in_failures_Ext_pre_choice (X := Y)]
    constructor
    · rintro (⟨rfl, hY⟩ | ⟨y, b, t', hyY, hyb, rfl, hf⟩)
      · refine Or.inl ⟨W, rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨z, hzY, rfl⟩, he⟩
        have hm : (event.Ev z : event α) ∈ event.Ev '' Y ∩ ren_inv (fun_to_rel g) W :=
          ⟨⟨z, hzY, rfl⟩, ren_inv_mem_Ev.mpr ⟨z, by rw [mem_fun_to_rel, hg z hzY], he⟩⟩
        rw [hY] at hm
        exact hm
      · rw [mem_fun_to_rel, hg y hyY] at hyb
        subst hyb
        exact Or.inr ⟨b, t', W, rfl, hf, hyY⟩
    · rintro (⟨V, hEq, hY⟩ | ⟨y, t', V, hEq, hf, hyY⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        refine Or.inl ⟨rfl, ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨z, hzY, rfl⟩, he⟩
        obtain ⟨b, hzb, hbW⟩ := ren_inv_mem_Ev.mp he
        rw [mem_fun_to_rel, hg z hzY] at hzb
        subst hzb
        have hm : (event.Ev b : event α) ∈ event.Ev '' Y ∩ W := ⟨⟨b, hzY, rfl⟩, hbW⟩
        rw [hY] at hm
        exact hm
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        exact Or.inr ⟨y, y, t', hyY, by rw [mem_fun_to_rel, hg y hyY], rfl, hf⟩

private theorem image_inter_filter {x : Type _} {f : x → α} {X : Set x} {A : Set α} :
    f '' {y | y ∈ X ∧ f y ∈ A} = (f '' X) ∩ A := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzX, hzA⟩, rfl⟩
    exact ⟨⟨z, hzX, rfl⟩, hzA⟩
  · rintro ⟨⟨z, hzX, rfl⟩, hyA⟩
    exact ⟨z, ⟨hzX, hyA⟩, rfl⟩

private theorem image_diff_filter {x : Type _} {f : x → α} {X : Set x} {A : Set α} :
    f '' (X \ {y | y ∈ X ∧ f y ∈ A}) = (f '' X) \ A := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzX, hz⟩, rfl⟩
    exact ⟨⟨z, hzX, rfl⟩, fun hA => hz ⟨hzX, hA⟩⟩
  · rintro ⟨⟨z, hzX, rfl⟩, hyA⟩
    exact ⟨z, ⟨hzX, fun hz => hyA hz.2⟩, rfl⟩

theorem cspF_Ext_pre_choice_Renaming_fun_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {f : α → α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[fun_to_rel f]]) M M
      (proc.Ext_pre_choice (f '' X) fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ y = f x} fun x =>
          (Pf x)[[fun_to_rel f]]) := by
  refine cspF_rw_left_eq cspF_Renaming_step ?_
  have hS : {y | ∃ x, x ∈ X ∧ (x, y) ∈ fun_to_rel f} = f '' X := by
    ext y
    simp [Set.mem_image, eq_comm]
  refine cspF_Ext_pre_choice_cong hS fun a ha => ?_
  have hT : {x | x ∈ X ∧ (x, a) ∈ fun_to_rel f} = {x | x ∈ X ∧ a = f x} := by
    ext x
    simp
  rw [hT]
  exact cspF_reflex_eq_P

theorem cspF_Act_prefix_Renaming_fun_step
    {a : α} {P : proc p α} {f : α → α} {M : p → domFType α} :
    eqF (((a ~> P)[[fun_to_rel f]]) ) M M (f a ~> P[[fun_to_rel f]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Renaming_fun_step` is represented by
   `cspF_Ext_pre_choice_Renaming_fun_step` and
   `cspF_Act_prefix_Renaming_fun_step`. -/

theorem cspF_Act_prefix_Renaming1_event1_step_in
    {a b : α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[a <--> b]]) ) M M (b ~> P[[a <--> b]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming1_event2_step_in
    {a b : α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[b <--> a]]) ) M M (b ~> P[[b <--> a]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming1_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domFType α} :
    a ≠ c →
      b ≠ c →
      eqF (((c ~> P)[[a <--> b]]) ) M M (c ~> P[[a <--> b]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming1_event_step` is
   represented by `cspF_Act_prefix_Renaming1_event1_step_in`,
   `cspF_Act_prefix_Renaming1_event2_step_in`, and
   `cspF_Act_prefix_Renaming1_event_step_notin`. -/

theorem cspF_Act_prefix_Renaming2_set_event_step_in
    {a b : α} {A : Set α} {P : proc p α} {M : p → domFType α} :
    a ∈ A →
      eqF (((a ~> P)[[A <<- b]]) ) M M (b ~> P[[A <<- b]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming2_set_event_step_notin
    {b c : α} {A : Set α} {P : proc p α} {M : p → domFType α} :
    c ∉ A →
      eqF (((c ~> P)[[A <<- b]]) ) M M (c ~> P[[A <<- b]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming2_set_event_step
    {a b : α} {A : Set α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[A <<- b]]) ) M M
      (procIte (a ∈ A) (b ~> P[[A <<- b]]) (a ~> P[[A <<- b]])) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming2_set_event_steps` is
   represented by `cspF_Act_prefix_Renaming2_set_event_step_in` and
   `cspF_Act_prefix_Renaming2_set_event_step_notin`. -/

theorem cspF_Act_prefix_Renaming2_event_step_in
    {a b : α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[a <-- b]]) ) M M (b ~> P[[a <-- b]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming2_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domFType α} :
    c ≠ a →
      eqF (((c ~> P)[[a <-- b]]) ) M M (c ~> P[[a <-- b]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming2_event_step` is
   represented by `cspF_Act_prefix_Renaming2_event_step_in` and
   `cspF_Act_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming_event_step` is
   represented by `cspF_Act_prefix_Renaming1_event_step` and
   `cspF_Act_prefix_Renaming2_event_step`. -/

theorem cspF_Act_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((((f v) ~> P)[[f <==> g]]) ) M M (g v ~> P[[f <==> g]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((((f v) ~> P)[[g <==> f]]) ) M M (g v ~> P[[g <==> f]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α} {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqF ((((h v) ~> P)[[f <==> g]]) ) M M ((h v) ~> P[[f <==> g]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming1_channel_step` is
   represented by `cspF_Act_prefix_Renaming1_channel1_step_in`,
   `cspF_Act_prefix_Renaming1_channel2_step_in`, and
   `cspF_Act_prefix_Renaming1_channel_step_notin`. -/

theorem cspF_Act_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((((f v) ~> P)[[f <== g]]) ) M M (g v ~> P[[f <== g]]) := by
  cspF_auto_step_dist

theorem cspF_Act_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f : x → α} {g : x → α} {h : y → α} {v : y}
    {P : proc p α} {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqF ((((h v) ~> P)[[f <== g]]) ) M M ((h v) ~> P[[f <== g]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming2_channel_step` is
   represented by `cspF_Act_prefix_Renaming2_channel_step_in` and
   `cspF_Act_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming_channel_step` is
   represented by `cspF_Act_prefix_Renaming1_channel_step` and
   `cspF_Act_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming_step` is represented
   by `cspF_Act_prefix_Renaming_fun_step`,
   `cspF_Act_prefix_Renaming_event_step`, and
   `cspF_Act_prefix_Renaming_channel_step`. -/

theorem cspF_Ext_pre_choice_Renaming1_event1_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])) := by
  have hra : Renaming1_event_fun a b a = b := by simp [Renaming1_event_fun]
  have hrb : Renaming1_event_fun a b b = a := by
    by_cases h : b = a <;> simp [Renaming1_event_fun, h]
  have hrz : ∀ z, z ≠ a → z ≠ b → Renaming1_event_fun a b z = z := by
    intro z h1 h2
    simp [Renaming1_event_fun, h1, h2]
  refine cspF_eqF_of_eqT cspT_Ext_pre_choice_Renaming1_event_step ?_
  intro u W
  have hT1 : ¬ ((Abs_trace [event.Tick] : traceType α) :t
      traces (procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) (proc.STOP : proc p α)) (fstF ∘ M)) :=
    Tick_notin_traces_procIte
  have hT2 : ¬ ((Abs_trace [event.Tick] : traceType α) :t
      traces (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) (proc.STOP : proc p α)) (fstF ∘ M)) :=
    Tick_notin_traces_procIte
  have hT3 : ¬ ((Abs_trace [event.Tick] : traceType α) :t
      traces (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])
        (fstF ∘ M)) :=
    Tick_notin_traces_Ext_pre_choice
  have hT12 : ¬ ((Abs_trace [event.Tick] : traceType α) :t
      traces ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) (proc.STOP : proc p α)) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) (proc.STOP : proc p α))) (fstF ∘ M)) := by
    intro h
    rcases in_traces_Ext_choice.mp h with h | h
    · exact hT1 h
    · exact hT2 h
  rw [in_failures_Ext_choice_noTick hT12 hT3, in_failures_Ext_choice_noTick hT1 hT2,
    in_failures_procIte_Act_prefix (c := b) (P := (Pf a)[[a <--> b]]),
    in_failures_procIte_Act_prefix (c := a) (P := (Pf b)[[a <--> b]]),
    in_failures_Ext_pre_choice (X := X \ ({a, b} : Set α)),
    in_failures_Renaming_Ext_pre_choice, ren_inv_disjoint_iff]
  constructor
  · rintro (⟨rfl, hX⟩ | ⟨x, c, t', hxX, hxc, rfl, hf⟩)
    · refine Or.inl ⟨rfl, Or.inl ⟨rfl, Or.inl ⟨rfl, ?_⟩, Or.inl ⟨rfl, ?_⟩⟩,
        Or.inl ⟨W, rfl, ?_⟩⟩
      · intro haX
        exact hX a haX b (by rw [mem_Renaming1_event, hra])
      · intro hbX
        exact hX b hbX a (by rw [mem_Renaming1_event, hrb])
      · rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨z, ⟨hzX, hz⟩, rfl⟩, he⟩
        have hza : z ≠ a := fun h => hz (Or.inl h)
        have hzb : z ≠ b := fun h => hz (Or.inr h)
        exact hX z hzX z (by rw [mem_Renaming1_event, hrz z hza hzb]) he
    · rw [mem_Renaming1_event] at hxc
      refine Or.inr ⟨by simp, ?_⟩
      by_cases hxa : x = a
      · rw [hxa] at hxX hf
        rw [hxa, hra] at hxc
        rw [hxc]
        exact Or.inl (Or.inr ⟨by simp, Or.inl (Or.inr ⟨hxX, t', rfl, hf⟩)⟩)
      · by_cases hxb : x = b
        · rw [hxb] at hxX hf
          rw [hxb, hrb] at hxc
          rw [hxc]
          exact Or.inl (Or.inr ⟨by simp, Or.inr (Or.inr ⟨hxX, t', rfl, hf⟩)⟩)
        · rw [hrz x hxa hxb] at hxc
          rw [hxc]
          refine Or.inr (Or.inr ⟨x, t', W, rfl, hf, ⟨hxX, ?_⟩⟩)
          rintro (h | h)
          · exact hxa h
          · exact hxb h
  · rintro (⟨rfl, h12, h3⟩ | ⟨hne, hor⟩)
    · refine Or.inl ⟨rfl, ?_⟩
      rcases h12 with ⟨-, h1, h2⟩ | ⟨hne, -⟩
      · rcases h1 with ⟨-, h1⟩ | ⟨-, t1, hEq1, -⟩
        · rcases h2 with ⟨-, h2⟩ | ⟨-, t2, hEq2, -⟩
          · rcases h3 with ⟨V, hE3, h3⟩ | ⟨z, s, V, hE3, -, -⟩
            · obtain ⟨-, rfl⟩ := Prod.mk.inj hE3
              intro z hzX c hzc
              rw [mem_Renaming1_event] at hzc
              by_cases hza : z = a
              · rw [hza] at hzX
                rw [hza, hra] at hzc
                rw [hzc]
                exact h1 hzX
              · by_cases hzb : z = b
                · rw [hzb] at hzX
                  rw [hzb, hrb] at hzc
                  rw [hzc]
                  exact h2 hzX
                · rw [hrz z hza hzb] at hzc
                  rw [hzc]
                  intro hcW
                  have hm : (event.Ev z : event α) ∈ event.Ev '' (X \ ({a, b} : Set α)) ∩ W :=
                    ⟨⟨z, ⟨hzX, by simp [hza, hzb]⟩, rfl⟩, hcW⟩
                  rw [h3] at hm
                  exact hm
            · exact absurd (Prod.mk.inj hE3).1 (by simp)
          · exact absurd hEq2 (by simp)
        · exact absurd hEq1 (by simp)
      · exact absurd rfl hne
    · rcases hor with h12 | h3
      · rcases h12 with ⟨hnil, -⟩ | ⟨-, h1 | h2⟩
        · exact absurd hnil hne
        · rcases h1 with ⟨hnil, -⟩ | ⟨haX, t', rfl, hf⟩
          · exact absurd hnil hne
          · exact Or.inr ⟨a, b, t', haX, by rw [mem_Renaming1_event, hra], rfl, hf⟩
        · rcases h2 with ⟨hnil, -⟩ | ⟨hbX, t', rfl, hf⟩
          · exact absurd hnil hne
          · exact Or.inr ⟨b, a, t', hbX, by rw [mem_Renaming1_event, hrb], rfl, hf⟩
      · rcases h3 with ⟨V, hE3, -⟩ | ⟨z, s, V, hE3, hf, hz⟩
        · exact absurd (Prod.mk.inj hE3).1 hne
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE3
          have hza : z ≠ a := fun h => hz.2 (Or.inl h)
          have hzb : z ≠ b := fun h => hz.2 (Or.inr h)
          exact Or.inr ⟨z, z, s, hz.1, by rw [mem_Renaming1_event, hrz z hza hzb], rfl, hf⟩

theorem cspF_Ext_pre_choice_Renaming1_event2_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    a = b →
      eqF ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
        ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
          (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
          (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])) := by
  intro _
  exact cspF_Ext_pre_choice_Renaming1_event1_step


theorem cspF_Ext_pre_choice_Renaming1_event_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]])) := by
  exact cspF_Ext_pre_choice_Renaming1_event1_step


theorem cspF_Ext_pre_choice_Renaming2_set_event_step_in [Inhabited α]
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domFType α} :
    X ∩ A ≠ ∅ →
      eqF ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]]) := by
  intro hXA
  obtain ⟨c, hcX, hcA⟩ : ∃ c, c ∈ X ∧ c ∈ A := by
    by_contra hcon
    exact hXA (Set.eq_empty_iff_forall_notMem.mpr fun z hz => hcon ⟨z, hz.1, hz.2⟩)
  refine cspF_eqF_of_eqT (cspT_Ext_pre_choice_Renaming2_set_event_step_in hXA) ?_
  intro u W
  rw [in_failures_Renaming_Ext_pre_choice, in_failures_Ext_choice, ren_inv_disjoint_iff]
  constructor
  · rintro (⟨rfl, hX⟩ | ⟨x, b, t', hxX, hxb, rfl, hf⟩)
    · refine Or.inl ⟨⟨W, rfl⟩, ?_, ?_⟩
      · exact in_failures_Act_prefix.mpr (Or.inl ⟨W, rfl, hX c hcX a (Renaming2_pair hcA)⟩)
      · refine in_failures_Ext_pre_choice.mpr (Or.inl ⟨W, rfl, ?_⟩)
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨⟨z, ⟨hzX, hzA⟩, rfl⟩, he⟩
        exact hX z hzX z (Renaming2_pair' hzA) he
    · rw [mem_Renaming2_event] at hxb
      refine Or.inr (Or.inl ⟨Abs_trace [event.Ev b] ^^^ t', ⟨W, rfl⟩, ?_, by simp⟩)
      by_cases hxA : x ∈ A
      · have hba : b = a := by rw [hxb]; simp [Renaming2_event_fun, hxA]
        subst hba
        exact Or.inl (in_failures_Act_prefix.mpr (Or.inr ⟨t', W, rfl,
          in_failures_Rep_int_choice_com.mpr ⟨x, ⟨hxX, hxA⟩, hf⟩⟩))
      · have hbx : b = x := by rw [hxb]; simp [Renaming2_event_fun, hxA]
        subst hbx
        exact Or.inr (in_failures_Ext_pre_choice.mpr
          (Or.inr ⟨b, t', W, rfl, hf, ⟨hxX, hxA⟩⟩))
  · rintro (⟨⟨V, hEq⟩, hP, hQ⟩ | ⟨v, ⟨V, hEq⟩, hor, hne⟩ | ⟨V, hEq, hTk, -⟩)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
      refine Or.inl ⟨rfl, ?_⟩
      rcases in_failures_Act_prefix.mp hP with ⟨V1, hE1, haW⟩ | ⟨s1, V1, hE1, -⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj hE1
        rcases in_failures_Ext_pre_choice.mp hQ with ⟨V2, hE2, hXA'⟩ | ⟨z, s2, V2, hE2, -, -⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj hE2
          intro z hzX b hzb hbW
          rw [mem_Renaming2_event] at hzb
          by_cases hzA : z ∈ A
          · have hba : b = a := by rw [hzb]; simp [Renaming2_event_fun, hzA]
            exact haW (hba ▸ hbW)
          · have hbz : b = z := by rw [hzb]; simp [Renaming2_event_fun, hzA]
            subst hbz
            have hm : (event.Ev b : event α) ∈ event.Ev '' (X \ A) ∩ W :=
              ⟨⟨b, ⟨hzX, hzA⟩, rfl⟩, hbW⟩
            rw [hXA'] at hm
            exact hm
        · exact absurd (Prod.mk.inj hE2).1 (by simp)
      · exact absurd (Prod.mk.inj hE1).1 (by simp)
    · obtain ⟨rfl, -⟩ := Prod.mk.inj hEq
      rcases hor with hP | hQ
      · rcases in_failures_Act_prefix.mp hP with ⟨V1, hE1, -⟩ | ⟨s1, V1, hE1, hQf⟩
        · exact absurd (Prod.mk.inj hE1).1 hne
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
          obtain ⟨z, ⟨hzX, hzA⟩, hf⟩ := in_failures_Rep_int_choice_com.mp hQf
          exact Or.inr ⟨z, a, s1, hzX, Renaming2_pair hzA, rfl, hf⟩
      · rcases in_failures_Ext_pre_choice.mp hQ with ⟨V1, hE1, -⟩ | ⟨z, s1, V1, hE1, hf, hz⟩
        · exact absurd (Prod.mk.inj hE1).1 hne
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hE1
          exact Or.inr ⟨z, z, s1, hz.1, Renaming2_pair' hz.2, rfl, hf⟩
    · rcases hTk with hT | hT
      · rw [in_traces_Act_prefix] at hT
        rcases hT with hT | ⟨w, hw, -⟩
        · simp at hT
        · have hhd := congrArg hdt hw
          simp [hdt_appt] at hhd
      · exact absurd hT Tick_notin_traces_Ext_pre_choice

theorem cspF_Ext_pre_choice_Renaming2_set_event_step_notin
    {X A : Set α} {Pf : α → proc p α} {b : α} {M : p → domFType α} :
    X ∩ A = ∅ →
      eqF ((proc.Ext_pre_choice X Pf)[[A <<- b]]) M M
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- b]]) := by
  intro hXA
  refine Renaming_fun_Ext_pre_choice_id (g := Renaming2_event_fun A b) ?_
  intro y hyY
  have hyA : y ∉ A := by
    intro hy
    have hm : y ∈ X ∩ A := ⟨hyY, hy⟩
    rw [hXA] at hm
    exact hm
  simp [Renaming2_event_fun, hyA]

theorem cspF_Ext_pre_choice_Renaming2_set_event_step [Inhabited α]
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
      (procIte (X ∩ A ≠ ∅)
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- a]])) := by
  by_cases h : X ∩ A ≠ ∅
  · rw [procIte_pos h]
    exact cspF_Ext_pre_choice_Renaming2_set_event_step_in h
  · rw [procIte_neg h]
    exact cspF_Ext_pre_choice_Renaming2_set_event_step_notin (by simpa using h)

theorem cspF_Ext_pre_choice_Renaming2_event_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[a <-- b]]) M M
      (procIte (a ∈ X)
        ((b ~> (Pf a)[[a <-- b]]) [+]
          proc.Ext_pre_choice (X \ ({a} : Set α)) fun x => (Pf x)[[a <-- b]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[a <-- b]])) := by
  by_cases haX : a ∈ X
  · rw [procIte_pos haX]
    have hne : X ∩ ({a} : Set α) ≠ ∅ := by
      intro hEq
      exact Set.eq_empty_iff_forall_notMem.mp hEq a ⟨haX, rfl⟩
    refine cspF_trans_left_eq
      (cspF_Ext_pre_choice_Renaming2_set_event_step_in (A := ({a} : Set α)) hne) ?_
    refine cspF_Ext_choice_cong (cspF_Act_prefix_cong rfl ?_) cspF_reflex_eq_P
    refine cspF_Rep_int_choice_com_const hne ?_
    rintro z ⟨-, rfl⟩
    rfl
  · rw [procIte_neg haX]
    refine cspF_Ext_pre_choice_Renaming2_set_event_step_notin ?_
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzX, rfl⟩
    exact haX hzX

/- The Isabelle theorem bundle `cspF_Ext_pre_choice_Renaming_event_step` is
   represented by `cspF_Ext_pre_choice_Renaming1_event_step`,
   `cspF_Ext_pre_choice_Renaming2_set_event_step`, and
   `cspF_Ext_pre_choice_Renaming2_event_step`. -/

theorem cspF_Send_prefix_Renaming1_event1_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Send_prefix f v P)[[a <--> f v]]) M M (a ~> P[[a <--> f v]]) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming1_event2_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Send_prefix f v P)[[f v <--> a]]) M M (a ~> P[[f v <--> a]]) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming1_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domFType α} :
    a ≠ f v →
      b ≠ f v →
      eqF ((Send_prefix f v P)[[a <--> b]]) M M
        (Send_prefix f v (P[[a <--> b]])) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming1_event_step` is
   represented by `cspF_Send_prefix_Renaming1_event1_step_in`,
   `cspF_Send_prefix_Renaming1_event2_step_in`, and
   `cspF_Send_prefix_Renaming1_event_step_notin`. -/

theorem cspF_Send_prefix_Renaming2_set_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domFType α} :
    f v ∈ A →
      eqF ((Send_prefix f v P)[[A <<- a]]) M M (a ~> P[[A <<- a]]) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming2_set_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {b : α}
    {M : p → domFType α} :
    f v ∉ A →
      eqF ((Send_prefix f v P)[[A <<- b]]) M M
        (Send_prefix f v (P[[A <<- b]])) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming2_set_event_step
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domFType α} :
    eqF ((Send_prefix f v P)[[A <<- a]]) M M
      (procIte (f v ∈ A) (a ~> P[[A <<- a]]) (Send_prefix f v (P[[A <<- a]]))) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming2_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domFType α} :
    eqF ((Send_prefix f v P)[[f v <-- a]]) M M (a ~> P[[f v <-- a]]) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming2_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domFType α} :
    a ≠ f v →
      eqF ((Send_prefix f v P)[[a <-- b]]) M M
        (Send_prefix f v (P[[a <-- b]])) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming2_event_step` is
   represented by `cspF_Send_prefix_Renaming2_event_step_in` and
   `cspF_Send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming_event_step` is
   represented by `cspF_Send_prefix_Renaming1_event_step` and
   `cspF_Send_prefix_Renaming2_event_step`. -/

theorem cspF_Send_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((Send_prefix f v P)[[f <==> g]]) M M (Send_prefix g v (P[[f <==> g]])) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((Send_prefix f v P)[[g <==> f]]) M M (Send_prefix g v (P[[g <==> f]])) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqF ((Send_prefix h v P)[[f <==> g]]) M M
        (Send_prefix h v (P[[f <==> g]])) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming1_channel_step` is
   represented by `cspF_Send_prefix_Renaming1_channel1_step_in`,
   `cspF_Send_prefix_Renaming1_channel2_step_in`, and
   `cspF_Send_prefix_Renaming1_channel_step_notin`. -/

theorem cspF_Send_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((Send_prefix f v P)[[f <== g]]) M M (Send_prefix g v (P[[f <== g]])) := by
  cspF_auto_step_dist

theorem cspF_Send_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqF ((Send_prefix h v P)[[f <== g]]) M M
        (Send_prefix h v (P[[f <== g]])) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming2_channel_step` is
   represented by `cspF_Send_prefix_Renaming2_channel_step_in` and
   `cspF_Send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming_channel_step` is
   represented by `cspF_Send_prefix_Renaming1_channel_step` and
   `cspF_Send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming_step` is
   represented by `cspF_Send_prefix_Renaming_event_step` and
   `cspF_Send_prefix_Renaming_channel_step`. -/

theorem cspF_Rec_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqF ((Rec_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]]) := by
  cspF_auto_step_dist

theorem cspF_Rec_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqF ((Rec_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]]) := by
  cspF_auto_step_dist

theorem cspF_Rec_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      ((∀ x, x ∈ X → b ≠ f x) ∨ b ∉ f '' X) →
      eqF ((Rec_prefix f X Pf)[[a <--> b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <--> b]]) := by
  intro ha hb
  have haX : a ∉ f '' X := by
    rcases ha with ha | ha
    · rintro ⟨z, hzX, rfl⟩
      exact ha z hzX rfl
    · exact ha
  have hbX : b ∉ f '' X := by
    rcases hb with hb | hb
    · rintro ⟨z, hzX, rfl⟩
      exact hb z hzX rfl
    · exact hb
  rw [Rec_prefix_def, Rec_prefix_def]
  refine Renaming_fun_Ext_pre_choice_id (g := Renaming1_event_fun a b) ?_
  intro y hy
  have hya : y ≠ a := fun h => haX (h ▸ hy)
  have hyb : y ≠ b := fun h => hbX (h ▸ hy)
  simp [Renaming1_event_fun, hya, hyb]

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming1_event_step` is
   represented by `cspF_Rec_prefix_Renaming1_event1_step_in`,
   `cspF_Rec_prefix_Renaming1_event2_step_in`, and
   `cspF_Rec_prefix_Renaming1_event_step_notin`. -/

theorem cspF_Rec_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqF ((Rec_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
          Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]]) := by
  intro _ hex
  have hne : (f '' X) ∩ A ≠ ∅ := by
    obtain ⟨z, hzX, hzA⟩ := hex
    intro hEq
    exact Set.eq_empty_iff_forall_notMem.mp hEq (f z) ⟨⟨z, hzX, rfl⟩, hzA⟩
  rw [Rec_prefix_def, Rec_prefix_def, Rep_int_choice_f_def, image_inter_filter,
    image_diff_filter]
  exact cspF_Ext_pre_choice_Renaming2_set_event_step_in hne

theorem cspF_Rec_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {A : Set α} {b : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqF ((Rec_prefix f X Pf)[[A <<- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[A <<- b]]) := by
  intro hnot
  have hne : (f '' X) ∩ A = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨⟨z, hzX, rfl⟩, heA⟩
    rcases hnot with hnot | hnot
    · exact hnot z hzX heA
    · exact Set.eq_empty_iff_forall_notMem.mp hnot (f z) ⟨heA, ⟨z, hzX, rfl⟩⟩
  rw [Rec_prefix_def, Rec_prefix_def]
  exact cspF_Ext_pre_choice_Renaming2_set_event_step_notin hne

theorem cspF_Rec_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Rec_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
            Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Rec_prefix f X fun x => (Pf x)[[A <<- a]])) := by
  intro hinj
  by_cases hex : ∃ x, x ∈ X ∧ f x ∈ A
  · rw [procIte_pos hex]
    exact cspF_Rec_prefix_Renaming2_set_event_step_in hinj hex
  · rw [procIte_neg hex]
    refine cspF_Rec_prefix_Renaming2_set_event_step_notin (Or.inl ?_)
    intro z hzX hzA
    exact hex ⟨z, hzX, hzA⟩

theorem cspF_Rec_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      eqF ((Rec_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]]) := by
  cspF_auto_step_dist

theorem cspF_Rec_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      eqF ((Rec_prefix f X Pf)[[a <-- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <-- b]]) := by
  intro ha
  have haX : a ∉ f '' X := by
    rcases ha with ha | ha
    · rintro ⟨z, hzX, rfl⟩
      exact ha z hzX rfl
    · exact ha
  rw [Rec_prefix_def, Rec_prefix_def]
  refine Renaming_fun_Ext_pre_choice_id (g := Renaming2_event_fun ({a} : Set α) b) ?_
  intro y hy
  have hya : y ≠ a := fun h => haX (h ▸ hy)
  simp [Renaming2_event_fun, hya]

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming2_event_step` is
   represented by `cspF_Rec_prefix_Renaming2_event_step_in` and
   `cspF_Rec_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming_event_step` is
   represented by `cspF_Rec_prefix_Renaming1_event_step` and
   `cspF_Rec_prefix_Renaming2_event_step`. -/

theorem cspF_Rec_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix f X Pf)[[f <==> g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <==> g]]) := by
  cspF_auto_step_dist

theorem cspF_Rec_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix f X Pf)[[g <==> f]]) M M
        (Rec_prefix g X fun x => (Pf x)[[g <==> f]]) := by
  cspF_auto_step_dist

/- The Isabelle lemmas `Renaming_channel_fun_h` and
   `Renaming_channel_fun_map_h` are already represented in
   `LeanCspProver.CSP.Infra_ren`. -/

theorem cspF_Rec_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domFType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix h X Pf)[[f <==> g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <==> g]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming1_channel_step` is
   represented by `cspF_Rec_prefix_Renaming1_channel1_step_in`,
   `cspF_Rec_prefix_Renaming1_channel2_step_in`, and
   `cspF_Rec_prefix_Renaming1_channel_step_notin`. -/

theorem cspF_Rec_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix f X Pf)[[f <== g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <== g]]) := by
  cspF_auto_step_dist

theorem cspF_Rec_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domFType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix h X Pf)[[f <== g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <== g]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming2_channel_step` is
   represented by `cspF_Rec_prefix_Renaming2_channel_step_in` and
   `cspF_Rec_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming_channel_step` is
   represented by `cspF_Rec_prefix_Renaming1_channel_step` and
   `cspF_Rec_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming_step` is represented
   by `cspF_Rec_prefix_Renaming_event_step` and
   `cspF_Rec_prefix_Renaming_channel_step`. -/

theorem cspF_Nondet_send_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqF ((Nondet_send_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqF ((Nondet_send_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domFType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      ((∀ x, b ≠ f x) ∨ b ∉ Set.range f) →
      eqF ((Nondet_send_prefix f X Pf)[[a <--> b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <--> b]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming1_event_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_event1_step_in`,
   `cspF_Nondet_send_prefix_Renaming1_event2_step_in`, and
   `cspF_Nondet_send_prefix_Renaming1_event_step_notin`. -/

/-- The `Int_pre_choice` counterpart of
    `cspF_Ext_pre_choice_Renaming2_set_event_step_in`. -/
private theorem Int_pre_choice_Renaming2_set_event_in [Inhabited α]
    {Y A : Set α} {Qf : α → proc p α} {a : α} {M : p → domFType α} :
    Y ∩ A ≠ ∅ →
      eqF ((Int_pre_choice Y Qf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_com (Y ∩ A) fun y => (Qf y)[[A <<- a]]) |~|
          Rep_int_choice_com (Y \ A) fun y => y ~> (Qf y)[[A <<- a]]) := by
  intro hYA
  rw [Int_pre_choice_def]
  have hsplit : Y = (Y ∩ A) ∪ (Y \ A) := (Set.inter_union_diff Y A).symm
  refine cspF_trans_left_eq cspF_Renaming_Dist_com ?_
  refine cspF_trans_left_eq
    (cspF_Rep_int_choice_cong_com hsplit fun y _ => cspF_Act_prefix_Renaming_fun_step) ?_
  refine cspF_trans_left_eq cspF_Rep_int_choice_com_Un ?_
  refine cspF_Int_choice_cong ?_ ?_
  · refine cspF_trans_left_eq
      (cspF_Rep_int_choice_cong_com (X2 := Y ∩ A) rfl fun y hy => ?_)
      (cspF_sym (cspF_Act_prefix_Dist_com hYA))
    exact cspF_Act_prefix_cong (by simp [Renaming2_event_fun, hy.2]) cspF_reflex_eq_P
  · refine cspF_Rep_int_choice_cong_com rfl fun y hy => ?_
    exact cspF_Act_prefix_cong (by simp [Renaming2_event_fun, hy.2]) cspF_reflex_eq_P

theorem cspF_Nondet_send_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqF ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
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

theorem cspF_Nondet_send_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqF ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
            Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]])) := by
  intro hinj
  by_cases hex : ∃ x, x ∈ X ∧ f x ∈ A
  · rw [procIte_pos hex]
    exact cspF_Nondet_send_prefix_Renaming2_set_event_step_in hinj hex
  · rw [procIte_neg hex]
    refine cspF_Nondet_send_prefix_Renaming2_set_event_step_notin (Or.inl ?_)
    intro z hzX hzA
    exact hex ⟨z, hzX, hzA⟩

theorem cspF_Nondet_send_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqF ((Nondet_send_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domFType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      eqF ((Nondet_send_prefix f X Pf)[[a <-- b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <-- b]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming2_event_step`
   is represented by `cspF_Nondet_send_prefix_Renaming2_event_step_in` and
   `cspF_Nondet_send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming_event_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_event_step` and
   `cspF_Nondet_send_prefix_Renaming2_event_step`. -/

theorem cspF_Nondet_send_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Nondet_send_prefix f X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <==> g]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Nondet_send_prefix f X Pf)[[g <==> f]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[g <==> f]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited α] [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domFType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      eqF ((Nondet_send_prefix h X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <==> g]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming1_channel_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_channel1_step_in`,
   `cspF_Nondet_send_prefix_Renaming1_channel2_step_in`, and
   `cspF_Nondet_send_prefix_Renaming1_channel_step_notin`. -/

theorem cspF_Nondet_send_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Nondet_send_prefix f X Pf)[[f <== g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <== g]]) := by
  cspF_auto_step_dist

theorem cspF_Nondet_send_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited α] [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domFType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      eqF ((Nondet_send_prefix h X Pf)[[f <== g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <== g]]) := by
  cspF_auto_step_dist

/- The Isabelle theorem bundle
   `cspF_Nondet_send_prefix_Renaming2_channel_step` is represented by
   `cspF_Nondet_send_prefix_Renaming2_channel_step_in` and
   `cspF_Nondet_send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming_channel_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_channel_step` and
   `cspF_Nondet_send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming_step` is
   represented by `cspF_Nondet_send_prefix_Renaming_event_step` and
   `cspF_Nondet_send_prefix_Renaming_channel_step`. -/

/- The Isabelle theorem bundle `cspF_prefix_Renaming_in_step` is represented
   by the `..._step_in` theorems in this file. -/

/- The Isabelle theorem bundle `cspF_prefix_Renaming_notin_step` is
   represented by the `..._step_notin` theorems together with
   `cspF_Act_prefix_Renaming2_set_event_step`,
   `cspF_Send_prefix_Renaming2_set_event_step`,
   `cspF_Rec_prefix_Renaming2_set_event_step`,
   `cspF_Nondet_send_prefix_Renaming2_set_event_step`, and
   `cspF_Ext_pre_choice_Renaming_event_step`. -/

end
