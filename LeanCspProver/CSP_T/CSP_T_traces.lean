           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               December 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_semantics

open SumType

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.          -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

/-
(*********************************************************
                        DomT
 *********************************************************)
-/

/- --------------------------------*
 |             STOP               |
 *-------------------------------- -/

theorem in_traces_STOP {t : traceType α} {M : p → domTType α} :
    (t :t traces proc.STOP M) ↔ t = <> := by
  simp [traces]

/- --------------------------------*
 |             SKIP               |
 *-------------------------------- -/

theorem in_traces_SKIP {t : traceType α} {M : p → domTType α} :
    (t :t traces proc.SKIP M) ↔
      (t = <> ∨ t = (Abs_trace [event.Tick] : traceType α)) := by
  simpa [traces] using (memT_nilt_one (t := t) (a := event.Tick))

/- --------------------------------*
 |              DIV               |
 *-------------------------------- -/

/- (*** DIV ***) -/

theorem in_traces_DIV {t : traceType α} {M : p → domTType α} :
    (t :t traces proc.DIV M) ↔ t = <> := by
  simp [traces]

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

/- (*** Act_prefix_domT ***) -/

theorem Act_prefix_domT {a : α} {T : domTType α} :
    {t : traceType α |
      t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t T} ∈ domT (α := α) := by
  change HC_T1 {t : traceType α | t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t T}
  constructor
  · intro hEmpty
    have hNil :
        (<> : traceType α) ∈
          {t : traceType α | t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t T} := by
      simp
    have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
      rwa [hEmpty] at hNil
    simp at hNil'
  · intro u t h
    rcases h with ⟨ht, hp⟩
    rcases ht with rfl | ⟨s, rfl, hsT⟩
    · simp [prefix_of_nil.mp hp]
    · rcases (prefix_same_head_inv (a := a) (v := u) (u := s)).1 hp with hu | ⟨u', hu, hp'⟩
      · simp [hu]
      · exact Or.inr ⟨u', hu, memT_prefix_closed hsT hp'⟩

/- (*** Act_prefix ***) -/

theorem in_traces_Act_prefix {t : traceType α} {a : α} {P : proc p α} {M : p → domTType α} :
    (t :t traces (a ~> P) M) ↔
      (t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t traces P M) := by
  simpa [traces] using
    (CollectT_open_memT
      (P := fun t : traceType α => t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t traces P M)
      (t := t) (Act_prefix_domT (a := a) (T := traces P M)))

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- (*** Ext_pre_choice_domT ***) -/

theorem Ext_pre_choice_domT {X : Set α} {Tf : α → domTType α} :
    {t : traceType α |
      t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t Tf a ∧ a ∈ X} ∈ domT (α := α) := by
  change HC_T1 {t : traceType α |
    t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t Tf a ∧ a ∈ X}
  constructor
  · intro hEmpty
    have hNil :
        (<> : traceType α) ∈
          {t : traceType α |
            t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t Tf a ∧ a ∈ X} := by
      simp
    have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
      rwa [hEmpty] at hNil
    simp at hNil'
  · intro u t h
    rcases h with ⟨ht, hp⟩
    rcases ht with rfl | ⟨a, s, rfl, hsT, haX⟩
    · simp [prefix_of_nil.mp hp]
    · rcases (prefix_same_head_inv (a := a) (v := u) (u := s)).1 hp with hu | ⟨u', hu, hp'⟩
      · simp [hu]
      · exact Or.inr ⟨a, u', hu, memT_prefix_closed hsT hp', haX⟩

/- (*** Ext_pre_choice ***) -/

theorem in_traces_Ext_pre_choice
    {t : traceType α} {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    (t :t traces (proc.Ext_pre_choice X Pf) M) ↔
      (t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t traces (Pf a) M ∧ a ∈ X) := by
  simpa [traces] using
    (CollectT_open_memT
      (P := fun t : traceType α =>
        t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t traces (Pf a) M ∧ a ∈ X)
      (t := t) (Ext_pre_choice_domT (X := X) (Tf := fun a => traces (Pf a) M)))

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- (*** Ext_choice_memT ***) -/

theorem in_traces_Ext_choice {t : traceType α} {P Q : proc p α} {M : p → domTType α} :
    (t :t traces (P [+] Q) M) ↔ (t :t traces P M ∨ t :t traces Q M) := by
  simp [traces, memT, domT_UnT_Rep]

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- (*** Int_choice_memT ***) -/

theorem in_traces_Int_choice {t : traceType α} {P Q : proc p α} {M : p → domTType α} :
    (t :t traces (P |~| Q) M) ↔ (t :t traces P M ∨ t :t traces Q M) := by
  simp [traces, memT, domT_UnT_Rep]

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- (*** Rep_int_choice_domT ***) -/

theorem Rep_int_choice_domT {ι : Type _} {X : Set ι} {Tf : ι → domTType α} :
    {t : traceType α | t = <> ∨ ∃ a, a ∈ X ∧ t :t Tf a} ∈ domT (α := α) := by
  change HC_T1 {t : traceType α | t = <> ∨ ∃ a, a ∈ X ∧ t :t Tf a}
  constructor
  · intro hEmpty
    have hNil : (<> : traceType α) ∈ {t : traceType α | t = <> ∨ ∃ a, a ∈ X ∧ t :t Tf a} := by
      simp
    have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
      rwa [hEmpty] at hNil
    simp at hNil'
  · intro u t h
    rcases h with ⟨ht, hp⟩
    rcases ht with rfl | ⟨a, haX, htT⟩
    · simp [prefix_of_nil.mp hp]
    · by_cases hu : u = <>
      · simp [hu]
      · exact Or.inr ⟨a, haX, memT_prefix_closed htT hp⟩

/- (*** Union_proc ***) -/

theorem in_traces_Union_proc {ι : Type _} {t : traceType α} {X : Set ι} {Tf : ι → domTType α} :
    (t :t CollectT (fun t : traceType α => t = <> ∨ ∃ a, a ∈ X ∧ t :t Tf a)) ↔
      (t = <> ∨ ∃ a, a ∈ X ∧ t :t Tf a) := by
  simpa using
    (CollectT_open_memT
      (P := fun t : traceType α => t = <> ∨ ∃ a, a ∈ X ∧ t :t Tf a)
      (t := t) (Rep_int_choice_domT (X := X) (Tf := Tf)))

theorem in_traces_UNIV_Union_proc [Inhabited ι] {t : traceType α} {Tf : ι → domTType α} :
    (t :t CollectT (fun t : traceType α => ∃ a, t :t Tf a)) ↔ ∃ a, t :t Tf a := by
  have hdom : {t : traceType α | ∃ a, t :t Tf a} ∈ domT (α := α) := by
    change HC_T1 {t : traceType α | ∃ a, t :t Tf a}
    constructor
    · intro hEmpty
      have hNil : (<> : traceType α) ∈ {t : traceType α | ∃ a, t :t Tf a} := by
        exact ⟨default, nilt_in_T⟩
      have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
        rwa [hEmpty] at hNil
      simp at hNil'
    · intro s t h
      rcases h with ⟨⟨a, htT⟩, hp⟩
      exact ⟨a, memT_prefix_closed htT hp⟩
  simpa using
    (CollectT_open_memT (P := fun t : traceType α => ∃ a, t :t Tf a) (t := t) hdom)

/- (*** Rep_int_choice ***) -/

theorem in_traces_Rep_int_choice_sum
    {t : traceType α} {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domTType α} :
    (t :t traces (proc.Rep_int_choice C Pf) M) ↔
      (t = <> ∨ ∃ c, c ∈ sumset C ∧ t :t traces (Pf c) M) := by
  simpa [traces] using
    (in_traces_Union_proc (t := t) (X := sumset C) (Tf := fun c => traces (Pf c) M))

theorem in_traces_Rep_int_choice_nat
    {t : traceType α} {N : Set Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    (t :t traces (Rep_int_choice_nat N Pf) M) ↔
      (t = <> ∨ ∃ n, n ∈ N ∧ t :t traces (Pf n) M) := by
  simpa [Rep_int_choice_traces_nat] using
    (in_traces_Union_proc (t := t) (X := N) (Tf := fun n => traces (Pf n) M))

theorem in_traces_Rep_int_choice_set
    {t : traceType α} {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domTType α} :
    (t :t traces (Rep_int_choice_set Xs Pf) M) ↔
      (t = <> ∨ ∃ X, X ∈ Xs ∧ t :t traces (Pf X) M) := by
  simpa [Rep_int_choice_traces_set] using
    (in_traces_Union_proc (t := t) (X := Xs) (Tf := fun X => traces (Pf X) M))

theorem in_traces_Rep_int_choice_com [Inhabited α]
    {t : traceType α} {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    (t :t traces (Rep_int_choice_com X Pf) M) ↔
      (t = <> ∨ ∃ a, a ∈ X ∧ t :t traces (Pf a) M) := by
  simpa [Rep_int_choice_traces_com] using
    (in_traces_Union_proc (t := t) (X := X) (Tf := fun a => traces (Pf a) M))

theorem in_traces_Rep_int_choice_f [Inhabited α] [Inhabited β]
    {t : traceType α} {f : β → α} (hf : Function.Injective f)
    {X : Set β} {Pf : β → proc p α} {M : p → domTType α} :
    (t :t traces (Rep_int_choice_f f X Pf) M) ↔
      (t = <> ∨ ∃ a, a ∈ X ∧ t :t traces (Pf a) M) := by
  simpa [Rep_int_choice_traces_f hf] using
    (in_traces_Union_proc (t := t) (X := X) (Tf := fun a => traces (Pf a) M))

/- The Isabelle theorem bundle `in_traces_Rep_int_choice` is represented by
   `in_traces_Rep_int_choice_sum`, `in_traces_Rep_int_choice_set`,
   `in_traces_Rep_int_choice_nat`, `in_traces_Rep_int_choice_com`,
   and `in_traces_Rep_int_choice_f`. -/

/- --------------------------------*
 |               IF               |
 *-------------------------------- -/

/- (*** IF ***) -/

theorem in_traces_IF {t : traceType α} {b : Bool} {P Q : proc p α} {M : p → domTType α} :
    (t :t traces (IF b THEN P ELSE Q) M) ↔
      (if b then t :t traces P M else t :t traces Q M) := by
  by_cases hb : b <;> simp [traces, hb]

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** Parallel_domT ***) -/

theorem Parallel_domT {X : Set α} {T S : domTType α} :
    {u : traceType α | ∃ s t, u ∈ s |[X]|tr t ∧ s :t T ∧ t :t S} ∈ domT (α := α) := by
  change HC_T1 {u : traceType α | ∃ s t, u ∈ s |[X]|tr t ∧ s :t T ∧ t :t S}
  constructor
  · intro hEmpty
    have hNil :
        (<> : traceType α) ∈ {u : traceType α | ∃ s t, u ∈ s |[X]|tr t ∧ s :t T ∧ t :t S} := by
      exact ⟨<>, <>, par_tr_nil_nil, nilt_in_T, nilt_in_T⟩
    have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
      rwa [hEmpty] at hNil
    simp at hNil'
  · intro v u h
    rcases h with ⟨⟨s, t, hu, hsT, htS⟩, hp⟩
    rcases par_tr_prefix hp hu with ⟨s', t', hv, hs', ht'⟩
    exact ⟨s', t', hv, memT_prefix_closed hsT hs', memT_prefix_closed htS ht'⟩

/- (*** Parallel ***) -/

theorem in_traces_Parallel {u : traceType α} {P Q : proc p α} {X : Set α} {M : p → domTType α} :
    (u :t traces (P |[X]| Q) M) ↔
      ∃ s t, u ∈ s |[X]|tr t ∧ s :t traces P M ∧ t :t traces Q M := by
  simpa [traces] using
    (CollectT_open_memT
      (P := fun u : traceType α =>
        ∃ s t, u ∈ s |[X]|tr t ∧ s :t traces P M ∧ t :t traces Q M)
      (t := u) (Parallel_domT (X := X) (T := traces P M) (S := traces Q M)))

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- (*** Hiding_domT ***) -/

theorem Hiding_domT {X : Set α} {T : domTType α} :
    {t : traceType α | ∃ s, t = hide_tr s X ∧ s :t T} ∈ domT (α := α) := by
  change HC_T1 {t : traceType α | ∃ s, t = hide_tr s X ∧ s :t T}
  constructor
  · intro hEmpty
    have hNil : (<> : traceType α) ∈ {t : traceType α | ∃ s, t = hide_tr s X ∧ s :t T} := by
      exact ⟨<>, by simp, nilt_in_T⟩
    have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
      rwa [hEmpty] at hNil
    simp at hNil'
  · intro u t h
    rcases h with ⟨⟨s, rfl, hsT⟩, hp⟩
    rcases (hide_tr_prefix.mp hp) with ⟨t', hu, hp'⟩
    exact ⟨t', hu, memT_prefix_closed hsT hp'⟩

/- (*** Hiding ***) -/

theorem in_traces_Hiding {t : traceType α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    (t :t traces (proc.Hiding P X) M) ↔ ∃ s, t = hide_tr s X ∧ s :t traces P M := by
  simpa [traces] using
    (CollectT_open_memT
      (P := fun t : traceType α => ∃ s, t = hide_tr s X ∧ s :t traces P M)
      (t := t) (Hiding_domT (X := X) (T := traces P M)))

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** Renaming_domT ***) -/

theorem Renaming_domT {r : Set (α × α)} {T : domTType α} :
    {t : traceType α | ∃ s, s [[r]]* t ∧ s :t T} ∈ domT (α := α) := by
  change HC_T1 {t : traceType α | ∃ s, s [[r]]* t ∧ s :t T}
  constructor
  · intro hEmpty
    have hNil : (<> : traceType α) ∈ {t : traceType α | ∃ s, s [[r]]* t ∧ s :t T} := by
      exact ⟨<>, ren_tr_nil, nilt_in_T⟩
    have hNil' : (<> : traceType α) ∈ (∅ : Set (traceType α)) := by
      rwa [hEmpty] at hNil
    simp at hNil'
  · intro u t h
    rcases h with ⟨⟨s, hs, hsT⟩, hp⟩
    rcases ren_tr_prefix hp hs with ⟨t', hp', ht'⟩
    exact ⟨t', ht', memT_prefix_closed hsT hp'⟩

/- (*** Renaming ***) -/

theorem in_traces_Renaming {t : traceType α} {P : proc p α} {r : Set (α × α)} {M : p → domTType α} :
    (t :t traces (P[[r]]) M) ↔ ∃ s, s [[r]]* t ∧ s :t traces P M := by
  simpa [traces] using
    (CollectT_open_memT
      (P := fun t : traceType α => ∃ s, s [[r]]* t ∧ s :t traces P M)
      (t := t) (Renaming_domT (r := r) (T := traces P M)))

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** Seq_compo_domT ***) -/

axiom Seq_compo_domT {S T : domTType α} :
    {u : traceType α |
      (∃ s, u = rmTick s ∧ s :t S) ∨
        ∃ s t, u = s ^^^ t ∧
          s ^^^ (Abs_trace [event.Tick] : traceType α) :t S ∧ t :t T ∧ noTick s} ∈ domT (α := α)

/- (*** Seq_compo ***) -/

theorem in_traces_Seq_compo {u : traceType α} {P Q : proc p α} {M : p → domTType α} :
    (u :t traces (P ;; Q) M) ↔
      ((∃ s, u = rmTick s ∧ s :t traces P M) ∨
        ∃ s t, u = s ^^^ t ∧
          s ^^^ (Abs_trace [event.Tick] : traceType α) :t traces P M ∧
          t :t traces Q M ∧ noTick s) := by
  simpa [traces] using
    (CollectT_open_memT
      (P := fun u : traceType α =>
        (∃ s, u = rmTick s ∧ s :t traces P M) ∨
          ∃ s t, u = s ^^^ t ∧
            s ^^^ (Abs_trace [event.Tick] : traceType α) :t traces P M ∧
            t :t traces Q M ∧ noTick s)
      (t := u) (Seq_compo_domT (S := traces P M) (T := traces Q M)))

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** Depth_rest ***) -/

theorem in_traces_Depth_rest {t : traceType α} {P : proc p α} {n : Nat} {M : p → domTType α} :
    (t :t traces (P |. n) M) ↔ (t :t traces P M ∧ lengtht t ≤ n) := by
  simpa [traces] using (in_rest_domT (s := t) (T := traces P M) (n := n))

/- --------------------------------*
 |          Proc_name             |
 *-------------------------------- -/

/- (*** Proc_name ***) -/

theorem in_traces_Proc_name {t : traceType α} {p0 : p} {M : p → domTType α} :
    (t :t traces (proc.Proc_name p0) M) ↔ t :t M p0 := by
  simp [traces]

/- --------------------------------*
 |             alias              |
 *-------------------------------- -/

/- The Isabelle theorem bundle `traces_domT` is represented by
   `Act_prefix_domT`, `Ext_pre_choice_domT`, `Rep_int_choice_domT`,
   `Parallel_domT`, `Hiding_domT`, `Renaming_domT`, and `Seq_compo_domT`. -/

/- The Isabelle theorem bundle `in_traces` is represented by
   `in_traces_STOP`, `in_traces_SKIP`, `in_traces_DIV`,
   `in_traces_Act_prefix`, `in_traces_Ext_pre_choice`,
   `in_traces_Ext_choice`, `in_traces_Int_choice`,
   `in_traces_Rep_int_choice_sum`, `in_traces_Rep_int_choice_set`,
   `in_traces_Rep_int_choice_nat`, `in_traces_Rep_int_choice_com`,
   `in_traces_Rep_int_choice_f`, `in_traces_IF`,
   `in_traces_Parallel`, `in_traces_Hiding`,
   `in_traces_Renaming`, `in_traces_Seq_compo`,
   `in_traces_Union_proc`, `in_traces_UNIV_Union_proc`,
   `in_traces_Depth_rest`, and `in_traces_Proc_name`. -/

/- --------------------------------*
 |            Timeout             |
 *-------------------------------- -/

/- (*** Timemout ***) -/

theorem in_traces_Timeout1 {t : traceType α} {P Q : proc p α} {M : p → domTType α} :
    (t :t traces (P [> Q) M) ↔ (t :t traces P M ∨ t :t traces Q M) := by
  constructor
  · intro ht
    rcases (in_traces_Ext_choice (t := t) (P := P |~| proc.STOP) (Q := Q) (M := M)).1 ht with h | h
    · rcases (in_traces_Int_choice (t := t) (P := P) (Q := proc.STOP) (M := M)).1 h with hP | hSTOP
      · exact Or.inl hP
      · left
        rcases (in_traces_STOP (t := t) (M := M)).1 hSTOP with rfl
        exact nilt_in_T
    · exact Or.inr h
  · intro ht
    rcases ht with hP | hQ
    · exact
        (in_traces_Ext_choice (t := t) (P := P |~| proc.STOP) (Q := Q) (M := M)).2 <|
          Or.inl <|
            (in_traces_Int_choice (t := t) (P := P) (Q := proc.STOP) (M := M)).2 <| Or.inl hP
    · exact
        (in_traces_Ext_choice (t := t) (P := P |~| proc.STOP) (Q := Q) (M := M)).2 <|
          Or.inr hQ

theorem in_traces_Timeout2 {t : traceType α} {P Q : proc p α} {M : p → domTType α} :
    (t :t traces (Timeout P Q) M) ↔ (t :t traces P M ∨ t :t traces Q M) := by
  simpa [Timeout_def] using (in_traces_Timeout1 (t := t) (P := P) (Q := Q) (M := M))

/- The Isabelle theorem bundle `in_traces_Timeout` is represented by
   `in_traces_Timeout1` and `in_traces_Timeout2`. -/

end
