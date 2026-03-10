           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_semantics

open SumType

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.          -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

/-
(*********************************************************
                        setF
 *********************************************************)
-/

/- --------------------------------*
 |             STOP               |
 *-------------------------------- -/

/- (*** STOP_setF ***) -/

theorem STOP_setF :
    {f : failure α | ∃ X, f = (<>, X)} ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with ⟨Z, hEq⟩
  rcases Prod.mk.inj hEq with ⟨hs, hX⟩
  subst hs
  subst hX
  exact ⟨Y, rfl⟩

/- (*** STOP ***) -/

theorem in_failures_STOP {f : failure α} {M : p → domFType α} :
    (f :f failures proc.STOP M) ↔ ∃ X, f = (<>, X) := by
  simpa [failures] using
    (CollectF_open_memF (P := fun f : failure α => ∃ X, f = (<>, X)) (f := f) STOP_setF)

/- --------------------------------*
 |             SKIP               |
 *-------------------------------- -/

/- (*** SKIP_setF ***) -/

theorem SKIP_setF :
    {f : failure α |
      (∃ X, f = (<>, X) ∧ X ⊆ Evset) ∨
        ∃ X, f = ((Abs_trace [event.Tick] : traceType α), X)} ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs
  · rcases hs with ⟨Z, hEq, hZ⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    exact Or.inl ⟨Y, rfl, Set.Subset.trans hYX hZ⟩
  · rcases hs with ⟨Z, hEq⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    exact Or.inr ⟨Y, rfl⟩

/- (*** SKIP ***) -/

theorem in_failures_SKIP {f : failure α} {M : p → domFType α} :
    (f :f failures proc.SKIP M) ↔
      ((∃ X, f = (<>, X) ∧ X ⊆ Evset) ∨
        ∃ X, f = ((Abs_trace [event.Tick] : traceType α), X)) := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        (∃ X, f = (<>, X) ∧ X ⊆ Evset) ∨
          ∃ X, f = ((Abs_trace [event.Tick] : traceType α), X))
      (f := f) SKIP_setF)

/- --------------------------------*
 |              DIV               |
 *-------------------------------- -/

/- (*** DIV ***) -/

theorem in_failures_DIV {f : failure α} {M : p → domFType α} :
    f ~:f failures proc.DIV M := by
  simp [failures]

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

/- (*** Act_prefix_setF ***) -/

theorem Act_prefix_setF {a : α} {F : setFType α} :
    {f : failure α |
      (∃ X, f = (<>, X) ∧ event.Ev a ∉ X) ∨
        ∃ s X, f = (Abs_trace [event.Ev a] ^^^ s, X) ∧ (s, X) :f F} ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs
  · rcases hs with ⟨Z, hEq, hNot⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    refine Or.inl ⟨Y, rfl, ?_⟩
    intro hEv
    exact hNot (hYX hEv)
  · rcases hs with ⟨t, Z, hEq, htZ⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    exact Or.inr ⟨t, Y, rfl, memF_F2 htZ hYX⟩

/- (*** Act_prefix ***) -/

theorem in_failures_Act_prefix {f : failure α} {a : α} {P : proc p α} {M : p → domFType α} :
    (f :f failures (a ~> P) M) ↔
      ((∃ X, f = (<>, X) ∧ event.Ev a ∉ X) ∨
        ∃ s X, f = (Abs_trace [event.Ev a] ^^^ s, X) ∧ (s, X) :f failures P M) := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        (∃ X, f = (<>, X) ∧ event.Ev a ∉ X) ∨
          ∃ s X, f = (Abs_trace [event.Ev a] ^^^ s, X) ∧ (s, X) :f failures P M)
      (f := f) (Act_prefix_setF (a := a) (F := failures P M)))

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- (*** Ext_pre_choice_setF ***) -/

theorem Ext_pre_choice_setF {X : Set α} {Ff : α → setFType α} :
    {f : failure α |
      (∃ Y, f = (<>, Y) ∧ (event.Ev '' X) ∩ Y = ∅) ∨
        ∃ a s Y, f = (Abs_trace [event.Ev a] ^^^ s, Y) ∧ (s, Y) :f Ff a ∧ a ∈ X} ∈ setF (α := α) := by
  intro s Y Z hs hZY
  rcases hs with hs | hs
  · rcases hs with ⟨Y', hEq, hEmpty⟩
    rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
    subst hsEq
    have hZY' : Z ⊆ Y' := by
      simpa [hYEq] using hZY
    refine Or.inl ⟨Z, by simpa [hYEq], ?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro e he
    have : e ∈ (event.Ev '' X) ∩ Y' := ⟨he.1, hZY' he.2⟩
    simpa [hEmpty] using this
  · rcases hs with ⟨a, t, Y', hEq, htY, haX⟩
    rcases Prod.mk.inj hEq with ⟨hs, hY⟩
    subst hs
    subst hY
    exact Or.inr ⟨a, t, Z, rfl, memF_F2 htY hZY, haX⟩

/- (*** Ext_pre_choice ***) -/

theorem in_failures_Ext_pre_choice {f : failure α} {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (f :f failures (proc.Ext_pre_choice X Pf) M) ↔
      ((∃ Y, f = (<>, Y) ∧ (event.Ev '' X) ∩ Y = ∅) ∨
        ∃ a s Y, f = (Abs_trace [event.Ev a] ^^^ s, Y) ∧
          (s, Y) :f failures (Pf a) M ∧ a ∈ X) := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        (∃ Y, f = (<>, Y) ∧ (event.Ev '' X) ∩ Y = ∅) ∨
          ∃ a s Y, f = (Abs_trace [event.Ev a] ^^^ s, Y) ∧
            (s, Y) :f failures (Pf a) M ∧ a ∈ X)
      (f := f) (Ext_pre_choice_setF (X := X) (Ff := fun a => failures (Pf a) M)))

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- (*** Ext_choice_setF ***) -/

theorem Ext_choice_setF {F E : setFType α} {T S : domTType α} :
    {f : failure α |
      ((∃ X, f = (<>, X)) ∧ f :f F ∧ f :f E) ∨
        (∃ s, (∃ X, f = (s, X)) ∧ (f :f F ∨ f :f E) ∧ s ≠ <>) ∨
        ∃ X, f = (<>, X) ∧
          ((Abs_trace [event.Tick] : traceType α) :t T ∨
            (Abs_trace [event.Tick] : traceType α) :t S) ∧
          X ⊆ Evset} ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs | hs
  · rcases hs with ⟨⟨Z, hEq⟩, hsF, hsE⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    exact Or.inl ⟨⟨Y, rfl⟩, memF_F2 hsF hYX, memF_F2 hsE hYX⟩
  · rcases hs with ⟨u, hu, hsFE, huNe⟩
    rcases hu with ⟨Z, hEq⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    refine Or.inr <| Or.inl ?_
    refine ⟨_, ⟨Y, rfl⟩, ?_, huNe⟩
    rcases hsFE with hsF | hsE
    · exact Or.inl (memF_F2 hsF hYX)
    · exact Or.inr (memF_F2 hsE hYX)
  · rcases hs with ⟨Z, hEq, hTick, hZ⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    exact Or.inr <| Or.inr ⟨Y, rfl, hTick, Set.Subset.trans hYX hZ⟩

/- (*** Ext_choice ***) -/

theorem in_failures_Ext_choice {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (P [+] Q) M) ↔
      (((∃ X, f = (<>, X)) ∧ f :f failures P M ∧ f :f failures Q M) ∨
        (∃ s, (∃ X, f = (s, X)) ∧ (f :f failures P M ∨ f :f failures Q M) ∧ s ≠ <>) ∨
        ∃ X, f = (<>, X) ∧
          ((Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M) ∨
            (Abs_trace [event.Tick] : traceType α) :t traces Q (fstF ∘ M)) ∧
          X ⊆ Evset) := by
  simpa [failures, memF, memT, setF_IntF_Rep, setF_UnF_Rep, domT_UnT_Rep] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        ((∃ X, f = (<>, X)) ∧ f :f failures P M ∧ f :f failures Q M) ∨
          (∃ s, (∃ X, f = (s, X)) ∧ (f :f failures P M ∨ f :f failures Q M) ∧ s ≠ <>) ∨
          ∃ X, f = (<>, X) ∧
            ((Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M) ∨
              (Abs_trace [event.Tick] : traceType α) :t traces Q (fstF ∘ M)) ∧
            X ⊆ Evset)
      (f := f)
      (Ext_choice_setF (F := failures P M) (E := failures Q M)
        (T := traces P (fstF ∘ M)) (S := traces Q (fstF ∘ M))))

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- (*** Int_choice ***) -/

theorem in_failures_Int_choice {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (P |~| Q) M) ↔ (f :f failures P M ∨ f :f failures Q M) := by
  simp [failures, memF, setF_UnF_Rep]

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- (*** Rep_int_choice_setF ***) -/

theorem Rep_int_choice_setF {ι : Type _} {X : Set ι} {Ff : ι → setFType α} :
    {f : failure α | ∃ a, a ∈ X ∧ f :f Ff a} ∈ setF (α := α) := by
  intro s Y Z hs hZY
  rcases hs with ⟨a, haX, hsY⟩
  exact ⟨a, haX, memF_F2 hsY hZY⟩

/- (*** Union_proc ***) -/

theorem in_failures_Union_proc {ι : Type _} {f : failure α} {X : Set ι} {Ff : ι → setFType α} :
    f :f CollectF (fun f : failure α => ∃ a, a ∈ X ∧ f :f Ff a) ↔
      ∃ a, a ∈ X ∧ f :f Ff a := by
  simpa using
    (CollectF_open_memF
      (P := fun f : failure α => ∃ a, a ∈ X ∧ f :f Ff a)
      (f := f) (Rep_int_choice_setF (X := X) (Ff := Ff)))

theorem in_failures_UNIV_Union_proc {ι : Type _} {f : failure α} {Ff : ι → setFType α} :
    f :f CollectF (fun f : failure α => ∃ a, f :f Ff a) ↔ ∃ a, f :f Ff a := by
  simpa using
    (in_failures_Union_proc (f := f) (X := (Set.univ : Set ι)) (Ff := Ff))

/- (*** Rep_int_choice ***) -/

theorem in_failures_Rep_int_choice_sum {f : failure α}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (f :f failures (proc.Rep_int_choice C Pf) M) ↔
      ∃ c, c ∈ sumset C ∧ f :f failures (Pf c) M := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α => ∃ c, c ∈ sumset C ∧ f :f failures (Pf c) M)
      (f := f) (Rep_int_choice_setF (X := sumset C) (Ff := fun c => failures (Pf c) M)))

theorem in_failures_Rep_int_choice_nat {f : failure α}
    {N : Set Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    (f :f failures (Rep_int_choice_nat N Pf) M) ↔
      ∃ n, n ∈ N ∧ f :f failures (Pf n) M := by
  simpa [Rep_int_choice_failures_nat] using
    (in_failures_Union_proc (f := f) (X := N) (Ff := fun n => failures (Pf n) M))

theorem in_failures_Rep_int_choice_set {f : failure α}
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {M : p → domFType α} :
    (f :f failures (Rep_int_choice_set Xs Pf) M) ↔
      ∃ X, X ∈ Xs ∧ f :f failures (Pf X) M := by
  simpa [Rep_int_choice_failures_set] using
    (in_failures_Union_proc (f := f) (X := Xs) (Ff := fun X => failures (Pf X) M))

theorem in_failures_Rep_int_choice_com [Inhabited α] {f : failure α}
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (f :f failures (Rep_int_choice_com X Pf) M) ↔
      ∃ a, a ∈ X ∧ f :f failures (Pf a) M := by
  simpa [Rep_int_choice_failures_com] using
    (in_failures_Union_proc (f := f) (X := X) (Ff := fun a => failures (Pf a) M))

theorem in_failures_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : failure α}
    {g : β → α} (hg : Function.Injective g) {X : Set β} {Pf : β → proc p α} {M : p → domFType α} :
    (f :f failures (Rep_int_choice_f g X Pf) M) ↔
      ∃ a, a ∈ X ∧ f :f failures (Pf a) M := by
  simpa [Rep_int_choice_failures_f hg] using
    (in_failures_Union_proc (f := f) (X := X) (Ff := fun a => failures (Pf a) M))

/- The Isabelle theorem bundle `in_failures_Rep_int_choice` is represented by
   `in_failures_Rep_int_choice_sum`, `in_failures_Rep_int_choice_nat`,
   `in_failures_Rep_int_choice_set`, `in_failures_Rep_int_choice_com`,
   and `in_failures_Rep_int_choice_f`. -/

/- --------------------------------*
 |               IF               |
 *-------------------------------- -/

/- (*** IF ***) -/

theorem in_failures_IF {f : failure α} {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (IF b THEN P ELSE Q) M) ↔
      if b then f :f failures P M else f :f failures Q M := by
  by_cases hb : b <;> simp [hb, failures]

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** Parallel_setF ***) -/

theorem Parallel_setF {X : Set α} {F E : setFType α} :
    {f : failure α |
      ∃ u Y Z, f = (u, Y ∪ Z) ∧
        Y \ ((event.Ev '' X) ∪ {event.Tick}) = Z \ ((event.Ev '' X) ∪ {event.Tick}) ∧
        ∃ s t, u ∈ par_tr s X t ∧ (s, Y) :f F ∧ (t, Z) :f E} ∈ setF (α := α) := by
  intro v W W' hs hW'
  rcases hs with ⟨u, Y, Z, hEq, hYZ, s, t, hu, hsY, htZ⟩
  rcases Prod.mk.inj hEq with ⟨hv, hW⟩
  subst hv
  subst hW
  have hUnion : W' = (Y ∩ W') ∪ (Z ∩ W') := by
    ext e
    constructor
    · intro he
      have hYZ' : e ∈ Y ∪ Z := hW' he
      rcases hYZ' with hY | hZ
      · exact Or.inl ⟨hY, he⟩
      · exact Or.inr ⟨hZ, he⟩
    · intro he
      exact he.elim (fun h => h.2) (fun h => h.2)
  have hPair : (v, W') = (v, (Y ∩ W') ∪ (Z ∩ W')) :=
    congrArg (fun S => (v, S)) hUnion
  refine ⟨v, Y ∩ W', Z ∩ W', hPair, ?_, s, t, hu, ?_, ?_⟩
  · ext e
    constructor
    · intro he
      have hLeft : e ∈ Y \ ((event.Ev '' X) ∪ {event.Tick}) := ⟨he.1.1, he.2⟩
      have hRight : e ∈ Z \ ((event.Ev '' X) ∪ {event.Tick}) := hYZ ▸ hLeft
      exact ⟨⟨hRight.1, he.1.2⟩, hRight.2⟩
    · intro he
      have hLeft : e ∈ Z \ ((event.Ev '' X) ∪ {event.Tick}) := ⟨he.1.1, he.2⟩
      have hRight : e ∈ Y \ ((event.Ev '' X) ∪ {event.Tick}) := hYZ.symm ▸ hLeft
      exact ⟨⟨hRight.1, he.1.2⟩, hRight.2⟩
  · exact memF_F2 hsY (by intro e he; exact he.1)
  · exact memF_F2 htZ (by intro e he; exact he.1)

theorem in_failures_Parallel {f : failure α} {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (f :f failures (P |[X]| Q) M) ↔
      ∃ u Y Z, f = (u, Y ∪ Z) ∧
        Y \ ((event.Ev '' X) ∪ {event.Tick}) = Z \ ((event.Ev '' X) ∪ {event.Tick}) ∧
        ∃ s t, u ∈ par_tr s X t ∧ (s, Y) :f failures P M ∧ (t, Z) :f failures Q M := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        ∃ u Y Z, f = (u, Y ∪ Z) ∧
          Y \ ((event.Ev '' X) ∪ {event.Tick}) = Z \ ((event.Ev '' X) ∪ {event.Tick}) ∧
          ∃ s t, u ∈ par_tr s X t ∧ (s, Y) :f failures P M ∧ (t, Z) :f failures Q M)
      (f := f) (Parallel_setF (X := X) (F := failures P M) (E := failures Q M)))

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- (*** Hiding_setF ***) -/

theorem Hiding_setF {X : Set α} {F : setFType α} :
    {f : failure α | ∃ s Y, f = (hide_tr s X, Y) ∧ (s, (event.Ev '' X) ∪ Y) :f F} ∈ setF (α := α) := by
  intro t Y Z hs hZY
  rcases hs with ⟨s, Y', hEq, hsY⟩
  rcases Prod.mk.inj hEq with ⟨ht, hY⟩
  subst ht
  subst hY
  refine ⟨s, Z, rfl, memF_F2 hsY ?_⟩
  intro e he
  rcases he with he | he
  · exact Or.inl he
  · exact Or.inr (hZY he)

/- (*** Hiding ***) -/

theorem in_failures_Hiding {f : failure α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    (f :f failures (proc.Hiding P X) M) ↔
      ∃ s Y, f = (hide_tr s X, Y) ∧ (s, (event.Ev '' X) ∪ Y) :f failures P M := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        ∃ s Y, f = (hide_tr s X, Y) ∧ (s, (event.Ev '' X) ∪ Y) :f failures P M)
      (f := f) (Hiding_setF (X := X) (F := failures P M)))

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** Renaming_setF ***) -/

theorem Renaming_setF {r : Set (α × β)} {F : setFType α} :
    {f : failure β | ∃ s t X, f = (t, X) ∧ ren_tr s r t ∧ (s, ren_inv r X) :f F} ∈ setF (α := β) := by
  intro t X Y hs hYX
  rcases hs with ⟨s, t', X', hEq, hRen, hsX⟩
  rcases Prod.mk.inj hEq with ⟨ht, hX⟩
  subst ht
  subst hX
  refine ⟨s, _, Y, rfl, hRen, memF_F2 hsX ?_⟩
  exact ren_inv_sub hYX

/- (*** Renaming ***) -/

theorem in_failures_Renaming {f : failure α} {P : proc p α}
    {r : Set (α × α)} {M : p → domFType α} :
    (f :f failures (P[[r]]) M) ↔
      ∃ s t X, f = (t, X) ∧ ren_tr s r t ∧ (s, ren_inv r X) :f failures P M := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        ∃ s t X, f = (t, X) ∧ s [[r]]* t ∧ (s, [[r]]inv X) :f failures P M)
      (f := f) (Renaming_setF (r := r) (F := failures P M)))

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** Seq_compo_setF ***) -/

theorem Seq_compo_setF {F E : setFType α} {T : domTType α} :
    {f : failure α |
      (∃ t X, f = (t, X) ∧ (t, X ∪ {event.Tick}) :f F ∧ noTick t) ∨
        ∃ s t X, f = (s ^^^ t, X) ∧
          (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t T ∧
          (t, X) :f E ∧ noTick s} ∈ setF (α := α) := by
  intro u X Y hs hYX
  rcases hs with hs | hs
  · rcases hs with ⟨u, X', hEq, huX, hNo⟩
    rcases Prod.mk.inj hEq with ⟨hu, hX⟩
    subst hu
    subst hX
    refine Or.inl ⟨_, Y, rfl, memF_F2 huX ?_, hNo⟩
    intro e he
    rcases he with he | he
    · exact Or.inl (hYX he)
    · exact Or.inr he
  · rcases hs with ⟨s, u, X', hEq, hTick, huX, hNo⟩
    rcases Prod.mk.inj hEq with ⟨hu, hX⟩
    subst hu
    subst hX
    exact Or.inr ⟨s, u, Y, rfl, hTick, memF_F2 huX hYX, hNo⟩

/- (*** Seq_compo ***) -/

theorem in_failures_Seq_compo {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (P ;; Q) M) ↔
      ((∃ t X, f = (t, X) ∧ (t, X ∪ {event.Tick}) :f failures P M ∧ noTick t) ∨
        ∃ s t X, f = (s ^^^ t, X) ∧
          (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) ∧
          (t, X) :f failures Q M ∧ noTick s) := by
  simpa [failures] using
    (CollectF_open_memF
      (P := fun f : failure α =>
        (∃ t X, f = (t, X) ∧ (t, X ∪ {event.Tick}) :f failures P M ∧ noTick t) ∨
          ∃ s t X, f = (s ^^^ t, X) ∧
            (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) ∧
            (t, X) :f failures Q M ∧ noTick s)
      (f := f)
      (Seq_compo_setF (F := failures P M) (E := failures Q M) (T := traces P (fstF ∘ M))))

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** Depth_rest ***) -/

theorem in_failures_Depth_rest {f : failure α} {P : proc p α} {n : Nat} {M : p → domFType α} :
    (f :f failures (P |. n) M) ↔
      (∃ t, ∃ X, f = (t, X) ∧ (t, X) :f failures P M ∧
        (LT.lt (lengtht t) n ∨
          (lengtht t = n ∧ Exists fun s : traceType α =>
            t = s ^^^ tickTrace (α := α) ∧ noTick s))) := by
  rcases f with ⟨t, X⟩
  simpa [failures, restCond, tickTrace] using
    (in_rest_setF (F := failures P M) (s := t) (X := X) (n := n))

/- --------------------------------*
 |          Proc_name             |
 *-------------------------------- -/

/- (*** Proc_name ***) -/

theorem in_failures_Proc_name {f : failure α} {pn : p} {M : p → domFType α} :
    (f :f failures (proc.Proc_name pn) M) ↔ (f :f sndF (M pn)) := by
  simp [failures]

/- The Isabelle theorem bundle `failures_setF` is represented by
   `STOP_setF`, `SKIP_setF`, `Act_prefix_setF`, `Ext_pre_choice_setF`,
   `Ext_choice_setF`, `Rep_int_choice_setF`, `Parallel_setF`,
   `Hiding_setF`, `Renaming_setF`, and `Seq_compo_setF`. -/

/- The Isabelle theorem bundle `in_failures` is represented by
   `in_failures_STOP`, `in_failures_SKIP`, `in_failures_DIV`,
   `in_failures_Act_prefix`, `in_failures_Ext_pre_choice`,
   `in_failures_Ext_choice`, `in_failures_Int_choice`,
   `in_failures_Rep_int_choice_sum`, `in_failures_Rep_int_choice_nat`,
   `in_failures_Rep_int_choice_set`, `in_failures_Rep_int_choice_com`,
   `in_failures_Rep_int_choice_f`, `in_failures_IF`,
   `in_failures_Parallel`, `in_failures_Hiding`, `in_failures_Renaming`,
   `in_failures_Seq_compo`, `in_failures_Union_proc`,
   `in_failures_UNIV_Union_proc`, `in_failures_Depth_rest`,
   and `in_failures_Proc_name`. -/

end
