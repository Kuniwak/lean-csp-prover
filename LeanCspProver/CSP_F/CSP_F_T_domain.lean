           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                 August 2007               |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain

noncomputable section

/- =======================================================*
                 make 'a domF from 'a domT
     (this theory is not important and can be removed)
 *======================================================= -/

private abbrev Tickt : traceType α := (Abs_trace [event.Tick] : traceType α)

def traces_to_failures (T : domTType α) : setFType α :=
  Abs_setF
    {f : failure α |
      (∃ s, (∃ X, f = (s ^^^ Tickt (α := α), X)) ∧ (s ^^^ Tickt (α := α)) :t T) ∨
        ∃ s X, f = (s, X) ∧ noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset}

theorem traces_to_failures_def {T : domTType α} :
    traces_to_failures T =
      Abs_setF
        {f : failure α |
          (∃ s, (∃ X, f = (s ^^^ Tickt (α := α), X)) ∧ (s ^^^ Tickt (α := α)) :t T) ∨
            ∃ s X, f = (s, X) ∧ noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset} :=
  rfl

/- (*********************************************************
                        setF
 *********************************************************) -/

/- F2 -/

theorem traces_to_failures_in_setF {T : domTType α} :
    {f : failure α |
      (∃ s, (∃ X, f = (s ^^^ Tickt (α := α), X)) ∧ (s ^^^ Tickt (α := α)) :t T) ∨
        ∃ s X, f = (s, X) ∧ noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset} ∈
      setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs
  · rcases hs with ⟨t, ⟨Z, hEq⟩, htT⟩
    rcases Prod.mk.inj hEq with ⟨hsEq, _⟩
    refine Or.inl ⟨t, ⟨Y, ?_⟩, ?_⟩
    · cases hsEq
      rfl
    · cases hsEq
      exact htT
  · rcases hs with ⟨t, Z, hEq, htNo, htT, hZ⟩
    rcases Prod.mk.inj hEq with ⟨hsEq, hXEq⟩
    have hX : X ⊆ Evset := by
      cases hXEq
      exact hZ
    refine Or.inr ⟨t, Y, ?_, ?_, ?_, Set.Subset.trans hYX hX⟩
    · cases hsEq
      rfl
    · cases hsEq
      exact htNo
    · cases hsEq
      exact htT

theorem in_traces_to_failures {T : domTType α} {s : traceType α} {X : Set (event α)} :
    (s, X) :f traces_to_failures T ↔
      (∃ t, s = t ^^^ Tickt (α := α) ∧ (t ^^^ Tickt (α := α)) :t T) ∨
        (noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset) := by
  change
    (s, X) ∈ Rep_setF
      (Abs_setF
        {f : failure α |
          (∃ s, (∃ X, f = (s ^^^ Tickt (α := α), X)) ∧ (s ^^^ Tickt (α := α)) :t T) ∨
            ∃ s X, f = (s, X) ∧ noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset}) ↔
      (∃ t, s = t ^^^ Tickt (α := α) ∧ (t ^^^ Tickt (α := α)) :t T) ∨
        (noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset)
  rw [Abs_setF_inverse (F := {f : failure α |
    (∃ s, (∃ X, f = (s ^^^ Tickt (α := α), X)) ∧ (s ^^^ Tickt (α := α)) :t T) ∨
      ∃ s X, f = (s, X) ∧ noTick s ∧ (s ^^^ Tickt (α := α)) :t T ∧ X ⊆ Evset})
      traces_to_failures_in_setF]
  constructor
  · intro hsX
    rcases hsX with hsX | hsX
    · rcases hsX with ⟨t, ⟨Y, hEq⟩, htT⟩
      cases hEq
      exact Or.inl ⟨t, rfl, htT⟩
    · rcases hsX with ⟨t, Y, hEq, htNo, htT, hY⟩
      cases hEq
      exact Or.inr ⟨htNo, htT, hY⟩
  · intro hsX
    rcases hsX with hsX | hsX
    · rcases hsX with ⟨t, hsEq, htT⟩
      refine Or.inl ⟨t, ⟨X, ?_⟩, ?_⟩
      · cases hsEq
        rfl
      · cases hsEq
        exact htT
    · rcases hsX with ⟨hsNo, hsT, hX⟩
      exact Or.inr ⟨s, X, rfl, hsNo, hsT, hX⟩

/- (*********************************************************
                        domF
 *********************************************************) -/

/- T2 -/

theorem traces_to_failures_T2 {T : domTType α} :
    HC_T2 (T, traces_to_failures T) := by
  intro s X hsX
  rcases (in_traces_to_failures (T := T) (s := s) (X := X)).1 hsX with hsTick | hsStable
  · rcases hsTick with ⟨t, hsEq, htT⟩
    simpa [hsEq] using htT
  · exact memT_prefix_closed hsStable.2.1
      (prefix_appt_simp (s := s) (t := Tickt (α := α)) (Or.inl hsStable.1))

/- F3 -/

theorem traces_to_failures_F3 {T : domTType α} :
    HC_F3 (T, traces_to_failures T) := by
  intro s X Y hsX hsNo hY
  rcases (in_traces_to_failures (T := T) (s := s) (X := X)).1 hsX with hsTick | hsStable
  · rcases hsTick with ⟨t, hsEq, htT⟩
    exact (in_traces_to_failures (T := T) (s := s) (X := X ∪ Y)).2 (Or.inl ⟨t, hsEq, htT⟩)
  · refine (in_traces_to_failures (T := T) (s := s) (X := X ∪ Y)).2 (Or.inr ?_)
    refine ⟨hsNo, hsStable.2.1, ?_⟩
    intro a ha
    rcases ha with ha | ha
    · cases a with
      | Ev b =>
          simp [Evset]
      | Tick =>
          exact hsStable.2.2 ha
    · cases a with
      | Ev b =>
          simp [Evset]
      | Tick =>
          exfalso
          exact hY event.Tick ha hsStable.2.1

/- T3_F4 -/

theorem traces_to_failures_T3_F4 {T : domTType α} :
    HC_T3_F4 (T, traces_to_failures T) := by
  intro s hs
  constructor
  · exact
      (in_traces_to_failures (T := T) (s := s) (X := Evset)).2
        (Or.inr ⟨hs.2, hs.1, Set.Subset.rfl⟩)
  · intro X
    exact (in_traces_to_failures (T := T) (s := s ^^^ Tickt (α := α)) (X := X)).2
      (Or.inl ⟨s, rfl, hs.1⟩)

/- (*** traces_to_failures_domF ***) -/

@[simp]
theorem traces_to_failures_domF {T : domTType α} :
    (T, traces_to_failures T) ∈ domF (α := α) := by
  rw [domF_iff]
  exact ⟨traces_to_failures_T2 (T := T), traces_to_failures_F3 (T := T),
    traces_to_failures_T3_F4 (T := T)⟩

/- (*********************************************************
                        relation
 *********************************************************) -/

theorem traces_to_failures_EX :
    ∀ T : domTType α, ∃ F : domFType α, T = fstF F := by
  intro T
  refine ⟨T ,, traces_to_failures T, ?_⟩
  exact (pairF_fstF (S := T) (F := traces_to_failures T)
    (hSF := traces_to_failures_domF (T := T))).symm

theorem traces_to_failures_subset {T1 T2 : domTType α} :
    T1 <= T2 → traces_to_failures T1 <= traces_to_failures T2 := by
  intro hT
  rw [subsetF_iff]
  intro s X hsX
  rcases (in_traces_to_failures (T := T1) (s := s) (X := X)).1 hsX with hsTick | hsStable
  · rcases hsTick with ⟨t, hsEq, htT⟩
    exact (in_traces_to_failures (T := T2) (s := s) (X := X)).2
      (Or.inl ⟨t, hsEq, hT htT⟩)
  · exact (in_traces_to_failures (T := T2) (s := s) (X := X)).2
      (Or.inr ⟨hsStable.1, hT hsStable.2.1, hsStable.2.2⟩)

theorem traces_to_failures_refF {T1 T2 : domTType α} :
    T1 <= T2 →
      ∃ F1 F2 : domFType α, T1 = fstF F1 ∧ T2 = fstF F2 ∧ F1 <= F2 := by
  intro hT
  refine ⟨T1 ,, traces_to_failures T1, T2 ,, traces_to_failures T2, ?_, ?_, ?_⟩
  · exact (pairF_fstF (S := T1) (F := traces_to_failures T1)
      (hSF := traces_to_failures_domF (T := T1))).symm
  · exact (pairF_fstF (S := T2) (F := traces_to_failures T2)
      (hSF := traces_to_failures_domF (T := T2))).symm
  · rw [subdomF_decompo]
    simpa
      [pairF_fstF
          (S := T1) (F := traces_to_failures T1) (hSF := traces_to_failures_domF (T := T1)),
        pairF_sndF
          (S := T1) (F := traces_to_failures T1) (hSF := traces_to_failures_domF (T := T1)),
        pairF_fstF
          (S := T2) (F := traces_to_failures T2) (hSF := traces_to_failures_domF (T := T2)),
        pairF_sndF
          (S := T2) (F := traces_to_failures T2) (hSF := traces_to_failures_domF (T := T2))]
      using (show T1 <= T2 ∧ traces_to_failures T1 <= traces_to_failures T2 from
        ⟨hT, traces_to_failures_subset hT⟩)

/- (*** fun ***) -/

theorem traces_to_failures_fun_EX {ι : Type _} :
    ∀ Tf : ι → domTType α, ∃ Ff : ι → domFType α, Tf = fstF ∘ Ff := by
  intro Tf
  refine ⟨fun x => Tf x ,, traces_to_failures (Tf x), ?_⟩
  funext x
  simpa [Function.comp] using
    (pairF_fstF (S := Tf x) (F := traces_to_failures (Tf x))
      (hSF := traces_to_failures_domF (T := Tf x))).symm

theorem traces_to_failures_fun_refF {ι : Type _} {Tf1 Tf2 : ι → domTType α} :
    Tf1 <= Tf2 →
      ∃ Ff1 Ff2 : ι → domFType α,
        Tf1 = fstF ∘ Ff1 ∧ Tf2 = fstF ∘ Ff2 ∧ Ff1 <= Ff2 := by
  intro hTf
  refine ⟨(fun x => Tf1 x ,, traces_to_failures (Tf1 x)),
    (fun x => Tf2 x ,, traces_to_failures (Tf2 x)), ?_, ?_, ?_⟩
  · funext x
    simpa [Function.comp] using
      (pairF_fstF (S := Tf1 x) (F := traces_to_failures (Tf1 x))
        (hSF := traces_to_failures_domF (T := Tf1 x))).symm
  · funext x
    simpa [Function.comp] using
      (pairF_fstF (S := Tf2 x) (F := traces_to_failures (Tf2 x))
        (hSF := traces_to_failures_domF (T := Tf2 x))).symm
  · intro x
    rw [subdomF_decompo]
    simpa
      [pairF_fstF (S := Tf1 x) (F := traces_to_failures (Tf1 x))
          (hSF := traces_to_failures_domF (T := Tf1 x)),
        pairF_sndF (S := Tf1 x) (F := traces_to_failures (Tf1 x))
          (hSF := traces_to_failures_domF (T := Tf1 x)),
        pairF_fstF (S := Tf2 x) (F := traces_to_failures (Tf2 x))
          (hSF := traces_to_failures_domF (T := Tf2 x)),
        pairF_sndF (S := Tf2 x) (F := traces_to_failures (Tf2 x))
          (hSF := traces_to_failures_domF (T := Tf2 x))]
      using (show Tf1 x <= Tf2 x ∧ traces_to_failures (Tf1 x) <= traces_to_failures (Tf2 x) from
        ⟨hTf x, traces_to_failures_subset (hTf x)⟩)

end
