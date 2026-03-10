           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_traces

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `(notick \/ t = <>)`.          -/
/-                                                                     -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

private theorem ev_mem_insert_image {a : α} {X : Set α} :
    Ev a ∈ Set.insert Tick (Ev '' X) → a ∈ X := by
  intro h
  change Ev a = Tick ∨ Ev a ∈ Ev '' X at h
  rcases h with hTick | hImg
  · cases hTick
  · rcases hImg with ⟨b, hbX, hbEq⟩
    cases hbEq
    exact hbX

private theorem insert_image_subset_union_left {X Y : Set α} :
    Set.insert Tick (Ev '' X) ⊆ Set.insert Tick (Ev '' (X ∪ Y)) := by
  intro e he
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · change Tick = Tick ∨ Tick ∈ Ev '' (X ∪ Y)
    exact Or.inl rfl
  · have haX : a ∈ X := ev_mem_insert_image (X := X) he
    change Ev a = Tick ∨ Ev a ∈ Ev '' (X ∪ Y)
    exact Or.inr ⟨a, Or.inl haX, rfl⟩

private theorem insert_image_subset_union_right {X Y : Set α} :
    Set.insert Tick (Ev '' Y) ⊆ Set.insert Tick (Ev '' (X ∪ Y)) := by
  intro e he
  rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
  · change Tick = Tick ∨ Tick ∈ Ev '' (X ∪ Y)
    exact Or.inl rfl
  · have haY : a ∈ Y := ev_mem_insert_image (X := Y) he
    change Ev a = Tick ∨ Ev a ∈ Ev '' (X ∪ Y)
    exact Or.inr ⟨a, Or.inr haY, rfl⟩

/-
(*********************************************************
       Preparation (traces operated by par and hide)
 *********************************************************)
-/

/- (*** par rest ***) -/

/- (*** if ***) -/

theorem par_tr_rest_tr_if_all {X Y : Set α} {u : traceType α} :
    sett u ⊆ Set.insert Tick (Ev '' (X ∪ Y)) →
      u ∈ (u rest-tr X) |[X ∩ Y]|tr (u rest-tr Y) := by
  refine
    induct_trace
      (s := u)
      (P := fun u =>
        sett u ⊆ Set.insert Tick (Ev '' (X ∪ Y)) →
          u ∈ (u rest-tr X) |[X ∩ Y]|tr (u rest-tr Y))
      ?_ ?_ ?_
  · intro _
    simpa using (par_tr_nil_nil (X := X ∩ Y))
  · intro _
    simpa using (par_tr_Tick_Tick (X := X ∩ Y))
  · intro s a ih hsXY
    have hsXY' : sett s ⊆ Set.insert Tick (Ev '' (X ∪ Y)) := by
      intro e he
      apply hsXY
      rw [sett_appt1 (s := Abs_trace [Ev a]) (t := s) (Or.inl (noTick_Ev a))]
      exact Or.inr he
    have hsPar : s ∈ (s rest-tr X) |[X ∩ Y]|tr (s rest-tr Y) := ih hsXY'
    have haXY : a ∈ X ∪ Y := by
      have hEa : Ev a ∈ sett (Abs_trace [Ev a] ^^^ s) := by
        rw [sett_appt1 (s := Abs_trace [Ev a]) (t := s) (Or.inl (noTick_Ev a))]
        simp
      have hmem : Ev a ∈ Set.insert Tick (Ev '' (X ∪ Y)) := hsXY hEa
      exact ev_mem_insert_image (X := X ∪ Y) hmem
    by_cases haX : a ∈ X
    · by_cases haY : a ∈ Y
      · exact
          by
            simpa [haX, haY] using
              (par_tr_Ev_sync
                (u := s) (s := s rest-tr X) (t := s rest-tr Y) (X := X ∩ Y) (a := a)
                hsPar ⟨haX, haY⟩)
      · simpa [haX, haY] using
          (par_tr_Ev_left
            (u := s) (s := s rest-tr X) (t := s rest-tr Y) (X := X ∩ Y) (a := a)
            hsPar (by simp [haY]))
    · have haY : a ∈ Y := by
        rcases haXY with haX' | haY
        · exact False.elim (haX haX')
        · exact haY
      simpa [haX, haY] using
        (par_tr_Ev_right
          (u := s) (s := s rest-tr X) (t := s rest-tr Y) (X := X ∩ Y) (a := a)
          hsPar (by simp [haX]))

theorem par_tr_rest_tr_if {X Y : Set α} {u : traceType α} :
    sett u ⊆ Set.insert Tick (Ev '' (X ∪ Y)) →
      u ∈ (u rest-tr X) |[X ∩ Y]|tr (u rest-tr Y) :=
  par_tr_rest_tr_if_all

/- (*** only if ***) -/

theorem par_tr_rest_tr_only_if_all {X Y : Set α} {u : traceType α} :
    ∀ s t,
      (sett s ⊆ Set.insert Tick (Ev '' X) ∧
        sett t ⊆ Set.insert Tick (Ev '' Y) ∧
        u ∈ s |[X ∩ Y]|tr t) →
          s = u rest-tr X ∧
            t = u rest-tr Y ∧
              sett u ⊆ Set.insert Tick (Ev '' (X ∪ Y)) := by
  refine
    induct_trace
      (s := u)
      (P := fun u =>
        ∀ s t,
          (sett s ⊆ Set.insert Tick (Ev '' X) ∧
            sett t ⊆ Set.insert Tick (Ev '' Y) ∧
            u ∈ s |[X ∩ Y]|tr t) →
              s = u rest-tr X ∧
                t = u rest-tr Y ∧
                  sett u ⊆ Set.insert Tick (Ev '' (X ∪ Y)))
      ?_ ?_ ?_
  · intro s t h
    rcases h with ⟨_, _, hpar⟩
    rcases par_tr_nil_only_if hpar with ⟨rfl, rfl⟩
    simp
  · intro s t h
    rcases h with ⟨_, _, hpar⟩
    rcases par_tr_Tick_only_if hpar with ⟨rfl, rfl⟩
    constructor
    · simp
    · constructor
      · simp
      · intro e he
        have heTick : e = Tick := by
          simpa [sett_one] using he
        simpa [heTick] using
          (show Tick ∈ Set.insert Tick (Ev '' (X ∪ Y)) from by
            change Tick = Tick ∨ Tick ∈ Ev '' (X ∪ Y)
            exact Or.inl rfl)
  · intro u a ih s t h
    rcases h with ⟨hsX, htY, hpar⟩
    have huXY : sett (Abs_trace [Ev a] ^^^ u) ⊆ Set.insert Tick (Ev '' (X ∪ Y)) := by
      intro e he
      have hst : e ∈ sett s ∪ sett t := par_tr_sett hpar he
      rcases hst with hs | ht
      · exact insert_image_subset_union_left (X := X) (Y := Y) (hsX hs)
      · exact insert_image_subset_union_right (X := X) (Y := Y) (htY ht)
    rw [par_tr_head] at hpar
    rcases hpar with hsync | hleft | hright
    · rcases hsync with ⟨haXY, s', t', hpar', hsEq, htEq⟩
      rcases haXY with ⟨haX, haY⟩
      subst s
      subst t
      have hs'X : sett s' ⊆ Set.insert Tick (Ev '' X) := by
        intro e he
        apply hsX
        rw [sett_appt1 (s := Abs_trace [Ev a]) (t := s') (Or.inl (noTick_Ev a))]
        exact Or.inr he
      have ht'Y : sett t' ⊆ Set.insert Tick (Ev '' Y) := by
        intro e he
        apply htY
        rw [sett_appt1 (s := Abs_trace [Ev a]) (t := t') (Or.inl (noTick_Ev a))]
        exact Or.inr he
      rcases ih s' t' ⟨hs'X, ht'Y, hpar'⟩ with ⟨hsRest, htRest, _⟩
      constructor
      · simp [haX, hsRest]
      · constructor
        · simp [haY, htRest]
        · exact huXY
    · rcases hleft with ⟨haInt, s', hpar', hsEq⟩
      subst s
      have haX : a ∈ X := by
        have hEa : Ev a ∈ sett (Abs_trace [Ev a] ^^^ s') := by
          rw [sett_appt1 (s := Abs_trace [Ev a]) (t := s') (Or.inl (noTick_Ev a))]
          simp
        have hmem : Ev a ∈ Set.insert Tick (Ev '' X) := hsX hEa
        exact ev_mem_insert_image (X := X) hmem
      have haY : a ∉ Y := by
        intro haY
        exact haInt ⟨haX, haY⟩
      have hs'X : sett s' ⊆ Set.insert Tick (Ev '' X) := by
        intro e he
        apply hsX
        rw [sett_appt1 (s := Abs_trace [Ev a]) (t := s') (Or.inl (noTick_Ev a))]
        exact Or.inr he
      rcases ih s' t ⟨hs'X, htY, hpar'⟩ with ⟨hsRest, htRest, _⟩
      constructor
      · simp [haX, hsRest]
      · constructor
        · simp [haY, htRest]
        · exact huXY
    · rcases hright with ⟨haInt, t', hpar', htEq⟩
      subst t
      have haY : a ∈ Y := by
        have hEa : Ev a ∈ sett (Abs_trace [Ev a] ^^^ t') := by
          rw [sett_appt1 (s := Abs_trace [Ev a]) (t := t') (Or.inl (noTick_Ev a))]
          simp
        have hmem : Ev a ∈ Set.insert Tick (Ev '' Y) := htY hEa
        exact ev_mem_insert_image (X := Y) hmem
      have haX : a ∉ X := by
        intro haX
        exact haInt ⟨haX, haY⟩
      have ht'Y : sett t' ⊆ Set.insert Tick (Ev '' Y) := by
        intro e he
        apply htY
        rw [sett_appt1 (s := Abs_trace [Ev a]) (t := t') (Or.inl (noTick_Ev a))]
        exact Or.inr he
      rcases ih s t' ⟨hsX, ht'Y, hpar'⟩ with ⟨hsRest, htRest, _⟩
      constructor
      · simp [haX, hsRest]
      · constructor
        · simp [haY, htRest]
        · exact huXY

/- (*** par rest ***) -/

theorem par_tr_rest_tr {X Y : Set α} {u s t : traceType α}
    (hs : sett s ⊆ Set.insert Tick (Ev '' X))
    (ht : sett t ⊆ Set.insert Tick (Ev '' Y)) :
    u ∈ s |[X ∩ Y]|tr t ↔
      (s = u rest-tr X ∧ t = u rest-tr Y ∧
        sett u ⊆ Set.insert Tick (Ev '' (X ∪ Y))) := by
  constructor
  · intro hpar
    exact par_tr_rest_tr_only_if_all (X := X) (Y := Y) (u := u) s t ⟨hs, ht, hpar⟩
  · intro hpar
    rcases hpar with ⟨rfl, rfl, huXY⟩
    exact par_tr_rest_tr_if (X := X) (Y := Y) (u := u) huXY

/-
(*********************************************************
             Alphabetized Parallel eval
 *********************************************************)
-/

/- (*** Par and SKIP ***) -/

theorem in_traces_Parallel_SKIP {u : traceType α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    (u :t traces (P |[X]| proc.SKIP) M) ↔
      (u :t traces P M ∧ sett u ∩ Ev '' X = ∅) := by
  rw [in_traces_Parallel]
  constructor
  · rintro ⟨s, t, hpar, hs, ht⟩
    rw [in_traces_SKIP] at ht
    rcases ht with rfl | rfl
    · rcases (par_tr_nil_right.mp hpar) with ⟨huEq, _, hEmpty⟩
      constructor
      · simpa [huEq] using hs
      · simpa [huEq] using hEmpty
    · rcases (par_tr_Tick_right.mp hpar) with ⟨huEq, _, hEmpty⟩
      constructor
      · simpa [huEq] using hs
      · simpa [huEq] using hEmpty
  · rintro ⟨huP, hEmpty⟩
    by_cases hTick : Tick ∈ sett u
    · refine ⟨u, Abs_trace [Tick], ?_, huP, ?_⟩
      · exact (par_tr_Tick_right (u := u) (s := u) (X := X)).2 ⟨rfl, hTick, hEmpty⟩
      · exact (in_traces_SKIP (t := Abs_trace [Tick]) (M := M)).2 (Or.inr rfl)
    · refine ⟨u, <>, ?_, huP, ?_⟩
      · exact (par_tr_nil_right (u := u) (s := u) (X := X)).2 ⟨rfl, hTick, hEmpty⟩
      · exact (in_traces_SKIP (t := <>) (M := M)).2 (Or.inl rfl)

/- (*** complement ***) -/

theorem in_traces_Parallel_SKIP_comp
    {u : traceType α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    (u :t traces (P |[Xᶜ]| proc.SKIP) M) ↔
      (u :t traces P M ∧ sett u ⊆ Set.insert Tick (Ev '' X)) := by
  rw [in_traces_Parallel_SKIP]
  constructor
  · rintro ⟨huP, hEmpty⟩
    constructor
    · exact huP
    · intro e he
      rcases event_Tick_or_Ev e with rfl | ⟨a, rfl⟩
      · change Tick = Tick ∨ Tick ∈ Ev '' X
        exact Or.inl rfl
      · by_cases ha : a ∈ X
        · change Ev a = Tick ∨ Ev a ∈ Ev '' X
          exact Or.inr ⟨a, ha, rfl⟩
        · exfalso
          have hmem : Ev a ∈ sett u ∩ Ev '' Xᶜ := by
            constructor
            · exact he
            · exact ⟨a, by simpa using ha, rfl⟩
          rw [hEmpty] at hmem
          simp at hmem
  · rintro ⟨huP, huX⟩
    constructor
    · exact huP
    · ext e
      constructor
      · intro he
        exfalso
        rcases he with ⟨heU, heComp⟩
        rcases heComp with ⟨a, haComp, rfl⟩
        have haNot : a ∉ X := by
          simpa using haComp
        have hmem : Ev a ∈ Set.insert Tick (Ev '' X) := huX heU
        exact haNot (ev_mem_insert_image (X := X) hmem)
      · intro he
        simp at he

/- (*** Alpha_parallel_evalT ***) -/

theorem in_traces_Alpha_parallel
    {u : traceType α} {P Q : proc p α} {X1 X2 : Set α} {M : p → domTType α} :
    (u :t traces (P |[X1,X2]| Q) M) ↔
      ((u rest-tr X1) :t traces P M ∧
        (u rest-tr X2) :t traces Q M ∧
        sett u ⊆ Set.insert Tick (Ev '' (X1 ∪ X2))) := by
  rw [Alpha_parallel_def, in_traces_Parallel]
  constructor
  · rintro ⟨s, t, hpar, hs, ht⟩
    rw [in_traces_Parallel_SKIP_comp] at hs ht
    rcases hs with ⟨hsP, hsX⟩
    rcases ht with ⟨htQ, htY⟩
    rcases (par_tr_rest_tr (X := X1) (Y := X2) (u := u) (s := s) (t := t) hsX htY).1 hpar with
      ⟨hsRest, htRest, huXY⟩
    constructor
    · simpa [hsRest] using hsP
    · constructor
      · simpa [htRest] using htQ
      · exact huXY
  · rintro ⟨hsP, htQ, huXY⟩
    refine ⟨u rest-tr X1, u rest-tr X2, ?_, ?_, ?_⟩
    · exact par_tr_rest_tr_if (X := X1) (Y := X2) (u := u) huXY
    · exact
        (in_traces_Parallel_SKIP_comp
          (u := u rest-tr X1) (P := P) (X := X1) (M := M)).2
          ⟨hsP, rest_tr_subset_event⟩
    · exact
        (in_traces_Parallel_SKIP_comp
          (u := u rest-tr X2) (P := Q) (X := X2) (M := M)).2
          ⟨htQ, rest_tr_subset_event⟩

/- (*** Semantics for alphabetized parallel on T ***) -/

theorem traces_Alpha_parallel
    {P Q : proc p α} {X1 X2 : Set α} {M : p → domTType α} :
    traces (P |[X1,X2]| Q) M =
      CollectT (fun u : traceType α =>
        (u rest-tr X1) :t traces P M ∧
          (u rest-tr X2) :t traces Q M ∧
            sett u ⊆ Set.insert Tick (Ev '' (X1 ∪ X2))) := by
  rw [← CollectT_open (T := traces (P |[X1,X2]| Q) M)]
  apply CollectT_eq
  intro u
  exact propext (in_traces_Alpha_parallel (u := u) (P := P) (Q := Q) (X1 := X1) (X2 := X2) (M := M))

end
