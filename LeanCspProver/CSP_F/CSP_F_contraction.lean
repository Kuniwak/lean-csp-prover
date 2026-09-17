           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_contraction

open SumType

noncomputable section

/-
(*****************************************************************

         1. contraction failuresfun
         2. contraction failuresFun
         3. contraction [[ ]]Ffun
         4. contraction [[ ]]FFun

 *****************************************************************)
-/

/- (*** Lean port helpers ***) -/

theorem restCond_le' {α : Type _} {s : traceType α} {n : Nat} :
    restCond s n → lengtht s <= n := by
  rintro (h | ⟨h, -⟩) <;> omega

theorem restCond_lt' {α : Type _} {s : traceType α} {n : Nat} :
    restCond s n → noTick s → LT.lt (lengtht s) n := by
  rintro (h | ⟨h, s', rfl, hn'⟩) hno
  · exact h
  · exact absurd (decompo_appt_noTick_only_if (Or.inl hn') hno).2 not_noTick_Tick

theorem restCond_Ev_head {α : Type _} {a : α} {s : traceType α} {n : Nat} :
    restCond (Abs_trace [event.Ev a] ^^^ s) (Nat.succ n) ↔ restCond s n := by
  constructor
  · rintro (h | ⟨h, s', heq, hn'⟩)
    · rw [lengtht_app_event_Suc_head] at h
      exact Or.inl (by omega)
    · rw [lengtht_app_event_Suc_head] at h
      obtain ⟨s'', hs', hs, hn''⟩ := head_Ev_of_appt_Tick hn' heq.symm
      exact Or.inr ⟨by omega, s'', hs, hn''⟩
  · rintro (h | ⟨h, s', rfl, hn'⟩)
    · refine Or.inl ?_
      rw [lengtht_app_event_Suc_head]
      omega
    · refine Or.inr ⟨?_, Abs_trace [event.Ev a] ^^^ s', ?_,
        decompo_appt_noTick_if (noTick_Ev a) hn'⟩
      · rw [lengtht_app_event_Suc_head]
        omega
      · rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hn')]

theorem rest_setF_le_iff {α : Type _} {F E : setFType α} {n : Nat} :
    (F .|. n <= E .|. n) ↔ ∀ s X, (s, X) :f F → restCond s n → (s, X) :f E := by
  constructor
  · intro h s X hs hc
    exact (in_rest_setF.mp (memF_subsetF (in_rest_setF.mpr ⟨hs, hc⟩) h)).1
  · intro h
    refine subsetFI ?_
    intro s X hs
    obtain ⟨hs1, hc⟩ := in_rest_setF.mp hs
    exact in_rest_setF.mpr ⟨h s X hs1 hc, hc⟩

theorem rest_setF_eq_iff_le {α : Type _} {F E : setFType α} {n : Nat} :
    (F .|. n = E .|. n) ↔ ∀ s X, restCond s n → ((s, X) :f F ↔ (s, X) :f E) := by
  constructor
  · intro h s X hc
    exact ⟨fun hs => rest_setF_le_iff.mp (le_of_eq h) s X hs hc,
      fun hs => rest_setF_le_iff.mp (le_of_eq h.symm) s X hs hc⟩
  · intro h
    exact le_antisymm (rest_setF_le_iff.mpr (fun s X hs hc => (h s X hc).mp hs))
      (rest_setF_le_iff.mpr (fun s X hs hc => (h s X hc).mpr hs))

theorem two_elem_ne {γ : Type _} {a b : γ} : ({a, b} : Set γ) ≠ ∅ := by
  intro h0
  have hmem : a ∈ ({a, b} : Set γ) := Set.mem_insert _ _
  rw [h0] at hmem
  exact hmem

theorem one_elem_ne {γ : Type _} {a : γ} : ({a} : Set γ) ≠ ∅ := by
  intro h0
  have hmem : a ∈ ({a} : Set γ) := rfl
  rw [h0] at hmem
  exact hmem

theorem dist_pair_one_set {γ1 γ2 : Type _} [ms_rs γ1] [ms_rs γ2]
    {xps : Set (γ1 × γ1)} {z1 z2 : γ2} :
    xps ≠ ∅ →
      (∀ n, (∀ x ∈ xps, x.1 .|. n = x.2 .|. n) → z1 .|. n = z2 .|. n) →
        ∃ x ∈ xps, distance z1 z2 <= distance x.1 x.2 := by
  intro h1 h2
  obtain ⟨x, hx, hd⟩ := rest_to_dist_pair h1 h2
  refine ⟨x, hx, ?_⟩
  rw [ms0_rs.to_distance_rs, ms0_rs.to_distance_rs]
  exact hd

theorem dist_pair_two_sets {γ1 γ2 γ3 : Type _} [ms_rs γ1] [ms_rs γ2] [ms_rs γ3]
    {xps : Set (γ1 × γ1)} {yps : Set (γ2 × γ2)} {z1 z2 : γ3} :
    xps ≠ ∅ → yps ≠ ∅ →
      (∀ n, (∀ x ∈ xps, x.1 .|. n = x.2 .|. n) ∧ (∀ y ∈ yps, y.1 .|. n = y.2 .|. n) →
        z1 .|. n = z2 .|. n) →
        (∃ x ∈ xps, distance z1 z2 <= distance x.1 x.2) ∨
          ∃ y ∈ yps, distance z1 z2 <= distance y.1 y.2 := by
  intro h1 h2 h3
  rcases rest_to_dist_pair_two h1 h2 h3 with ⟨x, hx, hd⟩ | ⟨y, hy, hd⟩
  · refine Or.inl ⟨x, hx, ?_⟩
    rw [ms0_rs.to_distance_rs, ms0_rs.to_distance_rs]
    exact hd
  · refine Or.inr ⟨y, hy, ?_⟩
    rw [ms0_rs.to_distance_rs, ms0_rs.to_distance_rs]
    exact hd

theorem map_alpha_of_rest_one' {γ β : Type _} [ms β] [ms_rs γ] {g F : β → γ} {alpha : ℝ} :
    (∀ x y n, g x .|. n = g y .|. n → F x .|. n = F y .|. n) →
      map_alpha g alpha → map_alpha F alpha := by
  intro hrest hg
  refine ⟨hg.1, ?_⟩
  intro x y
  refine le_trans ?_ (hg.2 x y)
  rw [ms0_rs.to_distance_rs, ms0_rs.to_distance_rs]
  exact rest_distance_subset (fun n h => hrest x y n h)

theorem map_alpha_of_rest_two' {γ1 γ β : Type _} [ms β] [ms_rs γ1] [ms_rs γ]
    {g1 g2 : β → γ1} {F : β → γ} {alpha : ℝ} :
    (∀ x y n, g1 x .|. n = g1 y .|. n → g2 x .|. n = g2 y .|. n → F x .|. n = F y .|. n) →
      map_alpha g1 alpha → map_alpha g2 alpha → map_alpha F alpha := by
  intro hrest h1 h2
  refine ⟨h1.1, ?_⟩
  intro x y
  obtain ⟨PQ, hPQ, hd⟩ :=
    dist_pair_one_set (xps := ({(g1 x, g1 y), (g2 x, g2 y)} : Set (γ1 × γ1))) (z1 := F x)
      (z2 := F y) two_elem_ne
      (fun n hall => hrest x y n (hall _ (Set.mem_insert _ _))
        (hall _ (Set.mem_insert_of_mem _ rfl)))
  rcases hPQ with rfl | hPQ
  · exact le_trans hd (h1.2 x y)
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hd (h2.2 x y)

theorem map_alpha_of_rest_three' {γ1 γ β : Type _} [ms β] [ms_rs γ1] [ms_rs γ]
    {g0 : β → γ1} {g1 g2 F : β → γ} {alpha : ℝ} :
    (∀ x y n, g0 x .|. n = g0 y .|. n → g1 x .|. n = g1 y .|. n →
        g2 x .|. n = g2 y .|. n → F x .|. n = F y .|. n) →
      map_alpha g0 alpha → map_alpha g1 alpha → map_alpha g2 alpha → map_alpha F alpha := by
  intro hrest h0 h1 h2
  refine ⟨h0.1, ?_⟩
  intro x y
  rcases dist_pair_two_sets (xps := ({(g0 x, g0 y)} : Set (γ1 × γ1)))
      (yps := ({(g1 x, g1 y), (g2 x, g2 y)} : Set (γ × γ))) (z1 := F x) (z2 := F y)
      one_elem_ne two_elem_ne
      (fun n hall => hrest x y n (hall.1 _ rfl) (hall.2 _ (Set.mem_insert _ _))
        (hall.2 _ (Set.mem_insert_of_mem _ rfl))) with ⟨PQ, hPQ, hd⟩ | ⟨PQ, hPQ, hd⟩
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hd (h0.2 x y)
  · rcases hPQ with rfl | hPQ
    · exact le_trans hd (h1.2 x y)
    · rw [Set.mem_singleton_iff] at hPQ
      subst hPQ
      exact le_trans hd (h2.2 x y)

theorem map_alpha_of_rest_four' {γ1 γ β : Type _} [ms β] [ms_rs γ1] [ms_rs γ]
    {gA gB : β → γ1} {g1 g2 F : β → γ} {alpha : ℝ} :
    (∀ x y n, gA x .|. n = gA y .|. n → gB x .|. n = gB y .|. n →
        g1 x .|. n = g1 y .|. n → g2 x .|. n = g2 y .|. n → F x .|. n = F y .|. n) →
      map_alpha gA alpha → map_alpha gB alpha → map_alpha g1 alpha → map_alpha g2 alpha →
        map_alpha F alpha := by
  intro hrest hA hB h1 h2
  refine ⟨hA.1, ?_⟩
  intro x y
  rcases dist_pair_two_sets (xps := ({(gA x, gA y), (gB x, gB y)} : Set (γ1 × γ1)))
      (yps := ({(g1 x, g1 y), (g2 x, g2 y)} : Set (γ × γ))) (z1 := F x) (z2 := F y)
      two_elem_ne two_elem_ne
      (fun n hall => hrest x y n (hall.1 _ (Set.mem_insert _ _))
        (hall.1 _ (Set.mem_insert_of_mem _ rfl)) (hall.2 _ (Set.mem_insert _ _))
        (hall.2 _ (Set.mem_insert_of_mem _ rfl))) with ⟨PQ, hPQ, hd⟩ | ⟨PQ, hPQ, hd⟩
  · rcases hPQ with rfl | hPQ
    · exact le_trans hd (hA.2 x y)
    · rw [Set.mem_singleton_iff] at hPQ
      subst hPQ
      exact le_trans hd (hB.2 x y)
  · rcases hPQ with rfl | hPQ
    · exact le_trans hd (h1.2 x y)
    · rw [Set.mem_singleton_iff] at hPQ
      subst hPQ
      exact le_trans hd (h2.2 x y)

theorem fstF_rest {α : Type _} {F : domFType α} {n : Nat} :
    fstF (F .|. n) = fstF F .|. n := by
  rw [rest_domF_def, restTF_def]
  exact pairF_fstF restTF_in

theorem sndF_rest {α : Type _} {F : domFType α} {n : Nat} :
    sndF (F .|. n) = sndF F .|. n := by
  rw [rest_domF_def, restTF_def]
  exact pairF_sndF restTF_in

theorem non_expanding_fstF_comp {p α : Type _} :
    non_expanding (fun M : p → domFType α => fstF ∘ M) := by
  refine non_expanding_iff_rest.mpr ?_
  intro M1 M2 n h
  refine rest_to_prod_rest ?_
  intro i
  exact non_expanding_iff_rest.mp non_expanding_fstF _ _ n (congrFun h i)

theorem restCond_nil_pos {α : Type _} {n : Nat} :
    restCond (<> : traceType α) n → 0 < n := by
  rintro (h | ⟨h, s', heq, hn'⟩)
  · simpa using h
  · exact absurd ((appt_nil hn').mp heq.symm).2 (by simp [tickTrace])

theorem restCond_par_left {α : Type _} {u s t : traceType α} {X : Set α} {n : Nat} :
    u ∈ s |[X]|tr t → restCond u n → restCond s n := by
  intro hpar hc
  obtain ⟨hls, hlt⟩ := par_tr_lengtht hpar
  rcases hc with h | ⟨h, u', rfl, hnu⟩
  · exact Or.inl (by omega)
  · rcases par_tr_last_only_if hpar hnu with ⟨-, s', t', hpar', rfl, rfl, hns', hnt'⟩ |
      ⟨-, hne, -⟩ | ⟨-, hne, -⟩
    · rcases Nat.lt_or_ge (lengtht (s' ^^^ (Abs_trace [event.Tick] : traceType α))) n with hb | hb
      · exact Or.inl hb
      · exact Or.inr ⟨le_antisymm (by omega) hb, s', rfl, hns'⟩
    · exact absurd rfl hne
    · exact absurd rfl hne

theorem restCond_par_right {α : Type _} {u s t : traceType α} {X : Set α} {n : Nat} :
    u ∈ s |[X]|tr t → restCond u n → restCond t n := by
  intro hpar hc
  exact restCond_par_left (par_tr_sym_only_if hpar) hc

theorem restCond_ren {α : Type _} {s t : traceType α} {r : Set (α × α)} {n : Nat} :
    ren_tr s r t → restCond t n → restCond s n := by
  intro hren hc
  have hl : lengtht s = lengtht t := ren_tr_lengtht hren
  rcases hc with h | ⟨h, t', rfl, hn'⟩
  · exact Or.inl (by omega)
  · obtain ⟨s1, s2, hseq, hren1, hren2, hcond⟩ :=
      ren_tr_appt_decompo_right_only_if hren (Or.inl hn')
    have hs2 : s2 = Abs_trace [event.Tick] := ren_tr_Tick2.mp hren2
    subst hs2
    have hns1 : noTick s1 := by
      rcases hcond with hn | h0
      · exact hn
      · simp at h0
    exact Or.inr ⟨by omega, s1, hseq, hns1⟩

theorem restCond_Tick_len {α : Type _} {s t : traceType α} {m : Nat} :
    noTick s → restCond (s ^^^ t) m → lengtht s + 1 <= m := by
  intro hns hc
  have hlen : lengtht s + lengtht t <= m := by
    have h0 := restCond_le' hc
    rw [lengtht_app_decompo1 (Or.inl hns)] at h0
    exact h0
  rcases Nat.eq_zero_or_pos (lengtht t) with h0 | h0
  · have ht0 : t = <> := lengtht_zero.mp h0
    subst ht0
    rw [appt_nil_right] at hc
    have h1 := restCond_lt' hc hns
    omega
  · omega

theorem restCond_appt_right {α : Type _} {s t : traceType α} {m n : Nat} :
    noTick s → restCond (s ^^^ t) m → m <= lengtht s + n → restCond t n := by
  intro hns hc hmn
  have hlen : lengtht (s ^^^ t) = lengtht s + lengtht t := lengtht_app_decompo1 (Or.inl hns)
  rcases hc with h | ⟨h, u', heq, hnu⟩
  · rw [hlen] at h
    exact Or.inl (by omega)
  · rw [hlen] at h
    rcases Nat.lt_or_ge (lengtht t) n with hb | hb
    · exact Or.inl hb
    · have htne : t ≠ <> := by
        intro ht0
        subst ht0
        rw [appt_nil_right] at heq
        subst heq
        exact absurd (decompo_appt_noTick_only_if (Or.inl hnu) hns).2 not_noTick_Tick
      refine Or.inr ⟨by omega, ?_⟩
      rcases (appt_decompo (Or.inl hns) (Or.inl hnu)).mp heq with ⟨w, hw1, hw2, hw3⟩ |
        ⟨w, hw1, hw2, hw3⟩
      · rcases hw3 with hnw | ⟨-, h0⟩
        · exact ⟨w, hw2, hnw⟩
        · simp [tickTrace] at h0
      · have hnw : noTick w := by
          rcases hw3 with hnw | ⟨-, h0⟩
          · exact hnw
          · exact absurd h0 htne
        rcases (appt_decompo_one (Or.inl hnw)).mp hw2 with ⟨-, h0⟩ | ⟨h0, h1⟩
        · exact absurd h0 htne
        · exact ⟨<>, by rw [appt_nil_left]; exact h1, noTick_nil⟩

/- =============================================================*
 |                      traces fstF                            |
 *============================================================= -/

theorem non_expanding_traces_fstF {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (fun M => traces P (fstF ∘ M)) := by
  intro h
  exact compo_non_expand (non_expanding_traces h) non_expanding_fstF_comp

theorem contraction_alpha_traces_fstF {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (fun M => traces P (fstF ∘ M)) (1 / 2 : ℝ) := by
  intro h
  exact compo_contra_alpha_non_expand (contraction_alpha_traces h) non_expanding_fstF_comp

/- --------------------------------*
 |        STOP,SKIP,DIV           |
 *-------------------------------- -/

/- (*** STOP ***) -/

theorem map_alpha_failures_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (failures (p := p) (α := α) proc.STOP) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

theorem non_expanding_failures_STOP {p : Type _} {α : Type _} :
    non_expanding (failures (p := p) (α := α) proc.STOP) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

theorem contraction_alpha_failures_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (failures (p := p) (α := α) proc.STOP) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- (*** SKIP ***) -/

theorem map_alpha_failures_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (failures (p := p) (α := α) proc.SKIP) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

theorem non_expanding_failures_SKIP {p : Type _} {α : Type _} :
    non_expanding (failures (p := p) (α := α) proc.SKIP) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

theorem contraction_alpha_failures_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (failures (p := p) (α := α) proc.SKIP) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- (*** DIV ***) -/

theorem map_alpha_failures_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (failures (p := p) (α := α) proc.DIV) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

theorem non_expanding_failures_DIV {p : Type _} {α : Type _} :
    non_expanding (failures (p := p) (α := α) proc.DIV) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

theorem contraction_alpha_failures_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (failures (p := p) (α := α) proc.DIV) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

theorem Act_prefix_rest_setF_Suc {p q α : Type _}
    {a : α} {P : proc p α} {Q : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (failures P M1 .|. n = failures Q M2 .|. n) ↔
      (failures (a ~> P) M1 .|. Nat.succ n = failures (a ~> Q) M2 .|. Nat.succ n) := by
  rw [rest_setF_eq_iff_le, rest_setF_eq_iff_le]
  constructor
  · intro h t X hc
    rw [in_failures_Act_prefix, in_failures_Act_prefix]
    constructor
    · rintro (⟨Y, hEq, hY⟩ | ⟨s, Y, hEq, hs⟩)
      · exact Or.inl ⟨Y, hEq, hY⟩
      · rw [Prod.mk.injEq] at hEq
        obtain ⟨ht, hX⟩ := hEq
        subst ht
        subst hX
        exact Or.inr ⟨s, _, rfl, (h s _ (restCond_Ev_head.mp hc)).mp hs⟩
    · rintro (⟨Y, hEq, hY⟩ | ⟨s, Y, hEq, hs⟩)
      · exact Or.inl ⟨Y, hEq, hY⟩
      · rw [Prod.mk.injEq] at hEq
        obtain ⟨ht, hX⟩ := hEq
        subst ht
        subst hX
        exact Or.inr ⟨s, _, rfl, (h s _ (restCond_Ev_head.mp hc)).mpr hs⟩
  · intro h s X hc
    have h0 := h (Abs_trace [event.Ev a] ^^^ s) X (restCond_Ev_head.mpr hc)
    rw [in_failures_Act_prefix, in_failures_Act_prefix] at h0
    constructor
    · intro hs
      rcases h0.mp (Or.inr ⟨s, X, rfl, hs⟩) with ⟨Y, hEq, -⟩ | ⟨s', Y, hEq, hs'⟩
      · rw [Prod.mk.injEq] at hEq
        exact absurd hEq.1 (by simp)
      · rw [Prod.mk.injEq] at hEq
        obtain ⟨heq1, heq2⟩ := hEq
        obtain ⟨-, hss⟩ := appt_same_head_only_if heq1
        rw [hss, heq2]
        exact hs'
    · intro hs
      rcases h0.mpr (Or.inr ⟨s, X, rfl, hs⟩) with ⟨Y, hEq, -⟩ | ⟨s', Y, hEq, hs'⟩
      · rw [Prod.mk.injEq] at hEq
        exact absurd hEq.1 (by simp)
      · rw [Prod.mk.injEq] at hEq
        obtain ⟨heq1, heq2⟩ := hEq
        obtain ⟨-, hss⟩ := appt_same_head_only_if heq1
        rw [hss, heq2]
        exact hs'

theorem contraction_half_failures_Act_prefix_lm {p : Type _} {q : Type _} {α : Type _}
    {a : α} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    distance (failures (a ~> P) M1) (failures (a ~> Q) M2) * 2 =
      distance (failures P M1) (failures Q M2) := by
  have h := rest_Suc_dist_half (x1 := failures P M1) (x2 := failures Q M2)
    (y1 := failures (a ~> P) M1) (y2 := failures (a ~> Q) M2) (fun n => Act_prefix_rest_setF_Suc)
  rw [setF_distance_def, setF_distance_def]
  linarith

/- (***  contraction_half ***) -/

theorem contraction_half_failures_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (failures P) → contraction_alpha (failures (a ~> P)) (1 / 2 : ℝ) := by
  intro hP
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro M1 M2
  have h1 := contraction_half_failures_Act_prefix_lm (a := a) (P := P) (Q := P)
    (M1 := M1) (M2 := M2)
  have h2 := hP.2 M1 M2
  linarith

/- (***  contraction ***) -/

theorem contraction_failures_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (failures P) → contraction (failures (a ~> P)) := by
  intro hP
  exact ⟨(1 / 2 : ℝ), contraction_half_failures_Act_prefix hP⟩

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (failures P) → non_expanding (failures (a ~> P)) := by
  intro hP
  exact contraction_non_expanding (contraction_failures_Act_prefix hP)

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem Ext_pre_choice_Act_prefix_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ a ∈ X, failures (a ~> Pf a) M1 .|. n <= failures (a ~> Qf a) M2 .|. n) →
      failures (proc.Ext_pre_choice X Pf) M1 .|. n <= failures (proc.Ext_pre_choice X Qf) M2 .|. n
        := by
  intro h
  rw [rest_setF_le_iff]
  intro t X0 ht hc
  rcases in_failures_Ext_pre_choice.mp ht with ⟨Y, hEq, hY⟩ | ⟨a, s, Y, hEq, hs, haX⟩
  · exact in_failures_Ext_pre_choice.mpr (Or.inl ⟨Y, hEq, hY⟩)
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨ht1, hX1⟩ := hEq
    subst ht1
    subst hX1
    have h1 : (Abs_trace [event.Ev a] ^^^ s, X0) :f failures (a ~> Pf a) M1 :=
      in_failures_Act_prefix.mpr (Or.inr ⟨s, X0, rfl, hs⟩)
    have h2 := rest_setF_le_iff.mp (h a haX) _ _ h1 hc
    rcases in_failures_Act_prefix.mp h2 with ⟨Z, hEq2, -⟩ | ⟨s', Z, hEq2, hs'⟩
    · rw [Prod.mk.injEq] at hEq2
      exact absurd hEq2.1 (by simp)
    · rw [Prod.mk.injEq] at hEq2
      obtain ⟨he1, he2⟩ := hEq2
      obtain ⟨-, hss⟩ := appt_same_head_only_if he1
      refine in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, s, X0, rfl, ?_, haX⟩)
      rw [hss, he2]
      exact hs'

/- (*** rest_setF (equal) ***) -/

theorem Ext_pre_choice_Act_prefix_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ a ∈ X, failures (a ~> Pf a) M1 .|. n = failures (a ~> Qf a) M2 .|. n) →
      failures (proc.Ext_pre_choice X Pf) M1 .|. n = failures (proc.Ext_pre_choice X Qf) M2 .|. n
        := by
  intro h
  refine le_antisymm (Ext_pre_choice_Act_prefix_rest_setF_sub ?_)
    (Ext_pre_choice_Act_prefix_rest_setF_sub ?_)
  · intro a ha
    exact le_of_eq (h a ha)
  · intro a ha
    exact le_of_eq (h a ha).symm

/- (*** distF lemma ***) -/

theorem Ext_pre_choice_Act_prefix_distF_nonempty {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (setFType α × setFType α)}
    {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      PQs =
        {PQ | ∃ a, a ∈ X ∧ PQ = (failures (a ~> Pf a) M1, failures (a ~> Qf a) M2)} →
          ∃ PQ, PQ ∈ PQs ∧
            distance
                (failures (proc.Ext_pre_choice X Pf) M1)
                (failures (proc.Ext_pre_choice X Qf) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hX hPQs
  have hne : PQs ≠ ∅ := by
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hX
    intro h0
    have hmem : (failures (a ~> Pf a) M1, failures (a ~> Qf a) M2) ∈ PQs := by
      rw [hPQs]
      exact ⟨a, ha, rfl⟩
    rw [h0] at hmem
    exact hmem
  refine dist_pair_one_set hne ?_
  intro n hall
  refine Ext_pre_choice_Act_prefix_rest_setF ?_
  intro a ha
  exact hall (failures (a ~> Pf a) M1, failures (a ~> Qf a) M2) (by rw [hPQs]; exact ⟨a, ha, rfl⟩)

/- (*** contraction lemma ***) -/

theorem contraction_half_failures_Ext_pre_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : setFType α} :
    X ≠ ∅ →
      (∀ a, distance (failures (Pf a) M1) (failures (Qf a) M2) <= distance x1 x2) →
        distance
            (failures (proc.Ext_pre_choice X Pf) M1)
            (failures (proc.Ext_pre_choice X Qf) M2) * 2 <=
          distance x1 x2 := by
  intro hX hd
  obtain ⟨PQ, hPQ, hdist⟩ :=
    Ext_pre_choice_Act_prefix_distF_nonempty
      (PQs := {PQ | ∃ a, a ∈ X ∧ PQ = (failures (a ~> Pf a) M1, failures (a ~> Qf a) M2)})
      hX rfl
  obtain ⟨a, ha, rfl⟩ := hPQ
  have h1 := contraction_half_failures_Act_prefix_lm (a := a) (P := Pf a) (Q := Qf a)
    (M1 := M1) (M2 := M2)
  have h2 := hd a
  dsimp only at hdist
  linarith


/- (*** general-`ms` version of the lemma above (Lean port helper) ***) -/

theorem contraction_half_failures_Ext_pre_choice_lm_gen {p q α : Type _} {β : Type _} [ms β]
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {x1 x2 : β} :
    X ≠ ∅ →
      (∀ a, distance (failures (Pf a) M1) (failures (Qf a) M2) <= distance x1 x2) →
        distance
            (failures (proc.Ext_pre_choice X Pf) M1)
            (failures (proc.Ext_pre_choice X Qf) M2) * 2 <=
          distance x1 x2 := by
  intro hX hd
  obtain ⟨PQ, hPQ, hdist⟩ :=
    Ext_pre_choice_Act_prefix_distF_nonempty
      (PQs := {PQ | ∃ a, a ∈ X ∧ PQ = (failures (a ~> Pf a) M1, failures (a ~> Qf a) M2)})
      hX rfl
  obtain ⟨a, ha, rfl⟩ := hPQ
  have h1 := contraction_half_failures_Act_prefix_lm (a := a) (P := Pf a) (Q := Qf a)
    (M1 := M1) (M2 := M2)
  have h2 := hd a
  dsimp only at hdist
  linarith

/- (*** contraction_half ***) -/

theorem contraction_half_failures_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (failures (Pf a))) →
      contraction_alpha (failures (proc.Ext_pre_choice X Pf)) (1 / 2 : ℝ) := by
  intro hPf
  by_cases hX : X = ∅
  · subst hX
    refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
    intro M1 M2
    refine le_antisymm (subsetFI ?_) (subsetFI ?_) <;>
      · intro s X0 ht
        rcases in_failures_Ext_pre_choice.mp ht with ⟨Y, hEq, hY⟩ | ⟨a, s', Y, -, -, haX⟩
        · exact in_failures_Ext_pre_choice.mpr (Or.inl ⟨Y, hEq, hY⟩)
        · exact absurd haX (by simp)
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro M1 M2
    have h1 := contraction_half_failures_Ext_pre_choice_lm_gen (X := X) (Pf := Pf) (Qf := Pf)
      (M1 := M1) (M2 := M2) (x1 := M1) (x2 := M2) hX (fun a => by
        have h2 := (hPf a).2 M1 M2
        linarith)
    linarith

/- (*** Ext_pre_choice_evalT_contraction ***) -/

theorem contraction_failures_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (failures (Pf a))) →
      contraction (failures (proc.Ext_pre_choice X Pf)) := by
  intro hPf
  exact ⟨(1 / 2 : ℝ), contraction_half_failures_Ext_pre_choice hPf⟩

/- (*** Ext_pre_choice_evalT_non_expanding ***) -/

theorem non_expanding_failures_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (failures (Pf a))) →
      non_expanding (failures (proc.Ext_pre_choice X Pf)) := by
  intro hPf
  exact contraction_non_expanding (contraction_failures_Ext_pre_choice hPf)

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Ext_choice_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n <= traces P2 (fstF ∘ M2) .|. n →
      traces Q1 (fstF ∘ M1) .|. n <= traces Q2 (fstF ∘ M2) .|. n →
        failures P1 M1 .|. n <= failures P2 M2 .|. n →
          failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
            failures (P1 [+] Q1) M1 .|. n <= failures (P2 [+] Q2) M2 .|. n := by
  intro hT1 hT2 hF1 hF2
  rw [rest_setF_le_iff]
  intro t X0 ht hc
  rcases in_failures_Ext_choice.mp ht with ⟨⟨Y, hEq⟩, hP, hQ⟩ | ⟨s, ⟨Y, hEq⟩, hPQ, hne⟩ |
    ⟨Y, hEq, hTick, hY⟩
  · exact in_failures_Ext_choice.mpr
      (Or.inl ⟨⟨Y, hEq⟩, rest_setF_le_iff.mp hF1 _ _ hP hc, rest_setF_le_iff.mp hF2 _ _ hQ hc⟩)
  · refine in_failures_Ext_choice.mpr (Or.inr (Or.inl ⟨s, ⟨Y, hEq⟩, ?_, hne⟩))
    rcases hPQ with hP | hQ
    · exact Or.inl (rest_setF_le_iff.mp hF1 _ _ hP hc)
    · exact Or.inr (rest_setF_le_iff.mp hF2 _ _ hQ hc)
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨ht1, hX1⟩ := hEq
    subst ht1
    have hpos : 0 < n := restCond_nil_pos hc
    refine in_failures_Ext_choice.mpr (Or.inr (Or.inr ⟨Y, by rw [hX1], ?_, hY⟩))
    rcases hTick with hTP | hTQ
    · exact Or.inl (rest_domT_le_iff.mp hT1 _ hTP (by simp; omega))
    · exact Or.inr (rest_domT_le_iff.mp hT2 _ hTQ (by simp; omega))

/- (*** rest_setF (equal) ***) -/

theorem Ext_choice_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n = traces P2 (fstF ∘ M2) .|. n →
      traces Q1 (fstF ∘ M1) .|. n = traces Q2 (fstF ∘ M2) .|. n →
        failures P1 M1 .|. n = failures P2 M2 .|. n →
          failures Q1 M1 .|. n = failures Q2 M2 .|. n →
            failures (P1 [+] Q1) M1 .|. n = failures (P2 [+] Q2) M2 .|. n := by
  intro hT1 hT2 hF1 hF2
  exact le_antisymm
    (Ext_choice_rest_setF_sub (le_of_eq hT1) (le_of_eq hT2) (le_of_eq hF1) (le_of_eq hF2))
    (Ext_choice_rest_setF_sub (le_of_eq hT1.symm) (le_of_eq hT2.symm) (le_of_eq hF1.symm)
      (le_of_eq hF2.symm))

/- (*** distF lemma ***) -/

theorem Ext_choice_distF {p : Type _} {q : Type _} {α : Type _}
    {PQTs : Set (domTType α × domTType α)} {PQFs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQTs =
      ({(traces P1 (fstF ∘ M1), traces P2 (fstF ∘ M2)),
        (traces Q1 (fstF ∘ M1), traces Q2 (fstF ∘ M2))} :
          Set (domTType α × domTType α)) →
      PQFs =
        ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
          Set (setFType α × setFType α)) →
        (∃ PQ, PQ ∈ PQTs ∧
          distance (failures (P1 [+] Q1) M1) (failures (P2 [+] Q2) M2) <=
            distance (Prod.fst PQ) (Prod.snd PQ)) ∨
          ∃ PQ, PQ ∈ PQFs ∧
            distance (failures (P1 [+] Q1) M1) (failures (P2 [+] Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hT hF
  subst hT
  subst hF
  refine dist_pair_two_sets two_elem_ne two_elem_ne ?_
  intro n hall
  exact Ext_choice_rest_setF (hall.1 _ (Set.mem_insert _ _))
    (hall.1 _ (Set.mem_insert_of_mem _ rfl)) (hall.2 _ (Set.mem_insert _ _))
    (hall.2 _ (Set.mem_insert_of_mem _ rfl))

/- (*** map_alpha F lemma ***) -/

theorem map_alpha_failures_Ext_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 (fstF ∘ M1)) (traces P2 (fstF ∘ M2)) <= alpha * distance x1 x2 →
      distance (traces Q1 (fstF ∘ M1)) (traces Q2 (fstF ∘ M2)) <= alpha * distance x1 x2 →
        distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
          distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
            distance (failures (P1 [+] Q1) M1) (failures (P2 [+] Q2) M2) <=
              alpha * distance x1 x2 := by
  intro h1 h2 h3 h4
  rcases dist_pair_two_sets
      (xps := ({(traces P1 (fstF ∘ M1), traces P2 (fstF ∘ M2)),
        (traces Q1 (fstF ∘ M1), traces Q2 (fstF ∘ M2))} : Set (domTType α × domTType α)))
      (yps := ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)))
      two_elem_ne two_elem_ne
      (fun n hall => Ext_choice_rest_setF (hall.1 _ (Set.mem_insert _ _))
        (hall.1 _ (Set.mem_insert_of_mem _ rfl)) (hall.2 _ (Set.mem_insert _ _))
        (hall.2 _ (Set.mem_insert_of_mem _ rfl))) with ⟨PQ, hPQ, hd⟩ | ⟨PQ, hPQ, hd⟩
  · rcases hPQ with rfl | hPQ
    · exact le_trans hd h1
    · rw [Set.mem_singleton_iff] at hPQ
      subst hPQ
      exact le_trans hd h2
  · rcases hPQ with rfl | hPQ
    · exact le_trans hd h3
    · rw [Set.mem_singleton_iff] at hPQ
      subst hPQ
      exact le_trans hd h4

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (fun M => traces P (fstF ∘ M)) alpha →
      map_alpha (fun M => traces Q (fstF ∘ M)) alpha →
        map_alpha (failures P) alpha →
          map_alpha (failures Q) alpha →
            map_alpha (failures (P [+] Q)) alpha := by
  intro h1 h2 h3 h4
  exact map_alpha_of_rest_four'
    (fun M1 M2 n ha hb hc hd => Ext_choice_rest_setF ha hb hc hd) h1 h2 h3 h4

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (fun M => traces P (fstF ∘ M)) →
      non_expanding (fun M => traces Q (fstF ∘ M)) →
        non_expanding (failures P) →
          non_expanding (failures Q) →
            non_expanding (failures (P [+] Q)) := by
  intro h1 h2 h3 h4
  exact map_alpha_failures_Ext_choice h1 h2 h3 h4

/- (*** contraction ***) -/

theorem contraction_alpha_failures_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (fun M => traces P (fstF ∘ M)) alpha →
      contraction_alpha (fun M => traces Q (fstF ∘ M)) alpha →
        contraction_alpha (failures P) alpha →
          contraction_alpha (failures Q) alpha →
            contraction_alpha (failures (P [+] Q)) alpha := by
  intro h1 h2 h3 h4
  exact ⟨h1.1, map_alpha_failures_Ext_choice h1.2 h2.2 h3.2 h4.2⟩

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Int_choice_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n <= failures P2 M2 .|. n →
      failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
        failures (P1 |~| Q1) M1 .|. n <= failures (P2 |~| Q2) M2 .|. n := by
  intro h1 h2
  rw [rest_setF_le_iff]
  intro t X0 ht hc
  rcases in_failures_Int_choice.mp ht with h | h
  · exact in_failures_Int_choice.mpr (Or.inl (rest_setF_le_iff.mp h1 _ _ h hc))
  · exact in_failures_Int_choice.mpr (Or.inr (rest_setF_le_iff.mp h2 _ _ h hc))

/- (*** rest_setF (equal) ***) -/

theorem Int_choice_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n = failures P2 M2 .|. n →
      failures Q1 M1 .|. n = failures Q2 M2 .|. n →
        failures (P1 |~| Q1) M1 .|. n = failures (P2 |~| Q2) M2 .|. n := by
  intro h1 h2
  exact le_antisymm (Int_choice_rest_setF_sub (le_of_eq h1) (le_of_eq h2))
    (Int_choice_rest_setF_sub (le_of_eq h1.symm) (le_of_eq h2.symm))

/- (*** distF lemma ***) -/

theorem Int_choice_distF {p : Type _} {q : Type _} {α : Type _}
    {PQs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQs =
      ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (P1 |~| Q1) M1) (failures (P2 |~| Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  refine dist_pair_one_set two_elem_ne ?_
  intro n hall
  exact Int_choice_rest_setF (hall _ (Set.mem_insert _ _))
    (hall _ (Set.mem_insert_of_mem _ rfl))

/- (*** map_alpha F lemma ***) -/

theorem map_alpha_failures_Int_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
      distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
        distance (failures (P1 |~| Q1) M1) (failures (P2 |~| Q2) M2) <=
          alpha * distance x1 x2 := by
  intro h1 h2
  obtain ⟨PQ, hPQ, hd⟩ := Int_choice_distF
    (PQs := ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
      Set (setFType α × setFType α))) rfl
  rcases hPQ with rfl | hPQ
  · exact le_trans hd h1
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hd h2

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures Q) alpha →
        map_alpha (failures (P |~| Q)) alpha := by
  intro h1 h2
  exact map_alpha_of_rest_two' (fun M1 M2 n ha hb => Int_choice_rest_setF ha hb) h1 h2

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (failures P) →
      non_expanding (failures Q) →
        non_expanding (failures (P |~| Q)) := by
  intro h1 h2
  exact map_alpha_failures_Int_choice h1 h2

/- (*** contraction ***) -/

theorem contraction_alpha_failures_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures Q) alpha →
        contraction_alpha (failures (P |~| Q)) alpha := by
  intro h1 h2
  exact ⟨h1.1, map_alpha_failures_Int_choice h1.2 h2.2⟩

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem Rep_int_choice_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ c ∈ sumset C, failures (Pf c) M1 .|. n <= failures (Qf c) M2 .|. n) →
      failures (proc.Rep_int_choice C Pf) M1 .|. n <= failures (proc.Rep_int_choice C Qf) M2 .|. n
        := by
  intro h
  rw [rest_setF_le_iff]
  intro t X0 ht hc
  obtain ⟨c, hcC, ht'⟩ := in_failures_Rep_int_choice_sum.mp ht
  exact in_failures_Rep_int_choice_sum.mpr
    ⟨c, hcC, rest_setF_le_iff.mp (h c hcC) _ _ ht' hc⟩

/- (*** rest_setF (equal) ***) -/

theorem Rep_int_choice_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ c ∈ sumset C, failures (Pf c) M1 .|. n = failures (Qf c) M2 .|. n) →
      failures (proc.Rep_int_choice C Pf) M1 .|. n = failures (proc.Rep_int_choice C Qf) M2 .|. n
        := by
  intro h
  refine le_antisymm (Rep_int_choice_rest_setF_sub ?_) (Rep_int_choice_rest_setF_sub ?_)
  · intro c hc
    exact le_of_eq (h c hc)
  · intro c hc
    exact le_of_eq (h c hc).symm

/- (*** distF lemma ***) -/

theorem Rep_int_choice_distF_nonempty {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {PQs : Set (setFType α × setFType α)}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      PQs = {PQ | ∃ c, c ∈ sumset C ∧ PQ = (failures (Pf c) M1, failures (Qf c) M2)} →
        ∃ PQ, PQ ∈ PQs ∧
          distance
              (failures (proc.Rep_int_choice C Pf) M1)
              (failures (proc.Rep_int_choice C Qf) M2) <=
            distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hC hPQs
  have hne : PQs ≠ ∅ := by
    obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.mpr hC
    intro h0
    have hmem : (failures (Pf c) M1, failures (Qf c) M2) ∈ PQs := by
      rw [hPQs]
      exact ⟨c, hc, rfl⟩
    rw [h0] at hmem
    exact hmem
  refine dist_pair_one_set hne ?_
  intro n hall
  refine Rep_int_choice_rest_setF ?_
  intro c hc
  exact hall (failures (Pf c) M1, failures (Qf c) M2) (by rw [hPQs]; exact ⟨c, hc, rfl⟩)

/- (*** map_alpha F lemma ***) -/

theorem map_alpha_failures_Rep_int_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {C : sets_nats α}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    sumset C ≠ ∅ →
      (∀ c, distance (failures (Pf c) M1) (failures (Qf c) M2) <= alpha * distance x1 x2) →
        distance
            (failures (proc.Rep_int_choice C Pf) M1)
            (failures (proc.Rep_int_choice C Qf) M2) <=
          alpha * distance x1 x2 := by
  intro hC hd
  obtain ⟨PQ, hPQ, hdist⟩ :=
    Rep_int_choice_distF_nonempty
      (PQs := {PQ | ∃ c, c ∈ sumset C ∧ PQ = (failures (Pf c) M1, failures (Qf c) M2)}) hC rfl
  obtain ⟨c, hc, rfl⟩ := hPQ
  dsimp only at hdist
  exact le_trans hdist (hd c)

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, map_alpha (failures (Pf c)) alpha) →
      map_alpha (failures (proc.Rep_int_choice C Pf)) alpha := by
  intro hPf
  refine ⟨(hPf (type2 0)).1, ?_⟩
  intro M1 M2
  by_cases hC : sumset C = ∅
  · have hconst : failures (proc.Rep_int_choice C Pf) M1 =
        failures (proc.Rep_int_choice C Pf) M2 := by
      refine le_antisymm (subsetFI ?_) (subsetFI ?_) <;>
        · intro s X0 ht
          obtain ⟨c, hc, -⟩ := in_failures_Rep_int_choice_sum.mp ht
          rw [hC] at hc
          exact hc.elim
    rw [hconst, same_pnt_zero]
    exact mul_nonneg (hPf (type2 0)).1 (ms.positive_ms M1 M2)
  · exact map_alpha_failures_Rep_int_choice_lm hC (fun c => (hPf c).2 M1 M2)

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, non_expanding (failures (Pf c))) →
      non_expanding (failures (proc.Rep_int_choice C Pf)) := by
  intro hPf
  exact map_alpha_failures_Rep_int_choice hPf

/- (*** Rep_int_choice_evalT_contraction_alpha ***) -/

theorem contraction_alpha_failures_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, contraction_alpha (failures (Pf c)) alpha) →
      contraction_alpha (failures (proc.Rep_int_choice C Pf)) alpha := by
  intro hPf
  exact ⟨(hPf (type2 0)).1, map_alpha_failures_Rep_int_choice (fun c => (hPf c).2)⟩

/- --------------------------------*
 |              IF                |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem IF_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n <= failures P2 M2 .|. n →
      failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
        failures (IF b THEN P1 ELSE Q1) M1 .|. n <= failures (IF b THEN P2 ELSE Q2) M2 .|. n := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- (*** rest_setF (equal) ***) -/

theorem IF_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n = failures P2 M2 .|. n →
      failures Q1 M1 .|. n = failures Q2 M2 .|. n →
        failures (IF b THEN P1 ELSE Q1) M1 .|. n = failures (IF b THEN P2 ELSE Q2) M2 .|. n := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- (*** distF lemma ***) -/

theorem IF_distF {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {PQs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQs =
      ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (IF b THEN P1 ELSE Q1) M1) (failures (IF b THEN P2 ELSE Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  refine dist_pair_one_set two_elem_ne ?_
  intro n hall
  exact IF_rest_setF (hall _ (Set.mem_insert _ _)) (hall _ (Set.mem_insert_of_mem _ rfl))

/- (*** map_alpha F lemma ***) -/

theorem map_alpha_failures_IF_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
      distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
        distance (failures (IF b THEN P1 ELSE Q1) M1) (failures (IF b THEN P2 ELSE Q2) M2) <=
          alpha * distance x1 x2 := by
  intro h1 h2
  obtain ⟨PQ, hPQ, hd⟩ := IF_distF (b := b)
    (PQs := ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
      Set (setFType α × setFType α))) rfl
  rcases hPQ with rfl | hPQ
  · exact le_trans hd h1
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hd h2

/- (*** map_alpha ***) -/

theorem map_alpha_failures_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures Q) alpha →
        map_alpha (failures (IF b THEN P ELSE Q)) alpha := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- (*** non_expanding ***) -/

theorem non_expanding_failures_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} :
    non_expanding (failures P) →
      non_expanding (failures Q) →
        non_expanding (failures (IF b THEN P ELSE Q)) := by
  intro h1 h2
  exact map_alpha_failures_IF h1 h2

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_failures_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures Q) alpha →
        contraction_alpha (failures (IF b THEN P ELSE Q)) alpha := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem Parallel_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n <= failures P2 M2 .|. n →
      failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
        failures (P1 |[X]| Q1) M1 .|. n <= failures (P2 |[X]| Q2) M2 .|. n := by
  intro h1 h2
  rw [rest_setF_le_iff]
  intro u X0 hu hc
  obtain ⟨u', Y, Z, hEq, hdiff, s, t, hpar, hs, ht⟩ := in_failures_Parallel.mp hu
  rw [Prod.mk.injEq] at hEq
  obtain ⟨hu1, hX1⟩ := hEq
  subst hu1
  subst hX1
  exact in_failures_Parallel.mpr ⟨_, Y, Z, rfl, hdiff, s, t, hpar,
    rest_setF_le_iff.mp h1 _ _ hs (restCond_par_left hpar hc),
    rest_setF_le_iff.mp h2 _ _ ht (restCond_par_right hpar hc)⟩

/- (*** rest_setF (equal) ***) -/

theorem Parallel_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n = failures P2 M2 .|. n →
      failures Q1 M1 .|. n = failures Q2 M2 .|. n →
        failures (P1 |[X]| Q1) M1 .|. n = failures (P2 |[X]| Q2) M2 .|. n := by
  intro h1 h2
  exact le_antisymm (Parallel_rest_setF_sub (le_of_eq h1) (le_of_eq h2))
    (Parallel_rest_setF_sub (le_of_eq h1.symm) (le_of_eq h2.symm))

/- (*** distF lemma ***) -/

theorem Parallel_distF {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQs =
      ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (P1 |[X]| Q1) M1) (failures (P2 |[X]| Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  refine dist_pair_one_set two_elem_ne ?_
  intro n hall
  exact Parallel_rest_setF (hall _ (Set.mem_insert _ _)) (hall _ (Set.mem_insert_of_mem _ rfl))

/- (*** map_alpha F lemma ***) -/

theorem map_alpha_failures_Parallel_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
      distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
        distance (failures (P1 |[X]| Q1) M1) (failures (P2 |[X]| Q2) M2) <=
          alpha * distance x1 x2 := by
  intro h1 h2
  obtain ⟨PQ, hPQ, hd⟩ := Parallel_distF (X := X)
    (PQs := ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
      Set (setFType α × setFType α))) rfl
  rcases hPQ with rfl | hPQ
  · exact le_trans hd h1
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hd h2

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures Q) alpha →
        map_alpha (failures (P |[X]| Q)) alpha := by
  intro h1 h2
  exact map_alpha_of_rest_two' (fun M1 M2 n ha hb => Parallel_rest_setF ha hb) h1 h2

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} :
    non_expanding (failures P) →
      non_expanding (failures Q) →
        non_expanding (failures (P |[X]| Q)) := by
  intro h1 h2
  exact map_alpha_failures_Parallel h1 h2

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_failures_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures Q) alpha →
        contraction_alpha (failures (P |[X]| Q)) alpha := by
  intro h1 h2
  exact ⟨h1.1, map_alpha_failures_Parallel h1.2 h2.2⟩

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- cms rules for Hiding is not necessary
   because processes are guarded. -/

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem Renaming_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P M1 .|. n <= failures Q M2 .|. n →
      failures (P [[r]]) M1 .|. n <= failures (Q [[r]]) M2 .|. n := by
  intro h
  rw [rest_setF_le_iff]
  intro t X0 ht hc
  obtain ⟨s, t', X', hEq, hren, hs⟩ := in_failures_Renaming.mp ht
  rw [Prod.mk.injEq] at hEq
  obtain ⟨ht1, hX1⟩ := hEq
  subst ht1
  subst hX1
  exact in_failures_Renaming.mpr ⟨s, _, _, rfl, hren,
    rest_setF_le_iff.mp h _ _ hs (restCond_ren hren hc)⟩

/- (*** rest_setF (equal) ***) -/

theorem Renaming_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P M1 .|. n = failures Q M2 .|. n →
      failures (P [[r]]) M1 .|. n = failures (Q [[r]]) M2 .|. n := by
  intro h
  exact le_antisymm (Renaming_rest_setF_sub (le_of_eq h))
    (Renaming_rest_setF_sub (le_of_eq h.symm))

/- (*** distF lemma ***) -/

theorem Renaming_distF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    distance (failures (P [[r]]) M1) (failures (Q [[r]]) M2) <=
      distance (failures P M1) (failures Q M2) := by
  rw [setF_distance_def, setF_distance_def]
  exact rest_distance_subset (fun n h => Renaming_rest_setF h)

/- (*** map_alphaT lemma ***) -/

theorem map_alpha_failures_Renaming_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P M1) (failures Q M2) <= alpha * distance x1 x2 →
      distance (failures (P [[r]]) M1) (failures (Q [[r]]) M2) <= alpha * distance x1 x2 := by
  intro h
  exact le_trans Renaming_distF h

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures (P [[r]])) alpha := by
  intro h
  exact map_alpha_of_rest_one' (fun M1 M2 n hn => Renaming_rest_setF hn) h

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} :
    non_expanding (failures P) →
      non_expanding (failures (P [[r]])) := by
  intro h
  exact map_alpha_failures_Renaming h

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_failures_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures (P [[r]])) alpha := by
  intro h
  exact ⟨h.1, map_alpha_failures_Renaming h.2⟩

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem Seq_compo_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n <= traces P2 (fstF ∘ M2) .|. n →
      failures P1 M1 .|. n <= failures P2 M2 .|. n →
        failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
          failures (P1 ;; Q1) M1 .|. n <= failures (P2 ;; Q2) M2 .|. n := by
  intro hT hF1 hF2
  rw [rest_setF_le_iff]
  intro u X0 hu hc
  rcases in_failures_Seq_compo.mp hu with ⟨t, Y, hEq, ht, hnt⟩ | ⟨s, t, Y, hEq, hTick, ht, hns⟩
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hu1, hX1⟩ := hEq
    subst hu1
    subst hX1
    exact in_failures_Seq_compo.mpr
      (Or.inl ⟨_, _, rfl, rest_setF_le_iff.mp hF1 _ _ ht hc, hnt⟩)
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hu1, hX1⟩ := hEq
    subst hu1
    subst hX1
    refine in_failures_Seq_compo.mpr (Or.inr ⟨s, t, _, rfl, ?_, ?_, hns⟩)
    · refine rest_domT_le_iff.mp hT _ hTick ?_
      rw [lengtht_app_event_Suc_last hns]
      have h0 := restCond_Tick_len hns hc
      omega
    · exact rest_setF_le_iff.mp hF2 _ _ ht (restCond_appt_right hns hc (by omega))

/- (*** rest_setF (equal) ***) -/

theorem Seq_compo_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n = traces P2 (fstF ∘ M2) .|. n →
      failures P1 M1 .|. n = failures P2 M2 .|. n →
        failures Q1 M1 .|. n = failures Q2 M2 .|. n →
          failures (P1 ;; Q1) M1 .|. n = failures (P2 ;; Q2) M2 .|. n := by
  intro hT hF1 hF2
  exact le_antisymm
    (Seq_compo_rest_setF_sub (le_of_eq hT) (le_of_eq hF1) (le_of_eq hF2))
    (Seq_compo_rest_setF_sub (le_of_eq hT.symm) (le_of_eq hF1.symm) (le_of_eq hF2.symm))

/- (*** distF lemma ***) -/

theorem Seq_compo_distF {p : Type _} {q : Type _} {α : Type _}
    {PQTs : Set (domTType α × domTType α)} {PQFs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQTs = ({(traces P1 (fstF ∘ M1), traces P2 (fstF ∘ M2))} : Set (domTType α × domTType α)) →
      PQFs =
        ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
          Set (setFType α × setFType α)) →
        (∃ PQ, PQ ∈ PQTs ∧
          distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) <=
            distance (Prod.fst PQ) (Prod.snd PQ)) ∨
          ∃ PQ, PQ ∈ PQFs ∧
            distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hT hF
  subst hT
  subst hF
  refine dist_pair_two_sets one_elem_ne two_elem_ne ?_
  intro n hall
  exact Seq_compo_rest_setF (hall.1 _ rfl) (hall.2 _ (Set.mem_insert _ _))
    (hall.2 _ (Set.mem_insert_of_mem _ rfl))

/- (*** map_alpha F lemma ***) -/

theorem map_alpha_failures_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 (fstF ∘ M1)) (traces P2 (fstF ∘ M2)) <= alpha * distance x1 x2 →
      distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
        distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
          distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) <=
            alpha * distance x1 x2 := by
  intro h1 h2 h3
  rcases dist_pair_two_sets
      (xps := ({(traces P1 (fstF ∘ M1), traces P2 (fstF ∘ M2))} : Set (domTType α × domTType α)))
      (yps := ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)))
      one_elem_ne two_elem_ne
      (fun n hall => Seq_compo_rest_setF (hall.1 _ rfl) (hall.2 _ (Set.mem_insert _ _))
        (hall.2 _ (Set.mem_insert_of_mem _ rfl))) with ⟨PQ, hPQ, hd⟩ | ⟨PQ, hPQ, hd⟩
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hd h1
  · rcases hPQ with rfl | hPQ
    · exact le_trans hd h2
    · rw [Set.mem_singleton_iff] at hPQ
      subst hPQ
      exact le_trans hd h3

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (fun M => traces P (fstF ∘ M)) alpha →
      map_alpha (failures P) alpha →
        map_alpha (failures Q) alpha →
          map_alpha (failures (P ;; Q)) alpha := by
  intro h1 h2 h3
  exact map_alpha_of_rest_three'
    (fun M1 M2 n ha hb hcc => Seq_compo_rest_setF ha hb hcc) h1 h2 h3

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (fun M => traces P (fstF ∘ M)) →
      non_expanding (failures P) →
        non_expanding (failures Q) →
          non_expanding (failures (P ;; Q)) := by
  intro h1 h2 h3
  exact map_alpha_failures_Seq_compo h1 h2 h3

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (fun M => traces P (fstF ∘ M)) alpha →
      contraction_alpha (failures P) alpha →
        contraction_alpha (failures Q) alpha →
          contraction_alpha (failures (P ;; Q)) alpha := by
  intro h1 h2 h3
  exact ⟨h1.1, map_alpha_failures_Seq_compo h1.2 h2.2 h3.2⟩

/- --------------------------------*
 |       Seq_compo  (gSKIP)       |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

theorem gSKIP_Seq_compo_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. Nat.succ n <= traces P2 (fstF ∘ M2) .|. Nat.succ n →
      failures P1 M1 .|. Nat.succ n <= failures P2 M2 .|. Nat.succ n →
        failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 (fstF ∘ M1)) →
            ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 (fstF ∘ M2)) →
              failures (P1 ;; Q1) M1 .|. Nat.succ n <= failures (P2 ;; Q2) M2 .|. Nat.succ n := by
  intro hT hF1 hF2 hT1 _
  rw [rest_setF_le_iff]
  intro u X0 hu hc
  rcases in_failures_Seq_compo.mp hu with ⟨t, Y, hEq, ht, hnt⟩ | ⟨s, t, Y, hEq, hTick, ht, hns⟩
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hu1, hX1⟩ := hEq
    subst hu1
    subst hX1
    exact in_failures_Seq_compo.mpr
      (Or.inl ⟨_, _, rfl, rest_setF_le_iff.mp hF1 _ _ ht hc, hnt⟩)
  · rw [Prod.mk.injEq] at hEq
    obtain ⟨hu1, hX1⟩ := hEq
    subst hu1
    subst hX1
    have hsne : s ≠ <> := by
      intro h0
      subst h0
      rw [appt_nil_left] at hTick
      exact hT1 hTick
    have hls : 1 <= lengtht s := by
      rcases Nat.eq_zero_or_pos (lengtht s) with h0 | h0
      · exact absurd (lengtht_zero.mp h0) hsne
      · exact h0
    refine in_failures_Seq_compo.mpr (Or.inr ⟨s, t, _, rfl, ?_, ?_, hns⟩)
    · refine rest_domT_le_iff.mp hT _ hTick ?_
      rw [lengtht_app_event_Suc_last hns]
      have h0 := restCond_Tick_len hns hc
      omega
    · exact rest_setF_le_iff.mp hF2 _ _ ht (restCond_appt_right hns hc (by omega))

/- (*** rest_setF (equal) ***) -/

theorem gSKIP_Seq_compo_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. Nat.succ n = traces P2 (fstF ∘ M2) .|. Nat.succ n →
      failures P1 M1 .|. Nat.succ n = failures P2 M2 .|. Nat.succ n →
        failures Q1 M1 .|. n = failures Q2 M2 .|. n →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 (fstF ∘ M1)) →
            ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 (fstF ∘ M2)) →
              failures (P1 ;; Q1) M1 .|. Nat.succ n = failures (P2 ;; Q2) M2 .|. Nat.succ n := by
  intro hT hF1 hF2 hT1 hT2
  exact le_antisymm
    (gSKIP_Seq_compo_rest_setF_sub (le_of_eq hT) (le_of_eq hF1) (le_of_eq hF2) hT1 hT2)
    (gSKIP_Seq_compo_rest_setF_sub (le_of_eq hT.symm) (le_of_eq hF1.symm) (le_of_eq hF2.symm)
      hT2 hT1)

/- (*** map_alpha F lemma ***) -/

theorem gSKIP_map_alpha_failures_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    distance (traces P1 (fstF ∘ M1)) (traces P2 (fstF ∘ M2)) * 2 <= (1 / 2 : ℝ) ^ n →
      distance (failures P1 M1) (failures P2 M2) * 2 <= (1 / 2 : ℝ) ^ n →
        distance (failures Q1 M1) (failures Q2 M2) <= (1 / 2 : ℝ) ^ n →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 (fstF ∘ M1)) →
            ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 (fstF ∘ M2)) →
              distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) * 2 <=
                (1 / 2 : ℝ) ^ n := by
  intro h1 h2 h3 hT1 hT2
  have hp : ((1 : ℝ) / 2) ^ Nat.succ n = ((1 : ℝ) / 2) ^ n * (1 / 2) := pow_succ _ _
  have e1 : traces P1 (fstF ∘ M1) .|. Nat.succ n = traces P2 (fstF ∘ M2) .|. Nat.succ n := by
    refine distance_rs_le_1_if ?_
    rw [← domT_distance_def, hp]
    linarith
  have e2 : failures P1 M1 .|. Nat.succ n = failures P2 M2 .|. Nat.succ n := by
    refine distance_rs_le_1_if ?_
    rw [← setF_distance_def, hp]
    linarith
  have e3 : failures Q1 M1 .|. n = failures Q2 M2 .|. n := by
    refine distance_rs_le_1_if ?_
    rw [← setF_distance_def]
    exact h3
  have h4 := distance_rs_le_1_only_if (gSKIP_Seq_compo_rest_setF e1 e2 e3 hT1 hT2)
  rw [← setF_distance_def, hp] at h4
  linarith

/- (*** map_alpha ***) -/

theorem gSKIP_contraction_half_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    contraction_alpha (fun M => traces P (fstF ∘ M)) (1 / 2 : ℝ) →
      contraction_alpha (failures P) (1 / 2 : ℝ) →
        non_expanding (failures Q) →
          gSKIP P →
            contraction_alpha (failures (P ;; Q)) (1 / 2 : ℝ) := by
  intro hTP hP hQ hg
  rw [contraction_half_iff_constructive]
  intro M1 M2 n hM
  exact gSKIP_Seq_compo_rest_setF
    (contraction_half_iff_constructive.mp hTP M1 M2 n hM)
    (contraction_half_iff_constructive.mp hP M1 M2 n hM)
    (non_expanding_iff_rest.mp hQ M1 M2 n hM)
    (gSKIP_to_Tick_notin_traces P (fstF ∘ M1) hg)
    (gSKIP_to_Tick_notin_traces P (fstF ∘ M2) hg)

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** rest_setF (equal) ***) -/

theorem Depth_rest_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m n : Nat}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    failures P M1 .|. n = failures Q M2 .|. n →
      failures (P |. m) M1 .|. n = failures (Q |. m) M2 .|. n := by
  intro h
  rw [rest_setF_eq_iff_le] at h ⊢
  intro s X0 hc
  constructor
  · intro hs
    obtain ⟨hs1, hcm⟩ := in_rest_setF.mp hs
    exact in_rest_setF.mpr ⟨(h s X0 hc).mp hs1, hcm⟩
  · intro hs
    obtain ⟨hs1, hcm⟩ := in_rest_setF.mp hs
    exact in_rest_setF.mpr ⟨(h s X0 hc).mpr hs1, hcm⟩

/- (*** distF lemma ***) -/

theorem Depth_rest_distF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    distance (failures (P |. m) M1) (failures (Q |. m) M2) <=
      distance (failures P M1) (failures Q M2) := by
  rw [setF_distance_def, setF_distance_def]
  exact rest_distance_subset (fun n h => Depth_rest_rest_setF h)

/- (*** map_alphaT lemma ***) -/

theorem map_alpha_failures_Depth_rest_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P M1) (failures Q M2) <= alpha * distance x1 x2 →
      distance (failures (P |. m) M1) (failures (Q |. m) M2) <= alpha * distance x1 x2 := by
  intro h
  exact le_trans Depth_rest_distF h

/- (*** map_alpha ***) -/

theorem map_alpha_failures_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {n : Nat} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures (P |. n)) alpha := by
  intro h
  exact map_alpha_of_rest_one' (fun M1 M2 n hn => Depth_rest_rest_setF hn) h

/- (*** non_expanding ***) -/

theorem non_expanding_failures_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {n : Nat} :
    non_expanding (failures P) →
      non_expanding (failures (P |. n)) := by
  intro h
  exact map_alpha_failures_Depth_rest h

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_failures_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {n : Nat} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures (P |. n)) alpha := by
  intro h
  exact ⟨h.1, map_alpha_failures_Depth_rest h.2⟩

/- --------------------------------*
 |            variable            |
 *-------------------------------- -/

/- (*** non_expanding ***) -/

theorem non_expanding_failures_variable_lm {p : Type _} {α : Type _} {p0 : p} :
    non_expanding (fun M : p → domFType α => sndF (M p0)) := by
  exact compo_non_expand (f := (sndF : domFType α → setFType α))
    (g := (proj_fun p0 : (p → domFType α) → domFType α)) non_expanding_sndF
    (proj_non_expand p0)

theorem non_expanding_failures_variable {p : Type _} {α : Type _} {p0 : p} :
    non_expanding (failures (proc.Proc_name p0 : proc p α)) := by
  exact non_expanding_failures_variable_lm

/- --------------------------------*
 |            Procfun             |
 *-------------------------------- -/

/- (*****************************************************************
 |                         non_expanding                         |
 *****************************************************************) -/

theorem non_expanding_failures_lm {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (failures P) := by
  induction P with
  | STOP =>
      intro _
      exact non_expanding_failures_STOP
  | SKIP =>
      intro _
      exact non_expanding_failures_SKIP
  | DIV =>
      intro _
      exact non_expanding_failures_DIV
  | Act_prefix a P ih =>
      intro h
      exact non_expanding_failures_Act_prefix (ih h)
  | Ext_pre_choice X Pf ih =>
      intro h
      exact non_expanding_failures_Ext_pre_choice (fun a => ih a (h a))
  | Ext_choice P Q ihP ihQ =>
      intro h
      exact non_expanding_failures_Ext_choice (non_expanding_traces_fstF h.1)
        (non_expanding_traces_fstF h.2) (ihP h.1) (ihQ h.2)
  | Int_choice P Q ihP ihQ =>
      intro h
      exact non_expanding_failures_Int_choice (ihP h.1) (ihQ h.2)
  | Rep_int_choice C Pf ih =>
      intro h
      exact non_expanding_failures_Rep_int_choice (fun c => ih c (h c))
  | «IF» b P Q ihP ihQ =>
      intro h
      exact non_expanding_failures_IF (ihP h.1) (ihQ h.2)
  | Parallel P X Q ihP ihQ =>
      intro h
      exact non_expanding_failures_Parallel (ihP h.1) (ihQ h.2)
  | Hiding P X ih =>
      intro h
      obtain ⟨F, hF⟩ := failures_noPN_Constant h
      refine map_alpha_of_const (by norm_num) ?_
      intro M1 M2
      have hFM : failures P M1 = failures P M2 := by rw [hF]
      simp only [failures, hFM]
  | Renaming P r ih =>
      intro h
      exact non_expanding_failures_Renaming (ih h)
  | Seq_compo P Q ihP ihQ =>
      intro h
      exact non_expanding_failures_Seq_compo (non_expanding_traces_fstF h.1) (ihP h.1)
        (ihQ h.2)
  | Depth_rest P n ih =>
      intro h
      rcases h with h | h
      · exact non_expanding_failures_Depth_rest (ih h)
      · subst h
        refine map_alpha_of_const (by norm_num) ?_
        intro M1 M2
        simp only [failures]
        exact zero_eq_rs_setF _ _
  | Proc_name pn =>
      intro _
      exact non_expanding_failures_variable

theorem non_expanding_failures {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (failures P) := by
  exact non_expanding_failures_lm

/- =============================================================*
 |                          [[P]]Ff                            |
 *============================================================= -/

theorem non_expanding_semFf {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (semFf P) := by
  intro h
  refine non_expanding_iff_rest.mpr ?_
  intro M1 M2 n hM
  refine (eqF_decompo).mpr ⟨?_, ?_⟩
  · rw [fstF_rest, fstF_rest, fstF_semFf, fstF_semFf]
    exact non_expanding_iff_rest.mp (non_expanding_traces_fstF h) M1 M2 n hM
  · rw [sndF_rest, sndF_rest, sndF_semFf, sndF_semFf]
    exact non_expanding_iff_rest.mp (non_expanding_failures h) M1 M2 n hM

/- =============================================================*
 |                         [[P]]Ffun                           |
 *============================================================= -/

theorem non_expanding_semFfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    noHidefun Pf → non_expanding (semFfun Pf) := by
  intro hPf
  rcases isEmpty_or_nonempty p with hp | hp
  · refine map_alpha_of_const (by norm_num) ?_
    intro x y
    have hxy : x = y := funext (fun i => (IsEmpty.false i).elim)
    rw [hxy]
  · refine prod_non_expand_if ?_
    intro i
    exact non_expanding_semFf (hPf i)

/- (*****************************************************************
 |                         contraction                           |
 *****************************************************************) -/

theorem contraction_alpha_failures_lm {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (failures P) (1 / 2 : ℝ) := by
  induction P with
  | STOP =>
      intro _
      exact contraction_alpha_failures_STOP (by norm_num) (by norm_num)
  | SKIP =>
      intro _
      exact contraction_alpha_failures_SKIP (by norm_num) (by norm_num)
  | DIV =>
      intro _
      exact contraction_alpha_failures_DIV (by norm_num) (by norm_num)
  | Act_prefix a P ih =>
      intro h
      exact contraction_half_failures_Act_prefix (non_expanding_failures h)
  | Ext_pre_choice X Pf ih =>
      intro h
      exact contraction_half_failures_Ext_pre_choice (fun a => non_expanding_failures (h a))
  | Ext_choice P Q ihP ihQ =>
      intro h
      exact contraction_alpha_failures_Ext_choice (contraction_alpha_traces_fstF h.1)
        (contraction_alpha_traces_fstF h.2) (ihP h.1) (ihQ h.2)
  | Int_choice P Q ihP ihQ =>
      intro h
      exact contraction_alpha_failures_Int_choice (ihP h.1) (ihQ h.2)
  | Rep_int_choice C Pf ih =>
      intro h
      exact contraction_alpha_failures_Rep_int_choice (fun c => ih c (h c))
  | «IF» b P Q ihP ihQ =>
      intro h
      exact contraction_alpha_failures_IF (ihP h.1) (ihQ h.2)
  | Parallel P X Q ihP ihQ =>
      intro h
      exact contraction_alpha_failures_Parallel (ihP h.1) (ihQ h.2)
  | Hiding P X ih =>
      intro h
      obtain ⟨F, hF⟩ := failures_noPN_Constant h
      refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
      intro M1 M2
      have hFM : failures P M1 = failures P M2 := by rw [hF]
      simp only [failures, hFM]
  | Renaming P r ih =>
      intro h
      exact contraction_alpha_failures_Renaming (ih h)
  | Seq_compo P Q ihP ihQ =>
      intro h
      rcases h with ⟨hgP, hsP, hnQ⟩ | ⟨hgP, hgQ⟩
      · exact gSKIP_contraction_half_failures_Seq_compo (contraction_alpha_traces_fstF hgP)
          (ihP hgP) (non_expanding_failures hnQ) hsP
      · exact contraction_alpha_failures_Seq_compo (contraction_alpha_traces_fstF hgP)
          (ihP hgP) (ihQ hgQ)
  | Depth_rest P n ih =>
      intro h
      rcases h with h | h
      · exact contraction_alpha_failures_Depth_rest (ih h)
      · subst h
        refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
        intro M1 M2
        simp only [failures]
        exact zero_eq_rs_setF _ _
  | Proc_name pn =>
      intro h
      exact h.elim

theorem contraction_alpha_failures {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (failures P) (1 / 2 : ℝ) := by
  exact contraction_alpha_failures_lm

/- =============================================================*
 |                          [[P]]Ff                            |
 *============================================================= -/

theorem contraction_alpha_semFf {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (semFf P) (1 / 2 : ℝ) := by
  intro h
  rw [contraction_half_iff_constructive]
  intro M1 M2 n hM
  refine (eqF_decompo).mpr ⟨?_, ?_⟩
  · rw [fstF_rest, fstF_rest, fstF_semFf, fstF_semFf]
    exact contraction_half_iff_constructive.mp (contraction_alpha_traces_fstF h) M1 M2 n hM
  · rw [sndF_rest, sndF_rest, sndF_semFf, sndF_semFf]
    exact contraction_half_iff_constructive.mp (contraction_alpha_failures h) M1 M2 n hM

/- =============================================================*
 |                         [[P]]Ffun                           |
 *============================================================= -/

theorem contraction_alpha_semFfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction_alpha (semFfun Pf) (1 / 2 : ℝ) := by
  intro hPf
  rcases isEmpty_or_nonempty p with hp | hp
  · refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
    intro x y
    have hxy : x = y := funext (fun i => (IsEmpty.false i).elim)
    rw [hxy]
  · refine prod_contra_alpha_if ?_
    intro i
    exact contraction_alpha_semFf (hPf i)

/- =============================================================*
 |                        contraction                          |
 *============================================================= -/

theorem contraction_semFfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction (semFfun Pf) := by
  intro hPf
  exact ⟨(1 / 2 : ℝ), contraction_alpha_semFfun hPf⟩

end
