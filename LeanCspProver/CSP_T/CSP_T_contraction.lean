           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
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

import LeanCspProver.CSP_T.CSP_T_traces
import LeanCspProver.CSP.RS_prod

open SumType

noncomputable section

/-
(*****************************************************************

         1. contraction traces
         2. contraction [[ ]]Tfun

 *****************************************************************)
-/

/- (*** Lean port helpers ***) -/

theorem rest_domT_le_iff {α : Type _} {T S : domTType α} {n : Nat} :
    (T .|. n ≤ S .|. n) ↔ ∀ s, s :t T → lengtht s ≤ n → s :t S := by
  constructor
  · intro h s hs hlen
    exact (in_rest_domT.mp (memT_subdomT (in_rest_domT.mpr ⟨hs, hlen⟩) h)).1
  · intro h
    refine subdomTI ?_
    intro s hs
    obtain ⟨hs1, hlen⟩ := in_rest_domT.mp hs
    exact in_rest_domT.mpr ⟨h s hs1 hlen, hlen⟩

theorem rest_domT_eq_iff_le {α : Type _} {T S : domTType α} {n : Nat} :
    (T .|. n = S .|. n) ↔ ∀ s, lengtht s ≤ n → (s :t T ↔ s :t S) := by
  constructor
  · intro h s hlen
    exact ⟨fun hs => rest_domT_le_iff.mp (le_of_eq h) s hs hlen,
      fun hs => rest_domT_le_iff.mp (le_of_eq h.symm) s hs hlen⟩
  · intro h
    exact le_antisymm (rest_domT_le_iff.mpr (fun s hs hlen => (h s hlen).mp hs))
      (rest_domT_le_iff.mpr (fun s hs hlen => (h s hlen).mpr hs))

theorem map_alpha_of_const {β γ : Type _} [ms β] [ms γ] {f : β → γ} {alpha : ℝ} :
    0 ≤ alpha → (∀ x y, f x = f y) → map_alpha f alpha := by
  intro halpha hconst
  refine ⟨halpha, ?_⟩
  intro x y
  rw [hconst x y, same_pnt_zero]
  exact mul_nonneg halpha (ms.positive_ms x y)

theorem distT_pair_two {α : Type _} {T1 T2 S1 S2 z1 z2 : domTType α} :
    (∀ n, T1 .|. n = T2 .|. n → S1 .|. n = S2 .|. n → z1 .|. n = z2 .|. n) →
      ∃ PQ ∈ ({(T1, T2), (S1, S2)} : Set (domTType α × domTType α)),
        distance z1 z2 <= distance PQ.1 PQ.2 := by
  intro hrest
  have hne : ({(T1, T2), (S1, S2)} : Set (domTType α × domTType α)) ≠ ∅ := by
    intro h0
    have hmem : (T1, T2) ∈ ({(T1, T2), (S1, S2)} : Set (domTType α × domTType α)) :=
      Set.mem_insert _ _
    rw [h0] at hmem
    exact hmem
  have hkey : ∀ n, (∀ x ∈ ({(T1, T2), (S1, S2)} : Set (domTType α × domTType α)),
      x.1 .|. n = x.2 .|. n) → z1 .|. n = z2 .|. n := by
    intro n hall
    exact hrest n (hall (T1, T2) (Set.mem_insert _ _))
      (hall (S1, S2) (Set.mem_insert_of_mem _ rfl))
  obtain ⟨PQ, hPQ, hdist⟩ := rest_to_dist_pair hne hkey
  exact ⟨PQ, hPQ, by simpa using hdist⟩

theorem map_alpha_of_distT_pair_two {α β : Type _} [ms β] {T1 T2 S1 S2 z1 z2 : domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    (∀ n, T1 .|. n = T2 .|. n → S1 .|. n = S2 .|. n → z1 .|. n = z2 .|. n) →
      distance T1 T2 <= alpha * distance x1 x2 →
        distance S1 S2 <= alpha * distance x1 x2 →
          distance z1 z2 <= alpha * distance x1 x2 := by
  intro hrest h1 h2
  obtain ⟨PQ, hPQ, hdist⟩ := distT_pair_two hrest
  rcases hPQ with rfl | hPQ
  · exact le_trans hdist h1
  · rw [Set.mem_singleton_iff] at hPQ
    subst hPQ
    exact le_trans hdist h2

theorem map_alpha_of_rest_one {α β : Type _} [ms β]
    {g F : β → domTType α} {alpha : ℝ} :
    (∀ x y n, g x .|. n = g y .|. n → F x .|. n = F y .|. n) →
      map_alpha g alpha → map_alpha F alpha := by
  intro hrest hg
  refine ⟨hg.1, ?_⟩
  intro x y
  refine le_trans ?_ (hg.2 x y)
  rw [domT_distance_def, domT_distance_def]
  exact rest_distance_subset (fun n h => hrest x y n h)

theorem map_alpha_of_rest_two {α β : Type _} [ms β]
    {g1 g2 F : β → domTType α} {alpha : ℝ} :
    (∀ x y n, g1 x .|. n = g1 y .|. n → g2 x .|. n = g2 y .|. n → F x .|. n = F y .|. n) →
      map_alpha g1 alpha → map_alpha g2 alpha → map_alpha F alpha := by
  intro hrest h1 h2
  refine ⟨h1.1, ?_⟩
  intro x y
  exact map_alpha_of_distT_pair_two (fun n ha hb => hrest x y n ha hb) (h1.2 x y) (h2.2 x y)

theorem non_expanding_iff_rest {β γ : Type _} [ms_rs β] [ms_rs γ] {f : β → γ} :
    non_expanding f ↔ ∀ x y n, x .|. n = y .|. n → (f x) .|. n = (f y) .|. n := by
  constructor
  · intro hf x y n hxy
    refine distance_rs_le_1_if ?_
    have h1 : distance_rs x y <= (1 / 2 : ℝ) ^ n := distance_rs_le_1_only_if hxy
    have h2 := hf.2 x y
    rw [ms0_rs.to_distance_rs, ms0_rs.to_distance_rs] at h2
    linarith
  · intro hf
    refine ⟨by norm_num, ?_⟩
    intro x y
    rw [ms0_rs.to_distance_rs, ms0_rs.to_distance_rs, one_mul]
    exact rest_distance_subset (fun n h => hf x y n h)

theorem contraction_half_iff_constructive {β γ : Type _} [ms_rs β] [ms_rs γ] {f : β → γ} :
    contraction_alpha f (1 / 2 : ℝ) ↔ constructive_rs f := by
  constructor
  · exact contra_alpha_to_contst (fun x y => ms0_rs.to_distance_rs x y)
      (fun x y => ms0_rs.to_distance_rs x y)
  · exact contst_to_contra_alpha (fun x y => ms0_rs.to_distance_rs x y)
      (fun x y => ms0_rs.to_distance_rs x y)

/- ============================================*
 |                   gSKIP                    |
 *============================================ -/

theorem gSKIP_to_Tick_notin_traces {p : Type _} {α : Type _} :
    ∀ (P : proc p α) (M : p → domTType α),
      gSKIP P → ((Abs_trace [event.Tick] : traceType α) ~:t traces P M) := by
  intro P
  induction P with
  | STOP =>
      intro M _ hmem
      exact absurd (in_traces_STOP.mp hmem) (by simp)
  | SKIP =>
      intro M hg _
      exact hg.elim
  | DIV =>
      intro M _ hmem
      exact absurd (in_traces_DIV.mp hmem) (by simp)
  | Act_prefix a P ih =>
      intro M _ hmem
      rcases in_traces_Act_prefix.mp hmem with h | ⟨s, heq, _⟩
      · simp at h
      · rcases (appt_decompo_one_sym (Or.inl (noTick_Ev a))).mp heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          simp at h1
  | Ext_pre_choice X Pf ih =>
      intro M _ hmem
      rcases in_traces_Ext_pre_choice.mp hmem with h | ⟨a, s, heq, _, _⟩
      · simp at h
      · rcases (appt_decompo_one_sym (Or.inl (noTick_Ev a))).mp heq with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
          simp at h1
  | Ext_choice P Q ihP ihQ =>
      intro M hg hmem
      rcases in_traces_Ext_choice.mp hmem with h | h
      · exact ihP M hg.1 h
      · exact ihQ M hg.2 h
  | Int_choice P Q ihP ihQ =>
      intro M hg hmem
      rcases in_traces_Int_choice.mp hmem with h | h
      · exact ihP M hg.1 h
      · exact ihQ M hg.2 h
  | Rep_int_choice C Pf ih =>
      intro M hg hmem
      rcases in_traces_Rep_int_choice_sum.mp hmem with h | ⟨c, _, h⟩
      · simp at h
      · exact ih c M (hg c) h
  | «IF» b P Q ihP ihQ =>
      intro M hg hmem
      rw [in_traces_IF] at hmem
      cases b
      · exact ihQ M hg.2 (by simpa using hmem)
      · exact ihP M hg.1 (by simpa using hmem)
  | Parallel P X Q ihP ihQ =>
      intro M hg hmem
      obtain ⟨s, t, hpar, hsP, htQ⟩ := in_traces_Parallel.mp hmem
      obtain ⟨hs, ht⟩ := par_tr_Tick_only_if hpar
      subst hs
      subst ht
      rcases hg with hg | hg
      · exact ihP M hg hsP
      · exact ihQ M hg htQ
  | Hiding P X ih =>
      intro M hg _
      exact hg.elim
  | Renaming P r ih =>
      intro M hg hmem
      obtain ⟨s, hren, hsP⟩ := in_traces_Renaming.mp hmem
      have hs : s = Abs_trace [event.Tick] := ren_tr_Tick2.mp hren
      subst hs
      exact ih M hg hsP
  | Seq_compo P Q ihP ihQ =>
      intro M hg hmem
      rcases in_traces_Seq_compo.mp hmem with ⟨s, heq, _⟩ | ⟨s, t, heq, hTP, htQ, hns⟩
      · have h0 : noTick (Abs_trace [event.Tick] : traceType α) := by
          rw [heq]
          exact noTick_rmTick
        exact not_noTick_Tick h0
      · rcases (appt_decompo_one_sym (Or.inl hns)).mp heq with ⟨h1, _⟩ | ⟨h1, h2⟩
        · subst h1
          exact not_noTick_Tick hns
        · subst h1
          subst h2
          rw [appt_nil_left] at hTP
          rcases hg with hg | hg
          · exact ihP M hg hTP
          · exact ihQ M hg htQ
  | Depth_rest P n ih =>
      intro M hg hmem
      obtain ⟨hP, hlen⟩ := in_traces_Depth_rest.mp hmem
      rcases hg with hg | hg
      · exact ih M hg hP
      · subst hg
        simp at hlen
  | Proc_name pn =>
      intro M hg _
      exact hg.elim

/- --------------------------------*
 |        STOP,SKIP,DIV           |
 *-------------------------------- -/

/- (*** Constant_contraction ***) -/

theorem map_alpha_Constant {β : Type _} {γ : Type _} [ms β] [ms γ] {C : γ} {alpha : ℝ} :
    0 <= alpha → map_alpha (fun _ : β => C) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

/- (*** non_expanding_Constant ***) -/

theorem non_expanding_Constant {β : Type _} {γ : Type _} [ms β] [ms γ] {C : γ} :
    non_expanding (fun _ : β => C) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

/- (*** Constant_contraction_alpha ***) -/

theorem contraction_alpha_Constant {β : Type _} {γ : Type _} [ms β] [ms γ]
    {C : γ} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (fun _ : β => C) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- (*** STOP ***) -/

theorem map_alpha_traces_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (traces (p := p) (α := α) proc.STOP) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

theorem non_expanding_traces_STOP {p : Type _} {α : Type _} :
    non_expanding (traces (p := p) (α := α) proc.STOP) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

theorem contraction_alpha_traces_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (traces (p := p) (α := α) proc.STOP) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- (*** SKIP ***) -/

theorem map_alpha_traces_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (traces (p := p) (α := α) proc.SKIP) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

theorem non_expanding_traces_SKIP {p : Type _} {α : Type _} :
    non_expanding (traces (p := p) (α := α) proc.SKIP) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

theorem contraction_alpha_traces_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (traces (p := p) (α := α) proc.SKIP) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- (*** DIV ***) -/

theorem map_alpha_traces_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (traces (p := p) (α := α) proc.DIV) alpha := by
  intro h
  exact map_alpha_of_const h (fun _ _ => rfl)

theorem non_expanding_traces_DIV {p : Type _} {α : Type _} :
    non_expanding (traces (p := p) (α := α) proc.DIV) := by
  exact map_alpha_of_const (by norm_num) (fun _ _ => rfl)

theorem contraction_alpha_traces_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (traces (p := p) (α := α) proc.DIV) alpha := by
  intro h1 h2
  exact ⟨h2, map_alpha_of_const h1 (fun _ _ => rfl)⟩

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

theorem Act_prefix_rest_domT_Suc {p q α : Type _}
    {a : α} {P : proc p α} {Q : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (traces P M1 .|. n = traces Q M2 .|. n) ↔
      (traces (a ~> P) M1 .|. Nat.succ n = traces (a ~> Q) M2 .|. Nat.succ n) := by
  rw [rest_domT_eq_iff_le, rest_domT_eq_iff_le]
  constructor
  · intro h t hlen
    rw [in_traces_Act_prefix, in_traces_Act_prefix]
    constructor
    · rintro (rfl | ⟨s, rfl, hs⟩)
      · exact Or.inl rfl
      · refine Or.inr ⟨s, rfl, (h s ?_).mp hs⟩
        rw [lengtht_app_event_Suc_head] at hlen
        omega
    · rintro (rfl | ⟨s, rfl, hs⟩)
      · exact Or.inl rfl
      · refine Or.inr ⟨s, rfl, (h s ?_).mpr hs⟩
        rw [lengtht_app_event_Suc_head] at hlen
        omega
  · intro h s hlen
    have h0 := h (Abs_trace [event.Ev a] ^^^ s) (by rw [lengtht_app_event_Suc_head]; omega)
    rw [in_traces_Act_prefix, in_traces_Act_prefix] at h0
    constructor
    · intro hs
      rcases h0.mp (Or.inr ⟨s, rfl, hs⟩) with h1 | ⟨s', heq, hs'⟩
      · simp at h1
      · obtain ⟨-, hss⟩ := appt_same_head_only_if heq
        rw [hss]
        exact hs'
    · intro hs
      rcases h0.mpr (Or.inr ⟨s, rfl, hs⟩) with h1 | ⟨s', heq, hs'⟩
      · simp at h1
      · obtain ⟨-, hss⟩ := appt_same_head_only_if heq
        rw [hss]
        exact hs'

theorem contraction_half_traces_Act_prefix_lm {p : Type _} {q : Type _} {α : Type _}
    {a : α} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    distance (traces (a ~> P) M1) (traces (a ~> Q) M2) * 2 =
      distance (traces P M1) (traces Q M2) := by
  have h := rest_Suc_dist_half (x1 := traces P M1) (x2 := traces Q M2)
    (y1 := traces (a ~> P) M1) (y2 := traces (a ~> Q) M2) (fun n => Act_prefix_rest_domT_Suc)
  rw [domT_distance_def, domT_distance_def]
  linarith

/- (***  contraction_half ***) -/

theorem contraction_half_traces_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (traces P) → contraction_alpha (traces (a ~> P)) (1 / 2 : ℝ) := by
  intro hP
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro M1 M2
  have h1 := contraction_half_traces_Act_prefix_lm (a := a) (P := P) (Q := P)
    (M1 := M1) (M2 := M2)
  have h2 := hP.2 M1 M2
  linarith

/- (***  contraction ***) -/

theorem contraction_traces_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (traces P) → contraction (traces (a ~> P)) := by
  intro hP
  exact ⟨(1 / 2 : ℝ), contraction_half_traces_Act_prefix hP⟩

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (traces P) → non_expanding (traces (a ~> P)) := by
  intro hP
  exact contraction_non_expanding (contraction_traces_Act_prefix hP)

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Ext_pre_choice_Act_prefix_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ a ∈ X, traces (a ~> Pf a) M1 .|. n <= traces (a ~> Qf a) M2 .|. n) →
      traces (proc.Ext_pre_choice X Pf) M1 .|. n <=
        traces (proc.Ext_pre_choice X Qf) M2 .|. n := by
  intro h
  rw [rest_domT_le_iff]
  intro t ht hlen
  rcases in_traces_Ext_pre_choice.mp ht with rfl | ⟨a, s, rfl, hs, haX⟩
  · exact nilt_in_T
  · have h1 : (Abs_trace [event.Ev a] ^^^ s) :t traces (a ~> Pf a) M1 :=
      in_traces_Act_prefix.mpr (Or.inr ⟨s, rfl, hs⟩)
    have h2 := rest_domT_le_iff.mp (h a haX) _ h1 hlen
    rcases in_traces_Act_prefix.mp h2 with h3 | ⟨s', heq, hs'⟩
    · simp at h3
    · obtain ⟨-, hss⟩ := appt_same_head_only_if heq
      refine in_traces_Ext_pre_choice.mpr (Or.inr ⟨a, s, rfl, ?_, haX⟩)
      rw [hss]
      exact hs'

/- (*** rest_domT (equal) ***) -/

theorem Ext_pre_choice_Act_prefix_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ a ∈ X, traces (a ~> Pf a) M1 .|. n = traces (a ~> Qf a) M2 .|. n) →
      traces (proc.Ext_pre_choice X Pf) M1 .|. n =
        traces (proc.Ext_pre_choice X Qf) M2 .|. n := by
  intro h
  refine le_antisymm (Ext_pre_choice_Act_prefix_rest_domT_sub ?_)
    (Ext_pre_choice_Act_prefix_rest_domT_sub ?_)
  · intro a ha
    exact le_of_eq (h a ha)
  · intro a ha
    exact le_of_eq (h a ha).symm

/- (*** distT lemma ***) -/

theorem Ext_pre_choice_Act_prefix_distT_nonempty {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (domTType α × domTType α)}
    {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    X ≠ ∅ →
      PQs =
        {PQ | ∃ a, a ∈ X ∧ PQ = (traces (a ~> Pf a) M1, traces (a ~> Qf a) M2)} →
          ∃ PQ, PQ ∈ PQs ∧
            distance
                (traces (proc.Ext_pre_choice X Pf) M1)
                (traces (proc.Ext_pre_choice X Qf) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hX hPQs
  have hne : PQs ≠ ∅ := by
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hX
    intro h0
    have hmem : (traces (a ~> Pf a) M1, traces (a ~> Qf a) M2) ∈ PQs := by
      rw [hPQs]
      exact ⟨a, ha, rfl⟩
    rw [h0] at hmem
    exact hmem
  have hkey : ∀ n, (∀ x ∈ PQs, x.1 .|. n = x.2 .|. n) →
      traces (proc.Ext_pre_choice X Pf) M1 .|. n =
        traces (proc.Ext_pre_choice X Qf) M2 .|. n := by
    intro n hall
    refine Ext_pre_choice_Act_prefix_rest_domT ?_
    intro a ha
    exact hall (traces (a ~> Pf a) M1, traces (a ~> Qf a) M2) (by rw [hPQs]; exact ⟨a, ha, rfl⟩)
  obtain ⟨PQ, hPQ, hdist⟩ := rest_to_dist_pair hne hkey
  exact ⟨PQ, hPQ, by simpa using hdist⟩

/- (*** contraction lemma ***) -/

theorem contraction_half_traces_Ext_pre_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : domTType α} :
    X ≠ ∅ →
      (∀ a, distance (traces (Pf a) M1) (traces (Qf a) M2) <= distance x1 x2) →
        distance
            (traces (proc.Ext_pre_choice X Pf) M1)
            (traces (proc.Ext_pre_choice X Qf) M2) * 2 <=
          distance x1 x2 := by
  intro hX hd
  obtain ⟨PQ, hPQ, hdist⟩ :=
    Ext_pre_choice_Act_prefix_distT_nonempty
      (PQs := {PQ | ∃ a, a ∈ X ∧ PQ = (traces (a ~> Pf a) M1, traces (a ~> Qf a) M2)})
      hX rfl
  obtain ⟨a, ha, rfl⟩ := hPQ
  have h1 := contraction_half_traces_Act_prefix_lm (a := a) (P := Pf a) (Q := Qf a)
    (M1 := M1) (M2 := M2)
  have h2 := hd a
  dsimp only at hdist
  linarith


/- (*** general-`ms` version of the lemma above (Lean port helper) ***) -/

theorem contraction_half_traces_Ext_pre_choice_lm_gen {p q α : Type _} {β : Type _} [ms β]
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {x1 x2 : β} :
    X ≠ ∅ →
      (∀ a, distance (traces (Pf a) M1) (traces (Qf a) M2) <= distance x1 x2) →
        distance
            (traces (proc.Ext_pre_choice X Pf) M1)
            (traces (proc.Ext_pre_choice X Qf) M2) * 2 <=
          distance x1 x2 := by
  intro hX hd
  obtain ⟨PQ, hPQ, hdist⟩ :=
    Ext_pre_choice_Act_prefix_distT_nonempty
      (PQs := {PQ | ∃ a, a ∈ X ∧ PQ = (traces (a ~> Pf a) M1, traces (a ~> Qf a) M2)})
      hX rfl
  obtain ⟨a, ha, rfl⟩ := hPQ
  have h1 := contraction_half_traces_Act_prefix_lm (a := a) (P := Pf a) (Q := Qf a)
    (M1 := M1) (M2 := M2)
  have h2 := hd a
  dsimp only at hdist
  linarith

/- (*** contraction_half ***) -/

theorem contraction_half_traces_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (traces (Pf a))) →
      contraction_alpha (traces (proc.Ext_pre_choice X Pf)) (1 / 2 : ℝ) := by
  intro hPf
  by_cases hX : X = ∅
  · subst hX
    refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
    intro M1 M2
    refine le_antisymm (subdomTI ?_) (subdomTI ?_)
    · intro t ht
      rcases in_traces_Ext_pre_choice.mp ht with rfl | ⟨a, s, -, -, haX⟩
      · exact nilt_in_T
      · exact absurd haX (by simp)
    · intro t ht
      rcases in_traces_Ext_pre_choice.mp ht with rfl | ⟨a, s, -, -, haX⟩
      · exact nilt_in_T
      · exact absurd haX (by simp)
  · refine ⟨by norm_num, by norm_num, ?_⟩
    intro M1 M2
    have h1 := contraction_half_traces_Ext_pre_choice_lm_gen (X := X) (Pf := Pf) (Qf := Pf)
      (M1 := M1) (M2 := M2) (x1 := M1) (x2 := M2) hX (fun a => by
        have h2 := (hPf a).2 M1 M2
        linarith)
    linarith

/- (*** Ext_pre_choice_evalT_contraction ***) -/

theorem contraction_traces_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (traces (Pf a))) →
      contraction (traces (proc.Ext_pre_choice X Pf)) := by
  intro hPf
  exact ⟨(1 / 2 : ℝ), contraction_half_traces_Ext_pre_choice hPf⟩

/- (*** Ext_pre_choice_evalT_non_expanding ***) -/

theorem non_expanding_traces_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (traces (Pf a))) →
      non_expanding (traces (proc.Ext_pre_choice X Pf)) := by
  intro hPf
  exact contraction_non_expanding (contraction_traces_Ext_pre_choice hPf)

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Ext_choice_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (P1 [+] Q1) M1 .|. n <= traces (P2 [+] Q2) M2 .|. n := by
  intro h1 h2
  rw [rest_domT_le_iff]
  intro t ht hlen
  rcases in_traces_Ext_choice.mp ht with h | h
  · exact in_traces_Ext_choice.mpr (Or.inl (rest_domT_le_iff.mp h1 t h hlen))
  · exact in_traces_Ext_choice.mpr (Or.inr (rest_domT_le_iff.mp h2 t h hlen))

/- (*** rest_domT (equal) ***) -/

theorem Ext_choice_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (P1 [+] Q1) M1 .|. n = traces (P2 [+] Q2) M2 .|. n := by
  intro h1 h2
  exact le_antisymm (Ext_choice_rest_domT_sub (le_of_eq h1) (le_of_eq h2))
    (Ext_choice_rest_domT_sub (le_of_eq h1.symm) (le_of_eq h2.symm))

/- (*** distT lemma ***) -/

theorem Ext_choice_distT {p : Type _} {q : Type _} {α : Type _}
    {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (P1 [+] Q1) M1) (traces (P2 [+] Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  exact distT_pair_two (fun n ha hb => Ext_choice_rest_domT ha hb)

/- (*** map_alpha T lemma ***) -/

theorem map_alpha_traces_Ext_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (P1 [+] Q1) M1) (traces (P2 [+] Q2) M2) <=
          alpha * distance x1 x2 := by
  intro h1 h2
  exact map_alpha_of_distT_pair_two (fun n ha hb => Ext_choice_rest_domT ha hb) h1 h2

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P [+] Q)) alpha := by
  intro h1 h2
  exact map_alpha_of_rest_two (fun M1 M2 n ha hb => Ext_choice_rest_domT ha hb) h1 h2

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P [+] Q)) := by
  intro h1 h2
  exact map_alpha_traces_Ext_choice h1 h2

/- (*** contraction ***) -/

theorem contraction_alpha_traces_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P [+] Q)) alpha := by
  intro h1 h2
  exact ⟨h1.1, map_alpha_traces_Ext_choice h1.2 h2.2⟩

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P |~| Q)) alpha := by
  intro h1 h2
  rw [traces_Int_choice_Ext_choice]
  exact map_alpha_traces_Ext_choice h1 h2

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P |~| Q)) := by
  intro h1 h2
  exact map_alpha_traces_Int_choice h1 h2

/- (*** contraction ***) -/

theorem contraction_alpha_traces_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P |~| Q)) alpha := by
  intro h1 h2
  exact ⟨h1.1, map_alpha_traces_Int_choice h1.2 h2.2⟩

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Rep_int_choice_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ c ∈ sumset C, traces (Pf c) M1 .|. n <= traces (Qf c) M2 .|. n) →
      traces (proc.Rep_int_choice C Pf) M1 .|. n <= traces (proc.Rep_int_choice C Qf) M2 .|. n := by
  intro h
  rw [rest_domT_le_iff]
  intro t ht hlen
  rcases in_traces_Rep_int_choice_sum.mp ht with rfl | ⟨c, hc, ht'⟩
  · exact nilt_in_T
  · exact in_traces_Rep_int_choice_sum.mpr
      (Or.inr ⟨c, hc, rest_domT_le_iff.mp (h c hc) t ht' hlen⟩)

/- (*** rest_domT (equal) ***) -/

theorem Rep_int_choice_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ c ∈ sumset C, traces (Pf c) M1 .|. n = traces (Qf c) M2 .|. n) →
      traces (proc.Rep_int_choice C Pf) M1 .|. n = traces (proc.Rep_int_choice C Qf) M2 .|. n := by
  intro h
  refine le_antisymm (Rep_int_choice_rest_domT_sub ?_) (Rep_int_choice_rest_domT_sub ?_)
  · intro c hc
    exact le_of_eq (h c hc)
  · intro c hc
    exact le_of_eq (h c hc).symm

/- (*** distT lemma ***) -/

theorem Rep_int_choice_distT_nonempty {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {PQs : Set (domTType α × domTType α)}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    sumset C ≠ ∅ →
      PQs =
        {PQ | ∃ c, c ∈ sumset C ∧ PQ = (traces (Pf c) M1, traces (Qf c) M2)} →
          ∃ PQ, PQ ∈ PQs ∧
            distance
                (traces (proc.Rep_int_choice C Pf) M1)
                (traces (proc.Rep_int_choice C Qf) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hC hPQs
  have hne : PQs ≠ ∅ := by
    obtain ⟨c, hc⟩ := Set.nonempty_iff_ne_empty.mpr hC
    intro h0
    have hmem : (traces (Pf c) M1, traces (Qf c) M2) ∈ PQs := by
      rw [hPQs]
      exact ⟨c, hc, rfl⟩
    rw [h0] at hmem
    exact hmem
  have hkey : ∀ n, (∀ x ∈ PQs, x.1 .|. n = x.2 .|. n) →
      traces (proc.Rep_int_choice C Pf) M1 .|. n =
        traces (proc.Rep_int_choice C Qf) M2 .|. n := by
    intro n hall
    refine Rep_int_choice_rest_domT ?_
    intro c hc
    exact hall (traces (Pf c) M1, traces (Qf c) M2) (by rw [hPQs]; exact ⟨c, hc, rfl⟩)
  obtain ⟨PQ, hPQ, hdist⟩ := rest_to_dist_pair hne hkey
  exact ⟨PQ, hPQ, by simpa using hdist⟩

/- (*** map_alpha T lemma ***) -/

theorem map_alpha_traces_Rep_int_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {C : sets_nats α}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    sumset C ≠ ∅ →
      (∀ c, distance (traces (Pf c) M1) (traces (Qf c) M2) <= alpha * distance x1 x2) →
        distance (traces (proc.Rep_int_choice C Pf) M1) (traces (proc.Rep_int_choice C Qf) M2) <=
          alpha * distance x1 x2 := by
  intro hC hd
  obtain ⟨PQ, hPQ, hdist⟩ :=
    Rep_int_choice_distT_nonempty
      (PQs := {PQ | ∃ c, c ∈ sumset C ∧ PQ = (traces (Pf c) M1, traces (Qf c) M2)}) hC rfl
  obtain ⟨c, hc, rfl⟩ := hPQ
  dsimp only at hdist
  exact le_trans hdist (hd c)

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, map_alpha (traces (Pf c)) alpha) →
      map_alpha (traces (proc.Rep_int_choice C Pf)) alpha := by
  intro hPf
  refine ⟨(hPf (type2 0)).1, ?_⟩
  intro M1 M2
  by_cases hC : sumset C = ∅
  · have hconst : traces (proc.Rep_int_choice C Pf) M1 = traces (proc.Rep_int_choice C Pf) M2 := by
      refine le_antisymm (subdomTI ?_) (subdomTI ?_) <;>
        · intro t ht
          rcases in_traces_Rep_int_choice_sum.mp ht with rfl | ⟨c, hc, -⟩
          · exact nilt_in_T
          · rw [hC] at hc
            exact hc.elim
    rw [hconst, same_pnt_zero]
    exact mul_nonneg (hPf (type2 0)).1 (ms.positive_ms M1 M2)
  · exact map_alpha_traces_Rep_int_choice_lm hC (fun c => (hPf c).2 M1 M2)

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, non_expanding (traces (Pf c))) →
      non_expanding (traces (proc.Rep_int_choice C Pf)) := by
  intro hPf
  exact map_alpha_traces_Rep_int_choice hPf

/- (*** Rep_int_choice_evalT_contraction_alpha ***) -/

theorem contraction_alpha_traces_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, contraction_alpha (traces (Pf c)) alpha) →
      contraction_alpha (traces (proc.Rep_int_choice C Pf)) alpha := by
  intro hPf
  exact ⟨(hPf (type2 0)).1, map_alpha_traces_Rep_int_choice (fun c => (hPf c).2)⟩

/- --------------------------------*
 |               IF               |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem IF_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (IF b THEN P1 ELSE Q1) M1 .|. n <= traces (IF b THEN P2 ELSE Q2) M2 .|. n := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- (*** rest_domT (equal) ***) -/

theorem IF_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (IF b THEN P1 ELSE Q1) M1 .|. n = traces (IF b THEN P2 ELSE Q2) M2 .|. n := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- (*** distT lemma ***) -/

theorem IF_distT {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (IF b THEN P1 ELSE Q1) M1) (traces (IF b THEN P2 ELSE Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  exact distT_pair_two (fun n ha hb => IF_rest_domT ha hb)

/- (*** map_alpha T lemma (not used) ***) -/

theorem map_alpha_traces_IF_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (IF b THEN P1 ELSE Q1) M1) (traces (IF b THEN P2 ELSE Q2) M2) <=
          alpha * distance x1 x2 := by
  intro h1 h2
  exact map_alpha_of_distT_pair_two (fun n ha hb => IF_rest_domT ha hb) h1 h2

/- (*** map_alpha ***) -/

theorem map_alpha_traces_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (IF b THEN P ELSE Q)) alpha := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- (*** non_expanding ***) -/

theorem non_expanding_traces_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (IF b THEN P ELSE Q)) := by
  intro h1 h2
  exact map_alpha_traces_IF h1 h2

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_traces_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (IF b THEN P ELSE Q)) alpha := by
  intro h1 h2
  cases b
  · exact h2
  · exact h1

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Parallel_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (P1 |[X]| Q1) M1 .|. n <= traces (P2 |[X]| Q2) M2 .|. n := by
  intro h1 h2
  rw [rest_domT_le_iff]
  intro u hu hlen
  obtain ⟨s, t, hpar, hs, ht⟩ := in_traces_Parallel.mp hu
  obtain ⟨hls, hlt⟩ := par_tr_lengtht hpar
  exact in_traces_Parallel.mpr ⟨s, t, hpar,
    rest_domT_le_iff.mp h1 s hs (le_trans hls hlen),
    rest_domT_le_iff.mp h2 t ht (le_trans hlt hlen)⟩

/- (*** rest_domT (equal) ***) -/

theorem Parallel_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (P1 |[X]| Q1) M1 .|. n = traces (P2 |[X]| Q2) M2 .|. n := by
  intro h1 h2
  exact le_antisymm (Parallel_rest_domT_sub (le_of_eq h1) (le_of_eq h2))
    (Parallel_rest_domT_sub (le_of_eq h1.symm) (le_of_eq h2.symm))

/- (*** distT lemma ***) -/

theorem Parallel_distT {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (P1 |[X]| Q1) M1) (traces (P2 |[X]| Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  exact distT_pair_two (fun n ha hb => Parallel_rest_domT ha hb)

/- (*** map_alpha T lemma ***) -/

theorem map_alpha_traces_Parallel_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (P1 |[X]| Q1) M1) (traces (P2 |[X]| Q2) M2) <=
          alpha * distance x1 x2 := by
  intro h1 h2
  exact map_alpha_of_distT_pair_two (fun n ha hb => Parallel_rest_domT ha hb) h1 h2

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P |[X]| Q)) alpha := by
  intro h1 h2
  exact map_alpha_of_rest_two (fun M1 M2 n ha hb => Parallel_rest_domT ha hb) h1 h2

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P |[X]| Q)) := by
  intro h1 h2
  exact map_alpha_traces_Parallel h1 h2

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_traces_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P |[X]| Q)) alpha := by
  intro h1 h2
  exact ⟨h1.1, map_alpha_traces_Parallel h1.2 h2.2⟩

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- cms rules for Hiding is not necessary
   because processes are guarded. -/

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Renaming_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P M1 .|. n <= traces Q M2 .|. n →
      traces (P [[r]]) M1 .|. n <= traces (Q [[r]]) M2 .|. n := by
  intro h
  rw [rest_domT_le_iff]
  intro t ht hlen
  obtain ⟨s, hren, hs⟩ := in_traces_Renaming.mp ht
  have hl : lengtht s = lengtht t := ren_tr_lengtht hren
  exact in_traces_Renaming.mpr ⟨s, hren, rest_domT_le_iff.mp h s hs (by rw [hl]; exact hlen)⟩

/- (*** rest_domT (equal) ***) -/

theorem Renaming_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P M1 .|. n = traces Q M2 .|. n →
      traces (P [[r]]) M1 .|. n = traces (Q [[r]]) M2 .|. n := by
  intro h
  exact le_antisymm (Renaming_rest_domT_sub (le_of_eq h))
    (Renaming_rest_domT_sub (le_of_eq h.symm))

/- (*** distT lemma ***) -/

theorem Renaming_distT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    distance (traces (P [[r]]) M1) (traces (Q [[r]]) M2) <=
      distance (traces P M1) (traces Q M2) := by
  rw [domT_distance_def, domT_distance_def]
  exact rest_distance_subset (fun n h => Renaming_rest_domT h)

/- (*** map_alphaT lemma ***) -/

theorem map_alpha_traces_Renaming_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P M1) (traces Q M2) <= alpha * distance x1 x2 →
      distance (traces (P [[r]]) M1) (traces (Q [[r]]) M2) <= alpha * distance x1 x2 := by
  intro h
  exact le_trans Renaming_distT h

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    map_alpha (traces P) alpha → map_alpha (traces (P [[r]])) alpha := by
  intro h
  exact map_alpha_of_rest_one (fun M1 M2 n hn => Renaming_rest_domT hn) h

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} :
    non_expanding (traces P) → non_expanding (traces (P [[r]])) := by
  intro h
  exact map_alpha_traces_Renaming h

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_traces_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    contraction_alpha (traces P) alpha → contraction_alpha (traces (P [[r]])) alpha := by
  intro h
  exact ⟨h.1, map_alpha_traces_Renaming h.2⟩

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem Seq_compo_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (P1 ;; Q1) M1 .|. n <= traces (P2 ;; Q2) M2 .|. n := by
  intro h1 h2
  rw [rest_domT_le_iff]
  intro u hu hlen
  rcases in_traces_Seq_compo.mp hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hTick, ht, hns⟩
  · have h3 : rmTick s :t traces P1 M1 := memT_prefix_closed hs rmTick_prefix_rev_simp
    have h4 : rmTick s :t traces P2 M2 := rest_domT_le_iff.mp h1 _ h3 hlen
    exact in_traces_Seq_compo.mpr
      (Or.inl ⟨rmTick s, (rmTick_nochange noTick_rmTick).symm, h4⟩)
  · by_cases htnil : t = <>
    · subst htnil
      rw [appt_nil_right] at hlen ⊢
      have hsP1 : s :t traces P1 M1 :=
        memT_prefix_closed hTick (prefix_appt_simp (Or.inl hns))
      have hsP2 : s :t traces P2 M2 := rest_domT_le_iff.mp h1 _ hsP1 hlen
      exact in_traces_Seq_compo.mpr (Or.inl ⟨s, (rmTick_nochange hns).symm, hsP2⟩)
    · rw [lengtht_app_decompo1 (Or.inl hns)] at hlen
      have hlt : 1 <= lengtht t := by
        rcases Nat.eq_zero_or_pos (lengtht t) with h0 | h0
        · exact absurd (lengtht_zero.mp h0) htnil
        · exact h0
      have hTick2 : (s ^^^ Abs_trace [event.Tick]) :t traces P2 M2 := by
        refine rest_domT_le_iff.mp h1 _ hTick ?_
        rw [lengtht_app_event_Suc_last hns]
        omega
      have ht2 : t :t traces Q2 M2 := by
        refine rest_domT_le_iff.mp h2 _ ht ?_
        omega
      exact in_traces_Seq_compo.mpr (Or.inr ⟨s, t, rfl, hTick2, ht2, hns⟩)

/- (*** rest_domT (equal) ***) -/

theorem Seq_compo_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (P1 ;; Q1) M1 .|. n = traces (P2 ;; Q2) M2 .|. n := by
  intro h1 h2
  exact le_antisymm (Seq_compo_rest_domT_sub (le_of_eq h1) (le_of_eq h2))
    (Seq_compo_rest_domT_sub (le_of_eq h1.symm) (le_of_eq h2.symm))

/- (*** distT lemma ***) -/

theorem Seq_compo_distT {p : Type _} {q : Type _} {α : Type _}
    {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (P1 ;; Q1) M1) (traces (P2 ;; Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ) := by
  intro hPQs
  subst hPQs
  exact distT_pair_two (fun n ha hb => Seq_compo_rest_domT ha hb)

/- (*** map_alpha T lemma ***) -/

theorem map_alpha_traces_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (P1 ;; Q1) M1) (traces (P2 ;; Q2) M2) <= alpha * distance x1 x2 := by
  intro h1 h2
  exact map_alpha_of_distT_pair_two (fun n ha hb => Seq_compo_rest_domT ha hb) h1 h2

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P ;; Q)) alpha := by
  intro h1 h2
  exact map_alpha_of_rest_two (fun M1 M2 n ha hb => Seq_compo_rest_domT ha hb) h1 h2

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P ;; Q)) := by
  intro h1 h2
  exact map_alpha_traces_Seq_compo h1 h2

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P ;; Q)) alpha := by
  intro h1 h2
  exact ⟨h1.1, map_alpha_traces_Seq_compo h1.2 h2.2⟩

/- --------------------------------*
 |       Seq_compo  (gSKIP)       |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

theorem gSKIP_Seq_compo_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. Nat.succ n <= traces P2 M2 .|. Nat.succ n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 M1) →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 M2) →
            traces (P1 ;; Q1) M1 .|. Nat.succ n <= traces (P2 ;; Q2) M2 .|. Nat.succ n := by
  intro h1 h2 hT1 _
  rw [rest_domT_le_iff]
  intro u hu hlen
  rcases in_traces_Seq_compo.mp hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hTick, ht, hns⟩
  · have h3 : rmTick s :t traces P1 M1 := memT_prefix_closed hs rmTick_prefix_rev_simp
    have h4 : rmTick s :t traces P2 M2 := rest_domT_le_iff.mp h1 _ h3 hlen
    exact in_traces_Seq_compo.mpr
      (Or.inl ⟨rmTick s, (rmTick_nochange noTick_rmTick).symm, h4⟩)
  · have hsne : s ≠ <> := by
      intro h0
      subst h0
      rw [appt_nil_left] at hTick
      exact hT1 hTick
    have hls : 1 <= lengtht s := by
      rcases Nat.eq_zero_or_pos (lengtht s) with h0 | h0
      · exact absurd (lengtht_zero.mp h0) hsne
      · exact h0
    by_cases htnil : t = <>
    · subst htnil
      rw [appt_nil_right] at hlen ⊢
      have hsP1 : s :t traces P1 M1 :=
        memT_prefix_closed hTick (prefix_appt_simp (Or.inl hns))
      have hsP2 : s :t traces P2 M2 := rest_domT_le_iff.mp h1 _ hsP1 hlen
      exact in_traces_Seq_compo.mpr (Or.inl ⟨s, (rmTick_nochange hns).symm, hsP2⟩)
    · rw [lengtht_app_decompo1 (Or.inl hns)] at hlen
      have hlt : 1 <= lengtht t := by
        rcases Nat.eq_zero_or_pos (lengtht t) with h0 | h0
        · exact absurd (lengtht_zero.mp h0) htnil
        · exact h0
      have hTick2 : (s ^^^ Abs_trace [event.Tick]) :t traces P2 M2 := by
        refine rest_domT_le_iff.mp h1 _ hTick ?_
        rw [lengtht_app_event_Suc_last hns]
        omega
      have ht2 : t :t traces Q2 M2 := by
        refine rest_domT_le_iff.mp h2 _ ht ?_
        omega
      exact in_traces_Seq_compo.mpr (Or.inr ⟨s, t, rfl, hTick2, ht2, hns⟩)

/- (*** rest_domT (equal) ***) -/

theorem gSKIP_Seq_compo_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. Nat.succ n = traces P2 M2 .|. Nat.succ n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 M1) →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 M2) →
            traces (P1 ;; Q1) M1 .|. Nat.succ n = traces (P2 ;; Q2) M2 .|. Nat.succ n := by
  intro h1 h2 hT1 hT2
  exact le_antisymm
    (gSKIP_Seq_compo_rest_domT_sub (le_of_eq h1) (le_of_eq h2) hT1 hT2)
    (gSKIP_Seq_compo_rest_domT_sub (le_of_eq h1.symm) (le_of_eq h2.symm) hT2 hT1)

/- (*** map_alpha T lemma ***) -/

theorem gSKIP_map_alpha_traces_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    distance (traces P1 M1) (traces P2 M2) * 2 <= (1 / 2 : ℝ) ^ n →
      distance (traces Q1 M1) (traces Q2 M2) <= (1 / 2 : ℝ) ^ n →
        ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 M1) →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 M2) →
            distance (traces (P1 ;; Q1) M1) (traces (P2 ;; Q2) M2) * 2 <= (1 / 2 : ℝ) ^ n := by
  intro h1 h2 hT1 hT2
  have hp : ((1 : ℝ) / 2) ^ Nat.succ n = ((1 : ℝ) / 2) ^ n * (1 / 2) := pow_succ _ _
  have e1 : traces P1 M1 .|. Nat.succ n = traces P2 M2 .|. Nat.succ n := by
    refine distance_rs_le_1_if ?_
    rw [← domT_distance_def, hp]
    linarith
  have e2 : traces Q1 M1 .|. n = traces Q2 M2 .|. n := by
    refine distance_rs_le_1_if ?_
    rw [← domT_distance_def]
    exact h2
  have h3 := distance_rs_le_1_only_if (gSKIP_Seq_compo_rest_domT e1 e2 hT1 hT2)
  rw [← domT_distance_def, hp] at h3
  linarith

/- (*** map_alpha ***) -/

theorem gSKIP_contraction_half_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    contraction_alpha (traces P) (1 / 2 : ℝ) →
      non_expanding (traces Q) →
        gSKIP P →
          contraction_alpha (traces (P ;; Q)) (1 / 2 : ℝ) := by
  intro hP hQ hg
  rw [contraction_half_iff_constructive]
  intro M1 M2 n hM
  exact gSKIP_Seq_compo_rest_domT
    (contraction_half_iff_constructive.mp hP M1 M2 n hM)
    (non_expanding_iff_rest.mp hQ M1 M2 n hM)
    (gSKIP_to_Tick_notin_traces P M1 hg) (gSKIP_to_Tick_notin_traces P M2 hg)

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** rest_domT (equal) ***) -/

theorem Depth_rest_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m n : Nat}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    traces P M1 .|. n = traces Q M2 .|. n →
      traces (P |. m) M1 .|. n = traces (Q |. m) M2 .|. n := by
  intro h
  rw [rest_domT_eq_iff_le] at h ⊢
  intro t hlen
  rw [in_traces_Depth_rest, in_traces_Depth_rest]
  constructor
  · rintro ⟨ht, hlm⟩
    exact ⟨(h t hlen).mp ht, hlm⟩
  · rintro ⟨ht, hlm⟩
    exact ⟨(h t hlen).mpr ht, hlm⟩

/- (*** distT lemma ***) -/

theorem Depth_rest_distT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    distance (traces (P |. m) M1) (traces (Q |. m) M2) <= distance (traces P M1) (traces Q M2) := by
  rw [domT_distance_def, domT_distance_def]
  exact rest_distance_subset (fun n h => Depth_rest_rest_domT h)

/- (*** map_alphaT lemma ***) -/

theorem map_alpha_traces_Depth_rest_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P M1) (traces Q M2) <= alpha * distance x1 x2 →
      distance (traces (P |. m) M1) (traces (Q |. m) M2) <= alpha * distance x1 x2 := by
  intro h
  exact le_trans Depth_rest_distT h

/- (*** map_alpha ***) -/

theorem map_alpha_traces_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {m : Nat} {alpha : ℝ} :
    map_alpha (traces P) alpha → map_alpha (traces (P |. m)) alpha := by
  intro h
  exact map_alpha_of_rest_one (fun M1 M2 n hn => Depth_rest_rest_domT hn) h

/- (*** non_expanding ***) -/

theorem non_expanding_traces_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {m : Nat} :
    non_expanding (traces P) → non_expanding (traces (P |. m)) := by
  intro h
  exact map_alpha_traces_Depth_rest h

/- (*** contraction_alpha ***) -/

theorem contraction_alpha_traces_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {m : Nat} {alpha : ℝ} :
    contraction_alpha (traces P) alpha → contraction_alpha (traces (P |. m)) alpha := by
  intro h
  exact ⟨h.1, map_alpha_traces_Depth_rest h.2⟩

/- --------------------------------*
 |            variable            |
 *-------------------------------- -/

/- (*** non_expanding ***) -/

theorem non_expanding_traces_variable {p : Type _} {α : Type _} {pn : p} :
    non_expanding (traces (proc.Proc_name pn : proc p α)) := by
  exact non_expanding_prod_variable pn

/- --------------------------------*
 |            Procfun             |
 *-------------------------------- -/

/- (*****************************************************************
 |                         non_expanding                         |
 *****************************************************************) -/

theorem non_expanding_traces_lm {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (traces P) := by
  induction P with
  | STOP =>
      intro _
      exact non_expanding_traces_STOP
  | SKIP =>
      intro _
      exact non_expanding_traces_SKIP
  | DIV =>
      intro _
      exact non_expanding_traces_DIV
  | Act_prefix a P ih =>
      intro h
      exact non_expanding_traces_Act_prefix (ih h)
  | Ext_pre_choice X Pf ih =>
      intro h
      exact non_expanding_traces_Ext_pre_choice (fun a => ih a (h a))
  | Ext_choice P Q ihP ihQ =>
      intro h
      exact non_expanding_traces_Ext_choice (ihP h.1) (ihQ h.2)
  | Int_choice P Q ihP ihQ =>
      intro h
      exact non_expanding_traces_Int_choice (ihP h.1) (ihQ h.2)
  | Rep_int_choice C Pf ih =>
      intro h
      exact non_expanding_traces_Rep_int_choice (fun c => ih c (h c))
  | «IF» b P Q ihP ihQ =>
      intro h
      exact non_expanding_traces_IF (ihP h.1) (ihQ h.2)
  | Parallel P X Q ihP ihQ =>
      intro h
      exact non_expanding_traces_Parallel (ihP h.1) (ihQ h.2)
  | Hiding P X ih =>
      intro h
      obtain ⟨T, hT⟩ := traces_noPN_Constant h
      refine map_alpha_of_const (by norm_num) ?_
      intro M1 M2
      have hPM : traces P M1 = traces P M2 := by rw [hT]
      simp only [traces, hPM]
  | Renaming P r ih =>
      intro h
      exact non_expanding_traces_Renaming (ih h)
  | Seq_compo P Q ihP ihQ =>
      intro h
      exact non_expanding_traces_Seq_compo (ihP h.1) (ihQ h.2)
  | Depth_rest P n ih =>
      intro h
      rcases h with h | h
      · exact non_expanding_traces_Depth_rest (ih h)
      · subst h
        refine map_alpha_of_const (by norm_num) ?_
        intro M1 M2
        simp only [traces]
        exact zero_eq_rs_domT _ _
  | Proc_name pn =>
      intro _
      exact non_expanding_traces_variable

theorem non_expanding_traces {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (traces P) := by
  exact non_expanding_traces_lm

/- =============================================================*
 |                          [[P]]Tf                            |
 *============================================================= -/

theorem non_expanding_semTf {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (semTf P) := by
  exact non_expanding_traces

/- =============================================================*
 |                         [[P]]Tfun                           |
 *============================================================= -/

theorem non_expanding_semTfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    noHidefun Pf → non_expanding (semTfun Pf) := by
  intro hPf
  rcases isEmpty_or_nonempty p with hp | hp
  · refine map_alpha_of_const (by norm_num) ?_
    intro x y
    have hxy : x = y := funext (fun i => (IsEmpty.false i).elim)
    rw [hxy]
  · refine prod_non_expand_if ?_
    intro i
    exact non_expanding_semTf (hPf i)

/- (*****************************************************************
 |                         contraction                           |
 *****************************************************************) -/

theorem contraction_alpha_traces_lm {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (traces P) (1 / 2 : ℝ) := by
  induction P with
  | STOP =>
      intro _
      exact contraction_alpha_traces_STOP (by norm_num) (by norm_num)
  | SKIP =>
      intro _
      exact contraction_alpha_traces_SKIP (by norm_num) (by norm_num)
  | DIV =>
      intro _
      exact contraction_alpha_traces_DIV (by norm_num) (by norm_num)
  | Act_prefix a P ih =>
      intro h
      exact contraction_half_traces_Act_prefix (non_expanding_traces h)
  | Ext_pre_choice X Pf ih =>
      intro h
      exact contraction_half_traces_Ext_pre_choice (fun a => non_expanding_traces (h a))
  | Ext_choice P Q ihP ihQ =>
      intro h
      exact contraction_alpha_traces_Ext_choice (ihP h.1) (ihQ h.2)
  | Int_choice P Q ihP ihQ =>
      intro h
      exact contraction_alpha_traces_Int_choice (ihP h.1) (ihQ h.2)
  | Rep_int_choice C Pf ih =>
      intro h
      exact contraction_alpha_traces_Rep_int_choice (fun c => ih c (h c))
  | «IF» b P Q ihP ihQ =>
      intro h
      exact contraction_alpha_traces_IF (ihP h.1) (ihQ h.2)
  | Parallel P X Q ihP ihQ =>
      intro h
      exact contraction_alpha_traces_Parallel (ihP h.1) (ihQ h.2)
  | Hiding P X ih =>
      intro h
      obtain ⟨T, hT⟩ := traces_noPN_Constant h
      refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
      intro M1 M2
      have hPM : traces P M1 = traces P M2 := by rw [hT]
      simp only [traces, hPM]
  | Renaming P r ih =>
      intro h
      exact contraction_alpha_traces_Renaming (ih h)
  | Seq_compo P Q ihP ihQ =>
      intro h
      rcases h with ⟨hgP, hsP, hnQ⟩ | ⟨hgP, hgQ⟩
      · exact gSKIP_contraction_half_traces_Seq_compo (ihP hgP) (non_expanding_traces hnQ) hsP
      · exact contraction_alpha_traces_Seq_compo (ihP hgP) (ihQ hgQ)
  | Depth_rest P n ih =>
      intro h
      rcases h with h | h
      · exact contraction_alpha_traces_Depth_rest (ih h)
      · subst h
        refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
        intro M1 M2
        simp only [traces]
        exact zero_eq_rs_domT _ _
  | Proc_name pn =>
      intro h
      exact h.elim

theorem contraction_alpha_traces {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (traces P) (1 / 2 : ℝ) := by
  exact contraction_alpha_traces_lm

/- =============================================================*
 |                          [[P]]Tf                            |
 *============================================================= -/

theorem contraction_alpha_semTf {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (semTf P) (1 / 2 : ℝ) := by
  exact contraction_alpha_traces

/- =============================================================*
 |                         [[P]]Tfun                           |
 *============================================================= -/

theorem contraction_alpha_semTfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction_alpha (semTfun Pf) (1 / 2 : ℝ) := by
  intro hPf
  rcases isEmpty_or_nonempty p with hp | hp
  · refine ⟨by norm_num, map_alpha_of_const (by norm_num) ?_⟩
    intro x y
    have hxy : x = y := funext (fun i => (IsEmpty.false i).elim)
    rw [hxy]
  · refine prod_contra_alpha_if ?_
    intro i
    exact contraction_alpha_semTf (hPf i)

/- =============================================================*
 |                        contraction                          |
 *============================================================= -/

theorem contraction_semTfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction (semTfun Pf) := by
  intro hPf
  exact ⟨(1 / 2 : ℝ), contraction_alpha_semTfun hPf⟩

end
