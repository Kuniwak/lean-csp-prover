           /- -------------------------------------------*
            |        lean-csp-prover                    |
            |                                           |
            |   Simp sets and tactics for the laws      |
            |   of the stable-failures model F          |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_simp
import LeanCspProver.CSP_F.CSP_F_law_decompo

/-!
# Simp sets and tactics for `cspF_*` laws

`eqF P M1 M2 Q` is equality of the pair `(traces P (fstF ∘ M1), failures P M1)`
with the corresponding pair for `Q`.  `cspF_eqF_iff` splits it into

  `(∀ t, t :t traces P (fstF ∘ M1) ↔ t :t traces Q (fstF ∘ M2))`   -- the T part
  `(∀ s X, (s, X) :f failures P M1 ↔ (s, X) :f failures Q M2)`     -- the F part

The T part is handled by `CSP_T_simp`; the `csp_F` simp set
(`in_failures_*`) unfolds the F part.

Laws involving `[+]` additionally need the healthiness conditions of
`domF` (T2, T3, F3, F4), which relate failures to traces.  They are
provided as `failures_T2`, `failures_T3`, `failures_F2`, `failures_F3`,
`failures_F4`, `failures_F2_F4`, `failures_Tick_nil` and are handed to
`grind` by `cspF_grind`.
-/

open SumType Function

noncomputable section

/-! ## Extensionality -/

theorem setF_eq_iff {F E : setFType α} : F = E ↔ ∀ s X, (s, X) :f F ↔ (s, X) :f E := by
  constructor
  · rintro rfl s X; exact Iff.rfl
  · intro h
    exact le_antisymm (subsetF_iff.mpr fun s X => (h s X).1)
      (subsetF_iff.mpr fun s X => (h s X).2)

theorem cspF_eqF_iff {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q ↔
      (∀ t, t :t traces P (fstF ∘ M1) ↔ t :t traces Q (fstF ∘ M2)) ∧
      (∀ s X, (s, X) :f failures P M1 ↔ (s, X) :f failures Q M2) := by
  rw [cspF_eqF_semantics, domT_eq_iff, setF_eq_iff]

theorem cspF_refF_iff {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    refF P M1 M2 Q ↔
      (∀ t, t :t traces Q (fstF ∘ M2) → t :t traces P (fstF ∘ M1)) ∧
      (∀ s X, (s, X) :f failures Q M2 → (s, X) :f failures P M1) := by
  rw [cspF_refF_semantics, subdomT_iff, subsetF_iff]

/-- An `F` law from the corresponding `T` law plus the failures part. -/
theorem cspF_eqF_of_eqT {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hT : eqT P (fstF ∘ M1) (fstF ∘ M2) Q)
    (hF : ∀ s X, (s, X) :f failures P M1 ↔ (s, X) :f failures Q M2) :
    eqF P M1 M2 Q :=
  cspF_eqF_iff.mpr ⟨cspT_eqT_iff.mp hT, hF⟩

theorem cspF_refF_of_refT {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (hT : refT P (fstF ∘ M1) (fstF ∘ M2) Q)
    (hF : ∀ s X, (s, X) :f failures Q M2 → (s, X) :f failures P M1) :
    refF P M1 M2 Q :=
  cspF_refF_iff.mpr ⟨cspT_refT_iff.mp hT, hF⟩

/-! ## Healthiness conditions, stated for `failures P M` -/

theorem failures_T2 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)}
    (h : (s, X) :f failures P M) : s :t traces P (fstF ∘ M) := by
  have := pairF_domF_T2 (SF := semFf P M) (s := s) (X := X) (by simpa using h)
  simpa using this

theorem failures_T3 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)}
    (hTick : s ^^^ (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M))
    (hNo : noTick s) :
    (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f failures P M := by
  have := pairF_domF_T3 (SF := semFf P M) (s := s) (X := X) (by simpa using hTick) hNo
  simpa using this

theorem failures_F2 {P : proc p α} {M : p → domFType α} {s : traceType α} {X Y : Set (event α)}
    (h : (s, X) :f failures P M) (hYX : Y ⊆ X) : (s, Y) :f failures P M :=
  memF_F2 h hYX

theorem failures_F3 {P : proc p α} {M : p → domFType α} {s : traceType α} {X Y : Set (event α)}
    (h : (s, X) :f failures P M) (hNo : noTick s)
    (hY : ∀ a, a ∈ Y → ¬ (s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) :
    (s, X ∪ Y) :f failures P M := by
  have := pairF_domF_F3 (SF := semFf P M) (s := s) (X := X) (Y := Y)
    (by simpa using h) hNo (by simpa using hY)
  simpa using this

theorem failures_F4 {P : proc p α} {M : p → domFType α} {s : traceType α}
    (hTick : s ^^^ (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M))
    (hNo : noTick s) :
    (s, Evset) :f failures P M := by
  have := pairF_domF_F4 (SF := semFf P M) (s := s) (by simpa using hTick) hNo
  simpa using this

theorem failures_F2_F4 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)}
    (hTick : s ^^^ (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M))
    (hNo : noTick s) (hX : X ⊆ Evset) :
    (s, X) :f failures P M :=
  failures_F2 (failures_F4 hTick hNo) hX

/-- The instance of `failures_F2_F4` at the empty trace, which is what the
    `[+]` laws need. -/
theorem failures_Tick_nil {P : proc p α} {M : p → domFType α} {X : Set (event α)}
    (hTick : (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M)) (hX : X ⊆ Evset) :
    (<>, X) :f failures P M :=
  failures_F2_F4 (by simpa [appt_nil_left] using hTick) noTick_nil hX

/-! ## The `csp_F` simp set -/

/-- `Depth_rest` failures mention `tickTrace`; unfold it so that the
    `Abs_trace [event.Tick]` lemmas apply. -/
@[csp_F] theorem tickTrace_eq : (tickTrace : traceType α) = Abs_trace [event.Tick] := rfl

attribute [csp_F]
  in_failures_STOP in_failures_SKIP in_failures_DIV in_failures_Act_prefix
  in_failures_Ext_pre_choice in_failures_Ext_choice in_failures_Int_choice
  in_failures_Rep_int_choice_sum in_failures_Rep_int_choice_nat in_failures_Rep_int_choice_set
  in_failures_Rep_int_choice_com in_failures_Rep_int_choice_f
  in_failures_IF in_failures_Parallel in_failures_Hiding in_failures_Renaming
  in_failures_Seq_compo in_failures_Depth_rest in_failures_Proc_name

/-! ### `ren_inv` membership -/

@[csp_F] theorem Ev_mem_ren_inv {r : Set (α × β)} {X : Set (event β)} {a : α} :
    event.Ev a ∈ ren_inv r X ↔ ∃ b, (a, b) ∈ r ∧ event.Ev b ∈ X := by
  constructor
  · rintro ⟨eb, heb, ⟨h, _⟩ | ⟨a', b, hab, ha', rfl⟩⟩
    · exact absurd h (by simp)
    · cases ha'
      exact ⟨b, hab, heb⟩
  · rintro ⟨b, hab, hb⟩
    exact ⟨event.Ev b, hb, Or.inr ⟨a, b, hab, rfl, rfl⟩⟩

@[csp_F] theorem Tick_mem_ren_inv {r : Set (α × β)} {X : Set (event β)} :
    event.Tick ∈ ren_inv r X ↔ event.Tick ∈ X := by
  constructor
  · rintro ⟨eb, heb, ⟨_, rfl⟩ | ⟨a', b, _, ha', _⟩⟩
    · exact heb
    · exact absurd ha' (by simp)
  · intro h
    exact ⟨event.Tick, h, Or.inl ⟨rfl, rfl⟩⟩

/-! ### `Renaming` pushed through a prefix (failures part)

The traces part of the `[[r]]`-step laws is handled by
`in_traces_Renaming_Act_prefix` / `in_traces_Renaming_Ext_pre_choice`
(see `CSP_T_simp`); these are the corresponding one-shot unfoldings of the
failures, avoiding the looping `ren_tr` decomposition lemmas in `grind`. -/

@[csp_F 1100] theorem in_failures_Renaming_Act_prefix
    {t : traceType α} {Xa : Set (event α)} {a : α} {P : proc p α}
    {r : Set (α × α)} {M : p → domFType α} :
    ((t, Xa) :f failures ((a ~> P)[[r]]) M) ↔
      ((t = <> ∧ event.Ev a ∉ ren_inv r Xa) ∨
        ∃ b u, (a, b) ∈ r ∧ t = Abs_trace [event.Ev b] ^^^ u ∧
          (u, Xa) :f failures (P[[r]]) M) := by
  rw [in_failures_Renaming]
  constructor
  · rintro ⟨s, t', X', heq, hren, hF⟩
    cases heq
    rcases (in_failures_Act_prefix).mp hF with ⟨X', heq, hnotin⟩ | ⟨s', X', heq, hF'⟩
    · cases heq
      exact Or.inl ⟨ren_tr_nil1.mp hren, hnotin⟩
    · cases heq
      rcases ren_tr_decompo_left.mp hren with ⟨b, u, rfl, hab, hren'⟩
      exact Or.inr ⟨b, u, hab, rfl,
        (in_failures_Renaming).mpr ⟨s', u, Xa, rfl, hren', hF'⟩⟩
  · rintro (⟨rfl, hnotin⟩ | ⟨b, u, hab, rfl, hu⟩)
    · exact ⟨<>, <>, Xa, rfl, ren_tr_nil1.mpr rfl,
        (in_failures_Act_prefix).mpr (Or.inl ⟨ren_inv r Xa, rfl, hnotin⟩)⟩
    · rcases (in_failures_Renaming).mp hu with ⟨s', t', X', heq, hren', hF'⟩
      cases heq
      exact ⟨Abs_trace [event.Ev a] ^^^ s', _, Xa, rfl,
        ren_tr_decompo_left_if hab hren',
        (in_failures_Act_prefix).mpr (Or.inr ⟨s', ren_inv r Xa, rfl, hF'⟩)⟩

@[csp_F 1100] theorem in_failures_Renaming_Ext_pre_choice
    {t : traceType α} {Xa : Set (event α)} {A : Set α} {Pf : α → proc p α}
    {r : Set (α × α)} {M : p → domFType α} :
    ((t, Xa) :f failures ((proc.Ext_pre_choice A Pf)[[r]]) M) ↔
      ((t = <> ∧ (event.Ev '' A) ∩ ren_inv r Xa = ∅) ∨
        ∃ x b u, x ∈ A ∧ (x, b) ∈ r ∧ t = Abs_trace [event.Ev b] ^^^ u ∧
          (u, Xa) :f failures ((Pf x)[[r]]) M) := by
  rw [in_failures_Renaming]
  constructor
  · rintro ⟨s, t', X', heq, hren, hF⟩
    cases heq
    rcases (in_failures_Ext_pre_choice).mp hF with ⟨Y, heq, hempty⟩ | ⟨x, s', Y, heq, hF', hx⟩
    · cases heq
      exact Or.inl ⟨ren_tr_nil1.mp hren, hempty⟩
    · cases heq
      rcases ren_tr_decompo_left.mp hren with ⟨b, u, rfl, hab, hren'⟩
      exact Or.inr ⟨x, b, u, hx, hab, rfl,
        (in_failures_Renaming).mpr ⟨s', u, Xa, rfl, hren', hF'⟩⟩
  · rintro (⟨rfl, hempty⟩ | ⟨x, b, u, hx, hab, rfl, hu⟩)
    · exact ⟨<>, <>, Xa, rfl, ren_tr_nil1.mpr rfl,
        (in_failures_Ext_pre_choice).mpr (Or.inl ⟨ren_inv r Xa, rfl, hempty⟩)⟩
    · rcases (in_failures_Renaming).mp hu with ⟨s', t', X', heq, hren', hF'⟩
      cases heq
      exact ⟨Abs_trace [event.Ev x] ^^^ s', _, Xa, rfl,
        ren_tr_decompo_left_if hab hren',
        (in_failures_Ext_pre_choice).mpr (Or.inr ⟨x, s', ren_inv r Xa, rfl, hF', hx⟩)⟩

/-- Pointwise form of the `Ext_pre_choice` nil-refusal condition. -/
theorem Ev_image_inter_empty_iff {α : Type _} {A : Set α} {Y : Set (event α)} :
    (event.Ev '' A) ∩ Y = ∅ ↔ ∀ a ∈ A, event.Ev a ∉ Y := by
  constructor
  · intro h a ha hY
    exact Set.eq_empty_iff_forall_notMem.mp h (event.Ev a) ⟨⟨a, ha, rfl⟩, hY⟩
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro e ⟨⟨a, ha, rfl⟩, hY⟩
    exact h a ha hY

/-! ### `Rec_prefix` / `Nondet_send_prefix` failures without `Function.invFun`

Mirrors `in_traces_Rec_prefix` / `in_traces_Nondet_send_prefix` in
`CSP_T_simp` (see there for why `grind` cannot handle `invFun`). -/

@[csp_F 1100] theorem in_failures_Rec_prefix {x α : Type _} {p : Type _} [Inhabited x]
    {f : x → α} (hf : Function.Injective f) {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {Xa : Set (event α)} {M : p → domFType α} :
    ((t, Xa) :f failures (Rec_prefix f X Pf) M) ↔
      ((t = <> ∧ ∀ w ∈ X, event.Ev (f w) ∉ Xa) ∨
        ∃ w u, w ∈ X ∧ t = Abs_trace [event.Ev (f w)] ^^^ u ∧
          (u, Xa) :f failures (Pf w) M) := by
  rw [Rec_prefix_def, in_failures_Ext_pre_choice]
  constructor
  · rintro (⟨Y, heq, hempty⟩ | ⟨a, s, Y, heq, hF, ha⟩)
    · cases heq
      refine Or.inl ⟨rfl, fun w hw => ?_⟩
      exact Ev_image_inter_empty_iff.mp hempty (f w) ⟨w, hw, rfl⟩
    · cases heq
      rcases ha with ⟨w, hw, rfl⟩
      rw [invFun_comp_self hf] at hF
      exact Or.inr ⟨w, s, hw, rfl, hF⟩
  · rintro (⟨rfl, hpt⟩ | ⟨w, u, hw, rfl, hF⟩)
    · refine Or.inl ⟨Xa, rfl, Ev_image_inter_empty_iff.mpr ?_⟩
      rintro a ⟨w, hw, rfl⟩
      exact hpt w hw
    · exact Or.inr ⟨f w, u, Xa, rfl,
        by rw [invFun_comp_self hf]; exact hF, ⟨w, hw, rfl⟩⟩

@[csp_F] theorem in_failures_Rec_prefix' {x α : Type _} {p : Type _} [Inhabited x]
    {f : x → α} {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {Xa : Set (event α)} {M : p → domFType α} :
    ((t, Xa) :f failures (Rec_prefix f X Pf) M) ↔
      ((∃ Y, (t, Xa) = ((<> : traceType α), Y) ∧ (event.Ev '' (f '' X)) ∩ Y = ∅) ∨
        ∃ a s Y, (t, Xa) = (Abs_trace [event.Ev a] ^^^ s, Y) ∧
          (s, Y) :f failures (Pf (Function.invFun f a)) M ∧ a ∈ f '' X) := by
  rw [Rec_prefix_def, in_failures_Ext_pre_choice]

@[csp_F 1100] theorem in_failures_Nondet_send_prefix {x α : Type _} {p : Type _}
    [Inhabited x]
    {f : x → α} (hf : Function.Injective f) {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {Xa : Set (event α)} {M : p → domFType α} :
    ((t, Xa) :f failures (Nondet_send_prefix f X Pf) M) ↔
      ((t = <> ∧ ∃ w, w ∈ X ∧ event.Ev (f w) ∉ Xa) ∨
        ∃ w u, w ∈ X ∧ t = Abs_trace [event.Ev (f w)] ^^^ u ∧
          (u, Xa) :f failures (Pf w) M) := by
  rw [Nondet_send_prefix_def, Int_pre_choice_def, in_failures_Rep_int_choice_com]
  constructor
  · rintro ⟨a, ⟨w, hw, rfl⟩, hF⟩
    rw [in_failures_Act_prefix] at hF
    rcases hF with ⟨Y, heq, hnotin⟩ | ⟨s, Y, heq, hF⟩
    · cases heq
      exact Or.inl ⟨rfl, w, hw, hnotin⟩
    · cases heq
      rw [invFun_comp_self hf] at hF
      exact Or.inr ⟨w, s, hw, rfl, hF⟩
  · rintro (⟨rfl, w, hw, hnotin⟩ | ⟨w, u, hw, rfl, hF⟩)
    · exact ⟨f w, ⟨w, hw, rfl⟩,
        (in_failures_Act_prefix).mpr (Or.inl ⟨Xa, rfl, hnotin⟩)⟩
    · exact ⟨f w, ⟨w, hw, rfl⟩,
        (in_failures_Act_prefix).mpr
          (Or.inr ⟨u, Xa, rfl, by rw [invFun_comp_self hf]; exact hF⟩)⟩

@[csp_F] theorem in_failures_Nondet_send_prefix' {x α : Type _} {p : Type _}
    [Inhabited x]
    {f : x → α} {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {Xa : Set (event α)} {M : p → domFType α} :
    ((t, Xa) :f failures (Nondet_send_prefix f X Pf) M) ↔
      (∃ a, a ∈ f '' X ∧
        (t, Xa) :f failures (a ~> Pf (Function.invFun f a)) M) := by
  rw [Nondet_send_prefix_def, Int_pre_choice_def, in_failures_Rep_int_choice_com]

/-! ## Tactics -/

/-- Split `eqF`/`refF` (goal and hypotheses) into the T part and the F part
    and introduce everything (`t` resp. `s X`). -/
macro "cspF_ext" : tactic =>
  `(tactic| (intros
             (try simp only [cspF_eqF_iff, cspF_refF_iff, cspT_eqT_iff, cspT_refT_iff] at *)
             (try constructor) <;> (try intro t) <;> (try intro X)))

/-- Unfold `traces` and `failures` (raw form). -/
macro "cspF_simp" : tactic =>
  `(tactic| simp only [csp_T, csp_F, *])

/-- Unfold and distribute `∃` over `∨` (for `itauto!`). -/
macro "cspF_dist" : tactic =>
  `(tactic| simp [csp_T, csp_F, *, or_and_right, and_or_left, exists_or])

/-- `grind` with the trace facts and the healthiness conditions. -/
macro "cspF_grind" : tactic =>
  `(tactic| grind [nilt_in_T, exists_mem_of_ne_empty, appt_nil_right, appt_nil_left, par_tr_sym,
      one_neq_nil, event_app_not_nil_left, event_app_not_nil_right, appt_same_head,
      noTick_nil, noTick_Ev,
      hide_tr_nil, par_tr_nil_left, par_tr_nil_right, par_tr_Tick_left, par_tr_Tick_right,
      par_tr_nil_nil, par_tr_Tick_Tick, sett_nil,
      ren_tr_nil1, ren_tr_nil2, ren_tr_Tick1, ren_tr_Tick2,
      ren_tr_decompo_left, ren_tr_one_decompo_left, ren_tr_one_decompo_right, ren_tr_one,
      rmTick_nil, rmTick_Tick, rmTick_nochange, noTick_rmTick,
      Renaming1_event_fun_left, Renaming1_event_fun_right, Renaming1_event_fun_of_ne,
      Renaming1_event_fun_left', Renaming1_event_fun_right',
      Renaming2_event_fun_of_mem, Renaming2_event_fun_of_not_mem,
      Set.union_comm, Set.union_assoc,
      failures_Tick_nil, failures_T2, failures_F2])

/-- `cspF_grind` plus the head-computation rules for the *step* laws
    (see `cspT_grind_step`). -/
macro "cspF_grind_step" : tactic =>
  `(tactic| grind [nilt_in_T, exists_mem_of_ne_empty, appt_nil_right, appt_nil_left, par_tr_sym,
      not_mem_right_of_inter_empty, not_mem_left_of_inter_empty,
      one_neq_nil, event_app_not_nil_left, event_app_not_nil_right, appt_same_head,
      noTick_nil, noTick_Ev,
      hide_tr_nil, hide_tr_Tick, hide_tr_Ev_appt_ite, hide_tr_one_ite,
      Renaming1_event_fun_ite, Renaming2_event_fun_ite,
      Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
      rmTick_Ev_appt, rmTick_idem,
      par_tr_nil_left, par_tr_nil_right, par_tr_Tick_left, par_tr_Tick_right,
      par_tr_nil_nil, par_tr_Tick_Tick, sett_nil, par_tr_nil1, par_tr_Tick1,
      Tick_neq_Ev_appt, Ev_appt_neq_Tick,
      ren_tr_nil1, ren_tr_nil2, ren_tr_Tick1, ren_tr_Tick2,
      ren_tr_decompo_left, ren_tr_one_decompo_left, ren_tr_one_decompo_right, ren_tr_one,
      rmTick_nil, rmTick_Tick, rmTick_nochange, noTick_rmTick,
      Renaming1_event_fun_left, Renaming1_event_fun_right, Renaming1_event_fun_of_ne,
      Renaming1_event_fun_left', Renaming1_event_fun_right',
      Renaming2_event_fun_of_mem, Renaming2_event_fun_of_not_mem,
      Set.union_comm, Set.union_assoc,
      failures_Tick_nil, failures_T2, failures_F2])

/-- `cspT_auto_step` for the failures model (see `CSP_T_simp`). -/
macro "cspF_auto_step" : tactic =>
  `(tactic| (intros
             (try simp only [cspF_eqF_iff, cspF_refF_iff, cspT_eqT_iff, cspT_refT_iff] at *)
             (try constructor) <;>
               (try (intro t
                     (try intro X)
                     rcases trace_nil_or_Tick_or_Ev t with hnil | hnil | ⟨a, s, hnil⟩ <;>
                       subst hnil)) <;>
             first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try simp only [csp_T, csp_F, par_tr_nil1, par_tr_Tick1,
                    false_and, and_false, exists_false, or_false, false_or, *])
                  first
                    | done
                    | cspF_grind_step
                    | ((try simp [csp_T, csp_F, par_tr_head, par_tr_nil1, par_tr_Tick1,
                          Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
                          Renaming1_channel_fun_notin_range, Renaming2_channel_fun_notin_range,
                          -Subtype.exists, or_and_right, and_or_left, exists_or, *])
                       first
                         | done
                         | cspF_grind_step
                         | itauto!))))

/-- `cspT_step_simp` with the failures unfoldings (see `CSP_T_simp`;
    `simp only` with an explicit closure for the same profiling reason
    documented there). -/
macro "cspF_step_simp" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only
      [csp_T, csp_F, par_tr_head, par_tr_nil1, par_tr_Tick1,
       or_and_right, and_or_left, exists_or,
       and_true, true_and, and_false, false_and, and_self, and_self_left, and_self_right,
       or_self, or_false, false_or, true_or, or_true, or_self_left, or_self_right,
       iff_or_self, not_true_eq_false, not_false_eq_true, and_imp, forall_exists_index,
       ne_eq, exists_false, exists_eq_left, exists_eq_left', exists_eq_right,
       exists_eq_right', exists_eq, exists_and_left, exists_and_right, exists_prop,
       ↓existsAndEq, appt_nil, appt_same_head, appt_decompo_one_sym, one_neq_nil,
       appt_decompo_one, appt_nil_sym, par_tr_nil2, par_tr_nil_Tick,
       exists_eq_right_right', and_not_self, exists_const, exists_eq',
       Prod.mk.injEq, Set.union_singleton,
       noTick_Ev, not_noTick_Tick, not_noTick_unnil, Event_eq,
       Subtype.forall, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
       reduceCtorEq, ↓reduceIte, *])

/-- `cspF_grind_step` with raised search limits. -/
macro "cspF_grind_step_big" : tactic =>
  `(tactic| grind (splits := 25) (ematch := 18) (gen := 14) [nilt_in_T, exists_mem_of_ne_empty,
      appt_nil_right, appt_nil_left, par_tr_sym,
      not_mem_right_of_inter_empty, not_mem_left_of_inter_empty,
      one_neq_nil, event_app_not_nil_left, event_app_not_nil_right, appt_same_head,
      noTick_nil, noTick_Ev,
      hide_tr_nil, hide_tr_Tick, hide_tr_Ev_appt_ite, hide_tr_one_ite,
      Renaming1_event_fun_ite, Renaming2_event_fun_ite,
      Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
      rmTick_Ev_appt, rmTick_idem,
      par_tr_nil_left, par_tr_nil_right, par_tr_Tick_left, par_tr_Tick_right,
      par_tr_nil_nil, par_tr_Tick_Tick, sett_nil, par_tr_nil1, par_tr_Tick1,
      Tick_neq_Ev_appt, Ev_appt_neq_Tick,
      ren_tr_nil1, ren_tr_nil2, ren_tr_Tick1, ren_tr_Tick2,
      ren_tr_decompo_left, ren_tr_one_decompo_left, ren_tr_one_decompo_right, ren_tr_one,
      rmTick_nil, rmTick_Tick, rmTick_nochange, noTick_rmTick,
      Renaming1_event_fun_left, Renaming1_event_fun_right, Renaming1_event_fun_of_ne,
      Renaming1_event_fun_left', Renaming1_event_fun_right',
      Renaming2_event_fun_of_mem, Renaming2_event_fun_of_not_mem,
      Set.union_comm, Set.union_assoc,
      failures_Tick_nil, failures_T2, failures_F2])

/-- `cspT_auto_step_dist` for the failures model. -/
macro "cspF_auto_step_dist" : tactic =>
  `(tactic| (intros
             (try simp only [cspF_eqF_iff, cspF_refF_iff, cspT_eqT_iff, cspT_refT_iff] at *)
             (try constructor) <;>
               (try (intro t
                     (try intro X)
                     rcases trace_nil_or_Tick_or_Ev t with hnil | hnil | ⟨a, s, hnil⟩ <;>
                       subst hnil)) <;>
             first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try simp [csp_T, csp_F, par_tr_head, par_tr_nil1, par_tr_Tick1,
                     Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
                     Renaming1_channel_fun_notin_range, Renaming2_channel_fun_notin_range,
                     -Subtype.exists, or_and_right, and_or_left, exists_or, *])
                  first
                    | done
                    | cspF_grind_step
                    | itauto!)))

/-- `cspF_grind` extended with the channel-renaming computation rules. -/
macro "cspF_grind_chan" : tactic =>
  `(tactic| grind [nilt_in_T, exists_mem_of_ne_empty, appt_nil_right, appt_nil_left, par_tr_sym,
      not_mem_right_of_inter_empty, not_mem_left_of_inter_empty,
      one_neq_nil, event_app_not_nil_left, event_app_not_nil_right, appt_same_head,
      noTick_nil, noTick_Ev,
      hide_tr_nil, hide_tr_Tick, hide_tr_Ev_appt_ite, hide_tr_one_ite,
      Renaming1_event_fun_ite, Renaming2_event_fun_ite,
      Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
      rmTick_Ev_appt, rmTick_idem,
      par_tr_nil_left, par_tr_nil_right, par_tr_Tick_left, par_tr_Tick_right,
      par_tr_nil_nil, par_tr_Tick_Tick, sett_nil, par_tr_nil1, par_tr_Tick1,
      Tick_neq_Ev_appt, Ev_appt_neq_Tick,
      ren_tr_nil1, ren_tr_nil2, ren_tr_Tick1, ren_tr_Tick2,
      ren_tr_decompo_left, ren_tr_one_decompo_left, ren_tr_one_decompo_right, ren_tr_one,
      rmTick_nil, rmTick_Tick, rmTick_nochange, noTick_rmTick,
      Set.union_comm, Set.union_assoc,
      failures_Tick_nil, failures_T2, failures_F2,
      Renaming1_channel_fun_f, Renaming2_channel_fun_f, Renaming_channel_fun_g,
      Renaming1_channel_fun_h, Renaming2_channel_fun_h,
      Renaming1_channel_fun_notin, Renaming2_channel_fun_notin])

/-- `cspF_auto` with `cspF_grind_chan` (for the channel-renaming step laws). -/
macro "cspF_auto_chan" : tactic =>
  `(tactic| (intros
             (try simp only [cspF_eqF_iff, cspF_refF_iff, cspT_eqT_iff, cspT_refT_iff] at *)
             (try constructor) <;>
               (try (intro t
                     (try intro X)
                     rcases eq_or_ne t <> with hnil | hnil
                     (try subst hnil))) <;>
             first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try cspF_simp)
                  first
                    | done
                    | cspF_grind_chan
                    | (cspF_dist; first | done | itauto!))))

macro "cspF_auto" : tactic =>
  `(tactic| (intros
             (try simp only [cspF_eqF_iff, cspF_refF_iff, cspT_eqT_iff, cspT_refT_iff] at *)
             (try constructor) <;>
               (try (intro t
                     (try intro X)
                     -- NB: a literal `rfl` pattern inside a macro is hygienised
                     -- into a plain hypothesis name, so `subst` must be explicit
                     rcases eq_or_ne t <> with hnil | hnil
                     (try subst hnil))) <;>
             first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try cspF_simp)
                  first
                    | done
                    | cspF_grind
                    | (cspF_dist; first | done | itauto!))))


/-! ## Failures of `SKIP` and of `(? :Y -> Pf) [+] (SKIP | DIV)` -/

/-- Failures of `SKIP`, split by the trace. -/
theorem in_failures_SKIP_split {s : traceType α} {W : Set (event α)}
    {M : p → domFType α} :
    ((s, W) :f failures (proc.SKIP : proc p α) M) ↔
      ((s = <> ∧ W ⊆ Evset) ∨ s = (Abs_trace [event.Tick] : traceType α)) := by
  rw [in_failures_SKIP]
  constructor
  · rintro (⟨V, hEq, hV⟩ | ⟨V, hEq⟩)
    · exact Or.inl ⟨(Prod.mk.inj hEq).1, by rw [(Prod.mk.inj hEq).2]; exact hV⟩
    · exact Or.inr (Prod.mk.inj hEq).1
  · rintro (⟨rfl, hW⟩ | rfl)
    · exact Or.inl ⟨W, rfl, hW⟩
    · exact Or.inr ⟨W, rfl⟩

theorem Tick_notin_traces_Ext_pre_choice {X : Set α} {Pf : α → proc p α}
    {M : p → domTType α} :
    ¬ ((Abs_trace [event.Tick] : traceType α) :t traces (proc.Ext_pre_choice X Pf) M) := by
  intro h
  rw [in_traces_Ext_pre_choice] at h
  rcases h with hnil | ⟨a, u, hu, -, -⟩
  · simp at hnil
  · simp at hu

/-- Failures of `(? :Y -> Pf) [+] Z` where `Z` is `SKIP` or `DIV`. -/
theorem in_failures_Ext_pre_choice_Ext_choice
    {Y : Set α} {Pf : α → proc p α} {Z : proc p α} {s : traceType α} {V : Set (event α)}
    {M : p → domFType α} (hZ : Z = proc.SKIP ∨ Z = proc.DIV) :
    ((s, V) :f failures ((proc.Ext_pre_choice Y Pf) [+] Z) M) ↔
      ((∃ a s', s = Abs_trace [event.Ev a] ^^^ s' ∧ (s', V) :f failures (Pf a) M ∧ a ∈ Y) ∨
        (Z = proc.SKIP ∧ s = (Abs_trace [event.Tick] : traceType α)) ∨
        (Z = proc.SKIP ∧ s = <> ∧ V ⊆ Evset)) := by
  rw [in_failures_Ext_choice]
  rcases hZ with rfl | rfl
  · constructor
    · rintro (⟨⟨V1, hEq⟩, -, hS⟩ | ⟨s1, ⟨V1, hEq⟩, hor, hne⟩ | ⟨V1, hEq, -, hsub⟩)
      · have hs : s = <> := (Prod.mk.inj hEq).1
        rw [in_failures_SKIP_split] at hS
        rcases hS with ⟨-, hW⟩ | hTk
        · exact Or.inr (Or.inr ⟨rfl, hs, hW⟩)
        · rw [hs] at hTk
          simp at hTk
      · have hs : s = s1 := (Prod.mk.inj hEq).1
        rcases hor with hpre | hS
        · rw [in_failures_Ext_pre_choice] at hpre
          rcases hpre with ⟨V', hEqn, -⟩ | ⟨a, s', V', hEqn, hPf, ha⟩
          · exact absurd ((Prod.mk.inj hEqn).1.symm.trans hs) (fun h => hne h.symm)
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqn
            exact Or.inl ⟨a, s', rfl, hPf, ha⟩
        · rw [in_failures_SKIP_split] at hS
          rcases hS with ⟨h0, -⟩ | hTk
          · exact absurd (hs.symm.trans h0) (fun h => hne (hs ▸ h))
          · exact Or.inr (Or.inl ⟨rfl, hTk⟩)
      · refine Or.inr (Or.inr ⟨rfl, (Prod.mk.inj hEq).1, ?_⟩)
        rw [(Prod.mk.inj hEq).2]
        exact hsub
    · rintro (⟨a, s', rfl, hPf, ha⟩ | ⟨-, rfl⟩ | ⟨-, rfl, hW⟩)
      · refine Or.inr (Or.inl ⟨Abs_trace [event.Ev a] ^^^ s', ⟨V, rfl⟩, Or.inl ?_, by simp⟩)
        rw [in_failures_Ext_pre_choice]
        exact Or.inr ⟨a, s', V, rfl, hPf, ha⟩
      · exact Or.inr (Or.inl ⟨Abs_trace [event.Tick], ⟨V, rfl⟩,
          Or.inr (in_failures_SKIP_split.mpr (Or.inr rfl)), by simp⟩)
      · exact Or.inr (Or.inr ⟨V, rfl, Or.inr (in_traces_SKIP.mpr (Or.inr rfl)), hW⟩)
  · constructor
    · rintro (⟨-, -, hD⟩ | ⟨s1, ⟨V1, hEq⟩, hor, hne⟩ | ⟨V1, hEq, hTk, -⟩)
      · exact absurd hD in_failures_DIV
      · have hs : s = s1 := (Prod.mk.inj hEq).1
        have hpre := hor.resolve_right in_failures_DIV
        rw [in_failures_Ext_pre_choice] at hpre
        rcases hpre with ⟨V', hEqn, -⟩ | ⟨a, s', V', hEqn, hPf, ha⟩
        · exact absurd ((Prod.mk.inj hEqn).1.symm.trans hs) (fun h => hne h.symm)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqn
          exact Or.inl ⟨a, s', rfl, hPf, ha⟩
      · rcases hTk with hT | hT
        · exact absurd hT Tick_notin_traces_Ext_pre_choice
        · rw [in_traces_DIV] at hT
          simp at hT
    · rintro (⟨a, s', rfl, hPf, ha⟩ | ⟨hS, -⟩ | ⟨hS, -, -⟩)
      · refine Or.inr (Or.inl ⟨Abs_trace [event.Ev a] ^^^ s', ⟨V, rfl⟩, Or.inl ?_, by simp⟩)
        rw [in_failures_Ext_pre_choice]
        exact Or.inr ⟨a, s', V, rfl, hPf, ha⟩
      · exact absurd hS (by simp)
      · exact absurd hS (by simp)


/-- Failures of `((? :Y -> Pf) [+] Z) -- X` for `Z` equal to `SKIP` or `DIV`. -/
theorem in_failures_Hiding_Ext_pre_choice_Ext_choice
    {X Y : Set α} {Pf : α → proc p α} {Z : proc p α} {M : p → domFType α}
    (hZ : Z = proc.SKIP ∨ Z = proc.DIV) (t : traceType α) (W : Set (event α)) :
    ((t, W) :f failures (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] Z) X) M) ↔
      ((t, W) :f failures
        ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] Z) |~|
          Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X))) M) := by
  rw [in_failures_Hiding, in_failures_Int_choice,
    in_failures_Ext_pre_choice_Ext_choice hZ, in_failures_Rep_int_choice_com]
  constructor
  · rintro ⟨s, V, hEq, hs⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Ext_pre_choice_Ext_choice hZ] at hs
    rcases hs with ⟨a, s', rfl, hPf, haY⟩ | ⟨hZS, hTk⟩ | ⟨hZS, hnil, hsub⟩
    · by_cases haX : a ∈ X
      · refine Or.inr ⟨a, ⟨haY, haX⟩, ?_⟩
        rw [in_failures_Hiding, hide_tr_in haX]
        exact ⟨s', W, rfl, hPf⟩
      · refine Or.inl ?_
        rw [hide_tr_notin_appt haX]
        exact Or.inl ⟨a, hide_tr s' X, rfl,
          in_failures_Hiding.mpr ⟨s', W, rfl, hPf⟩, ⟨haY, haX⟩⟩
    · rw [hTk, hide_tr_Tick]
      exact Or.inl (Or.inr (Or.inl ⟨hZS, rfl⟩))
    · rw [hnil, hide_tr_nil]
      refine Or.inl (Or.inr (Or.inr ⟨hZS, rfl, ?_⟩))
      exact fun e he => hsub (Or.inr he)
  · rintro (h | ⟨a, ⟨haY, haX⟩, hHide⟩)
    · rcases h with ⟨a, v, rfl, hHide, ⟨haY, haX⟩⟩ | ⟨hZS, hTk⟩ | ⟨hZS, hnil, hsub⟩
      · rw [in_failures_Hiding] at hHide
        obtain ⟨s', V, hEqv, hPf⟩ := hHide
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqv
        exact ⟨Abs_trace [event.Ev a] ^^^ s', W, by rw [hide_tr_notin_appt haX],
          (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inl ⟨a, s', rfl, hPf, haY⟩)⟩
      · exact ⟨Abs_trace [event.Tick], W, by rw [hTk, hide_tr_Tick],
          (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inr (Or.inl ⟨hZS, rfl⟩))⟩
      · refine ⟨<>, W, by rw [hnil, hide_tr_nil],
          (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inr (Or.inr ⟨hZS, rfl, ?_⟩))⟩
        rintro e (⟨b, -, rfl⟩ | he)
        · simp [Evset]
        · exact hsub he
    · rw [in_failures_Hiding] at hHide
      obtain ⟨s', V, hEqv, hPf⟩ := hHide
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqv
      exact ⟨Abs_trace [event.Ev a] ^^^ s', W, by rw [hide_tr_in haX],
        (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inl ⟨a, s', rfl, hPf, haY⟩)⟩

end
