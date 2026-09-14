           /- -------------------------------------------*
            |        lean-csp-prover                    |
            |                                           |
            |   Simp sets and tactics for the laws      |
            |   of the traces model T                   |
            *------------------------------------------- -/

import LeanCspProver.CSP.Csp_simp_attr
import LeanCspProver.CSP_T.CSP_T_law_decompo

/-!
# Simp sets and tactics for `cspT_*` laws

A law `eqT P M1 M2 Q` is, by `cspT_eqT_semantics`, an equality of two
elements of `domTType α`.  The lemmas below turn it into a statement
about trace membership,

  `∀ t, t :t traces P M1 ↔ t :t traces Q M2`

after which the `csp_T` simp set (`in_traces_*`) unfolds both sides into
a formula over the traces of the immediate subprocesses.  Most laws are
then closed by `grind` (which handles the `∃`/`∨` reasoning) or, for the
purely propositional ones, by `itauto`.

The usual shape of a proof is

```
theorem cspT_foo : eqT ... := by
  cspT_auto
```
or, when the automation needs help,
```
  cspT_ext          -- ∀ t, ... ↔ ...   (hypotheses are introduced)
  cspT_simp         -- unfold `traces` (raw form, `simp only [csp_T, *]`)
  cspT_grind        -- or `cspT_dist; itauto!`, or a manual argument
```

Things learnt while building this automation:

* `grind` works best on the *raw* unfolded form.  Distributing `∃` over
  `∨` first (`cspT_dist`) makes the propositional structure visible for
  `itauto`, but hides the witnesses `grind` needs.
* `aesop` is unusable here: its normalisation destructs `t : traceType α`
  into `⟨val, property⟩` and then spends all its heartbeats in `whnf` on
  `Abs_trace`/`nilt` terms.
* `tauto` case-splits on `∃`-hypotheses and cannot rebuild them; use
  `itauto!` (which treats `∃`-formulas as atoms) for the propositional part.
* Self-recursive decomposition lemmas (`ren_tr_decompo_right`, `par_tr_head`,
  `par_tr_head_Ev_Ev`, `par_tr_step`, ...) must NOT be handed to `grind`:
  every instance introduces fresh head/tail terms that re-match the pattern,
  and `grind` dies with a *stack overflow* (exit code 134), which produces no
  `file:line` error.  `scripts/axiom2thm.py` treats such builds as failed and
  restores the file.  Where a decomposition is needed, prove a one-shot
  unfolding lemma instead (see `in_traces_Renaming_Act_prefix` below).
* A literal `rfl` pattern inside a tactic *macro* is hygienised into a plain
  hypothesis name, so `rcases ... with rfl | _` does not `subst` — the macros
  below use an explicit `subst`.
* Conditional `@[csp_T]` lemmas are discharged with the same
  `simp only [csp_T, *]` call: an *atomic* hypothesis (e.g. `Injective f`)
  is found via `*`, but a disjunction or `∀`-form is not.
-/

open SumType Function

noncomputable section

/-! ## Extensionality -/

theorem domT_eq_iff {S T : domTType α} : S = T ↔ ∀ t, t :t S ↔ t :t T := by
  constructor
  · rintro rfl t; exact Iff.rfl
  · intro h
    exact le_antisymm (subdomT_iff.mpr fun t => (h t).1) (subdomT_iff.mpr fun t => (h t).2)

theorem cspT_eqT_iff {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT P M1 M2 Q ↔ ∀ t, t :t traces P M1 ↔ t :t traces Q M2 := by
  rw [cspT_eqT_semantics, domT_eq_iff]

theorem cspT_refT_iff {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    refT P M1 M2 Q ↔ ∀ t, t :t traces Q M2 → t :t traces P M1 := by
  rw [cspT_refT_semantics, subdomT_iff]

/-! ## The `csp_T` simp set -/

attribute [csp_T]
  nilt_in_T
  in_traces_STOP in_traces_SKIP in_traces_DIV in_traces_Act_prefix
  in_traces_Ext_pre_choice in_traces_Ext_choice in_traces_Int_choice
  in_traces_Rep_int_choice_sum in_traces_Rep_int_choice_nat in_traces_Rep_int_choice_set
  in_traces_Rep_int_choice_com in_traces_Rep_int_choice_f
  in_traces_IF in_traces_Parallel in_traces_Hiding in_traces_Renaming
  in_traces_Seq_compo in_traces_Depth_rest in_traces_Proc_name
  -- trace-level facts that the unfolded formulas need
  appt_same_head event_app_not_nil_left one_neq_nil one_neq_nil_sym
  appt_nil_left appt_nil_right noTick_nil noTick_Ev
  lengtht_zero
  ren_tr_decompo_left ren_tr_nil1 ren_tr_nil2
  mem_fun_to_rel mem_Renaming1_event mem_Renaming2_event mem_Renaming1_channel mem_Renaming2_channel
  -- channel-renaming computation rules; conditional, discharged from the
  -- hypotheses of the channel step laws (via the `*` in `cspT_simp`)
  Renaming1_channel_fun_f Renaming2_channel_fun_f Renaming_channel_fun_g
  Renaming1_channel_fun_h Renaming2_channel_fun_h
  -- derived operators are unfolded to the primitive ones
  Alpha_parallel_def Send_prefix_def Int_pre_choice_def Timeout_def
  -- (`Rec_prefix_def` / `Nondet_send_prefix_def` are NOT unfolded here: the
  --  membership lemmas below eliminate `Function.invFun`, which `grind`
  --  cannot reason about -- its e-matcher rejects variable-headed
  --  applications such as `f w`)
  -- index sets of replicated choice
  -- (`sumset` itself must NOT be in the set: on a variable `C` it unfolds to a
  --  `match` that no longer matches hypotheses such as `sumset C ≠ ∅`)
  open1 open2 type1check mem_sumset_cup
  -- set membership (the raw form uses `simp only`, so these have to be listed)
  Set.mem_setOf_eq Set.mem_union Set.mem_inter_iff Set.mem_diff Set.mem_compl_iff
  Set.mem_insert_iff Set.mem_singleton_iff Set.mem_image Set.mem_sUnion Set.mem_univ
  Set.mem_empty_iff_false Set.mem_range

open Classical in
/-- `∃ c ∈ S, if c ∈ S then P c else Q c` : the guard is always true. -/
@[csp_T] theorem exists_mem_ite {ι : Type _} {S : Set ι} {P Q : ι → Prop} :
    (∃ c ∈ S, if c ∈ S then P c else Q c) ↔ ∃ c ∈ S, P c := by
  constructor
  · rintro ⟨c, hc, h⟩; rw [if_pos hc] at h; exact ⟨c, hc, h⟩
  · rintro ⟨c, hc, h⟩; exact ⟨c, hc, by rw [if_pos hc]; exact h⟩

/-- Directional forms of `X ∩ Y = ∅` for `grind` (the `iff` form has no
    usable e-matching pattern). -/
theorem not_mem_right_of_inter_empty {ι : Type _} {X Y : Set ι} {x : ι}
    (h : X ∩ Y = ∅) (hx : x ∈ X) : x ∉ Y := fun hy =>
  Set.eq_empty_iff_forall_notMem.mp h x ⟨hx, hy⟩

theorem not_mem_left_of_inter_empty {ι : Type _} {X Y : Set ι} {x : ι}
    (h : X ∩ Y = ∅) (hy : x ∈ Y) : x ∉ X := fun hx =>
  Set.eq_empty_iff_forall_notMem.mp h x ⟨hx, hy⟩

/-- A witness from `S ≠ ∅`; handed to `grind`. -/
theorem exists_mem_of_ne_empty {ι : Type _} {S : Set ι} (h : S ≠ ∅) : ∃ x, x ∈ S :=
  Set.nonempty_iff_ne_empty.mpr h

@[csp_T] theorem exists_mem_of_ne_empty_iff {ι : Type _} {S : Set ι} (h : S ≠ ∅) :
    (∃ x, x ∈ S) ↔ True := by
  simpa using Set.nonempty_iff_ne_empty.mpr h

@[csp_T] theorem mem_lengthset {n : Nat} {P : proc p α} {M : p → domTType α} :
    n ∈ lengthset P M ↔
      ∃ t, t :t traces P M ∧ (n = lengtht t ∨ n = Nat.succ (lengtht t) ∧ noTick t) :=
  Iff.rfl

@[csp_T] theorem sumset_type1_def {X : Set α} :
    sumset (type1 X : sum (Set α) (Set β)) = type1 '' X := rfl

@[csp_T] theorem sumset_type2_def {X : Set β} :
    sumset (type2 X : sum (Set α) (Set β)) = type2 '' X := rfl

@[csp_T] theorem mem_sumset_type1 {c : sum α β} {X : Set α} :
    c ∈ sumset (type1 X : sum (Set α) (Set β)) ↔ ∃ x ∈ X, c = type1 x := by
  simp [sumset, eq_comm]

@[csp_T] theorem mem_sumset_type2 {c : sum α β} {X : Set β} :
    c ∈ sumset (type2 X : sum (Set α) (Set β)) ↔ ∃ x ∈ X, c = type2 x := by
  simp [sumset, eq_comm]

/-- `<Tick>` is not an `Ev`-headed trace (needed by the step laws, where the
    trace is split into the nil / Tick / Ev-headed cases first). -/
@[csp_T] theorem Tick_neq_Ev_appt {a : α} {s : traceType α} :
    (Abs_trace [event.Tick] : traceType α) ≠ Abs_trace [event.Ev a] ^^^ s := by
  intro h
  rcases (appt_decompo_one (a := event.Tick) (s := (Abs_trace [event.Ev a] : traceType α))
      (t := s) (Or.inl (noTick_Ev a))).mp h.symm with ⟨h1, _⟩ | ⟨h1, _⟩
  · have h2 := congrArg Rep_trace h1
    simp [Abs_trace_inverse] at h2
  · exact one_neq_nil h1

@[csp_T] theorem Ev_appt_neq_Tick {a : α} {s : traceType α} :
    Abs_trace [event.Ev a] ^^^ s ≠ (Abs_trace [event.Tick] : traceType α) :=
  fun h => Tick_neq_Ev_appt h.symm

/-- `Rec_prefix` and `Nondet_send_prefix` are defined via `Function.invFun`;
    computation rule for the injective case (`simp` matches the non-linear
    pattern, which `grind` cannot). -/
@[csp_T] theorem invFun_comp_self {x α : Type _} [Nonempty x] {f : x → α}
    (hf : Function.Injective f) {v : x} :
    Function.invFun f (f v) = v :=
  Function.leftInverse_invFun hf v

/-- Linear-pattern version of `invFun_comp_self` for `grind`
    (both `Function.invFun f c` and `f w` must occur as terms). -/
theorem invFun_comp_self' {x α : Type _} [Nonempty x] {f : x → α}
    (hf : Function.Injective f) {w : x} {c : α} (h : f w = c) :
    Function.invFun f c = w := by
  subst h; exact invFun_comp_self hf

open Classical in
/-- `Renaming1_event_fun` as an unconditional `if`, so that `grind`
    case-splits on `c = a` / `c = b` by itself. -/
theorem Renaming1_event_fun_ite {a b c : α} :
    Renaming1_event_fun a b c = if c = a then b else if c = b then a else c := by
  unfold Renaming1_event_fun
  rfl

open Classical in
/-- `Renaming2_event_fun` as an unconditional `if`. -/
theorem Renaming2_event_fun_ite {A : Set α} {b c : α} :
    Renaming2_event_fun A b c = if c ∈ A then b else c := by
  unfold Renaming2_event_fun
  rfl

open Classical in
/-- `hide_tr` on an `Ev`-headed trace, as an unconditional `if` so that
    `grind` case-splits on `a ∈ X` by itself (the Isabelle proofs do
    `case_tac "a : X"` by hand here). -/
theorem hide_tr_Ev_appt_ite {a : α} {X : Set α} {s : traceType α} :
    hide_tr (Abs_trace [event.Ev a] ^^^ s) X =
      if a ∈ X then hide_tr s X else Abs_trace [event.Ev a] ^^^ hide_tr s X := by
  by_cases h : a ∈ X
  · simp [h]
  · simp [h]

open Classical in
theorem hide_tr_one_ite {a : α} {X : Set α} :
    hide_tr (Abs_trace [event.Ev a] : traceType α) X =
      if a ∈ X then <> else Abs_trace [event.Ev a] := by
  by_cases h : a ∈ X
  · simp [h]
  · simp [h]

/-! ### `Rec_prefix` / `Nondet_send_prefix` membership

The definitions go through `Function.invFun`, which `grind` cannot handle
(its e-matcher rejects variable-headed application patterns such as `f w`).
With injectivity — which the step laws assume — the `invFun` disappears; the
unconditional primed versions are the fallback for non-injective uses. -/

@[csp_T 1100] theorem in_traces_Rec_prefix {x α : Type _} {p : Type _} [Inhabited x]
    {f : x → α} (hf : Function.Injective f) {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {M : p → domTType α} :
    (t :t traces (Rec_prefix f X Pf) M) ↔
      (t = <> ∨ ∃ w s, w ∈ X ∧ t = Abs_trace [event.Ev (f w)] ^^^ s ∧
        s :t traces (Pf w) M) := by
  rw [Rec_prefix_def, in_traces_Ext_pre_choice]
  constructor
  · rintro (rfl | ⟨a, s, rfl, hs, ha⟩)
    · exact Or.inl rfl
    · rcases ha with ⟨w, hw, rfl⟩
      rw [invFun_comp_self hf] at hs
      exact Or.inr ⟨w, s, hw, rfl, hs⟩
  · rintro (rfl | ⟨w, s, hw, rfl, hs⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨f w, s, rfl, by rw [invFun_comp_self hf]; exact hs, ⟨w, hw, rfl⟩⟩

@[csp_T] theorem in_traces_Rec_prefix' {x α : Type _} {p : Type _} [Inhabited x]
    {f : x → α} {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {M : p → domTType α} :
    (t :t traces (Rec_prefix f X Pf) M) ↔
      (t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧
        s :t traces (Pf (Function.invFun f a)) M ∧ a ∈ f '' X) := by
  rw [Rec_prefix_def, in_traces_Ext_pre_choice]

@[csp_T 1100] theorem in_traces_Nondet_send_prefix {x α : Type _} {p : Type _}
    [Inhabited α] [Inhabited x]
    {f : x → α} (hf : Function.Injective f) {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {M : p → domTType α} :
    (t :t traces (Nondet_send_prefix f X Pf) M) ↔
      (t = <> ∨ ∃ w s, w ∈ X ∧ t = Abs_trace [event.Ev (f w)] ^^^ s ∧
        s :t traces (Pf w) M) := by
  rw [Nondet_send_prefix_def, Int_pre_choice_def, in_traces_Rep_int_choice_com]
  constructor
  · rintro (rfl | ⟨a, ⟨w, hw, rfl⟩, hs⟩)
    · exact Or.inl rfl
    · rw [in_traces_Act_prefix] at hs
      rcases hs with rfl | ⟨s, rfl, hs⟩
      · exact Or.inl rfl
      · rw [invFun_comp_self hf] at hs
        exact Or.inr ⟨w, s, hw, rfl, hs⟩
  · rintro (rfl | ⟨w, s, hw, rfl, hs⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨f w, ⟨w, hw, rfl⟩, ?_⟩
      rw [in_traces_Act_prefix]
      exact Or.inr ⟨s, rfl, by rw [invFun_comp_self hf]; exact hs⟩

@[csp_T] theorem in_traces_Nondet_send_prefix' {x α : Type _} {p : Type _}
    [Inhabited α] [Inhabited x]
    {f : x → α} {X : Set x} {Pf : x → proc p α}
    {t : traceType α} {M : p → domTType α} :
    (t :t traces (Nondet_send_prefix f X Pf) M) ↔
      (t = <> ∨ ∃ a, a ∈ f '' X ∧
        t :t traces (a ~> Pf (Function.invFun f a)) M) := by
  rw [Nondet_send_prefix_def, Int_pre_choice_def, in_traces_Rep_int_choice_com]

/-- `rmTick` on an `Ev`-headed trace (linear pattern, safe for `grind`). -/
theorem rmTick_Ev_appt {a : α} {s : traceType α} :
    rmTick (Abs_trace [event.Ev a] ^^^ s) = Abs_trace [event.Ev a] ^^^ rmTick s :=
  rmTick_appt_dist (noTick_Ev a)

/-- `rmTick` is idempotent; `Seq_compo_assoc` produces nested `rmTick`s. -/
theorem rmTick_idem {s : traceType α} : rmTick (rmTick s) = rmTick s :=
  rmTick_nochange noTick_rmTick

/-! ### channel-renaming computation rules for the remaining cases -/

theorem forall_ne_of_channel_notin {x α : Type _} {f : x → α} {c : α}
    (h : (∀ x, c ≠ f x) ∨ c ∉ Set.range f) : ∀ x, c ≠ f x := by
  rcases h with h | h
  · exact h
  · exact fun x hx => h ⟨x, hx.symm⟩

/-- `cspT_Act_prefix_Renaming1_channel2_step_in` renames along `g <==> f`. -/
@[csp_T] theorem Renaming1_channel_fun_f_swap {x α : Type _} {f g : x → α} {v : x}
    (hf : Function.Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun g f (f v) = g v :=
  Renaming_channel_fun_g hf (fun a b => (hfg b a).symm)

@[csp_T] theorem Renaming1_channel_fun_notin {x α : Type _} {f g : x → α} {c : α}
    (hf : (∀ x, c ≠ f x) ∨ c ∉ Set.range f) (hg : (∀ x, c ≠ g x) ∨ c ∉ Set.range g) :
    Renaming1_channel_fun f g c = c := by
  classical
  by_cases hfg : ∀ x y, f x ≠ g y
  · have hfc : ¬ ∃ x, f x = c := fun ⟨x, hx⟩ => forall_ne_of_channel_notin hf x hx.symm
    have hgc : ¬ ∃ y, g y = c := fun ⟨y, hy⟩ => forall_ne_of_channel_notin hg y hy.symm
    simp [Renaming1_channel_fun, hfg, hfc, hgc]
  · simp [Renaming1_channel_fun, hfg]

@[csp_T] theorem Renaming2_channel_fun_notin {x α : Type _} {f g : x → α} {c : α}
    (hf : (∀ x, c ≠ f x) ∨ c ∉ Set.range f) :
    Renaming2_channel_fun f g c = c := by
  classical
  by_cases hfg : ∀ x y, f x ≠ g y
  · have hfc : ¬ ∃ x, f x = c := fun ⟨x, hx⟩ => forall_ne_of_channel_notin hf x hx.symm
    simp [Renaming2_channel_fun, hfg, hfc]
  · simp [Renaming2_channel_fun, hfg]

/-- Convert the `Set.range`-form "not a channel value" hypothesis of the
    `Rec_prefix`/`Nondet_send_prefix` notin laws into the pointwise form. -/
theorem chan_notin_of_range {x y α : Type _} {f : x → α} {h : y → α} {v : y}
    (hf : (∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) :
    (∀ x, h v ≠ f x) ∨ h v ∉ Set.range f := by
  rcases hf with hf | hf
  · exact Or.inl (fun x hx => hf x v hx.symm)
  · exact Or.inr (fun ⟨x, hx⟩ =>
      Set.eq_empty_iff_forall_notMem.mp hf (h v) ⟨⟨x, hx⟩, ⟨v, rfl⟩⟩)

theorem Renaming1_channel_fun_notin_range {x y α : Type _} {f g : x → α} {h : y → α} {v : y}
    (hf : (∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅)
    (hg : (∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) :
    Renaming1_channel_fun f g (h v) = h v :=
  Renaming1_channel_fun_notin (chan_notin_of_range hf) (chan_notin_of_range hg)

theorem Renaming2_channel_fun_notin_range {x y α : Type _} {f g : x → α} {h : y → α} {v : y}
    (hf : (∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) :
    Renaming2_channel_fun f g (h v) = h v :=
  Renaming2_channel_fun_notin (chan_notin_of_range hf)

/-! ### `Renaming` pushed through a prefix

`grind` loops on the recursive decomposition lemmas `ren_tr_decompo_left` /
`ren_tr_decompo_right` (each instance introduces a fresh renamed tail that
matches the other lemma again, until the stack overflows), so the
`[[r]]`-step of `Act_prefix` and `Ext_pre_choice` is unfolded once and for
all here; the priority puts these before the generic `in_traces_Renaming`. -/

@[csp_T 1100] theorem in_traces_Renaming_Act_prefix
    {t : traceType α} {a : α} {P : proc p α} {r : Set (α × α)} {M : p → domTType α} :
    (t :t traces ((a ~> P)[[r]]) M) ↔
      (t = <> ∨ ∃ b u, (a, b) ∈ r ∧ t = Abs_trace [event.Ev b] ^^^ u ∧
        u :t traces (P[[r]]) M) := by
  rw [in_traces_Renaming]
  constructor
  · rintro ⟨s, hren, hs⟩
    rcases (in_traces_Act_prefix).mp hs with rfl | ⟨s', rfl, hs'⟩
    · exact Or.inl (ren_tr_nil1.mp hren)
    · rcases ren_tr_decompo_left.mp hren with ⟨b, u, rfl, hab, hren'⟩
      exact Or.inr ⟨b, u, hab, rfl, (in_traces_Renaming).mpr ⟨s', hren', hs'⟩⟩
  · rintro (rfl | ⟨b, u, hab, rfl, hu⟩)
    · exact ⟨<>, ren_tr_nil1.mpr rfl, (in_traces_Act_prefix).mpr (Or.inl rfl)⟩
    · rcases (in_traces_Renaming).mp hu with ⟨s', hren', hs'⟩
      exact ⟨Abs_trace [event.Ev a] ^^^ s', ren_tr_decompo_left_if hab hren',
        (in_traces_Act_prefix).mpr (Or.inr ⟨s', rfl, hs'⟩)⟩

@[csp_T 1100] theorem in_traces_Renaming_Ext_pre_choice
    {t : traceType α} {X : Set α} {Pf : α → proc p α} {r : Set (α × α)}
    {M : p → domTType α} :
    (t :t traces ((proc.Ext_pre_choice X Pf)[[r]]) M) ↔
      (t = <> ∨ ∃ x b u, x ∈ X ∧ (x, b) ∈ r ∧ t = Abs_trace [event.Ev b] ^^^ u ∧
        u :t traces ((Pf x)[[r]]) M) := by
  rw [in_traces_Renaming]
  constructor
  · rintro ⟨s, hren, hs⟩
    rcases (in_traces_Ext_pre_choice).mp hs with rfl | ⟨x, s', rfl, hs', hx⟩
    · exact Or.inl (ren_tr_nil1.mp hren)
    · rcases ren_tr_decompo_left.mp hren with ⟨b, u, rfl, hab, hren'⟩
      exact Or.inr ⟨x, b, u, hx, hab, rfl, (in_traces_Renaming).mpr ⟨s', hren', hs'⟩⟩
  · rintro (rfl | ⟨x, b, u, hx, hab, rfl, hu⟩)
    · exact ⟨<>, ren_tr_nil1.mpr rfl, (in_traces_Ext_pre_choice).mpr (Or.inl rfl)⟩
    · rcases (in_traces_Renaming).mp hu with ⟨s', hren', hs'⟩
      exact ⟨Abs_trace [event.Ev x] ^^^ s', ren_tr_decompo_left_if hab hren',
        (in_traces_Ext_pre_choice).mpr (Or.inr ⟨x, s', rfl, hs', hx⟩)⟩

/-! ### renaming functions -/

@[simp] theorem Renaming1_event_fun_left {a b : α} : Renaming1_event_fun a b a = b := by
  unfold Renaming1_event_fun; simp

@[simp] theorem Renaming1_event_fun_right {a b : α} : Renaming1_event_fun a b b = a := by
  unfold Renaming1_event_fun
  by_cases h : b = a
  · subst h; simp
  · simp [h]

/-- Versions of `Renaming1_event_fun_left/right` with a *linear* pattern:
    `grind` cannot e-match `Renaming1_event_fun a b b` (non-linear), but it
    can use the equation hypothesis from its e-graph. -/
theorem Renaming1_event_fun_left' {a b c : α} (h : c = a) :
    Renaming1_event_fun a b c = b := by subst h; exact Renaming1_event_fun_left

theorem Renaming1_event_fun_right' {a b c : α} (h : c = b) :
    Renaming1_event_fun a b c = a := by subst h; exact Renaming1_event_fun_right

theorem Renaming1_event_fun_of_ne {a b c : α} (h1 : c ≠ a) (h2 : c ≠ b) :
    Renaming1_event_fun a b c = c := by
  unfold Renaming1_event_fun; simp [h1, h2]

theorem Renaming2_event_fun_of_mem {A : Set α} {b c : α} (h : c ∈ A) :
    Renaming2_event_fun A b c = b := by
  unfold Renaming2_event_fun; simp [h]

theorem Renaming2_event_fun_of_not_mem {A : Set α} {b c : α} (h : c ∉ A) :
    Renaming2_event_fun A b c = c := by
  unfold Renaming2_event_fun; simp [h]

/-! ## Tactics -/

/-- Turn an `eqT`/`refT` goal into a statement about one trace `t`
    (hypotheses of that form are unfolded as well, and everything is introduced). -/
macro "cspT_ext" : tactic =>
  `(tactic| (intros
             (try simp only [cspT_eqT_iff, cspT_refT_iff] at *)
             (try intro t)))

/-- Unfold `traces` with the `csp_T` simp set (raw form). -/
macro "cspT_simp" : tactic =>
  `(tactic| simp only [csp_T, *])

/-- Unfold `traces` and distribute `∃` over `∨` (for `itauto!`). -/
macro "cspT_dist" : tactic =>
  `(tactic| simp [csp_T, *, or_and_right, and_or_left, exists_or])

/-- `grind` with the trace facts that the unfolded laws need. -/
macro "cspT_grind" : tactic =>
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
      Renaming2_event_fun_of_mem, Renaming2_event_fun_of_not_mem])

/-- `cspT_grind` plus the head-computation rules that only the *step* laws
    need (kept out of `cspT_grind`: on the large alpha-parallel goals the
    extra instances push `grind` past the heartbeat limit). -/
macro "cspT_grind_step" : tactic =>
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
      Renaming2_event_fun_of_mem, Renaming2_event_fun_of_not_mem])

/-- The distributed unfolding used by the hand-written step proofs
    (hypotheses such as the `a ∈ X` case-split facts are picked up via `*`;
    as a macro this does not trigger the unused-simp-args linter on the
    per-goal runs of a `<;>` chain).

    `simp only` on purpose: with the full default simp set, profiling showed
    most of the time went into Mathlib's `∃`-indexed lemmas that never fire
    here (`IsEmpty.exists_iff`, `nonempty_subtype`, `*.exists_mem_sup`, …)
    — each tried ~1k times per call, with `IsEmpty`/`Nonempty` instance
    searches wandering through unrelated instance chains.  The explicit list
    below is the union of `simp?` outputs over the step-law call sites plus
    the standard propositional normalisations; extend it if a new call site
    needs another default-set lemma. -/
macro "cspT_step_simp" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only
      [csp_T, par_tr_head, par_tr_nil1, par_tr_Tick1,
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

/-- `cspT_grind_step` with raised search limits, for the biggest step goals
    (`Parallel_Timeout_split` and friends). -/
macro "cspT_grind_step_big" : tactic =>
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
      Renaming2_event_fun_of_mem, Renaming2_event_fun_of_not_mem])

/-- Isabelle-style attempt for the *step* laws: split the trace into
    nil / `<Tick>` / `<Ev a> ^^^ s` first (`trace_nil_or_Tick_or_Ev`), close
    nil by T1, and use `par_tr_Tick1` / `par_tr_head` as *simp* rules — they
    only apply once the trace is syntactically of the right shape, so unlike
    their use as `grind` lemmas they cannot loop.  The `Ev`-headed case needs
    the distributed form so that the parallel witnesses are eliminated by the
    `∃ u, u = _ ∧ _` simplifications (in Isabelle the witnesses are given by
    hand with `rule_tac x=... in exI`). -/
macro "cspT_auto_step" : tactic =>
  `(tactic| (intros
             (try simp only [cspT_eqT_iff, cspT_refT_iff] at *)
             (try (intro t
                   rcases trace_nil_or_Tick_or_Ev t with hnil | hnil | ⟨a, s, hnil⟩ <;>
                     subst hnil))
             all_goals first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try simp only [csp_T, par_tr_nil1, par_tr_Tick1,
                    false_and, and_false, exists_false, or_false, false_or, *])
                  first
                    | done
                    | cspT_grind_step
                    | ((try simp [csp_T, par_tr_head, par_tr_nil1, par_tr_Tick1,
                          Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
                          Renaming1_channel_fun_notin_range, Renaming2_channel_fun_notin_range,
                          -Subtype.exists, or_and_right, and_or_left, exists_or, *])
                       first
                         | done
                         | cspT_grind_step
                         | itauto!))))

/-- `cspT_auto_step`, but going straight to the distributed form: on the
    `Nondet_send_prefix`/`Rec_prefix` laws the raw-form `grind` attempt dies
    with a stack overflow before the distributed attempt is ever reached. -/
macro "cspT_auto_step_dist" : tactic =>
  `(tactic| (intros
             (try simp only [cspT_eqT_iff, cspT_refT_iff] at *)
             (try (intro t
                   rcases trace_nil_or_Tick_or_Ev t with hnil | hnil | ⟨a, s, hnil⟩ <;>
                     subst hnil))
             all_goals first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try simp [csp_T, par_tr_head, par_tr_nil1, par_tr_Tick1,
                     Renaming1_channel_fun_notin, Renaming2_channel_fun_notin,
                     Renaming1_channel_fun_notin_range, Renaming2_channel_fun_notin_range,
                     -Subtype.exists, or_and_right, and_or_left, exists_or, *])
                  first
                    | done
                    | cspT_grind_step
                    | itauto!)))

/-- `cspT_grind` extended with the channel-renaming computation rules
    (kept out of `cspT_grind` itself: the conditional lemmas disturb the
    search on unrelated goals). -/
macro "cspT_grind_chan" : tactic =>
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
      Renaming1_channel_fun_f, Renaming2_channel_fun_f, Renaming_channel_fun_g,
      Renaming1_channel_fun_h, Renaming2_channel_fun_h,
      Renaming1_channel_fun_notin, Renaming2_channel_fun_notin])

/-- `cspT_auto` with `cspT_grind_chan` (for the channel-renaming step laws). -/
macro "cspT_auto_chan" : tactic =>
  `(tactic| (intros
             (try simp only [cspT_eqT_iff, cspT_refT_iff] at *)
             (try (intro t
                   rcases eq_or_ne t <> with hnil | hnil
                   (try subst hnil)))
             all_goals first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try cspT_simp)
                  first
                    | done
                    | cspT_grind_chan
                    | (cspT_dist; first | done | itauto!))))

/-- The standard attempt: extensionality, a case split on `t = <>` (the nil
    trace is in every trace set by T1, so that case is closed by `nilt_in_T`
    before unfolding — `grind` cannot invent the nil witnesses itself),
    unfolding, then `grind`, and as a fallback the distributed form with
    `itauto!`. -/
macro "cspT_auto" : tactic =>
  `(tactic| (intros
             (try simp only [cspT_eqT_iff, cspT_refT_iff] at *)
             (try (intro t
                   -- NB: a literal `rfl` pattern inside a macro is hygienised
                   -- into a plain hypothesis name, so `subst` must be explicit
                   rcases eq_or_ne t <> with hnil | hnil
                   (try subst hnil)))
             all_goals first
               | exact iff_of_true nilt_in_T nilt_in_T
               | exact fun _ => nilt_in_T
               | ((try cspT_simp)
                  first
                    | done
                    | cspT_grind
                    | (cspT_dist; first | done | itauto!))))

end
