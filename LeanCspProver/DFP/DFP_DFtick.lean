           /- -------------------------------------------*
            |                  DFtick                   |
            |                                           |
            |                   June 2007               |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DFP.DFP_Deadlock

open event
open fpmode

noncomputable section

variable {α : Type _}

/- Lean note:
   Isabelle's local simp-set update `declare csp_prefix_ss_def[simp]` has no
   direct analogue here. -/

/- *****************************************************************

         1. The most abstract deadlockfree process DFtick

 *****************************************************************) -/

/- *********************************************************
                         event
 *********************************************************) -/

/- typedecl Event    any event -/

inductive DFtickName where
  | DFtick
deriving DecidableEq, Inhabited

/- (*** Spc ***) -/

/- Lean note:
   Isabelle: `DFtickfun (DFtick) = (! x -> $(DFtick)) |~| SKIP`.
   `! x -> P` is the *internal* prefix choice (`Int_pre_choice`); an earlier
   port spelled it `Ext_pre_choice` (`? x -> P`), which breaks the
   deadlock-freedom characterisation: e.g. `(<>, X)` with `Tick ∈ X ≠ univ`
   is a failure of `! x -> P` (pick an offered event outside `X`) but not of
   `? x -> P` (which refuses only sets disjoint from its initials). Repaired.
   `Int_pre_choice` needs `[Inhabited α]` in this port (its `the_elem`
   encoding), hence that extra assumption throughout this file. -/

def DFtickfun [Inhabited α] : DFtickName → proc DFtickName α
  | DFtickName.DFtick =>
      Int_pre_choice Set.univ (fun _ : α => proc.Proc_name DFtickName.DFtick) |~| proc.SKIP

instance Set_DFtickfun [Inhabited α] : HasPNfun DFtickName α where
  PNfun := DFtickfun

@[simp]
theorem Set_DFtickfun_def [Inhabited α] (pn : DFtickName) :
    PNfun (p := DFtickName) (α := α) pn = DFtickfun (α := α) pn :=
  rfl

/- ---------------------------------------------------*
 |                  n-replicted spec                 |
 *--------------------------------------------------- -/

inductive RDFtickName where
  | RDFtick
deriving DecidableEq, Inhabited

/- (*** Spc ***) -/

def NatDFtick [Inhabited α] : Nat → proc RDFtickName α → proc RDFtickName α
  | 0, P => P
  | Nat.succ n, P =>
      (Int_pre_choice Set.univ (fun _ : α => NatDFtick n P) |~| proc.SKIP) |~| P

/- Lean note:
   Isabelle: `RDFtickfun (RDFtick) =
                (! x -> (!nat n .. NatDFtick n ($(RDFtick)))) |~| SKIP` —
   the prefix binds tighter than `|~|`, so `SKIP` is a *top-level* branch.
   An earlier port additionally read `! x ->` as `? x ->` and put the
   `|~| SKIP` inside the prefix body. Both repaired; without the repair
   `RDFtick_DFtick_ref2` is false (`SKIP`'s failure `(<>, Evset)` is not a
   failure of a process that must offer an event). -/

def RDFtickfun [Inhabited α] : RDFtickName → proc RDFtickName α
  | RDFtickName.RDFtick =>
      Int_pre_choice Set.univ (fun _ : α =>
        Rep_int_choice_nat Set.univ
          (fun n => NatDFtick n (proc.Proc_name RDFtickName.RDFtick))) |~| proc.SKIP

instance Set_RDFtickfun [Inhabited α] : HasPNfun RDFtickName α where
  PNfun := RDFtickfun

@[simp]
theorem Set_RDFtickfun_def [Inhabited α] (pn : RDFtickName) :
    PNfun (p := RDFtickName) (α := α) pn = RDFtickfun (α := α) pn :=
  rfl

/- *********************************************************
              DFtick lemma
 *********************************************************) -/

@[simp]
theorem guardedfun_DFtick [Inhabited α] :
    guardedfun (p := DFtickName) (q := DFtickName) (α := α) (DFtickfun (α := α)) := by
  intro pn
  cases pn
  exact ⟨(guarded_Int_pre_choice _ _).mpr fun _ => trivial, trivial⟩

private theorem noHide_NatDFtick [Inhabited α]
    {P : proc RDFtickName α} {n : Nat} (hP : noHide P) :
    noHide (NatDFtick n P) := by
  induction n with
  | zero => exact hP
  | succ n ih =>
      exact ⟨⟨(noHide_Int_pre_choice _ _).mpr fun _ => ih, trivial⟩, hP⟩

@[simp]
theorem guardedfun_RDFtick [Inhabited α] :
    guardedfun (p := RDFtickName) (q := RDFtickName) (α := α) (RDFtickfun (α := α)) := by
  intro pn
  cases pn
  refine ⟨(guarded_Int_pre_choice _ _).mpr fun _ => ?_, trivial⟩
  rw [noHide_Rep_int_choice_nat]
  intro n
  exact noHide_NatDFtick trivial

/- -------------------------------------------------*
 |                                                  |
 |  syntactical approach --> semantical approach    |
 |                                                  |
 * ------------------------------------------------- -/

/- (*** sub ***) -/

/- the `FPmode` disjunctions needed by unwind/FIX (any mode works, because
   both process functions are guarded) -/

private theorem DFtick_mode [Inhabited α] [HasFPmode] :
    FPmode = CPOmode ∨
      (FPmode = CMSmode ∧
        guardedfun (p := DFtickName) (q := DFtickName) (α := α) (DFtickfun (α := α))) ∨
      FPmode = MIXmode := by
  rcases hF : (FPmode : fpmode) with _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨rfl, guardedfun_DFtick⟩)
  · exact Or.inr (Or.inr rfl)

private theorem RDFtick_mode [Inhabited α] [HasFPmode] :
    FPmode = CPOmode ∨
      (FPmode = CMSmode ∧
        guardedfun (p := RDFtickName) (q := RDFtickName) (α := α) (RDFtickfun (α := α))) ∨
      FPmode = MIXmode := by
  rcases hF : (FPmode : fpmode) with _ | _ | _
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨rfl, guardedfun_RDFtick⟩)
  · exact Or.inr (Or.inr rfl)

theorem DFtick_is_DeadlockFree [Inhabited α] [HasFPmode] :
    isDeadlockFree (proc.Proc_name DFtickName.DFtick : proc DFtickName α) := by
  have hfail :
      failures (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF =
        failures (DFtickfun (α := α) DFtickName.DFtick) MF :=
    (cspF_eqF_semantics.mp («cspF_unwind» rfl DFtick_mode)).2
  rw [isDeadlockFree_def, DeadlockFree_def]
  intro s
  refine induct_trace
    (P := fun s => Tick ∉ sett s →
      ¬ ((s, Set.univ) :f
        failures (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF)) ?_ ?_ ?_
  · intro _ hFail
    rw [hfail] at hFail
    simp only [DFtickfun, Int_pre_choice] at hFail
    rcases in_failures_Int_choice.mp hFail with h | h
    · rcases in_failures_Rep_int_choice_com.mp h with ⟨a, -, ha⟩
      rcases in_failures_Act_prefix.mp ha with ⟨X, hEq, hnotin⟩ | ⟨s', X, hEq, -⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj hEq
        exact hnotin (Set.mem_univ _)
      · have hnil := (Prod.mk.inj hEq).1
        rcases (appt_nil_sym (noTick_Ev a)).mp hnil with ⟨h1, -⟩
        exact one_neq_nil h1
    · rcases in_failures_SKIP.mp h with ⟨X, hEq, hsub⟩ | ⟨X, hEq⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj hEq
        exact absurd (hsub (Set.mem_univ Tick)) (by simp [Evset])
      · exact one_neq_nil_sym (Prod.mk.inj hEq).1
  · intro hTick
    exact absurd (by rw [sett_one]; rfl) hTick
  · intro s a ih hTick hFail
    have hsett : sett (Abs_trace [Ev a] ^^^ s) = sett (Abs_trace [Ev a]) ∪ sett s :=
      sett_appt1 (Or.inl (noTick_Ev a))
    have hTick' : Tick ∉ sett s := by
      intro h
      exact hTick (by rw [hsett]; exact Set.mem_union_right _ h)
    rw [hfail] at hFail
    simp only [DFtickfun, Int_pre_choice] at hFail
    rcases in_failures_Int_choice.mp hFail with h | h
    · rcases in_failures_Rep_int_choice_com.mp h with ⟨b, -, hb⟩
      rcases in_failures_Act_prefix.mp hb with ⟨X, hEq, -⟩ | ⟨s', X, hEq, hs'⟩
      · have hnil := (Prod.mk.inj hEq).1
        exact one_neq_nil ((appt_nil (noTick_Ev a)).mp hnil).1
      · obtain ⟨hEq1, rfl⟩ := Prod.mk.inj hEq
        obtain ⟨-, rfl⟩ := appt_same_head.mp hEq1
        exact ih hTick' hs'
    · rcases in_failures_SKIP.mp h with ⟨X, hEq, -⟩ | ⟨X, hEq⟩
      · have hnil := (Prod.mk.inj hEq).1
        exact one_neq_nil ((appt_nil (noTick_Ev a)).mp hnil).1
      · have hone := (Prod.mk.inj hEq).1
        rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp hone with
          ⟨h1, -⟩ | ⟨h1, -⟩
        · have hnT := noTick_Ev (α := α) a
          rw [h1] at hnT
          exact hnT (by rw [sett_one]; rfl)
        · exact one_neq_nil h1

/- (*** main ***) -/

theorem DFtick_DeadlockFree [Inhabited α]
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α}
    (hRef : refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P) :
    isDeadlockFree P := by
  have hDF :
      DeadlockFree Set.univ (proc.Proc_name DFtickName.DFtick : proc DFtickName α) :=
    (isDeadlockFree_def _).mp DFtick_is_DeadlockFree
  have hFailSub :
      failures P MF <= failures (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF :=
    (cspF_refF_semantics
      (P := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
      (Q := P) (M1 := MF) (M2 := MF)).mp hRef |>.2
  rw [isDeadlockFree_def, DeadlockFree_def]
  intro s hsNoTick hsFail
  exact hDF s hsNoTick (hFailSub hsFail)

/- -------------------------------------------------*
 |                                                  |
 |  semantical approach --> syntactical approach    |
 |                                                  |
 * ------------------------------------------------- -/

private theorem FIX_DFtick_app [Inhabited α] :
    (FIX (DFtickfun (α := α))) DFtickName.DFtick =
      Rep_int_choice_nat Set.univ
        (fun n => FIXn n (DFtickfun (α := α)) DFtickName.DFtick) :=
  rfl

private theorem in_traces_FIX_DFtick [Inhabited α] [HasFPmode] {t : traceType α} :
    (t :t traces ((FIX (DFtickfun (α := α))) DFtickName.DFtick) (fstF ∘ MF)) ↔
      (t = <> ∨
        ∃ n, t :t traces (FIXn n (DFtickfun (α := α)) DFtickName.DFtick) (fstF ∘ MF)) := by
  rw [FIX_DFtick_app, in_traces_Rep_int_choice_nat]
  constructor
  · rintro (h | ⟨n, -, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, h⟩
  · rintro (h | ⟨n, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨n, Set.mem_univ n, h⟩

private theorem in_failures_FIX_DFtick [Inhabited α] [HasFPmode]
    {t : traceType α} {X : Set (event α)} :
    ((t, X) :f failures ((FIX (DFtickfun (α := α))) DFtickName.DFtick) MF) ↔
      ∃ n, (t, X) :f failures (FIXn n (DFtickfun (α := α)) DFtickName.DFtick) MF := by
  rw [FIX_DFtick_app, in_failures_Rep_int_choice_nat]
  exact ⟨fun ⟨n, _, h⟩ => ⟨n, h⟩, fun ⟨n, h⟩ => ⟨n, Set.mem_univ n, h⟩⟩

private theorem FIXn_succ_DFtick [Inhabited α] {n : Nat} :
    FIXn (n + 1) (DFtickfun (α := α)) DFtickName.DFtick =
      Int_pre_choice Set.univ
          (fun _ : α => FIXn n (DFtickfun (α := α)) DFtickName.DFtick) |~| proc.SKIP := by
  rw [FIXn_def, Function.iterate_succ_apply', ← FIXn_def]
  -- `Subst_procfun_Int_pre_choice` is no longer `rfl` (it goes through
  -- `(the_elem X).elim`), so the substitution has to be rewritten explicitly.
  rw [Subst_procfun_prod_p]
  change (Int_pre_choice Set.univ (fun _ : α => proc.Proc_name DFtickName.DFtick)
      << FIXn n DFtickfun) |~| proc.SKIP = _
  rw [Subst_procfun_Int_pre_choice]
  rfl

theorem traces_included_in_DFtick [Inhabited α] [HasFPmode] {t : traceType α} :
    t :t traces ((FIX DFtickfun) DFtickName.DFtick) (fstF ∘ MF) := by
  refine induct_trace ?_ ?_ ?_
  · exact in_traces_FIX_DFtick.mpr (Or.inl rfl)
  · refine in_traces_FIX_DFtick.mpr (Or.inr ⟨1, ?_⟩)
    rw [show (1 : Nat) = 0 + 1 from rfl, FIXn_succ_DFtick, in_traces_Int_choice]
    exact Or.inr (in_traces_SKIP.mpr (Or.inr rfl))
  · intro s a ih
    have hstep : ∀ n, s :t traces (FIXn n (DFtickfun (α := α)) DFtickName.DFtick) (fstF ∘ MF) →
        (Abs_trace [Ev a] ^^^ s) :t
          traces ((FIX (DFtickfun (α := α))) DFtickName.DFtick) (fstF ∘ MF) := by
      intro n hn
      refine in_traces_FIX_DFtick.mpr (Or.inr ⟨n + 1, ?_⟩)
      rw [FIXn_succ_DFtick, in_traces_Int_choice]
      refine Or.inl ?_
      rw [Int_pre_choice, in_traces_Rep_int_choice_com]
      exact Or.inr ⟨a, Set.mem_univ a, in_traces_Act_prefix.mpr (Or.inr ⟨s, rfl, hn⟩)⟩
    rcases in_traces_FIX_DFtick.mp ih with rfl | ⟨n, hn⟩
    · exact hstep 0 (in_traces_DIV.mpr rfl)
    · exact hstep n hn

theorem failures_included_in_DFtick_lm [Inhabited α] [HasFPmode]
    {t : traceType α} {X : Set (event α)} :
    (X ≠ Set.univ ∨ Tick ∈ sett t) →
      (t, X) :f failures ((FIX DFtickfun) DFtickName.DFtick) MF := by
  refine induct_trace
    (P := fun t => (X ≠ Set.univ ∨ Tick ∈ sett t) →
      (t, X) :f failures ((FIX (DFtickfun (α := α))) DFtickName.DFtick) MF) ?_ ?_ ?_
  · intro h
    have hX : X ≠ Set.univ := by
      rcases h with h | h
      · exact h
      · rw [sett_nil] at h
        exact absurd h (Set.notMem_empty _)
    rcases Set.ne_univ_iff_exists_notMem X |>.mp hX with ⟨e, he⟩
    refine in_failures_FIX_DFtick.mpr ⟨1, ?_⟩
    rw [show (1 : Nat) = 0 + 1 from rfl, FIXn_succ_DFtick, in_failures_Int_choice]
    rcases hcase : e with a | _
    · refine Or.inl ?_
      rw [Int_pre_choice, in_failures_Rep_int_choice_com]
      exact ⟨a, Set.mem_univ a,
        in_failures_Act_prefix.mpr (Or.inl ⟨X, rfl, hcase ▸ he⟩)⟩
    · refine Or.inr (in_failures_SKIP.mpr (Or.inl ⟨X, rfl, ?_⟩))
      intro x hx
      simp only [Evset, Set.mem_setOf_eq]
      intro hxTick
      exact he (hcase ▸ hxTick ▸ hx)
  · intro _
    refine in_failures_FIX_DFtick.mpr ⟨1, ?_⟩
    rw [show (1 : Nat) = 0 + 1 from rfl, FIXn_succ_DFtick, in_failures_Int_choice]
    exact Or.inr (in_failures_SKIP.mpr (Or.inr ⟨X, rfl⟩))
  · intro s a ih h
    have h' : X ≠ Set.univ ∨ Tick ∈ sett s := by
      rcases h with h | h
      · exact Or.inl h
      · rw [sett_appt1 (Or.inl (noTick_Ev a))] at h
        rcases h with h | h
        · rw [sett_one] at h
          exact absurd h (by simp)
        · exact Or.inr h
    rcases in_failures_FIX_DFtick.mp (ih h') with ⟨n, hn⟩
    refine in_failures_FIX_DFtick.mpr ⟨n + 1, ?_⟩
    rw [FIXn_succ_DFtick, in_failures_Int_choice]
    refine Or.inl ?_
    rw [Int_pre_choice, in_failures_Rep_int_choice_com]
    exact ⟨a, Set.mem_univ a, in_failures_Act_prefix.mpr (Or.inr ⟨s, X, rfl, hn⟩)⟩

theorem failures_included_in_DFtick [Inhabited α] [HasFPmode]
    {t : traceType α} {X : Set (event α)}
    (hX : X ≠ Set.univ) (_hTick : Tick ∈ sett t) :
    (t, X) :f failures ((FIX DFtickfun) DFtickName.DFtick) MF := by
  exact failures_included_in_DFtick_lm (t := t) (X := X) (Or.inl hX)

theorem DeadlockFree_DFtick [Inhabited α]
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α} :
    isDeadlockFree P →
      refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P := by
  intro hDF
  refine cspF_rw_left_ref (cspF_FIX DFtick_mode rfl) ?_
  rw [cspF_refF_semantics]
  constructor
  · rw [subdomT_iff]
    intro t _
    exact traces_included_in_DFtick
  · rw [subsetF_iff]
    intro t X htX
    refine failures_included_in_DFtick_lm ?_
    by_cases hX : X = Set.univ
    · subst hX
      by_cases hTick : Tick ∈ sett t
      · exact Or.inr hTick
      · exact absurd htX (hDF t hTick)
    · exact Or.inl hX

/- -------------------------------------------------*
 |                                                  |
 |  syntactical approach <--> semantical approach   |
 |                                                  |
 * ------------------------------------------------- -/

theorem DeadlockFree_DFtick_ref [Inhabited α]
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α} :
    isDeadlockFree P ↔
      refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P := by
  constructor
  · exact DeadlockFree_DFtick
  · exact DFtick_DeadlockFree

/- ================================================================*
 |                                                                |
 |                   n-replicted DF specification                 |
 |                                                                |
 *================================================================ -/

/- *******************************************************************
        relating function between DFtickName and Rep...
 *******************************************************************) -/

/- (*** ref1 ***) -/

def RepDF_to_DF : RDFtickName → proc DFtickName α
  | RDFtickName.RDFtick => proc.Proc_name DFtickName.DFtick

private theorem NatDFtick_succ_subst [Inhabited α] {n : Nat} {P : proc RDFtickName α}
    {f : RDFtickName → proc DFtickName α} :
    (NatDFtick (n + 1) P) << f =
      ((Int_pre_choice Set.univ (fun _ : α => (NatDFtick n P) << f) |~| proc.SKIP)
        |~| (P << f)) := by
  rw [show NatDFtick (n + 1) P =
      (Int_pre_choice Set.univ (fun _ : α => NatDFtick n P) |~| proc.SKIP) |~| P from rfl]
  simp only [Subst_procfun, Subst_procfun_Int_pre_choice]

theorem RDFtick_DFtick_ref1_induct_lm [Inhabited α] [HasFPmode] {n : Nat} :
    refF ((proc.Proc_name DFtickName.DFtick : proc DFtickName α)) MF MF
      ((NatDFtick n (proc.Proc_name RDFtickName.RDFtick)) << RepDF_to_DF) := by
  induction n with
  | zero => exact cspF_reflex_ref_P
  | succ n ih =>
      rw [NatDFtick_succ_subst]
      refine cspF_Int_choice_right ?_ cspF_reflex_ref_P
      refine cspF_rw_left_ref («cspF_unwind» rfl DFtick_mode) ?_
      refine cspF_Int_choice_mono ?_ cspF_reflex_ref_P
      refine cspF_Rep_int_choice_com_right (fun a _ => ?_)
      refine cspF_Rep_int_choice_com_left ⟨a, Set.mem_univ a, ?_⟩
      exact cspF_Act_prefix_mono rfl ih

theorem RDFtick_DFtick_ref1 [Inhabited α] [HasFPmode] :
    refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF
      (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) := by
  refine cspF_fp_induct_ref_right (Pf := RDFtickfun) (f := RepDF_to_DF)
    rfl RDFtick_mode cspF_reflex_ref_P (fun pn => ?_)
  cases pn
  simp only [RDFtickfun, Subst_procfun, Subst_procfun_Int_pre_choice,
    Subst_procfun_Rep_int_choice_nat]
  refine cspF_Int_choice_right ?_ ?_
  · refine cspF_rw_left_ref («cspF_unwind» rfl DFtick_mode) ?_
    refine cspF_Int_choice_left1 ?_
    refine cspF_Rep_int_choice_com_right (fun a _ => ?_)
    refine cspF_Rep_int_choice_com_left ⟨a, Set.mem_univ a, ?_⟩
    refine cspF_Act_prefix_mono rfl ?_
    refine cspF_Rep_int_choice_nat_right (fun n _ => ?_)
    exact RDFtick_DFtick_ref1_induct_lm
  · refine cspF_rw_left_ref («cspF_unwind» rfl DFtick_mode) ?_
    exact cspF_Int_choice_left2 cspF_reflex_ref_P

/- (*** ref2 ***) -/

def DF_to_RepDF : DFtickName → proc RDFtickName α
  | DFtickName.DFtick => proc.Proc_name RDFtickName.RDFtick

theorem RDFtick_DFtick_ref2 [Inhabited α] [HasFPmode] :
    refF (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) MF MF
      (proc.Proc_name DFtickName.DFtick : proc DFtickName α) := by
  refine cspF_fp_induct_ref_right (Pf := DFtickfun) (f := DF_to_RepDF)
    rfl DFtick_mode cspF_reflex_ref_P (fun pn => ?_)
  cases pn
  simp only [DFtickfun, Subst_procfun, Subst_procfun_Int_pre_choice]
  refine cspF_rw_left_ref («cspF_unwind» rfl RDFtick_mode) ?_
  refine cspF_Int_choice_mono ?_ cspF_reflex_ref_P
  refine cspF_Rep_int_choice_com_right (fun a _ => ?_)
  refine cspF_Rep_int_choice_com_left ⟨a, Set.mem_univ a, ?_⟩
  refine cspF_Act_prefix_mono rfl ?_
  refine cspF_Rep_int_choice_nat_left ⟨0, Set.mem_univ 0, ?_⟩
  exact cspF_reflex_ref_P

/- **************************** =F**************************** -/

theorem RDFtick_DFtick [Inhabited α] [HasFPmode] :
    eqF (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) MF MF
      (proc.Proc_name DFtickName.DFtick : proc DFtickName α) := by
  exact (cspF_eq_ref_iff
    (P1 := (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α))
    (P2 := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
    (M1 := MF) (M2 := MF)).2 ⟨RDFtick_DFtick_ref2, RDFtick_DFtick_ref1⟩

/- ---------------------------------------------------*
 |                                                    |
 |  syntactical approach 2 <--> semantical approach   |
 |                                                    |
 * --------------------------------------------------- -/

theorem DeadlockFree_RDFtick_ref [Inhabited α]
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α} :
    isDeadlockFree P ↔
      refF (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) MF MF P := by
  constructor
  · intro hDF
    have hDFtick :
        refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P :=
      (DeadlockFree_DFtick_ref (P := P)).1 hDF
    exact cspF_trans_left_ref
      (cspF_eq_ref
        (P1 := (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α))
        (P2 := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
        (M1 := MF) (M2 := MF) RDFtick_DFtick)
      hDFtick
  · intro hRDFtick
    have hDFtick :
        refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P :=
      cspF_trans_left_ref
        (cspF_eq_ref
          (P1 := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
          (P2 := (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α))
          (M1 := MF) (M2 := MF) (cspF_sym RDFtick_DFtick))
        hRDFtick
    exact (DeadlockFree_DFtick_ref (P := P)).2 hDFtick

/- Lean note:
   Isabelle's local simp-set update `declare csp_prefix_ss_def[simp del]` has
   no direct analogue here. -/
