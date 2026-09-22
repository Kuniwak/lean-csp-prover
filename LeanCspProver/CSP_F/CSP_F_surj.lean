           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_surj

open SumType

noncomputable section
attribute [local instance] Classical.propDecidable

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.          -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

/-
(*********************************************************
            inverse function : DomT => proc
 *********************************************************)
-/

def head_failures (F : setFType α) : Set α :=
  {a | ∃ t X, (Abs_trace [event.Ev a] ^^^ t, X) :f F}

theorem head_failures_def (F : setFType α) :
    head_failures F = {a | ∃ t X, (Abs_trace [event.Ev a] ^^^ t, X) :f F} :=
  rfl

def tail_failures (F : setFType α) : α → setFType α :=
  fun a => CollectF fun f => (Abs_trace [event.Ev a] ^^^ f.1, f.2) :f F

theorem tail_failures_def (F : setFType α) :
    tail_failures F =
      fun a => CollectF fun f => (Abs_trace [event.Ev a] ^^^ f.1, f.2) :f F :=
  rfl

/- Isabelle: `Proc_F_rec (Suc n) = (%SF. (! a:(head_failures (sndF SF)) .. a ->
   Proc_F_rec n (...)) [+] DIV)` -- a replicated *internal* choice (`Rep_int_choice_com`)
   over `a` whose branch then performs `a`.  Transcribed literally.
   `in_traces_Proc_F_rec_succ` / `in_failures_Proc_F_rec_succ` below show that, under
   `_ [+] DIV`, this agrees with the external prefix choice `? a:X -> Q a`. -/
def Proc_F_rec : Nat → domFType α → proc p α
  | 0 =>
      fun SF =>
        Rep_int_choice_set
          {X : Set α |
            ∃ Y : Set (event α),
              ((<> : traceType α), Y) :f sndF SF ∧
                (event.Ev '' X : Set (event α)) = ((Evset : Set (event α)) \ Y) ∧
                event.Tick ∈ Y ∧
              ∀ a ∈ X, (Abs_trace [event.Ev a] : traceType α) :t fstF SF}
          (fun X => proc.Ext_pre_choice X fun _ => proc.DIV)
  | Nat.succ n =>
      fun SF =>
        ((Rep_int_choice_com (head_failures (sndF SF)) fun a =>
            a ~> Proc_F_rec n (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)) [+]
          proc.DIV)

def Proc_F (SF : domFType α) : proc p α :=
  Proc_T (fstF SF) |~| Rep_int_choice_nat Set.univ fun n => Proc_F_rec n SF

theorem Proc_F_def {p : Type _} {α : Type _} (SF : domFType α) :
    Proc_F (p := p) SF =
      Proc_T (fstF SF) |~| Rep_int_choice_nat Set.univ (fun n => Proc_F_rec n SF) :=
  rfl

/- Under `_ [+] DIV`, the internal choice `! a:A .. a -> Q a` and the external prefix
   choice `? a:A -> Q a` have the same traces and the same failures.  The traces half is
   the CSP-Prover law `cspT_Ext_pre_choice_Rep_int_choice` (no `[+] DIV` needed; see
   `traces_Rep_int_choice_com_prefix_Ext_choice_DIV` in CSP_T_surj).  The failures half
   is where the two models differ (CSP_T_law.thy: "these rules show the difference between
   models T and F") and the `[+] DIV` is essential: `DIV` has no stable failures, so the
   nil refusals in which the two choices differ are discarded, and their non-nil failures
   coincide. -/

theorem in_traces_Rep_int_choice_com_prefix_Ext_choice_DIV
    {A : Set α} {Q : α → proc p α} {t : traceType α} {M : p → domTType α} :
    (t :t traces ((Rep_int_choice_com A fun a => a ~> Q a) [+] proc.DIV) M) ↔
      (t :t traces ((proc.Ext_pre_choice A Q) [+] proc.DIV) M) := by
  rw [traces_Rep_int_choice_com_prefix_Ext_choice_DIV]

private theorem Tick_notin_traces_Rep_int_choice_com_prefix
    {A : Set α} {Q : α → proc p α} {M : p → domTType α} :
    (Abs_trace [event.Tick] : traceType α) ~:t
      traces (Rep_int_choice_com A fun a => a ~> Q a) M := by
  intro h
  rw [in_traces_Rep_int_choice_com] at h
  rcases h with h | ⟨a, -, h⟩
  · simp at h
  · rw [in_traces_Act_prefix] at h
    rcases h with h | ⟨s, h, -⟩ <;> simp at h

private theorem Tick_notin_traces_Ext_pre_choice_DIV
    {A : Set α} {Q : α → proc p α} {M : p → domTType α} :
    (Abs_trace [event.Tick] : traceType α) ~:t traces (proc.Ext_pre_choice A Q) M := by
  intro h
  rw [in_traces_Ext_pre_choice] at h
  rcases h with h | ⟨a, s, h, -, -⟩ <;> simp at h

theorem in_failures_Rep_int_choice_com_prefix_Ext_choice_DIV
    {A : Set α} {Q : α → proc p α} {f : failure α} {M : p → domFType α} :
    (f :f failures ((Rep_int_choice_com A fun a => a ~> Q a) [+] proc.DIV) M) ↔
      (f :f failures ((proc.Ext_pre_choice A Q) [+] proc.DIV) M) := by
  rw [in_failures_Ext_choice, in_failures_Ext_choice]
  constructor
  · rintro (⟨-, -, hD⟩ | ⟨s, ⟨X, rfl⟩, hor, hne⟩ | ⟨X, rfl, hT, -⟩)
    · exact absurd hD in_failures_DIV
    · have hP := hor.resolve_right in_failures_DIV
      rw [in_failures_Rep_int_choice_com] at hP
      obtain ⟨a, ha, hpre⟩ := hP
      rw [in_failures_Act_prefix] at hpre
      rcases hpre with ⟨Y, hEq, -⟩ | ⟨s', Y, hEq, hs'⟩
      · exact absurd (Prod.mk.inj hEq).1 hne
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        refine Or.inr (Or.inl ⟨_, ⟨_, rfl⟩, Or.inl ?_, hne⟩)
        rw [in_failures_Ext_pre_choice]
        exact Or.inr ⟨a, s', _, rfl, hs', ha⟩
    · exfalso
      rcases hT with hT | hT
      · exact Tick_notin_traces_Rep_int_choice_com_prefix hT
      · rw [in_traces_DIV] at hT
        simp at hT
  · rintro (⟨-, -, hD⟩ | ⟨s, ⟨X, rfl⟩, hor, hne⟩ | ⟨X, rfl, hT, -⟩)
    · exact absurd hD in_failures_DIV
    · have hP := hor.resolve_right in_failures_DIV
      rw [in_failures_Ext_pre_choice] at hP
      rcases hP with ⟨Y, hEq, -⟩ | ⟨a, s', Y, hEq, hs', ha⟩
      · exact absurd (Prod.mk.inj hEq).1 hne
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
        refine Or.inr (Or.inl ⟨_, ⟨_, rfl⟩, Or.inl ?_, hne⟩)
        rw [in_failures_Rep_int_choice_com]
        exact ⟨a, ha, in_failures_Act_prefix.2 (Or.inr ⟨s', _, rfl, hs'⟩)⟩
    · exfalso
      rcases hT with hT | hT
      · exact Tick_notin_traces_Ext_pre_choice_DIV hT
      · rw [in_traces_DIV] at hT
        simp at hT

/- The successor case of `Proc_F_rec`, unfolded to the external-prefix-choice form. -/

theorem in_traces_Proc_F_rec_succ
    {n : Nat} {SF : domFType α} {t : traceType α} {M : p → domTType α} :
    (t :t traces (Proc_F_rec (Nat.succ n) SF) M) ↔
      (t :t traces ((proc.Ext_pre_choice (head_failures (sndF SF)) fun a =>
          Proc_F_rec n (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)) [+]
        proc.DIV) M) := by
  simp only [Proc_F_rec]
  exact in_traces_Rep_int_choice_com_prefix_Ext_choice_DIV

theorem in_failures_Proc_F_rec_succ
    {n : Nat} {SF : domFType α} {f : failure α} {M : p → domFType α} :
    (f :f failures (Proc_F_rec (Nat.succ n) SF) M) ↔
      (f :f failures ((proc.Ext_pre_choice (head_failures (sndF SF)) fun a =>
          Proc_F_rec n (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)) [+]
        proc.DIV) M) := by
  simp only [Proc_F_rec]
  exact in_failures_Rep_int_choice_com_prefix_Ext_choice_DIV

/- Isabelle temporarily removes simplification rules around the lemma that unfolds
   `Proc_T_rec (Suc n)`; Lean has no direct analogue for local simp-set mutation here. -/
theorem in_failures_Proc_T_rec_succ {n : Nat} {T : domTType α} {f : failure α}
    {M : p → domFType α} :
    (f :f failures (Proc_T_rec (Nat.succ n) T) M) ↔
      (f :f failures
        ((((proc.Ext_pre_choice (head_traces T) fun a => Proc_T_rec n (tail_traces T a)) [+]
            proc.DIV)
          |~|
            (IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
              proc.DIV))) M) := by
  simp only [Proc_T_rec]
  rw [in_failures_Int_choice, in_failures_Int_choice,
    in_failures_Rep_int_choice_com_prefix_Ext_choice_DIV]

/-
(*********************************************************
                     lemmas
 *********************************************************)
-/

/- tail in setF -/

theorem tail_failures_setF {F : setFType α} {a : α} :
    {f : failure α | (Abs_trace [event.Ev a] ^^^ f.1, f.2) :f F} ∈ setF (α := α) := by
  intro s X Y hs hYX
  exact memF_F2 hs hYX

/- tail -/

theorem in_tail_failures {F : setFType α} {a : α} {s : traceType α} {X : Set (event α)} :
    (s, X) :f tail_failures F a ↔ (Abs_trace [event.Ev a] ^^^ s, X) :f F := by
  simpa [tail_failures, tail_failures_def] using
    (CollectF_open_memF
      (P := fun f : failure α => (Abs_trace [event.Ev a] ^^^ f.1, f.2) :f F)
      (f := (s, X))
      tail_failures_setF)

/- head & tail -/

theorem head_tail_failures_only_if
    {F : setFType α} {a : α} {s : traceType α} {X : Set (event α)}
    (h : (Abs_trace [event.Ev a] ^^^ s, X) :f F) :
    a ∈ head_failures F ∧ (s, X) :f tail_failures F a := by
  exact ⟨⟨s, X, h⟩, (in_tail_failures (F := F) (a := a)).2 h⟩

/- iff -/

theorem head_tail_failures {F : setFType α} {a : α} {s : traceType α} {X : Set (event α)} :
    (Abs_trace [event.Ev a] ^^^ s, X) :f F ↔
      (a ∈ head_failures F ∧ (s, X) :f tail_failures F a) := by
  constructor
  · exact head_tail_failures_only_if
  · intro h
    exact (in_tail_failures (F := F) (a := a)).1 h.2

/- (*** domF ***) -/

/- head -/

theorem head_failures_traces {SF : domFType α} {a : α} :
    a ∈ head_failures (sndF SF) → a ∈ head_traces (fstF SF) := by
  intro h
  rcases h with ⟨t, X, ht⟩
  exact ⟨t, pairF_domF_T2 (SF := SF) ht⟩

/- T2 -/


theorem tail_traces_failures_T2 {SF : domFType α} {a : α} :
    HC_T2 (tail_traces (fstF SF) a, tail_failures (sndF SF) a) := by
  rw [HC_T2_pair]
  intro s X hsX
  have h : (Abs_trace [event.Ev a] ^^^ s, X) :f sndF SF := in_tail_failures.1 hsX
  have ha : a ∈ head_traces (fstF SF) :=
    head_failures_traces (head_tail_failures_only_if h).1
  exact (in_tail_traces ha).2 (pairF_domF_T2 (SF := SF) h)

/- F3 -/

theorem tail_traces_failures_F3 {SF : domFType α} {a : α} :
    a ∈ head_traces (fstF SF) →
      HC_F3 (tail_traces (fstF SF) a, tail_failures (sndF SF) a) := by
  intro ha
  rw [HC_F3_pair]
  intro s X Y hsX hNo hY
  refine in_tail_failures.2 ?_
  refine pairF_domF_F3 (SF := SF) (in_tail_failures.1 hsX)
    (decompo_appt_noTick_if (noTick_Ev a) hNo) ?_
  intro b hb
  rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNo)]
  exact fun hmem => hY b hb ((in_tail_traces ha).2 hmem)

/- T3_F4 -/

theorem tail_traces_failures_T3_F4 {SF : domFType α} {a : α} :
    a ∈ head_traces (fstF SF) →
      HC_T3_F4 (tail_traces (fstF SF) a, tail_failures (sndF SF) a) := by
  intro ha
  rw [HC_T3_F4_pair]
  rintro s ⟨hTick, hNo⟩
  have hTick' :
      ((Abs_trace [event.Ev a] ^^^ s) ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF := by
    rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNo)]
    exact (in_tail_traces ha).1 hTick
  have hNo' : noTick (Abs_trace [event.Ev a] ^^^ s) :=
    decompo_appt_noTick_if (noTick_Ev a) hNo
  refine ⟨in_tail_failures.2 (pairF_domF_F4 (SF := SF) hTick' hNo'), ?_⟩
  intro X
  refine in_tail_failures.2 ?_
  rw [← appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNo)]
  exact pairF_domF_T3 (SF := SF) hTick' hNo'

theorem tail_traces_failures_domF {SF : domFType α} {a : α} :
    a ∈ head_traces (fstF SF) ∨ a ∈ head_failures (sndF SF) →
      (tail_traces (fstF SF) a, tail_failures (sndF SF) a) ∈ domF (α := α) := by
  intro h
  have ha : a ∈ head_traces (fstF SF) := h.elim id head_failures_traces
  rcases (HC_T3_F4_iff
    (TF := (tail_traces (fstF SF) a, tail_failures (sndF SF) a))).1
      (tail_traces_failures_T3_F4 ha) with ⟨hT3, hF4⟩
  exact ⟨tail_traces_failures_T2, hT3, tail_traces_failures_F3 ha, hF4⟩

/- -------------------------------------*
 |   failures (Proc_T_rec n) --> Tick  |
 *------------------------------------- -/

theorem failures_Proc_T_rec_noTick_lm {M : p → domFType α} :
    ∀ {n : Nat} {T : domTType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_T_rec n T) M →
        noTick s →
          ∃ t, s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α) :t T ∧ noTick t := by
  intro n
  induction n with
  | zero =>
      intro T s X h _
      simp only [Proc_T_rec] at h
      exact absurd h in_failures_DIV
  | succ n ih =>
      intro T s X h hNo
      rw [in_failures_Proc_T_rec_succ, in_failures_Int_choice] at h
      rcases h with hL | hR
      · rw [in_failures_Ext_choice] at hL
        rcases hL with ⟨-, -, hdiv⟩ | ⟨s', ⟨Y, hEq⟩, hor, hne⟩ | ⟨-, -, hTick, -⟩
        · exact absurd hdiv in_failures_DIV
        · have hpre := hor.resolve_right in_failures_DIV
          rw [in_failures_Ext_pre_choice] at hpre
          rcases hpre with ⟨Y', hnil, -⟩ | ⟨a, s0, Y', hEq', hs0, ha⟩
          · exact absurd ((Prod.mk.inj hEq).1.symm.trans (Prod.mk.inj hnil).1) hne
          · rcases Prod.mk.inj hEq' with ⟨hs, -⟩
            subst hs
            have hNo0 : noTick s0 :=
              (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hNo).2
            rcases ih hs0 hNo0 with ⟨t, ht, hNot⟩
            refine ⟨t, ?_, hNot⟩
            rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNo0)]
            exact (in_tail_traces ha).1 ht
        · rcases hTick with hp | hd
          · rw [in_traces_Ext_pre_choice] at hp
            rcases hp with hnil | ⟨a, u, hu, -, -⟩
            · simp at hnil
            · simp at hu
          · rw [in_traces_DIV] at hd
            simp at hd
      · rw [in_failures_IF] at hR
        by_cases hT : (Abs_trace [event.Tick] : traceType α) :t T
        · have hskip : (s, X) :f failures proc.SKIP M := by simpa [hT] using hR
          rw [in_failures_SKIP] at hskip
          rcases hskip with ⟨Y, hEq, -⟩ | ⟨Y, hEq⟩
          · rcases Prod.mk.inj hEq with ⟨hs, -⟩
            subst hs
            exact ⟨<>, by simpa using hT, noTick_nil⟩
          · rcases Prod.mk.inj hEq with ⟨hs, -⟩
            subst hs
            exact absurd hNo not_noTick_Tick
        · have hdiv : (s, X) :f failures proc.DIV M := by simpa [hT] using hR
          exact absurd hdiv in_failures_DIV

theorem failures_Proc_T_rec_noTick {M : p → domFType α} {n : Nat} {T : domTType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_T_rec n T) M) (hNo : noTick s) :
    ∃ t, s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α) :t T ∧ noTick t :=
  failures_Proc_T_rec_noTick_lm hs hNo

theorem failures_Proc_T_rec_lm {M : p → domFType α} :
    ∀ {n : Nat} {T : domTType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_T_rec n T) M →
        s :t T := by
  intro n
  induction n with
  | zero =>
      intro T s X h
      simp only [Proc_T_rec] at h
      exact absurd h in_failures_DIV
  | succ n ih =>
      intro T s X h
      rw [in_failures_Proc_T_rec_succ, in_failures_Int_choice] at h
      rcases h with hL | hR
      · rw [in_failures_Ext_choice] at hL
        rcases hL with ⟨-, -, hdiv⟩ | ⟨s', ⟨Y, hEq⟩, hor, hne⟩ | ⟨Y, hEq, -, -⟩
        · exact absurd hdiv in_failures_DIV
        · have hpre := hor.resolve_right in_failures_DIV
          rw [in_failures_Ext_pre_choice] at hpre
          rcases hpre with ⟨Y', hnil, -⟩ | ⟨a, s0, Y', hEq', hs0, ha⟩
          · exact absurd ((Prod.mk.inj hEq).1.symm.trans (Prod.mk.inj hnil).1) hne
          · rcases Prod.mk.inj hEq' with ⟨hs, -⟩
            subst hs
            exact (in_tail_traces ha).1 (ih hs0)
        · rcases Prod.mk.inj hEq with ⟨hs, -⟩
          subst hs
          exact nilt_in_T
      · rw [in_failures_IF] at hR
        by_cases hT : (Abs_trace [event.Tick] : traceType α) :t T
        · have hskip : (s, X) :f failures proc.SKIP M := by simpa [hT] using hR
          rw [in_failures_SKIP] at hskip
          rcases hskip with ⟨Y, hEq, -⟩ | ⟨Y, hEq⟩ <;>
            · rcases Prod.mk.inj hEq with ⟨hs, -⟩
              subst hs
              first
                | exact nilt_in_T
                | exact hT
        · have hdiv : (s, X) :f failures proc.DIV M := by simpa [hT] using hR
          exact absurd hdiv in_failures_DIV

theorem failures_Proc_T_rec {M : p → domFType α} {n : Nat} {T : domTType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_T_rec n T) M) :
    s :t T :=
  failures_Proc_T_rec_lm hs

theorem failures_Proc_T_rec_T3 {M : p → domFType α} {n : Nat} {SF : domFType α}
    {s : traceType α} {X Y : Set (event α)} :
    (s, X) :f failures (Proc_T_rec n (fstF SF)) M →
      noTick s →
        ∃ t, (s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α), Y) :f sndF SF ∧ noTick t := by
  intro hs hNo
  rcases failures_Proc_T_rec_noTick_lm (M := M) hs hNo with ⟨t, ht, hNot⟩
  refine ⟨t, ?_, hNot⟩
  rw [← appt_assoc (Or.inl hNo) (Or.inl hNot)]
  refine pairF_domF_T3 (SF := SF) ?_ (decompo_appt_noTick_if hNo hNot)
  rw [appt_assoc (Or.inl hNo) (Or.inl hNot)]
  exact ht

/- (*** head T --> head F **) -/

theorem head_traces_failures_noTick {M : p → domFType α} {SF : domFType α} {a : α}
    {n : Nat} {s : traceType α} {X : Set (event α)} :
    a ∈ head_traces (fstF SF) →
      (s, X) :f failures (Proc_T_rec n (tail_traces (fstF SF) a)) M →
        noTick s →
          a ∈ head_failures (sndF SF) := by
  intro ha hs hNo
  rcases failures_Proc_T_rec_noTick_lm (M := M) hs hNo with ⟨t, ht, hNot⟩
  refine ⟨s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α), X, ?_⟩
  have hNost : noTick (s ^^^ t) := decompo_appt_noTick_if hNo hNot
  have hassoc :
      (Abs_trace [event.Ev a] ^^^ (s ^^^ t)) ^^^ (Abs_trace [event.Tick] : traceType α) =
        Abs_trace [event.Ev a] ^^^ s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α) := by
    rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNost),
      appt_assoc (Or.inl hNo) (Or.inl hNot)]
  rw [← hassoc]
  refine pairF_domF_T3 (SF := SF) ?_ (decompo_appt_noTick_if (noTick_Ev a) hNost)
  rw [hassoc]
  exact (in_tail_traces ha).1 ht

/- (*** head_traces_failures ***) -/

theorem head_traces_failures {M : p → domFType α} {SF : domFType α} {a : α}
    {n : Nat} {s : traceType α} {X : Set (event α)} :
    a ∈ head_traces (fstF SF) →
      (s, X) :f failures (Proc_T_rec n (tail_traces (fstF SF) a)) M →
        a ∈ head_failures (sndF SF) := by
  intro ha hs
  by_cases hNo : noTick s
  · exact head_traces_failures_noTick (M := M) (n := n) ha hs hNo
  · have hdec : s = butlastt s ^^^ (Abs_trace [event.Tick] : traceType α) := Tick_decompo hNo
    have hNob : noTick (butlastt s) := noTick_butlast (not_noTick_unnil hNo)
    have hmem : Abs_trace [event.Ev a] ^^^ s :t fstF SF :=
      (in_tail_traces ha).1 (failures_Proc_T_rec_lm (M := M) hs)
    refine ⟨s, X, ?_⟩
    have hassoc :
        (Abs_trace [event.Ev a] ^^^ butlastt s) ^^^ (Abs_trace [event.Tick] : traceType α) =
          Abs_trace [event.Ev a] ^^^ s := by
      rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNob), ← hdec]
    rw [← hassoc]
    refine pairF_domF_T3 (SF := SF) ?_ (decompo_appt_noTick_if (noTick_Ev a) hNob)
    rw [hassoc]
    exact hmem

/- ----------------------------*
 |         Proc_T lemma       |
 *---------------------------- -/

/- traces(Proc_F_rec) => fst SF (lm) -/

theorem Proc_F_to_T_lm {M : p → domTType α} :
    ∀ {n : Nat} {SF : domFType α} {t : traceType α},
      t :t traces (Proc_F_rec n SF) M →
        t :t fstF SF := by
  intro n
  induction n with
  | zero =>
      intro SF t h
      simp only [Proc_F_rec] at h
      rw [in_traces_Rep_int_choice_set] at h
      rcases h with rfl | ⟨X, hX, ht⟩
      · exact nilt_in_T
      · rw [in_traces_Ext_pre_choice] at ht
        rcases ht with rfl | ⟨a, u, rfl, hu, haX⟩
        · exact nilt_in_T
        · rw [in_traces_DIV] at hu
          subst hu
          rcases hX with ⟨-, -, -, -, hall⟩
          simpa using hall a haX
  | succ n ih =>
      intro SF t h
      rw [in_traces_Proc_F_rec_succ, in_traces_Ext_choice] at h
      rcases h with hpre | hdiv
      · rw [in_traces_Ext_pre_choice] at hpre
        rcases hpre with rfl | ⟨a, u, rfl, hu, ha⟩
        · exact nilt_in_T
        · have hdom := tail_traces_failures_domF (SF := SF) (a := a) (Or.inr ha)
          have hu' : u :t tail_traces (fstF SF) a := by
            have := ih hu
            rwa [pairF_fstF hdom] at this
          exact (in_tail_traces (head_failures_traces ha)).1 hu'
      · rw [in_traces_DIV] at hdiv
        subst hdiv
        exact nilt_in_T

/- traces(Proc_F_rec) => fst SF -/

theorem Proc_F_to_T {M : p → domTType α} {n : Nat} {SF : domFType α} {t : traceType α}
    (ht : t :t traces (Proc_F_rec n SF) M) :
    t :t fstF SF :=
  Proc_F_to_T_lm ht

/- traces(Proc_F_rec) => fst SF (lm) -/

theorem Proc_T_to_F_lm {M : p → domFType α} :
    ∀ {n : Nat} {SF : domFType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_T_rec n (fstF SF)) M →
        (s, X) :f sndF SF := by
  intro n
  induction n with
  | zero =>
      intro SF s X h
      simp only [Proc_T_rec] at h
      exact absurd h in_failures_DIV
  | succ n ih =>
      intro SF s X h
      rw [in_failures_Proc_T_rec_succ, in_failures_Int_choice] at h
      rcases h with hL | hR
      · rw [in_failures_Ext_choice] at hL
        rcases hL with ⟨-, -, hdiv⟩ | ⟨s', ⟨Y, hEq⟩, hor, hne⟩ | ⟨-, -, hTick, -⟩
        · exact absurd hdiv in_failures_DIV
        · have hpre := hor.resolve_right in_failures_DIV
          rw [in_failures_Ext_pre_choice] at hpre
          rcases hpre with ⟨Y', hnil, -⟩ | ⟨a, s0, Y', hEq', hs0, ha⟩
          · exact absurd ((Prod.mk.inj hEq).1.symm.trans (Prod.mk.inj hnil).1) hne
          · rcases Prod.mk.inj hEq' with ⟨hs, hX⟩
            subst hs
            subst hX
            have hdom := tail_traces_failures_domF (SF := SF) (a := a) (Or.inl ha)
            have hs0' :
                (s0, X) :f
                  failures
                    (Proc_T_rec n
                      (fstF (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a))) M := by
              rwa [pairF_fstF hdom]
            have := ih hs0'
            rw [pairF_sndF hdom] at this
            exact in_tail_failures.1 this
        · rcases hTick with hp | hd
          · rw [in_traces_Ext_pre_choice] at hp
            rcases hp with hnil | ⟨a, u, hu, -, -⟩
            · simp at hnil
            · simp at hu
          · rw [in_traces_DIV] at hd
            simp at hd
      · rw [in_failures_IF] at hR
        by_cases hT : (Abs_trace [event.Tick] : traceType α) :t fstF SF
        · have hskip : (s, X) :f failures proc.SKIP M := by simpa [hT] using hR
          rw [in_failures_SKIP] at hskip
          rcases hskip with ⟨Y, hEq, hsub⟩ | ⟨Y, hEq⟩
          · rcases Prod.mk.inj hEq with ⟨hs, hX⟩
            subst hs
            subst hX
            exact pairF_domF_F2_F4 (SF := SF) (by simpa using hT) noTick_nil hsub
          · rcases Prod.mk.inj hEq with ⟨hs, hX⟩
            subst hs
            subst hX
            exact pairF_domF_T3_Tick (SF := SF) hT
        · have hdiv : (s, X) :f failures proc.DIV M := by simpa [hT] using hR
          exact absurd hdiv in_failures_DIV

/- traces(Proc_F_rec) => fst SF -/

theorem Proc_T_to_F {M : p → domFType α} {n : Nat} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_T_rec n (fstF SF)) M) :
    (s, X) :f sndF SF :=
  Proc_T_to_F_lm hs

/- failures(Proc_F_rec) => snd SF (lm) -/

theorem Proc_F_to_F_lm {M : p → domFType α} :
    ∀ {n : Nat} {SF : domFType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_F_rec n SF) M →
        (s, X) :f sndF SF := by
  intro n
  induction n with
  | zero =>
      intro SF s X h
      simp only [Proc_F_rec] at h
      rw [in_failures_Rep_int_choice_set] at h
      rcases h with ⟨X0, hX0, hf⟩
      rw [in_failures_Ext_pre_choice] at hf
      rcases hf with ⟨Y, hEq, hdisj⟩ | ⟨a, u, Y, -, hu, -⟩
      · rcases Prod.mk.inj hEq with ⟨hs, hX⟩
        subst hs
        subst hX
        rcases hX0 with ⟨Y0, hY0, hEv, hTick0, -⟩
        refine memF_F2 hY0 ?_
        intro e he
        by_cases hTe : e = event.Tick
        · exact hTe ▸ hTick0
        · by_contra hne
          rcases (not_Tick_to_Ev (e := e)).1 hTe with ⟨b, rfl⟩
          have hmem : event.Ev b ∈ (event.Ev '' X0 : Set (event α)) := by
            rw [hEv]
            exact ⟨hTe, hne⟩
          have : event.Ev b ∈ ((event.Ev '' X0 : Set (event α)) ∩ X) := ⟨hmem, he⟩
          rw [hdisj] at this
          exact this
      · exact absurd hu in_failures_DIV
  | succ n ih =>
      intro SF s X h
      rw [in_failures_Proc_F_rec_succ, in_failures_Ext_choice] at h
      rcases h with ⟨-, -, hdiv⟩ | ⟨s', ⟨Y, hEq⟩, hor, hne⟩ | ⟨-, -, hTick, -⟩
      · exact absurd hdiv in_failures_DIV
      · have hpre := hor.resolve_right in_failures_DIV
        rw [in_failures_Ext_pre_choice] at hpre
        rcases hpre with ⟨Y', hnil, -⟩ | ⟨a, s0, Y', hEq', hs0, ha⟩
        · exact absurd ((Prod.mk.inj hEq).1.symm.trans (Prod.mk.inj hnil).1) hne
        · rcases Prod.mk.inj hEq' with ⟨hs, hX⟩
          subst hs
          subst hX
          have hdom := tail_traces_failures_domF (SF := SF) (a := a) (Or.inr ha)
          have := ih hs0
          rw [pairF_sndF hdom] at this
          exact in_tail_failures.1 this
      · rcases hTick with hp | hd
        · rw [in_traces_Ext_pre_choice] at hp
          rcases hp with hnil | ⟨a, u, hu, -, -⟩
          · simp at hnil
          · simp at hu
        · rw [in_traces_DIV] at hd
          simp at hd

theorem Proc_F_to_F {M : p → domFType α} {n : Nat} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_F_rec n SF) M) :
    (s, X) :f sndF SF :=
  Proc_F_to_F_lm hs

/- sndF SF => failures (Proc_F_rec) lm -/

theorem F_Proc_F_lm {M : p → domFType α} {s : traceType α} :
    ∀ {SF : domFType α} {X : Set (event α)},
      ((s, X) :f sndF SF ∧ noTick s ∧
          (event.Tick ∈ X ∨ (s ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF)) →
        (s, X) :f failures (Proc_F_rec (lengtht s) SF) M := by
  have key : ∀ w : traceType α, ∀ (SF : domFType α) (X : Set (event α)),
      ((w, X) :f sndF SF ∧ noTick w ∧
          (event.Tick ∈ X ∨ (w ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF)) →
        (w, X) :f failures (Proc_F_rec (lengtht w) SF) M := by
    intro w
    refine induct_trace
      (P := fun w : traceType α => ∀ (SF : domFType α) (X : Set (event α)),
        ((w, X) :f sndF SF ∧ noTick w ∧
            (event.Tick ∈ X ∨ (w ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF)) →
          (w, X) :f failures (Proc_F_rec (lengtht w) SF) M)
      (s := w) ?_ ?_ ?_
    · rintro SF X ⟨hsX, -, hTick⟩
      rw [lengtht_nil_zero]
      have hbase :
          ∀ Y : Set (event α), ((<> : traceType α), Y) :f sndF SF → event.Tick ∈ Y →
            (∀ b : α, (event.Ev b ∈ Y ↔
              (event.Ev b ∈ X ∨ (Abs_trace [event.Ev b] : traceType α) ~:t fstF SF))) →
            ((<> : traceType α), X) :f failures (Proc_F_rec 0 SF) M := by
        intro Y hY hTickY hEv
        simp only [Proc_F_rec]
        rw [in_failures_Rep_int_choice_set]
        refine ⟨{a : α | event.Ev a ∉ X ∧ (Abs_trace [event.Ev a] : traceType α) :t fstF SF},
          ⟨Y, hY, ?_, hTickY, fun a ha => ha.2⟩, ?_⟩
        · ext e
          constructor
          · rintro ⟨b, hb, rfl⟩
            refine ⟨by simp [Evset], ?_⟩
            intro hmem
            rcases (hEv b).1 hmem with h | h
            · exact hb.1 h
            · exact h hb.2
          · rintro ⟨hE, hYe⟩
            have hEne : e ≠ event.Tick := hE
            rcases (not_Tick_to_Ev (e := e)).1 hEne with ⟨b, rfl⟩
            refine ⟨b, ⟨fun hx => hYe ((hEv b).2 (Or.inl hx)), ?_⟩, rfl⟩
            by_contra hx
            exact hYe ((hEv b).2 (Or.inr hx))
        · rw [in_failures_Ext_pre_choice]
          refine Or.inl ⟨X, rfl, ?_⟩
          rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨⟨b, hb, rfl⟩, he⟩
          exact hb.1 he
      rcases hTick with hTX | hnt
      · refine hbase
          (X ∪ {e : event α | ∃ b : α,
            e = event.Ev b ∧ (Abs_trace [event.Ev b] : traceType α) ~:t fstF SF})
          (pairF_domF_F3 (SF := SF) hsX noTick_nil ?_) (Or.inl hTX) ?_
        · rintro e ⟨b, rfl, hb⟩
          simpa using hb
        · intro b
          constructor
          · rintro (h | ⟨c, hc, hcn⟩)
            · exact Or.inl h
            · cases hc
              exact Or.inr hcn
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr ⟨b, rfl, h⟩
      · refine hbase
          (X ∪ ({event.Tick} ∪ {e : event α | ∃ b : α,
            e = event.Ev b ∧ (Abs_trace [event.Ev b] : traceType α) ~:t fstF SF}))
          (pairF_domF_F3 (SF := SF) hsX noTick_nil ?_) (Or.inr (Or.inl rfl)) ?_
        · rintro e (he | ⟨b, rfl, hb⟩)
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact hnt
          · simpa using hb
        · intro b
          constructor
          · rintro (h | he | ⟨c, hc, hcn⟩)
            · exact Or.inl h
            · exact absurd (Set.mem_singleton_iff.1 he) (by simp)
            · cases hc
              exact Or.inr hcn
          · rintro (h | h)
            · exact Or.inl h
            · exact Or.inr (Or.inr ⟨b, rfl, h⟩)
    · rintro SF X ⟨-, hNo, -⟩
      exact absurd hNo not_noTick_Tick
    · rintro w a ih SF X ⟨hsX, hNo, hTick⟩
      have hspl := head_tail_failures_only_if hsX
      have ha : a ∈ head_failures (sndF SF) := hspl.1
      have hdom := tail_traces_failures_domF (SF := SF) (a := a) (Or.inr ha)
      have hNow : noTick w := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hNo).2
      have hrec :
          (w, X) :f
            failures (Proc_F_rec (lengtht w)
              (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)) M := by
        refine ih _ X ⟨?_, hNow, ?_⟩
        · rw [pairF_sndF hdom]
          exact hspl.2
        · rcases hTick with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            rw [pairF_fstF hdom]
            intro hmem
            apply h
            rw [appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNow)]
            exact (in_tail_traces (head_failures_traces ha)).1 hmem
      rw [lengtht_app_event_Suc_head, in_failures_Proc_F_rec_succ,
        in_failures_Ext_choice]
      refine Or.inr (Or.inl ⟨Abs_trace [event.Ev a] ^^^ w, ⟨X, rfl⟩, Or.inl ?_, by simp⟩)
      rw [in_failures_Ext_pre_choice]
      exact Or.inr ⟨a, w, X, rfl, hrec, ha⟩
  intro SF X h
  exact key s SF X h

/- sndF SF => failures (Proc_F_rec) -/

theorem F_Proc_F {M : p → domFType α} {SF : domFType α} {s : traceType α}
    {X : Set (event α)}
    (hs : (s, X) :f sndF SF) (hNo : noTick s)
    (hTick : event.Tick ∈ X ∨ (s ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF) :
    (s, X) :f failures (Proc_F_rec (lengtht s) SF) M :=
  F_Proc_F_lm ⟨hs, hNo, hTick⟩

theorem F_Proc_T_noTick_lm {M : p → domFType α} {s : traceType α} :
    ∀ {SF : domFType α} {X : Set (event α)},
      ((s, X) :f sndF SF ∧ noTick s ∧ event.Tick ∉ X ∧
          (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF) →
        (s, X) :f failures (Proc_T_rec (Nat.succ (lengtht s)) (fstF SF)) M := by
  have key : ∀ w : traceType α, ∀ (SF : domFType α) (X : Set (event α)),
      ((w, X) :f sndF SF ∧ noTick w ∧ event.Tick ∉ X ∧
          (w ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF) →
        (w, X) :f failures (Proc_T_rec (Nat.succ (lengtht w)) (fstF SF)) M := by
    intro w
    refine induct_trace
      (P := fun w : traceType α => ∀ (SF : domFType α) (X : Set (event α)),
        ((w, X) :f sndF SF ∧ noTick w ∧ event.Tick ∉ X ∧
            (w ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF) →
          (w, X) :f failures (Proc_T_rec (Nat.succ (lengtht w)) (fstF SF)) M)
      (s := w) ?_ ?_ ?_
    · rintro SF X ⟨-, -, hTickX, hTr⟩
      have hT : (Abs_trace [event.Tick] : traceType α) :t fstF SF := by simpa using hTr
      have hskip : ((<> : traceType α), X) :f failures (proc.SKIP : proc p α) M := by
        rw [in_failures_SKIP]
        exact Or.inl ⟨X, rfl, fun e he hTe => hTickX (hTe ▸ he)⟩
      rw [lengtht_nil_zero, in_failures_Proc_T_rec_succ, in_failures_Int_choice]
      refine Or.inr ?_
      rw [in_failures_IF]
      simpa [hT] using hskip
    · rintro SF X ⟨-, hNo, -, -⟩
      exact absurd hNo not_noTick_Tick
    · rintro w a ih SF X ⟨hsX, hNo, hTickX, hTr⟩
      have hNow : noTick w := (decompo_appt_noTick_only_if (Or.inl (noTick_Ev a)) hNo).2
      have hTr' :
          Abs_trace [event.Ev a] ^^^ (w ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF := by
        rw [← appt_assoc (Or.inl (noTick_Ev a)) (Or.inl hNow)]
        exact hTr
      have hsplT := head_tail_traces_only_if hTr'
      have ha : a ∈ head_traces (fstF SF) := hsplT.1
      have hdom := tail_traces_failures_domF (SF := SF) (a := a) (Or.inl ha)
      have hsplF := head_tail_failures_only_if hsX
      have hrec :
          (w, X) :f failures (Proc_T_rec (Nat.succ (lengtht w)) (tail_traces (fstF SF) a)) M := by
        have := ih (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a) X
          ⟨by rw [pairF_sndF hdom]; exact hsplF.2, hNow, hTickX,
            by rw [pairF_fstF hdom]; exact hsplT.2⟩
        rwa [pairF_fstF hdom] at this
      rw [lengtht_app_event_Suc_head, in_failures_Proc_T_rec_succ,
        in_failures_Int_choice]
      refine Or.inl ?_
      rw [in_failures_Ext_choice]
      refine Or.inr (Or.inl ⟨Abs_trace [event.Ev a] ^^^ w, ⟨X, rfl⟩, Or.inl ?_, by simp⟩)
      rw [in_failures_Ext_pre_choice]
      exact Or.inr ⟨a, w, X, rfl, hrec, ha⟩
  intro SF X h
  exact key s SF X h

/- sndF SF => failures (Proc_T_rec) noTick -/

theorem F_Proc_T_noTick {M : p → domFType α} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f sndF SF) (hNo : noTick s) (hTick : event.Tick ∉ X)
    (hTrace : (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF) :
    (s, X) :f failures (Proc_T_rec (Nat.succ (lengtht s)) (fstF SF)) M :=
  F_Proc_T_noTick_lm ⟨hs, hNo, hTick, hTrace⟩

/- Isabelle restores the deleted simp rules here; Lean again has no
   corresponding simp-set state to update. -/

/- sndF SF => failures (Proc_T_rec) (Tick) lm -/

theorem F_Proc_T_Tick_lm {M : p → domFType α} {s : traceType α} :
    ∀ {SF : domFType α} {X : Set (event α)},
      ((s, X) :f sndF SF ∧ ¬ noTick s) →
        (s, X) :f failures (Proc_T_rec (lengtht s) (fstF SF)) M := by
  have key : ∀ w : traceType α, ∀ (SF : domFType α) (X : Set (event α)),
      ((w, X) :f sndF SF ∧ ¬ noTick w) →
        (w, X) :f failures (Proc_T_rec (lengtht w) (fstF SF)) M := by
    intro w
    refine induct_trace
      (P := fun w : traceType α => ∀ (SF : domFType α) (X : Set (event α)),
        ((w, X) :f sndF SF ∧ ¬ noTick w) →
          (w, X) :f failures (Proc_T_rec (lengtht w) (fstF SF)) M)
      (s := w) ?_ ?_ ?_
    · rintro SF X ⟨-, hNo⟩
      exact absurd noTick_nil hNo
    · rintro SF X ⟨hsX, -⟩
      have hT : (Abs_trace [event.Tick] : traceType α) :t fstF SF := pairF_domF_T2 (SF := SF) hsX
      have hskip :
          ((Abs_trace [event.Tick] : traceType α), X) :f failures (proc.SKIP : proc p α) M := by
        rw [in_failures_SKIP]
        exact Or.inr ⟨X, rfl⟩
      have hlen : lengtht (Abs_trace [event.Tick] : traceType α) = Nat.succ 0 := by simp [lengtht]
      rw [hlen, in_failures_Proc_T_rec_succ, in_failures_Int_choice]
      refine Or.inr ?_
      rw [in_failures_IF]
      simpa [hT] using hskip
    · rintro w a ih SF X ⟨hsX, hNo⟩
      have hNow : ¬ noTick w := fun h => hNo (decompo_appt_noTick_if (noTick_Ev a) h)
      have hsplF := head_tail_failures_only_if hsX
      have ha : a ∈ head_failures (sndF SF) := hsplF.1
      have hdom := tail_traces_failures_domF (SF := SF) (a := a) (Or.inr ha)
      have hrec :
          (w, X) :f failures (Proc_T_rec (lengtht w) (tail_traces (fstF SF) a)) M := by
        have := ih (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a) X
          ⟨by rw [pairF_sndF hdom]; exact hsplF.2, hNow⟩
        rwa [pairF_fstF hdom] at this
      rw [lengtht_app_event_Suc_head, in_failures_Proc_T_rec_succ,
        in_failures_Int_choice]
      refine Or.inl ?_
      rw [in_failures_Ext_choice]
      refine Or.inr (Or.inl ⟨Abs_trace [event.Ev a] ^^^ w, ⟨X, rfl⟩, Or.inl ?_, by simp⟩)
      rw [in_failures_Ext_pre_choice]
      exact Or.inr ⟨a, w, X, rfl, hrec, head_failures_traces ha⟩
  intro SF X h
  exact key s SF X h

/- sndF SF => failures (Proc_T_rec) noTick -/

theorem F_Proc_T_Tick {M : p → domFType α} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f sndF SF) (hNo : ¬ noTick s) :
    (s, X) :f failures (Proc_T_rec (lengtht s) (fstF SF)) M :=
  F_Proc_T_Tick_lm ⟨hs, hNo⟩

/- ==================================================*
 |                Proc_F lemma (main)               |
 *================================================== -/

theorem traces_Proc_F_lm {SF : domFType α} {M : p → domTType α} :
    traces (Proc_F SF) M = fstF SF := by
  apply le_antisymm
  · intro t ht
    change t :t traces (Proc_F SF) M at ht
    change t :t fstF SF
    rw [Proc_F_def, in_traces_Int_choice] at ht
    rcases ht with hT | hF
    · rwa [traces_Proc_T] at hT
    · rw [in_traces_Rep_int_choice_nat] at hF
      rcases hF with rfl | ⟨n, -, hn⟩
      · exact nilt_in_T
      · exact Proc_F_to_T_lm hn
  · intro t ht
    change t :t fstF SF at ht
    change t :t traces (Proc_F SF) M
    rw [Proc_F_def, in_traces_Int_choice]
    refine Or.inl ?_
    rwa [traces_Proc_T]

theorem failures_Proc_F_lm {SF : domFType α} {M : p → domFType α} :
    failures (Proc_F SF) M = sndF SF := by
  apply le_antisymm
  · rintro ⟨s, X⟩ hf
    change (s, X) :f failures (Proc_F SF) M at hf
    change (s, X) :f sndF SF
    rw [Proc_F_def, in_failures_Int_choice] at hf
    rcases hf with hT | hF
    · rw [Proc_T_def, in_failures_Rep_int_choice_nat] at hT
      rcases hT with ⟨n, -, hn⟩
      exact Proc_T_to_F_lm (n := n) hn
    · rw [in_failures_Rep_int_choice_nat] at hF
      rcases hF with ⟨n, -, hn⟩
      exact Proc_F_to_F_lm (n := n) hn
  · rintro ⟨s, X⟩ hsX
    change (s, X) :f sndF SF at hsX
    change (s, X) :f failures (Proc_F SF) M
    rw [Proc_F_def, in_failures_Int_choice]
    by_cases hc :
        noTick s ∧
          (event.Tick ∈ X ∨ (s ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF)
    · refine Or.inr ?_
      rw [in_failures_Rep_int_choice_nat]
      exact ⟨lengtht s, Set.mem_univ _, F_Proc_F_lm ⟨hsX, hc.1, hc.2⟩⟩
    · refine Or.inl ?_
      rw [Proc_T_def, in_failures_Rep_int_choice_nat]
      by_cases hNo : noTick s
      · have h1 : event.Tick ∉ X := fun h => hc ⟨hNo, Or.inl h⟩
        have h2 : (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF := by
          by_contra h
          exact hc ⟨hNo, Or.inr h⟩
        exact ⟨Nat.succ (lengtht s), Set.mem_univ _,
          F_Proc_T_noTick_lm ⟨hsX, hNo, h1, h2⟩⟩
      · exact ⟨lengtht s, Set.mem_univ _, F_Proc_T_Tick_lm ⟨hsX, hNo⟩⟩

theorem semF_Proc_F {SF : domFType α} {M : p → domFType α} :
    semFf (Proc_F SF) M = SF :=
  semFf_decompo.2 ⟨traces_Proc_F_lm, failures_Proc_F_lm⟩

/- ----------------------------*
 |   [[ ]]F is surjective     |
 *---------------------------- -/

theorem EX_proc_domF [HasPNfun p α] [HasFPmode] :
    ∀ SF : domFType α, ∃ P : proc p α, semF P = SF := by
  intro SF
  exact ⟨Proc_F SF, by simpa [semF_def] using (semF_Proc_F (SF := SF) (M := MF))⟩

theorem surj_domF [HasPNfun p α] [HasFPmode] :
    Function.Surjective (fun P : proc p α => semF P) := by
  intro SF
  exact ⟨Proc_F SF, by simpa [semF_def] using (semF_Proc_F (SF := SF) (M := MF))⟩

/- ----------------------------*
 |   failures and Proc_F SF   |
 *---------------------------- -/

theorem failures_Proc_F {SF : domFType α} {M : p → domFType α} :
    failures (Proc_F SF) M = sndF SF := by
  exact
    (semFf_decompo (P := Proc_F SF) (M := M) (SF := SF)).1
      (semF_Proc_F (SF := SF) (M := M)) |>.2

/- ----------------------------*
 |    traces and Proc_F SF    |
 *---------------------------- -/

theorem make_failures_from_T {T : domTType α} {M : p → domFType α} :
    (T, failures (Proc_T T) M) ∈ domF (α := α) := by
  simpa [traces_Proc_T (M := fstF ∘ M) (T := T)] using (proc_domF (P := Proc_T T) (M := M))

theorem traces_Proc_F {SF : domFType α} {M : p → domTType α} :
    traces (Proc_F SF) M = fstF SF :=
  traces_Proc_F_lm

theorem traces_Proc_T_F {SF : domFType α} {M : p → domTType α} :
    traces (Proc_T (fstF SF)) M = traces (Proc_F SF) M := by
  rw [traces_Proc_T, traces_Proc_F]

/- ==========================================================*
 |                                                          |
 |              Generic Internal Choice                     |
 |                                                          |
 *========================================================== -/

def Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode] (Ps : Set (proc p α)) :
    proc p α :=
  Proc_F
    (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} ,,
      UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P MF})

theorem Gen_int_choice_F_plus_def [HasPNfun p α] [HasFPmode] (Ps : Set (proc p α)) :
    Gen_int_choice_F_plus Ps =
      Proc_F
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} ,,
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P MF}) :=
  rfl

/- lemmas -/

theorem traces_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domTType α} :
    Ps ≠ ∅ →
      traces (Gen_int_choice_F_plus Ps) M =
        UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} := by
  intro hPs
  rw [Gen_int_choice_F_plus_def, traces_Proc_F]
  exact pairF_fstF (non_empty_UnionT_UnionF_domF hPs)

theorem failures_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      failures (Gen_int_choice_F_plus Ps) M =
        UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P MF} := by
  intro hPs
  rw [Gen_int_choice_F_plus_def, failures_Proc_F]
  exact pairF_sndF (non_empty_UnionT_UnionF_domF hPs)

theorem semF_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} :
    Ps ≠ ∅ →
      semF (Gen_int_choice_F_plus Ps) =
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} ,,
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P MF}) := by
  intro hPs
  rw [eqF_decompo]
  refine ⟨?_, ?_⟩
  · rw [fstF_semF, traces_Gen_int_choice_F_plus hPs]
    exact (pairF_fstF (non_empty_UnionT_UnionF_domF hPs)).symm
  · rw [sndF_semF, failures_Gen_int_choice_F_plus hPs]
    exact (pairF_sndF (non_empty_UnionT_UnionF_domF hPs)).symm

theorem in_traces_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domTType α} {t : traceType α} :
    Ps ≠ ∅ →
      (t :t traces (Gen_int_choice_F_plus Ps) M ↔
        ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ MF)) := by
  intro hPs
  rw [traces_Gen_int_choice_F_plus hPs]
  constructor
  · intro ht
    have hne : {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} ≠ ∅ := by
      rcases Set.nonempty_iff_ne_empty.2 hPs with ⟨P0, hP0⟩
      intro hEmpty
      have hmem :
          traces P0 (fstF ∘ MF) ∈
            {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} := ⟨P0, hP0, rfl⟩
      rw [hEmpty] at hmem
      exact hmem
    rcases memT_UnionT_only_if hne ht with ⟨T, ⟨P, hP, rfl⟩, htT⟩
    exact ⟨P, hP, htT⟩
  · rintro ⟨P, hP, ht⟩
    exact memT_UnionT_if ⟨P, hP, rfl⟩ ht

theorem in_failures_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domFType α} {f : failure α} :
    Ps ≠ ∅ →
      (f :f failures (Gen_int_choice_F_plus Ps) M ↔
        ∃ P, P ∈ Ps ∧ f :f failures P MF) := by
  intro hPs
  rw [failures_Gen_int_choice_F_plus hPs]
  constructor
  · intro hf
    rcases memF_UnionF_only_if hf with ⟨F, ⟨P, hP, rfl⟩, hfF⟩
    exact ⟨P, hP, hfF⟩
  · rintro ⟨P, hP, hf⟩
    exact memF_UnionF_if ⟨P, hP, rfl⟩ hf

/- Isabelle re-enables `disj_not1` here; Lean has no corresponding simp rule
   state to restore. -/

end
