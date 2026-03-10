           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                 August 2005               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_traces

open Classical
open SumType

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.          -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

/-
(*********************************************************
            inverse function : DomT => proc
 *********************************************************)
-/

def head_traces (T : domTType α) : Set α := {a | ∃ t, Abs_trace [event.Ev a] ^^^ t :t T}

theorem head_traces_def (T : domTType α) :
    head_traces T = {a | ∃ t, Abs_trace [event.Ev a] ^^^ t :t T} :=
  rfl

def tail_traces (T : domTType α) : α → domTType α :=
  fun a =>
    if _h : a ∈ head_traces T then
      CollectT fun t => Abs_trace [event.Ev a] ^^^ t :t T
    else
      Abs_domT ({<>} : Set (traceType α))

theorem tail_traces_def (T : domTType α) :
    tail_traces T =
      fun a =>
        if _h : a ∈ head_traces T then
          CollectT fun t => Abs_trace [event.Ev a] ^^^ t :t T
        else
          Abs_domT ({<>} : Set (traceType α)) :=
  rfl

def Proc_T_rec : Nat → domTType α → proc p α
  | 0 => fun _ => proc.DIV
  | Nat.succ n =>
      fun T =>
        (((proc.Ext_pre_choice (head_traces T) fun a => Proc_T_rec n (tail_traces T a)) [+] proc.DIV)
          |~| (IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE proc.DIV))

def Proc_T (T : domTType α) : proc p α :=
  Rep_int_choice_nat Set.univ fun n => Proc_T_rec n T

theorem Proc_T_def {p : Type _} {α : Type _} (T : domTType α) :
    Proc_T (p := p) T = Rep_int_choice_nat Set.univ (fun n => Proc_T_rec (p := p) n T) :=
  rfl

def ALL_traces_Proc_T_rec (T : domTType α) (t : traceType α) (n : Nat)
    (M : p → domTType α) : Prop :=
  t :t traces (Proc_T_rec n T) M → t :t T

theorem ALL_traces_Proc_T_rec_def (T : domTType α) (t : traceType α) (n : Nat)
    (M : p → domTType α) :
    ALL_traces_Proc_T_rec T t n M ↔ (t :t traces (Proc_T_rec n T) M → t :t T) :=
  Iff.rfl

/-
(*********************************************************
                     lemmas
 *********************************************************)
-/

/- tail in domT -/

theorem tail_traces_domT {T : domTType α} {a : α}
    (ha : a ∈ head_traces T) :
    {t : traceType α | Abs_trace [event.Ev a] ^^^ t :t T} ∈ domT (α := α) := by
  change HC_T1 {t : traceType α | Abs_trace [event.Ev a] ^^^ t :t T}
  constructor
  · intro hEmpty
    rcases ha with ⟨t, ht⟩
    have ht' : t ∈ (∅ : Set (traceType α)) := by
      have : t ∈ {t : traceType α | Abs_trace [event.Ev a] ^^^ t :t T} := ht
      rwa [hEmpty] at this
    simp at ht'
  · intro s t h
    rcases h with ⟨ht, hp⟩
    exact memT_prefix_closed ht (prefix_same_head_if ⟨t, rfl, hp⟩)

/- tail -/

theorem in_tail_traces {T : domTType α} {a : α}
    (ha : a ∈ head_traces T) {s : traceType α} :
    s :t tail_traces T a ↔ Abs_trace [event.Ev a] ^^^ s :t T := by
  simp [tail_traces, ha, CollectT_open_memT, tail_traces_domT ha]

/- head & tail -/

theorem head_tail_traces_only_if {T : domTType α} {a : α} {s : traceType α}
    (h : Abs_trace [event.Ev a] ^^^ s :t T) :
    a ∈ head_traces T ∧ s :t tail_traces T a := by
  have ha : a ∈ head_traces T := ⟨s, h⟩
  exact ⟨ha, (in_tail_traces ha).2 h⟩

theorem head_tail_traces_if {T : domTType α} {a : α} {s : traceType α}
    (ha : a ∈ head_traces T) (hs : s :t tail_traces T a) :
    Abs_trace [event.Ev a] ^^^ s :t T := by
  exact (in_tail_traces ha).1 hs

/- iff -/

theorem head_tail_traces {T : domTType α} {a : α} {s : traceType α} :
    (Abs_trace [event.Ev a] ^^^ s :t T) ↔
      (a ∈ head_traces T ∧ s :t tail_traces T a) := by
  constructor
  · exact head_tail_traces_only_if
  · intro h
    exact head_tail_traces_if h.1 h.2

/- ----------------------------*
 |       Proc_T lemma         |
 *---------------------------- -/

/- only if lemma -/

theorem semT_Proc_T_only_if_lm {M : p → domTType α} :
    ∀ n (T : domTType α) (t : traceType α), t :t traces (Proc_T_rec n T) M → t :t T := by
  intro n
  induction n with
  | zero =>
      intro T t ht
      have hdiv : t :t traces proc.DIV M := by
        simpa [Proc_T_rec] using ht
      rw [in_traces_DIV] at hdiv
      simpa [hdiv] using (nilt_in_T (T := T))
  | succ n ih =>
      intro T t ht
      have hstep :
          t :t traces
            ((((proc.Ext_pre_choice (head_traces T) fun a =>
                    Proc_T_rec n (tail_traces T a)) [+] proc.DIV)
                |~|
                  (IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN
                    proc.SKIP
                  ELSE
                    proc.DIV))) M := by
        simpa [Proc_T_rec] using ht
      rcases
          (in_traces_Int_choice
            (t := t)
            (P := (proc.Ext_pre_choice (head_traces T) fun a => Proc_T_rec n (tail_traces T a)) [+]
              proc.DIV)
            (Q := IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
              proc.DIV)
            (M := M)).1 hstep with hleft | hright
      · rcases
            (in_traces_Ext_choice
              (t := t)
              (P := proc.Ext_pre_choice (head_traces T) fun a => Proc_T_rec n (tail_traces T a))
              (Q := proc.DIV)
              (M := M)).1 hleft with hpre | hdiv
        · rcases
              (in_traces_Ext_pre_choice
                (t := t)
                (X := head_traces T)
                (Pf := fun a => Proc_T_rec n (tail_traces T a))
                (M := M)).1 hpre with rfl | ⟨a, s, rfl, hs, ha⟩
          · exact nilt_in_T
          · exact head_tail_traces_if ha (ih (tail_traces T a) s hs)
        · rw [in_traces_DIV] at hdiv
          simpa [hdiv] using (nilt_in_T (T := T))
      · by_cases hTick : (Abs_trace [event.Tick] : traceType α) :t T
        · rw [in_traces_IF] at hright
          simp [hTick] at hright
          rcases (in_traces_SKIP (t := t) (M := M)).1 hright with rfl | rfl
          · exact nilt_in_T
          · exact hTick
        · rw [in_traces_IF] at hright
          simp [hTick] at hright
          rw [in_traces_DIV] at hright
          simpa [hright] using (nilt_in_T (T := T))

theorem semT_Proc_T_only_if {M : p → domTType α} {T : domTType α} {t : traceType α} :
    (∃ n, t :t traces (Proc_T_rec n T) M) → t :t T := by
  rintro ⟨n, ht⟩
  exact semT_Proc_T_only_if_lm (M := M) n T t ht

/- if lemma -/

theorem semT_Proc_T_if_lm {M : p → domTType α} :
    ∀ t (T : domTType α), t :t T → t :t traces (Proc_T_rec (lengtht t) T) M := by
  intro t
  refine
    (induct_trace
      (P := fun t : traceType α =>
        ∀ T : domTType α, t :t T → t :t traces (Proc_T_rec (lengtht t) T) M)
      (s := t)
      ?_
      ?_
      ?_)
  · intro T _ht
    have hdiv : ((<> : traceType α) :t traces proc.DIV M) := (in_traces_DIV (M := M)).2 rfl
    simpa [Proc_T_rec] using hdiv
  · intro T ht
    have hif :
        (Abs_trace [event.Tick] : traceType α) :t
          traces
            (IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
              proc.DIV) M := by
      rw [in_traces_IF]
      simpa [ht] using
        ((in_traces_SKIP (t := (Abs_trace [event.Tick] : traceType α)) (M := M)).2
          (Or.inr rfl))
    have hint :
        (Abs_trace [event.Tick] : traceType α) :t
          traces
            (((proc.Ext_pre_choice (head_traces T) fun a => Proc_T_rec 0 (tail_traces T a)) [+]
                proc.DIV)
              |~|
                (IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
                  proc.DIV)) M :=
      (in_traces_Int_choice
        (t := (Abs_trace [event.Tick] : traceType α))
        (P := (proc.Ext_pre_choice (head_traces T) fun a => Proc_T_rec 0 (tail_traces T a)) [+]
          proc.DIV)
        (Q := IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
          proc.DIV)
        (M := M)).2 (Or.inr hif)
    simpa [Proc_T_rec] using hint
  · intro s a ih T ht
    have hspl : a ∈ head_traces T ∧ s :t tail_traces T a := (head_tail_traces).1 ht
    have hrec : s :t traces (Proc_T_rec (lengtht s) (tail_traces T a)) M :=
      ih (tail_traces T a) hspl.2
    have hpre :
        (Abs_trace [event.Ev a] ^^^ s) :t
          traces
            (proc.Ext_pre_choice (head_traces T) fun x =>
              Proc_T_rec (lengtht s) (tail_traces T x)) M :=
      (in_traces_Ext_pre_choice
        (t := Abs_trace [event.Ev a] ^^^ s)
        (X := head_traces T)
        (Pf := fun x => Proc_T_rec (lengtht s) (tail_traces T x))
        (M := M)).2 (Or.inr ⟨a, s, rfl, hrec, hspl.1⟩)
    have hext :
        (Abs_trace [event.Ev a] ^^^ s) :t
          traces
            ((proc.Ext_pre_choice (head_traces T) fun x =>
                Proc_T_rec (lengtht s) (tail_traces T x)) [+] proc.DIV) M :=
      (in_traces_Ext_choice
        (t := Abs_trace [event.Ev a] ^^^ s)
        (P := proc.Ext_pre_choice (head_traces T) fun x =>
          Proc_T_rec (lengtht s) (tail_traces T x))
        (Q := proc.DIV)
        (M := M)).2 (Or.inl hpre)
    have hint :
        (Abs_trace [event.Ev a] ^^^ s) :t
          traces
            (((proc.Ext_pre_choice (head_traces T) fun x =>
                  Proc_T_rec (lengtht s) (tail_traces T x)) [+] proc.DIV)
              |~|
                (IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
                  proc.DIV)) M :=
      (in_traces_Int_choice
        (t := Abs_trace [event.Ev a] ^^^ s)
        (P := (proc.Ext_pre_choice (head_traces T) fun x =>
          Proc_T_rec (lengtht s) (tail_traces T x)) [+] proc.DIV)
        (Q := IF decide ((Abs_trace [event.Tick] : traceType α) :t T) THEN proc.SKIP ELSE
          proc.DIV)
        (M := M)).2 (Or.inl hext)
    simpa [Proc_T_rec, lengtht_app_event_Suc_head, Nat.succ_eq_add_one, Nat.add_comm] using hint

theorem semT_Proc_T_if {M : p → domTType α} {T : domTType α} {t : traceType α}
    (ht : t :t T) :
    t :t traces (Proc_T_rec (lengtht t) T) M := by
  exact semT_Proc_T_if_lm (M := M) t T ht

/- ----------------------------*
 |    Proc_T lemma (main)     |
 *---------------------------- -/

theorem semT_Proc_T {M : p → domTType α} {T : domTType α} :
    semTf (Proc_T T) M = T := by
  change traces (Proc_T T) M = T
  apply le_antisymm
  · intro t ht
    change t :t traces (Proc_T T) M at ht
    change t :t T
    rw [Proc_T_def, in_traces_Rep_int_choice_nat] at ht
    rcases ht with rfl | ⟨n, -, hrec⟩
    · exact nilt_in_T
    · exact semT_Proc_T_only_if (M := M) ⟨n, hrec⟩
  · intro t ht
    change t :t T at ht
    change t :t traces (Proc_T T) M
    rw [Proc_T_def, in_traces_Rep_int_choice_nat]
    exact Or.inr ⟨lengtht t, by simp, semT_Proc_T_if (M := M) ht⟩

theorem traces_Proc_T {M : p → domTType α} {T : domTType α} :
    traces (Proc_T T) M = T := by
  simpa [semTf] using (semT_Proc_T (M := M) (T := T))

/- ----------------------------*
 |   [[ ]]T is surjective     |
 *---------------------------- -/

theorem EX_proc_domT [HasPNfun p α] [HasFPmode] :
    ∀ T : domTType α, ∃ P : proc p α, semT P = T := by
  intro T
  refine ⟨Proc_T T, ?_⟩
  simpa [semT_def] using (semT_Proc_T (M := MT) (T := T))

theorem surj_domT [HasPNfun p α] [HasFPmode] :
    Function.Surjective (fun P : proc p α => semT P) := by
  intro y
  refine ⟨Proc_T y, ?_⟩
  simpa [semT_def] using (semT_Proc_T (M := MT) (T := y))

end
