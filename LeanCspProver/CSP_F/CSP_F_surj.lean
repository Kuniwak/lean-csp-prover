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
        ((proc.Ext_pre_choice (head_failures (sndF SF)) fun a =>
            a ~> Proc_F_rec n (tail_traces (fstF SF) a ,, tail_failures (sndF SF) a)) [+]
          proc.DIV)

def Proc_F (SF : domFType α) : proc p α :=
  Proc_T (fstF SF) |~| Rep_int_choice_nat Set.univ fun n => Proc_F_rec n SF

theorem Proc_F_def {p : Type _} {α : Type _} (SF : domFType α) :
    Proc_F (p := p) SF =
      Proc_T (fstF SF) |~| Rep_int_choice_nat Set.univ (fun n => Proc_F_rec n SF) :=
  rfl

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

axiom tail_traces_failures_T2 {SF : domFType α} {a : α} :
    HC_T2 (tail_traces (fstF SF) a, tail_failures (sndF SF) a)

/- F3 -/

axiom tail_traces_failures_F3 {SF : domFType α} {a : α} :
    a ∈ head_traces (fstF SF) →
      HC_F3 (tail_traces (fstF SF) a, tail_failures (sndF SF) a)

/- T3_F4 -/

axiom tail_traces_failures_T3_F4 {SF : domFType α} {a : α} :
    a ∈ head_traces (fstF SF) →
      HC_T3_F4 (tail_traces (fstF SF) a, tail_failures (sndF SF) a)

axiom tail_traces_failures_domF {SF : domFType α} {a : α} :
    a ∈ head_traces (fstF SF) ∨ a ∈ head_failures (sndF SF) →
      (tail_traces (fstF SF) a, tail_failures (sndF SF) a) ∈ domF (α := α)

/- -------------------------------------*
 |   failures (Proc_T_rec n) --> Tick  |
 *------------------------------------- -/

axiom failures_Proc_T_rec_noTick_lm {M : p → domFType α} :
    ∀ {n : Nat} {T : domTType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_T_rec n T) M →
        noTick s →
          ∃ t, s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α) :t T ∧ noTick t

theorem failures_Proc_T_rec_noTick {M : p → domFType α} {n : Nat} {T : domTType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_T_rec n T) M) (hNo : noTick s) :
    ∃ t, s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α) :t T ∧ noTick t :=
  failures_Proc_T_rec_noTick_lm hs hNo

axiom failures_Proc_T_rec_lm {M : p → domFType α} :
    ∀ {n : Nat} {T : domTType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_T_rec n T) M →
        s :t T

theorem failures_Proc_T_rec {M : p → domFType α} {n : Nat} {T : domTType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_T_rec n T) M) :
    s :t T :=
  failures_Proc_T_rec_lm hs

axiom failures_Proc_T_rec_T3 {M : p → domFType α} {n : Nat} {SF : domFType α}
    {s : traceType α} {X Y : Set (event α)} :
    (s, X) :f failures (Proc_T_rec n (fstF SF)) M →
      noTick s →
        ∃ t, (s ^^^ t ^^^ (Abs_trace [event.Tick] : traceType α), Y) :f sndF SF ∧ noTick t

/- (*** head T --> head F **) -/

axiom head_traces_failures_noTick {M : p → domFType α} {SF : domFType α} {a : α}
    {n : Nat} {s : traceType α} {X : Set (event α)} :
    a ∈ head_traces (fstF SF) →
      (s, X) :f failures (Proc_T_rec n (tail_traces (fstF SF) a)) M →
        noTick s →
          a ∈ head_failures (sndF SF)

/- (*** head_traces_failures ***) -/

axiom head_traces_failures {M : p → domFType α} {SF : domFType α} {a : α}
    {n : Nat} {s : traceType α} {X : Set (event α)} :
    a ∈ head_traces (fstF SF) →
      (s, X) :f failures (Proc_T_rec n (tail_traces (fstF SF) a)) M →
        a ∈ head_failures (sndF SF)

/- ----------------------------*
 |         Proc_T lemma       |
 *---------------------------- -/

/- traces(Proc_F_rec) => fst SF (lm) -/

axiom Proc_F_to_T_lm {M : p → domTType α} :
    ∀ {n : Nat} {SF : domFType α} {t : traceType α},
      t :t traces (Proc_F_rec n SF) M →
        t :t fstF SF

/- traces(Proc_F_rec) => fst SF -/

theorem Proc_F_to_T {M : p → domTType α} {n : Nat} {SF : domFType α} {t : traceType α}
    (ht : t :t traces (Proc_F_rec n SF) M) :
    t :t fstF SF :=
  Proc_F_to_T_lm ht

/- traces(Proc_F_rec) => fst SF (lm) -/

axiom Proc_T_to_F_lm {M : p → domFType α} :
    ∀ {n : Nat} {SF : domFType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_T_rec n (fstF SF)) M →
        (s, X) :f sndF SF

/- traces(Proc_F_rec) => fst SF -/

theorem Proc_T_to_F {M : p → domFType α} {n : Nat} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_T_rec n (fstF SF)) M) :
    (s, X) :f sndF SF :=
  Proc_T_to_F_lm hs

/- failures(Proc_F_rec) => snd SF (lm) -/

axiom Proc_F_to_F_lm {M : p → domFType α} :
    ∀ {n : Nat} {SF : domFType α} {s : traceType α} {X : Set (event α)},
      (s, X) :f failures (Proc_F_rec n SF) M →
        (s, X) :f sndF SF

theorem Proc_F_to_F {M : p → domFType α} {n : Nat} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f failures (Proc_F_rec n SF) M) :
    (s, X) :f sndF SF :=
  Proc_F_to_F_lm hs

/- sndF SF => failures (Proc_F_rec) lm -/

axiom F_Proc_F_lm {M : p → domFType α} {s : traceType α} :
    ∀ {SF : domFType α} {X : Set (event α)},
      ((s, X) :f sndF SF ∧ noTick s ∧
          (event.Tick ∈ X ∨ (s ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF)) →
        (s, X) :f failures (Proc_F_rec (lengtht s) SF) M

/- sndF SF => failures (Proc_F_rec) -/

theorem F_Proc_F {M : p → domFType α} {SF : domFType α} {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f sndF SF) (hNo : noTick s)
    (hTick : event.Tick ∈ X ∨ (s ^^^ (Abs_trace [event.Tick] : traceType α)) ~:t fstF SF) :
    (s, X) :f failures (Proc_F_rec (lengtht s) SF) M :=
  F_Proc_F_lm ⟨hs, hNo, hTick⟩

/- Isabelle temporarily removes simplification rules around the next lemma.
   Lean has no direct analogue for local simp-set mutation here. -/

axiom F_Proc_T_noTick_lm {M : p → domFType α} {s : traceType α} :
    ∀ {SF : domFType α} {X : Set (event α)},
      ((s, X) :f sndF SF ∧ noTick s ∧ event.Tick ∉ X ∧
          (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t fstF SF) →
        (s, X) :f failures (Proc_T_rec (Nat.succ (lengtht s)) (fstF SF)) M

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

axiom F_Proc_T_Tick_lm {M : p → domFType α} {s : traceType α} :
    ∀ {SF : domFType α} {X : Set (event α)},
      ((s, X) :f sndF SF ∧ ¬ noTick s) →
        (s, X) :f failures (Proc_T_rec (lengtht s) (fstF SF)) M

/- sndF SF => failures (Proc_T_rec) noTick -/

theorem F_Proc_T_Tick {M : p → domFType α} {SF : domFType α}
    {s : traceType α} {X : Set (event α)}
    (hs : (s, X) :f sndF SF) (hNo : ¬ noTick s) :
    (s, X) :f failures (Proc_T_rec (lengtht s) (fstF SF)) M :=
  F_Proc_T_Tick_lm ⟨hs, hNo⟩

/- ==================================================*
 |                Proc_F lemma (main)               |
 *================================================== -/

axiom semF_Proc_F {SF : domFType α} {M : p → domFType α} :
    semFf (Proc_F SF) M = SF

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

axiom traces_Proc_F {SF : domFType α} {M : p → domTType α} :
    traces (Proc_F SF) M = fstF SF

theorem traces_Proc_T_F {SF : domFType α} {M : p → domTType α} :
    traces (Proc_T (fstF SF)) M = traces (Proc_F SF) M := by
  rw [traces_Proc_T, traces_Proc_F]

/- ==========================================================*
 |                                                          |
 |              Generic Internal Choice                     |
 |                                                          |
 *========================================================== -/

def Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode] (Ps : Set (proc p α)) : proc p α :=
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

axiom traces_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domTType α} :
    Ps ≠ ∅ →
      traces (Gen_int_choice_F_plus Ps) M =
        UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)}

axiom failures_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      failures (Gen_int_choice_F_plus Ps) M =
        UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P MF}

axiom semF_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} :
    Ps ≠ ∅ →
      semF (Gen_int_choice_F_plus Ps) =
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ MF)} ,,
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P MF})

axiom in_traces_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domTType α} {t : traceType α} :
    Ps ≠ ∅ →
      (t :t traces (Gen_int_choice_F_plus Ps) M ↔
        ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ MF))

axiom in_failures_Gen_int_choice_F_plus [HasPNfun p α] [HasFPmode]
    {Ps : Set (proc p α)} {M : p → domFType α} {f : failure α} :
    Ps ≠ ∅ →
      (f :f failures (Gen_int_choice_F_plus Ps) M ↔
        ∃ P, P ∈ Ps ∧ f :f failures P MF)

/- Isabelle re-enables `disj_not1` here; Lean has no corresponding simp rule
   state to restore. -/

end
