           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_op_alpha_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq`,           -/
/-  `Inf_image_eq`, or `disj_not1`, so there is nothing to disable.     -/

/-============================================================*
 |                                                            |
 |            replicated alphabetized parallel                |
 |                                                            |
 *============================================================-/

/- (*** traces Inductive_parallel ***) -/

axiom in_traces_Inductive_parallel_lm1
    {P : proc p α} {X : Set α} {PXs : List (proc p α × Set α)} :
    (P, X) ∈ _root_.set PXs → X ⊆ Set.sUnion (Prod.snd '' _root_.set PXs)

/- main -/

axiom in_traces_Inductive_parallel_lm
    {PXs : List (proc p α × Set α)} {M : p → domTType α} :
    PXs ≠ [] →
      ∀ u,
        (u :t traces (Inductive_parallel PXs) M) ↔
          (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∀ P X, (P, X) ∈ _root_.set PXs → memT (u rest-tr X) (traces P M))

/- (*** remove ALL ***) -/

axiom in_traces_Inductive_parallel
    {PXs : List (proc p α × Set α)} {u : traceType α} {M : p → domTType α} :
    PXs ≠ [] →
      (u :t traces (Inductive_parallel PXs) M) ↔
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
          ∀ P X, (P, X) ∈ _root_.set PXs → memT (u rest-tr X) (traces P M))

/- (*** Semantics for replicated alphabetized parallel on T ***) -/

axiom traces_Inductive_parallel
    {PXs : List (proc p α × Set α)} {M : p → domTType α} :
    PXs ≠ [] →
      traces (Inductive_parallel PXs) M =
        CollectT (fun u : traceType α =>
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∀ P X, (P, X) ∈ _root_.set PXs → memT (u rest-tr X) (traces P M))

/-************************************
 |              traces              |
 ************************************-/

axiom sett_in_traces_Inductive_parallel
    {PXs : List (proc p α × Set α)} {t : traceType α} {M : p → domTType α} :
    PXs ≠ [] → t :t traces (Inductive_parallel PXs) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs)))

/- ---------------------------------------------------------*
 |        another expression of Inductive_parallel_eval    |
 *--------------------------------------------------------- -/

private def nth_inductive_parallel_cond
    (PXs : List (proc p α × Set α)) (u : traceType α) (M : p → domTType α) (i : Nat) : Prop :=
  let PX := nth PXs i
  memT (u rest-tr PX.2) (traces PX.1 M)

private def in_traces_Inductive_parallel_nth_stmt
    (PXs : List (proc p α × Set α)) (u : traceType α) (M : p → domTType α) : Prop :=
  PXs ≠ [] →
    (u :t traces (Inductive_parallel PXs) M) ↔
      And
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))))
        (∀ i : Nat, (i < PXs.length) → nth_inductive_parallel_cond PXs u M i)

axiom in_traces_Inductive_parallel_nth
    {PXs : List (proc p α × Set α)} {u : traceType α} {M : p → domTType α} :
    in_traces_Inductive_parallel_nth_stmt PXs u M

/-============================================================*
 |                                                            |
 |              indexed alphabetized parallel                 |
 |                                                            |
 *============================================================-/

/- (*** index_style ***) -/

axiom to_index_style_T
    {I : Set ι} {PXf : ι → proc p α × Set α} {u : traceType α} {M : p → domTType α} :
    (∀ P X, (P, X) ∈ PXf '' I → memT (u rest-tr X) (traces P M)) ↔
      (∀ i : ι, (i ∈ I) → memT (u rest-tr (Prod.snd (PXf i))) (traces (Prod.fst (PXf i)) M))

/- (*** in_traces_Rep_parallel (pre) ***) -/

axiom in_traces_Rep_parallel_pre
    {I : Set ι} {PXf : ι → proc p α × Set α} {u : traceType α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite →
      (u :t traces (Rep_parallel I PXf) M) ↔
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
          ∀ P X, (P, X) ∈ PXf '' I → memT (u rest-tr X) (traces P M))

/- (*** in_traces_Rep_parallel ***) -/

axiom in_traces_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {u : traceType α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite →
      (u :t traces (Rep_parallel I PXf) M) ↔
        (sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
          ∀ i : ι, (i ∈ I) → memT (u rest-tr (Prod.snd (PXf i))) (traces (Prod.fst (PXf i)) M))

/- The Isabelle theorem bundle `in_traces_par` is represented by
   `in_traces_Alpha_parallel`, `in_traces_Inductive_parallel`, and
   `in_traces_Rep_parallel`. -/

/- (*** Semantics for indexed alphabetized parallel on T ***) -/

axiom traces_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite →
      traces (Rep_parallel I PXf) M =
        CollectT (fun u : traceType α =>
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
            ∀ i : ι, (i ∈ I) → memT (u rest-tr (Prod.snd (PXf i))) (traces (Prod.fst (PXf i)) M))

/-************************************
 |              traces              |
 ************************************-/

axiom sett_in_traces_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {t : traceType α} {M : p → domTType α} :
    I ≠ ∅ → I.Finite → t :t traces (Rep_parallel I PXf) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I))))
