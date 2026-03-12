           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_op_alpha_par
import LeanCspProver.CSP_T.CSP_T_op_rep_par

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

/- (*** Inductive_parallel ***) -/

axiom in_failures_Inductive_parallel_lm1
    {a : proc p α × Set α} {Y : Set (event α)}
    {PXYs : List ((proc p α × Set α) × Set (event α))} :
    Set.inter Y (Set.insert Tick (Ev '' Prod.snd a)) ∪
        Set.sUnion {S | ∃ P X Ya, ((P, X), Ya) ∈ _root_.set PXYs ∧
          S = Set.inter Ya (Set.insert Tick (Ev '' X))} =
      Set.sUnion {S | ∃ P X Ya, (P = Prod.fst a ∧ X = Prod.snd a ∧ Ya = Y) ∨
        ((P, X), Ya) ∈ _root_.set PXYs ∧ S = Set.inter Ya (Set.insert Tick (Ev '' X))}

axiom in_failures_Inductive_parallel_lm2
    {s : List ((proc p α × Set α) × Set (event α))} {P : proc p α} {X : Set α} {Y : Set (event α)} :
    ((P, X), Y) ∈ _root_.set s → X ⊆ Set.sUnion (Prod.snd '' (Prod.fst '' _root_.set s))

axiom in_failures_Inductive_parallel_lm3
    {zs : List ((proc p α × Set α) × Set (event α))} :
    Set.sUnion
        {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set zs ∧ S = Set.inter Y (Set.insert Tick (Ev '' X))} ⊆
      Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (Prod.fst '' _root_.set zs))))

axiom in_failures_Inductive_parallel_lm4
    {zs : List ((proc p α × Set α) × Set (event α))} :
    Set.sUnion
        {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set zs ∧ S = Set.inter Y (Set.insert Tick (Ev '' X))} ∩
        Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (Prod.fst '' _root_.set zs)))) =
      Set.sUnion
        {S | ∃ P X Y,
          ((P, X), Y) ∈ _root_.set zs ∧
            S = Set.inter Y (Set.insert Tick (Ev '' X))}

axiom in_failures_Inductive_parallel_lm
    {PXs : List (proc p α × Set α)} {f : failure α} {M : p → domFType α} :
    PXs ≠ [] →
      (f :f failures (Inductive_parallel PXs) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                  List.map Prod.fst PXYs = PXs ∧
                    Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                        S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                    ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs → ((u rest-tr X), Y) :f failures P M

/- (*** remove ALL ***) -/

axiom in_failures_Inductive_parallel
    {PXs : List (proc p α × Set α)} {f : failure α} {M : p → domFType α} :
    PXs ≠ [] →
      (f :f failures (Inductive_parallel PXs) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                  List.map Prod.fst PXYs = PXs ∧
                    Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                        S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                    ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs → ((u rest-tr X), Y) :f failures P M

/- (*** Semantics for replicated alphabetized parallel on F ***) -/

axiom failures_Inductive_parallel
    {PXs : List (proc p α × Set α)} {M : p → domFType α} :
    PXs ≠ [] →
      failures (Inductive_parallel PXs) M =
        CollectF (fun f : failure α =>
          ∃ u,
            sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
              ∃ Z,
                f = (u, Z) ∧
                  ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                    List.map Prod.fst PXYs = PXs ∧
                      Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                        Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                          S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                      ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs → ((u rest-tr X), Y) :f failures P M)

/-************************************
 |              traces              |
 ************************************-/

axiom sett_in_failures_Inductive_parallel
    {PXs : List (proc p α × Set α)} {t : traceType α} {X : Set (event α)} {M : p → domFType α} :
    PXs ≠ [] → (t, X) :f failures (Inductive_parallel PXs) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs)))

/- ---------------------------------------------------------*
 |        another expression of Inductive_parallel_eval    |
 *--------------------------------------------------------- -/

private def inductive_parallel_nth_union
    (PXs : List (proc p α × Set α)) (Ys : List (Set (event α))) : Set (Set (event α)) :=
  fun S => ∃ i : Nat,
    And
      (i < PXs.length)
      (S = Set.inter (nth Ys i) (Set.insert Tick (Ev '' (Prod.snd (nth PXs i)))))

private def nth_inductive_parallel_failure_cond
    (PXs : List (proc p α × Set α)) (Ys : List (Set (event α)))
    (u : traceType α) (M : p → domFType α) (i : Nat) : Prop :=
  let PX := nth PXs i
  memF ((u rest-tr PX.2), nth Ys i) (failures PX.1 M)

private axiom nth_inductive_parallel_failure_all
    (PXs : List (proc p α × Set α)) (Ys : List (Set (event α)))
    (u : traceType α) (M : p → domFType α) : Prop

private def in_failures_Inductive_parallel_nth_stmt
    (PXs : List (proc p α × Set α)) (f : failure α) (M : p → domFType α) : Prop :=
  PXs ≠ [] →
    (f :f failures (Inductive_parallel PXs) M) ↔
      ∃ u,
        sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
          ∃ Z,
            f = (u, Z) ∧
              ∃ Ys : List (Set (event α)),
                And
                  (PXs.length = Ys.length)
                  (And
                    (Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion (inductive_parallel_nth_union PXs Ys))
                    (nth_inductive_parallel_failure_all PXs Ys u M))

axiom in_failures_Inductive_parallel_nth
    {PXs : List (proc p α × Set α)} {f : failure α} {M : p → domFType α} :
    in_failures_Inductive_parallel_nth_stmt PXs f M

/-============================================================*
 |                                                            |
 |              indexed alphabetized parallel                 |
 |                                                            |
 *============================================================-/

/- (*** failures Inductive_parallel ***) -/

private def rep_parallel_lm1_left
    (Is : List ι) (Ys : List (Set (event α))) (PXf : ι → proc p α × Set α) : Set (Set (event α)) :=
  fun S => ∃ i : Nat,
    And
      (i < Ys.length)
      (S = Set.inter (nth Ys i) (Set.insert Tick (Ev '' (Prod.snd (nth (List.map PXf Is) i)))))

private def rep_parallel_lm1_right
    [Inhabited ι] (I : Set ι) (Is : List ι) (Ys : List (Set (event α)))
    (PXf : ι → proc p α × Set α) :
    Set (Set (event α)) :=
  fun S => ∃ i : ι,
    And
      (i ∈ I)
      (S =
        Set.inter
          (nth Ys (THE (fun n : Nat => nth Is n = i ∧ n < Is.length)))
          (Set.insert Tick (Ev '' (Prod.snd (PXf i)))))

private def rep_parallel_lm2_left
    (I : Set ι) (PXf : ι → proc p α × Set α) (Yf : ι → Set (event α)) : Set (Set (event α)) :=
  fun S => ∃ i : ι,
    And
      (i ∈ I)
      (S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))))

private def rep_parallel_lm2_right
    (Is : List ι) (PXf : ι → proc p α × Set α) (Yf : ι → Set (event α)) : Set (Set (event α)) :=
  fun S => ∃ i : Nat,
    And
      (i < Is.length)
      (S =
        Set.inter
          (nth (List.map Yf Is) i)
          (Set.insert Tick (Ev '' (Prod.snd (nth (List.map PXf Is) i)))))

axiom in_failures_Rep_parallel_lm1
    [Inhabited ι] {I : Set ι} {Is : List ι} {Ys : List (Set (event α))}
    {PXf : ι → proc p α × Set α} :
    isListOf Is I → Ys.length = Is.length →
      Set.sUnion (rep_parallel_lm1_left Is Ys PXf) =
      Set.sUnion (rep_parallel_lm1_right I Is Ys PXf)

axiom in_failures_Rep_parallel_lm2
    {I : Set ι} {Is : List ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    isListOf Is I →
      Set.sUnion (rep_parallel_lm2_left I PXf Yf) =
      Set.sUnion (rep_parallel_lm2_right Is PXf Yf)

axiom in_failures_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {f : failure α} {M : p → domFType α} :
    I ≠ ∅ → I.Finite →
      (f :f failures (Rep_parallel I PXf) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ Yf : ι → Set (event α),
                  Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) =
                    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
                      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∧
                  ∀ i : ι, i ∈ I →
                    ((u rest-tr (Prod.snd (PXf i))), Yf i) :f failures (Prod.fst (PXf i)) M

/- The Isabelle theorem bundle `in_failures_par` is represented by
   `in_failures_Alpha_parallel`, `in_failures_Inductive_parallel`, and
   `in_failures_Rep_parallel`. -/

/- (*** Semantics for indexed alphabetized parallel on F ***) -/

axiom failures_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I ≠ ∅ → I.Finite →
      failures (Rep_parallel I PXf) M =
        CollectF (fun f : failure α =>
          ∃ u,
            sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
              ∃ Z,
                f = (u, Z) ∧
                ∃ Yf : ι → Set (event α),
                  Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) =
                    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
                      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∧
                  ∀ i : ι, i ∈ I →
                      ((u rest-tr (Prod.snd (PXf i))), Yf i) :f failures (Prod.fst (PXf i)) M)

/-************************************
 |              traces              |
 ************************************-/

axiom sett_in_failures_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {t : traceType α}
    {X : Set (event α)} {M : p → domFType α} :
    I ≠ ∅ → I.Finite → (t, X) :f failures (Rep_parallel I PXf) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I))))

end
