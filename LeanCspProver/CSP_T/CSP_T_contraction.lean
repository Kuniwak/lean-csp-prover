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

/- ============================================*
 |                   gSKIP                    |
 *============================================ -/

axiom gSKIP_to_Tick_notin_traces {p : Type _} {α : Type _} :
    ∀ (P : proc p α) (M : p → domTType α),
      gSKIP P → ((Abs_trace [event.Tick] : traceType α) ~:t traces P M)

/- --------------------------------*
 |        STOP,SKIP,DIV           |
 *-------------------------------- -/

/- (*** Constant_contraction ***) -/

axiom map_alpha_Constant {β : Type _} {γ : Type _} [ms β] [ms γ] {C : γ} {alpha : ℝ} :
    0 <= alpha → map_alpha (fun _ : β => C) alpha

/- (*** non_expanding_Constant ***) -/

axiom non_expanding_Constant {β : Type _} {γ : Type _} [ms β] [ms γ] {C : γ} :
    non_expanding (fun _ : β => C)

/- (*** Constant_contraction_alpha ***) -/

axiom contraction_alpha_Constant {β : Type _} {γ : Type _} [ms β] [ms γ]
    {C : γ} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (fun _ : β => C) alpha

/- (*** STOP ***) -/

axiom map_alpha_traces_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (traces (p := p) (α := α) proc.STOP) alpha

axiom non_expanding_traces_STOP {p : Type _} {α : Type _} :
    non_expanding (traces (p := p) (α := α) proc.STOP)

axiom contraction_alpha_traces_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (traces (p := p) (α := α) proc.STOP) alpha

/- (*** SKIP ***) -/

axiom map_alpha_traces_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (traces (p := p) (α := α) proc.SKIP) alpha

axiom non_expanding_traces_SKIP {p : Type _} {α : Type _} :
    non_expanding (traces (p := p) (α := α) proc.SKIP)

axiom contraction_alpha_traces_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (traces (p := p) (α := α) proc.SKIP) alpha

/- (*** DIV ***) -/

axiom map_alpha_traces_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (traces (p := p) (α := α) proc.DIV) alpha

axiom non_expanding_traces_DIV {p : Type _} {α : Type _} :
    non_expanding (traces (p := p) (α := α) proc.DIV)

axiom contraction_alpha_traces_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (traces (p := p) (α := α) proc.DIV) alpha

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

axiom contraction_half_traces_Act_prefix_lm {p : Type _} {q : Type _} {α : Type _}
    {a : α} {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    distance (traces (a ~> P) M1) (traces (a ~> Q) M2) * 2 =
      distance (traces P M1) (traces Q M2)

/- (***  contraction_half ***) -/

axiom contraction_half_traces_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (traces P) → contraction_alpha (traces (a ~> P)) (1 / 2 : ℝ)

/- (***  contraction ***) -/

axiom contraction_traces_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (traces P) → contraction (traces (a ~> P))

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (traces P) → non_expanding (traces (a ~> P))

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Ext_pre_choice_Act_prefix_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ a ∈ X, traces (a ~> Pf a) M1 .|. n <= traces (a ~> Qf a) M2 .|. n) →
      traces (proc.Ext_pre_choice X Pf) M1 .|. n <=
        traces (proc.Ext_pre_choice X Qf) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom Ext_pre_choice_Act_prefix_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ a ∈ X, traces (a ~> Pf a) M1 .|. n = traces (a ~> Qf a) M2 .|. n) →
      traces (proc.Ext_pre_choice X Pf) M1 .|. n =
        traces (proc.Ext_pre_choice X Qf) M2 .|. n

/- (*** distT lemma ***) -/

axiom Ext_pre_choice_Act_prefix_distT_nonempty {p : Type _} {q : Type _} {α : Type _}
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
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** contraction lemma ***) -/

axiom contraction_half_traces_Ext_pre_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : domTType α} :
    X ≠ ∅ →
      (∀ a, distance (traces (Pf a) M1) (traces (Qf a) M2) <= distance x1 x2) →
        distance
            (traces (proc.Ext_pre_choice X Pf) M1)
            (traces (proc.Ext_pre_choice X Qf) M2) * 2 <=
          distance x1 x2

/- (*** contraction_half ***) -/

axiom contraction_half_traces_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (traces (Pf a))) →
      contraction_alpha (traces (proc.Ext_pre_choice X Pf)) (1 / 2 : ℝ)

/- (*** Ext_pre_choice_evalT_contraction ***) -/

axiom contraction_traces_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (traces (Pf a))) →
      contraction (traces (proc.Ext_pre_choice X Pf))

/- (*** Ext_pre_choice_evalT_non_expanding ***) -/

axiom non_expanding_traces_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (traces (Pf a))) →
      non_expanding (traces (proc.Ext_pre_choice X Pf))

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Ext_choice_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (P1 [+] Q1) M1 .|. n <= traces (P2 [+] Q2) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom Ext_choice_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (P1 [+] Q1) M1 .|. n = traces (P2 [+] Q2) M2 .|. n

/- (*** distT lemma ***) -/

axiom Ext_choice_distT {p : Type _} {q : Type _} {α : Type _}
    {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (P1 [+] Q1) M1) (traces (P2 [+] Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha T lemma ***) -/

axiom map_alpha_traces_Ext_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (P1 [+] Q1) M1) (traces (P2 [+] Q2) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P [+] Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P [+] Q))

/- (*** contraction ***) -/

axiom contraction_alpha_traces_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P [+] Q)) alpha

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P |~| Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P |~| Q))

/- (*** contraction ***) -/

axiom contraction_alpha_traces_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P |~| Q)) alpha

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Rep_int_choice_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ c ∈ sumset C, traces (Pf c) M1 .|. n <= traces (Qf c) M2 .|. n) →
      traces (proc.Rep_int_choice C Pf) M1 .|. n <= traces (proc.Rep_int_choice C Qf) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom Rep_int_choice_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    (∀ c ∈ sumset C, traces (Pf c) M1 .|. n = traces (Qf c) M2 .|. n) →
      traces (proc.Rep_int_choice C Pf) M1 .|. n = traces (proc.Rep_int_choice C Qf) M2 .|. n

/- (*** distT lemma ***) -/

axiom Rep_int_choice_distT_nonempty {p : Type _} {q : Type _} {α : Type _}
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
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha T lemma ***) -/

axiom map_alpha_traces_Rep_int_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {C : sets_nats α}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    sumset C ≠ ∅ →
      (∀ c, distance (traces (Pf c) M1) (traces (Qf c) M2) <= alpha * distance x1 x2) →
        distance (traces (proc.Rep_int_choice C Pf) M1) (traces (proc.Rep_int_choice C Qf) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, map_alpha (traces (Pf c)) alpha) →
      map_alpha (traces (proc.Rep_int_choice C Pf)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, non_expanding (traces (Pf c))) →
      non_expanding (traces (proc.Rep_int_choice C Pf))

/- (*** Rep_int_choice_evalT_contraction_alpha ***) -/

axiom contraction_alpha_traces_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, contraction_alpha (traces (Pf c)) alpha) →
      contraction_alpha (traces (proc.Rep_int_choice C Pf)) alpha

/- --------------------------------*
 |               IF               |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom IF_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (IF b THEN P1 ELSE Q1) M1 .|. n <= traces (IF b THEN P2 ELSE Q2) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom IF_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (IF b THEN P1 ELSE Q1) M1 .|. n = traces (IF b THEN P2 ELSE Q2) M2 .|. n

/- (*** distT lemma ***) -/

axiom IF_distT {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (IF b THEN P1 ELSE Q1) M1) (traces (IF b THEN P2 ELSE Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha T lemma (not used) ***) -/

axiom map_alpha_traces_IF_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (IF b THEN P1 ELSE Q1) M1) (traces (IF b THEN P2 ELSE Q2) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (IF b THEN P ELSE Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (IF b THEN P ELSE Q))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_traces_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (IF b THEN P ELSE Q)) alpha

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Parallel_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (P1 |[X]| Q1) M1 .|. n <= traces (P2 |[X]| Q2) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom Parallel_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (P1 |[X]| Q1) M1 .|. n = traces (P2 |[X]| Q2) M2 .|. n

/- (*** distT lemma ***) -/

axiom Parallel_distT {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (P1 |[X]| Q1) M1) (traces (P2 |[X]| Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha T lemma ***) -/

axiom map_alpha_traces_Parallel_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (P1 |[X]| Q1) M1) (traces (P2 |[X]| Q2) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P |[X]| Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P |[X]| Q))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_traces_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P |[X]| Q)) alpha

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- cms rules for Hiding is not necessary
   because processes are guarded. -/

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Renaming_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P M1 .|. n <= traces Q M2 .|. n →
      traces (P [[r]]) M1 .|. n <= traces (Q [[r]]) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom Renaming_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P M1 .|. n = traces Q M2 .|. n →
      traces (P [[r]]) M1 .|. n = traces (Q [[r]]) M2 .|. n

/- (*** distT lemma ***) -/

axiom Renaming_distT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    distance (traces (P [[r]]) M1) (traces (Q [[r]]) M2) <= distance (traces P M1) (traces Q M2)

/- (*** map_alphaT lemma ***) -/

axiom map_alpha_traces_Renaming_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P M1) (traces Q M2) <= alpha * distance x1 x2 →
      distance (traces (P [[r]]) M1) (traces (Q [[r]]) M2) <= alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    map_alpha (traces P) alpha → map_alpha (traces (P [[r]])) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} :
    non_expanding (traces P) → non_expanding (traces (P [[r]]))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_traces_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    contraction_alpha (traces P) alpha → contraction_alpha (traces (P [[r]])) alpha

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Seq_compo_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n <= traces P2 M2 .|. n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        traces (P1 ;; Q1) M1 .|. n <= traces (P2 ;; Q2) M2 .|. n

/- (*** rest_domT (equal) ***) -/

axiom Seq_compo_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. n = traces P2 M2 .|. n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        traces (P1 ;; Q1) M1 .|. n = traces (P2 ;; Q2) M2 .|. n

/- (*** distT lemma ***) -/

axiom Seq_compo_distT {p : Type _} {q : Type _} {α : Type _}
    {PQs : Set (domTType α × domTType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    PQs =
      ({(traces P1 M1, traces P2 M2), (traces Q1 M1, traces Q2 M2)} :
        Set (domTType α × domTType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (traces (P1 ;; Q1) M1) (traces (P2 ;; Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha T lemma ***) -/

axiom map_alpha_traces_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 M1) (traces P2 M2) <= alpha * distance x1 x2 →
      distance (traces Q1 M1) (traces Q2 M2) <= alpha * distance x1 x2 →
        distance (traces (P1 ;; Q1) M1) (traces (P2 ;; Q2) M2) <= alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (traces P) alpha →
      map_alpha (traces Q) alpha →
        map_alpha (traces (P ;; Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (traces P) →
      non_expanding (traces Q) →
        non_expanding (traces (P ;; Q))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (traces P) alpha →
      contraction_alpha (traces Q) alpha →
        contraction_alpha (traces (P ;; Q)) alpha

/- --------------------------------*
 |       Seq_compo  (gSKIP)       |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom gSKIP_Seq_compo_rest_domT_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. Nat.succ n <= traces P2 M2 .|. Nat.succ n →
      traces Q1 M1 .|. n <= traces Q2 M2 .|. n →
        ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 M1) →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 M2) →
            traces (P1 ;; Q1) M1 .|. Nat.succ n <= traces (P2 ;; Q2) M2 .|. Nat.succ n

/- (*** rest_domT (equal) ***) -/

axiom gSKIP_Seq_compo_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    traces P1 M1 .|. Nat.succ n = traces P2 M2 .|. Nat.succ n →
      traces Q1 M1 .|. n = traces Q2 M2 .|. n →
        ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 M1) →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 M2) →
            traces (P1 ;; Q1) M1 .|. Nat.succ n = traces (P2 ;; Q2) M2 .|. Nat.succ n

/- (*** map_alpha T lemma ***) -/

axiom gSKIP_map_alpha_traces_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {n : Nat} :
    distance (traces P1 M1) (traces P2 M2) * 2 <= (1 / 2 : ℝ) ^ n →
      distance (traces Q1 M1) (traces Q2 M2) <= (1 / 2 : ℝ) ^ n →
        ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 M1) →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 M2) →
            distance (traces (P1 ;; Q1) M1) (traces (P2 ;; Q2) M2) * 2 <= (1 / 2 : ℝ) ^ n

/- (*** map_alpha ***) -/

axiom gSKIP_contraction_half_traces_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    contraction_alpha (traces P) (1 / 2 : ℝ) →
      non_expanding (traces Q) →
        gSKIP P →
          contraction_alpha (traces (P ;; Q)) (1 / 2 : ℝ)

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** rest_domT (equal) ***) -/

axiom Depth_rest_rest_domT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m n : Nat}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    traces P M1 .|. n = traces Q M2 .|. n →
      traces (P |. m) M1 .|. n = traces (Q |. m) M2 .|. n

/- (*** distT lemma ***) -/

axiom Depth_rest_distT {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domTType α} {M2 : q → domTType α} :
    distance (traces (P |. m) M1) (traces (Q |. m) M2) <= distance (traces P M1) (traces Q M2)

/- (*** map_alphaT lemma ***) -/

axiom map_alpha_traces_Depth_rest_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domTType α} {M2 : q → domTType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P M1) (traces Q M2) <= alpha * distance x1 x2 →
      distance (traces (P |. m) M1) (traces (Q |. m) M2) <= alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_traces_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {m : Nat} {alpha : ℝ} :
    map_alpha (traces P) alpha → map_alpha (traces (P |. m)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_traces_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {m : Nat} :
    non_expanding (traces P) → non_expanding (traces (P |. m))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_traces_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {m : Nat} {alpha : ℝ} :
    contraction_alpha (traces P) alpha → contraction_alpha (traces (P |. m)) alpha

/- --------------------------------*
 |            variable            |
 *-------------------------------- -/

/- (*** non_expanding ***) -/

axiom non_expanding_traces_variable {p : Type _} {α : Type _} {pn : p} :
    non_expanding (traces (proc.Proc_name pn : proc p α))

/- --------------------------------*
 |            Procfun             |
 *-------------------------------- -/

/- (*****************************************************************
 |                         non_expanding                         |
 *****************************************************************) -/

axiom non_expanding_traces_lm {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (traces P)

axiom non_expanding_traces {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (traces P)

/- =============================================================*
 |                          [[P]]Tf                            |
 *============================================================= -/

axiom non_expanding_semTf {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (semTf P)

/- =============================================================*
 |                         [[P]]Tfun                           |
 *============================================================= -/

axiom non_expanding_semTfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    noHidefun Pf → non_expanding (semTfun Pf)

/- (*****************************************************************
 |                         contraction                           |
 *****************************************************************) -/

axiom contraction_alpha_traces_lm {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (traces P) (1 / 2 : ℝ)

axiom contraction_alpha_traces {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (traces P) (1 / 2 : ℝ)

/- =============================================================*
 |                          [[P]]Tf                            |
 *============================================================= -/

axiom contraction_alpha_semTf {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (semTf P) (1 / 2 : ℝ)

/- =============================================================*
 |                         [[P]]Tfun                           |
 *============================================================= -/

axiom contraction_alpha_semTfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction_alpha (semTfun Pf) (1 / 2 : ℝ)

/- =============================================================*
 |                        contraction                          |
 *============================================================= -/

axiom contraction_semTfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction (semTfun Pf)

end
