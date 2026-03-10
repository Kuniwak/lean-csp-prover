           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
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

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_contraction

open Classical
open SumType

noncomputable section

/-
(*****************************************************************

         1. contraction failuresfun
         2. contraction failuresFun
         3. contraction [[ ]]Ffun
         4. contraction [[ ]]FFun

 *****************************************************************)
-/

/- =============================================================*
 |                      traces fstF                            |
 *============================================================= -/

axiom non_expanding_traces_fstF {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (fun M => traces P (fstF ∘ M))

axiom contraction_alpha_traces_fstF {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (fun M => traces P (fstF ∘ M)) (1 / 2 : ℝ)

/- --------------------------------*
 |        STOP,SKIP,DIV           |
 *-------------------------------- -/

/- (*** STOP ***) -/

axiom map_alpha_failures_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (failures (p := p) (α := α) proc.STOP) alpha

axiom non_expanding_failures_STOP {p : Type _} {α : Type _} :
    non_expanding (failures (p := p) (α := α) proc.STOP)

axiom contraction_alpha_failures_STOP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (failures (p := p) (α := α) proc.STOP) alpha

/- (*** SKIP ***) -/

axiom map_alpha_failures_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (failures (p := p) (α := α) proc.SKIP) alpha

axiom non_expanding_failures_SKIP {p : Type _} {α : Type _} :
    non_expanding (failures (p := p) (α := α) proc.SKIP)

axiom contraction_alpha_failures_SKIP {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (failures (p := p) (α := α) proc.SKIP) alpha

/- (*** DIV ***) -/

axiom map_alpha_failures_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → map_alpha (failures (p := p) (α := α) proc.DIV) alpha

axiom non_expanding_failures_DIV {p : Type _} {α : Type _} :
    non_expanding (failures (p := p) (α := α) proc.DIV)

axiom contraction_alpha_failures_DIV {p : Type _} {α : Type _} {alpha : ℝ} :
    0 <= alpha → 1 > alpha → contraction_alpha (failures (p := p) (α := α) proc.DIV) alpha

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

axiom contraction_half_failures_Act_prefix_lm {p : Type _} {q : Type _} {α : Type _}
    {a : α} {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    distance (failures (a ~> P) M1) (failures (a ~> Q) M2) * 2 =
      distance (failures P M1) (failures Q M2)

/- (***  contraction_half ***) -/

axiom contraction_half_failures_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (failures P) → contraction_alpha (failures (a ~> P)) (1 / 2 : ℝ)

/- (***  contraction ***) -/

axiom contraction_failures_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (failures P) → contraction (failures (a ~> P))

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Act_prefix {p : Type _} {α : Type _}
    {a : α} {P : proc p α} :
    non_expanding (failures P) → non_expanding (failures (a ~> P))

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom Ext_pre_choice_Act_prefix_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ a ∈ X, failures (a ~> Pf a) M1 .|. n <= failures (a ~> Qf a) M2 .|. n) →
      failures (proc.Ext_pre_choice X Pf) M1 .|. n <= failures (proc.Ext_pre_choice X Qf) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Ext_pre_choice_Act_prefix_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ a ∈ X, failures (a ~> Pf a) M1 .|. n = failures (a ~> Qf a) M2 .|. n) →
      failures (proc.Ext_pre_choice X Pf) M1 .|. n = failures (proc.Ext_pre_choice X Qf) M2 .|. n

/- (*** distF lemma ***) -/

axiom Ext_pre_choice_Act_prefix_distF_nonempty {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (setFType α × setFType α)}
    {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    X ≠ ∅ →
      PQs =
        {PQ | ∃ a, a ∈ X ∧ PQ = (failures (a ~> Pf a) M1, failures (a ~> Qf a) M2)} →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (proc.Ext_pre_choice X Pf) M1) (failures (proc.Ext_pre_choice X Qf) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** contraction lemma ***) -/

axiom contraction_half_failures_Ext_pre_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} {Qf : α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : setFType α} :
    X ≠ ∅ →
      (∀ a, distance (failures (Pf a) M1) (failures (Qf a) M2) <= distance x1 x2) →
        distance (failures (proc.Ext_pre_choice X Pf) M1) (failures (proc.Ext_pre_choice X Qf) M2) * 2 <=
          distance x1 x2

/- (*** contraction_half ***) -/

axiom contraction_half_failures_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (failures (Pf a))) →
      contraction_alpha (failures (proc.Ext_pre_choice X Pf)) (1 / 2 : ℝ)

/- (*** Ext_pre_choice_evalT_contraction ***) -/

axiom contraction_failures_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (failures (Pf a))) →
      contraction (failures (proc.Ext_pre_choice X Pf))

/- (*** Ext_pre_choice_evalT_non_expanding ***) -/

axiom non_expanding_failures_Ext_pre_choice {p : Type _} {α : Type _}
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, non_expanding (failures (Pf a))) →
      non_expanding (failures (proc.Ext_pre_choice X Pf))

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Ext_choice_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n <= traces P2 (fstF ∘ M2) .|. n →
      traces Q1 (fstF ∘ M1) .|. n <= traces Q2 (fstF ∘ M2) .|. n →
        failures P1 M1 .|. n <= failures P2 M2 .|. n →
          failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
            failures (P1 [+] Q1) M1 .|. n <= failures (P2 [+] Q2) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Ext_choice_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n = traces P2 (fstF ∘ M2) .|. n →
      traces Q1 (fstF ∘ M1) .|. n = traces Q2 (fstF ∘ M2) .|. n →
        failures P1 M1 .|. n = failures P2 M2 .|. n →
          failures Q1 M1 .|. n = failures Q2 M2 .|. n →
            failures (P1 [+] Q1) M1 .|. n = failures (P2 [+] Q2) M2 .|. n

/- (*** distF lemma ***) -/

axiom Ext_choice_distF {p : Type _} {q : Type _} {α : Type _}
    {PQTs : Set (domTType α × domTType α)} {PQFs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQTs =
      ({(traces P1 (fstF ∘ M1), traces P2 (fstF ∘ M2)),
        (traces Q1 (fstF ∘ M1), traces Q2 (fstF ∘ M2))} :
          Set (domTType α × domTType α)) →
      PQFs =
        ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
          Set (setFType α × setFType α)) →
        (∃ PQ, PQ ∈ PQTs ∧
          distance (failures (P1 [+] Q1) M1) (failures (P2 [+] Q2) M2) <=
            distance (Prod.fst PQ) (Prod.snd PQ)) ∨
          ∃ PQ, PQ ∈ PQFs ∧
            distance (failures (P1 [+] Q1) M1) (failures (P2 [+] Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha F lemma ***) -/

axiom map_alpha_failures_Ext_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 (fstF ∘ M1)) (traces P2 (fstF ∘ M2)) <= alpha * distance x1 x2 →
      distance (traces Q1 (fstF ∘ M1)) (traces Q2 (fstF ∘ M2)) <= alpha * distance x1 x2 →
        distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
          distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
            distance (failures (P1 [+] Q1) M1) (failures (P2 [+] Q2) M2) <=
              alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (fun M => traces P (fstF ∘ M)) alpha →
      map_alpha (fun M => traces Q (fstF ∘ M)) alpha →
        map_alpha (failures P) alpha →
          map_alpha (failures Q) alpha →
            map_alpha (failures (P [+] Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (fun M => traces P (fstF ∘ M)) →
      non_expanding (fun M => traces Q (fstF ∘ M)) →
        non_expanding (failures P) →
          non_expanding (failures Q) →
            non_expanding (failures (P [+] Q))

/- (*** contraction ***) -/

axiom contraction_alpha_failures_Ext_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (fun M => traces P (fstF ∘ M)) alpha →
      contraction_alpha (fun M => traces Q (fstF ∘ M)) alpha →
        contraction_alpha (failures P) alpha →
          contraction_alpha (failures Q) alpha →
            contraction_alpha (failures (P [+] Q)) alpha

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- (*** rest_domT (subset) ***) -/

axiom Int_choice_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n <= failures P2 M2 .|. n →
      failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
        failures (P1 |~| Q1) M1 .|. n <= failures (P2 |~| Q2) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Int_choice_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n = failures P2 M2 .|. n →
      failures Q1 M1 .|. n = failures Q2 M2 .|. n →
        failures (P1 |~| Q1) M1 .|. n = failures (P2 |~| Q2) M2 .|. n

/- (*** distF lemma ***) -/

axiom Int_choice_distF {p : Type _} {q : Type _} {α : Type _}
    {PQs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQs =
      ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (P1 |~| Q1) M1) (failures (P2 |~| Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha F lemma ***) -/

axiom map_alpha_failures_Int_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
      distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
        distance (failures (P1 |~| Q1) M1) (failures (P2 |~| Q2) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures Q) alpha →
        map_alpha (failures (P |~| Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (failures P) →
      non_expanding (failures Q) →
        non_expanding (failures (P |~| Q))

/- (*** contraction ***) -/

axiom contraction_alpha_failures_Int_choice {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures Q) alpha →
        contraction_alpha (failures (P |~| Q)) alpha

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom Rep_int_choice_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ c ∈ sumset C, failures (Pf c) M1 .|. n <= failures (Qf c) M2 .|. n) →
      failures (proc.Rep_int_choice C Pf) M1 .|. n <= failures (proc.Rep_int_choice C Qf) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Rep_int_choice_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    (∀ c ∈ sumset C, failures (Pf c) M1 .|. n = failures (Qf c) M2 .|. n) →
      failures (proc.Rep_int_choice C Pf) M1 .|. n = failures (proc.Rep_int_choice C Qf) M2 .|. n

/- (*** distF lemma ***) -/

axiom Rep_int_choice_distF_nonempty {p : Type _} {q : Type _} {α : Type _}
    {C : sets_nats α} {PQs : Set (setFType α × setFType α)}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    sumset C ≠ ∅ →
      PQs = {PQ | ∃ c, c ∈ sumset C ∧ PQ = (failures (Pf c) M1, failures (Qf c) M2)} →
        ∃ PQ, PQ ∈ PQs ∧
          distance (failures (proc.Rep_int_choice C Pf) M1) (failures (proc.Rep_int_choice C Qf) M2) <=
            distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha F lemma ***) -/

axiom map_alpha_failures_Rep_int_choice_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {C : sets_nats α}
    {Pf : aset_anat α → proc p α} {Qf : aset_anat α → proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    sumset C ≠ ∅ →
      (∀ c, distance (failures (Pf c) M1) (failures (Qf c) M2) <= alpha * distance x1 x2) →
        distance (failures (proc.Rep_int_choice C Pf) M1) (failures (proc.Rep_int_choice C Qf) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, map_alpha (failures (Pf c)) alpha) →
      map_alpha (failures (proc.Rep_int_choice C Pf)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, non_expanding (failures (Pf c))) →
      non_expanding (failures (proc.Rep_int_choice C Pf))

/- (*** Rep_int_choice_evalT_contraction_alpha ***) -/

axiom contraction_alpha_failures_Rep_int_choice {p : Type _} {α : Type _}
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {alpha : ℝ} :
    (∀ c, contraction_alpha (failures (Pf c)) alpha) →
      contraction_alpha (failures (proc.Rep_int_choice C Pf)) alpha

/- --------------------------------*
 |              IF                |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom IF_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n <= failures P2 M2 .|. n →
      failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
        failures (IF b THEN P1 ELSE Q1) M1 .|. n <= failures (IF b THEN P2 ELSE Q2) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom IF_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n = failures P2 M2 .|. n →
      failures Q1 M1 .|. n = failures Q2 M2 .|. n →
        failures (IF b THEN P1 ELSE Q1) M1 .|. n = failures (IF b THEN P2 ELSE Q2) M2 .|. n

/- (*** distF lemma ***) -/

axiom IF_distF {p : Type _} {q : Type _} {α : Type _}
    {b : Bool} {PQs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQs =
      ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (IF b THEN P1 ELSE Q1) M1) (failures (IF b THEN P2 ELSE Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha F lemma ***) -/

axiom map_alpha_failures_IF_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {b : Bool} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
      distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
        distance (failures (IF b THEN P1 ELSE Q1) M1) (failures (IF b THEN P2 ELSE Q2) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures Q) alpha →
        map_alpha (failures (IF b THEN P ELSE Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} :
    non_expanding (failures P) →
      non_expanding (failures Q) →
        non_expanding (failures (IF b THEN P ELSE Q))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_failures_IF {p : Type _} {α : Type _}
    {b : Bool} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures Q) alpha →
        contraction_alpha (failures (IF b THEN P ELSE Q)) alpha

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom Parallel_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n <= failures P2 M2 .|. n →
      failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
        failures (P1 |[X]| Q1) M1 .|. n <= failures (P2 |[X]| Q2) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Parallel_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P1 M1 .|. n = failures P2 M2 .|. n →
      failures Q1 M1 .|. n = failures Q2 M2 .|. n →
        failures (P1 |[X]| Q1) M1 .|. n = failures (P2 |[X]| Q2) M2 .|. n

/- (*** distF lemma ***) -/

axiom Parallel_distF {p : Type _} {q : Type _} {α : Type _}
    {X : Set α} {PQs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQs =
      ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
        Set (setFType α × setFType α)) →
          ∃ PQ, PQ ∈ PQs ∧
            distance (failures (P1 |[X]| Q1) M1) (failures (P2 |[X]| Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha F lemma ***) -/

axiom map_alpha_failures_Parallel_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {X : Set α} {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
      distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
        distance (failures (P1 |[X]| Q1) M1) (failures (P2 |[X]| Q2) M2) <=
          alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures Q) alpha →
        map_alpha (failures (P |[X]| Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} :
    non_expanding (failures P) →
      non_expanding (failures Q) →
        non_expanding (failures (P |[X]| Q))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_failures_Parallel {p : Type _} {α : Type _}
    {X : Set α} {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures Q) alpha →
        contraction_alpha (failures (P |[X]| Q)) alpha

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- cms rules for Hiding is not necessary
   because processes are guarded. -/

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom Renaming_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P M1 .|. n <= failures Q M2 .|. n →
      failures (P [[r]]) M1 .|. n <= failures (Q [[r]]) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Renaming_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    failures P M1 .|. n = failures Q M2 .|. n →
      failures (P [[r]]) M1 .|. n = failures (Q [[r]]) M2 .|. n

/- (*** distF lemma ***) -/

axiom Renaming_distF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    distance (failures (P [[r]]) M1) (failures (Q [[r]]) M2) <= distance (failures P M1) (failures Q M2)

/- (*** map_alphaT lemma ***) -/

axiom map_alpha_failures_Renaming_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {r : Set (α × α)}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P M1) (failures Q M2) <= alpha * distance x1 x2 →
      distance (failures (P [[r]]) M1) (failures (Q [[r]]) M2) <= alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures (P [[r]])) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} :
    non_expanding (failures P) →
      non_expanding (failures (P [[r]]))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_failures_Renaming {p : Type _} {α : Type _}
    {P : proc p α} {r : Set (α × α)} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures (P [[r]])) alpha

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom Seq_compo_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n <= traces P2 (fstF ∘ M2) .|. n →
      failures P1 M1 .|. n <= failures P2 M2 .|. n →
        failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
          failures (P1 ;; Q1) M1 .|. n <= failures (P2 ;; Q2) M2 .|. n

/- (*** rest_setF (equal) ***) -/

axiom Seq_compo_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. n = traces P2 (fstF ∘ M2) .|. n →
      failures P1 M1 .|. n = failures P2 M2 .|. n →
        failures Q1 M1 .|. n = failures Q2 M2 .|. n →
          failures (P1 ;; Q1) M1 .|. n = failures (P2 ;; Q2) M2 .|. n

/- (*** distF lemma ***) -/

axiom Seq_compo_distF {p : Type _} {q : Type _} {α : Type _}
    {PQTs : Set (domTType α × domTType α)} {PQFs : Set (setFType α × setFType α)}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    PQTs = ({(traces P1 (fstF ∘ M1), traces P2 (fstF ∘ M2))} : Set (domTType α × domTType α)) →
      PQFs =
        ({(failures P1 M1, failures P2 M2), (failures Q1 M1, failures Q2 M2)} :
          Set (setFType α × setFType α)) →
        (∃ PQ, PQ ∈ PQTs ∧
          distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) <=
            distance (Prod.fst PQ) (Prod.snd PQ)) ∨
          ∃ PQ, PQ ∈ PQFs ∧
            distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) <=
              distance (Prod.fst PQ) (Prod.snd PQ)

/- (*** map_alpha F lemma ***) -/

axiom map_alpha_failures_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (traces P1 (fstF ∘ M1)) (traces P2 (fstF ∘ M2)) <= alpha * distance x1 x2 →
      distance (failures P1 M1) (failures P2 M2) <= alpha * distance x1 x2 →
        distance (failures Q1 M1) (failures Q2 M2) <= alpha * distance x1 x2 →
          distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) <=
            alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    map_alpha (fun M => traces P (fstF ∘ M)) alpha →
      map_alpha (failures P) alpha →
        map_alpha (failures Q) alpha →
          map_alpha (failures (P ;; Q)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    non_expanding (fun M => traces P (fstF ∘ M)) →
      non_expanding (failures P) →
        non_expanding (failures Q) →
          non_expanding (failures (P ;; Q))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} {alpha : ℝ} :
    contraction_alpha (fun M => traces P (fstF ∘ M)) alpha →
      contraction_alpha (failures P) alpha →
        contraction_alpha (failures Q) alpha →
          contraction_alpha (failures (P ;; Q)) alpha

/- --------------------------------*
 |       Seq_compo  (gSKIP)       |
 *-------------------------------- -/

/- (*** rest_setF (subset) ***) -/

axiom gSKIP_Seq_compo_rest_setF_sub {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. Nat.succ n <= traces P2 (fstF ∘ M2) .|. Nat.succ n →
      failures P1 M1 .|. Nat.succ n <= failures P2 M2 .|. Nat.succ n →
        failures Q1 M1 .|. n <= failures Q2 M2 .|. n →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 (fstF ∘ M1)) →
            ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 (fstF ∘ M2)) →
              failures (P1 ;; Q1) M1 .|. Nat.succ n <= failures (P2 ;; Q2) M2 .|. Nat.succ n

/- (*** rest_setF (equal) ***) -/

axiom gSKIP_Seq_compo_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    traces P1 (fstF ∘ M1) .|. Nat.succ n = traces P2 (fstF ∘ M2) .|. Nat.succ n →
      failures P1 M1 .|. Nat.succ n = failures P2 M2 .|. Nat.succ n →
        failures Q1 M1 .|. n = failures Q2 M2 .|. n →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 (fstF ∘ M1)) →
            ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 (fstF ∘ M2)) →
              failures (P1 ;; Q1) M1 .|. Nat.succ n = failures (P2 ;; Q2) M2 .|. Nat.succ n

/- (*** map_alpha F lemma ***) -/

axiom gSKIP_map_alpha_failures_Seq_compo_lm {p : Type _} {q : Type _} {α : Type _}
    {P1 Q1 : proc p α} {P2 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α} {n : Nat} :
    distance (traces P1 (fstF ∘ M1)) (traces P2 (fstF ∘ M2)) * 2 <= (1 / 2 : ℝ) ^ n →
      distance (failures P1 M1) (failures P2 M2) * 2 <= (1 / 2 : ℝ) ^ n →
        distance (failures Q1 M1) (failures Q2 M2) <= (1 / 2 : ℝ) ^ n →
          ((Abs_trace [event.Tick] : traceType α) ~:t traces P1 (fstF ∘ M1)) →
            ((Abs_trace [event.Tick] : traceType α) ~:t traces P2 (fstF ∘ M2)) →
              distance (failures (P1 ;; Q1) M1) (failures (P2 ;; Q2) M2) * 2 <= (1 / 2 : ℝ) ^ n

/- (*** map_alpha ***) -/

axiom gSKIP_contraction_half_failures_Seq_compo {p : Type _} {α : Type _}
    {P Q : proc p α} :
    contraction_alpha (fun M => traces P (fstF ∘ M)) (1 / 2 : ℝ) →
      contraction_alpha (failures P) (1 / 2 : ℝ) →
        non_expanding (failures Q) →
          gSKIP P →
            contraction_alpha (failures (P ;; Q)) (1 / 2 : ℝ)

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** rest_setF (equal) ***) -/

axiom Depth_rest_rest_setF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m n : Nat}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    failures P M1 .|. n = failures Q M2 .|. n →
      failures (P |. m) M1 .|. n = failures (Q |. m) M2 .|. n

/- (*** distF lemma ***) -/

axiom Depth_rest_distF {p : Type _} {q : Type _} {α : Type _}
    {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domFType α} {M2 : q → domFType α} :
    distance (failures (P |. m) M1) (failures (Q |. m) M2) <= distance (failures P M1) (failures Q M2)

/- (*** map_alphaT lemma ***) -/

axiom map_alpha_failures_Depth_rest_lm {p : Type _} {q : Type _} {α : Type _}
    {β : Type _} [ms β] {P : proc p α} {Q : proc q α} {m : Nat}
    {M1 : p → domFType α} {M2 : q → domFType α}
    {x1 x2 : β} {alpha : ℝ} :
    distance (failures P M1) (failures Q M2) <= alpha * distance x1 x2 →
      distance (failures (P |. m) M1) (failures (Q |. m) M2) <= alpha * distance x1 x2

/- (*** map_alpha ***) -/

axiom map_alpha_failures_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {n : Nat} {alpha : ℝ} :
    map_alpha (failures P) alpha →
      map_alpha (failures (P |. n)) alpha

/- (*** non_expanding ***) -/

axiom non_expanding_failures_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {n : Nat} :
    non_expanding (failures P) →
      non_expanding (failures (P |. n))

/- (*** contraction_alpha ***) -/

axiom contraction_alpha_failures_Depth_rest {p : Type _} {α : Type _}
    {P : proc p α} {n : Nat} {alpha : ℝ} :
    contraction_alpha (failures P) alpha →
      contraction_alpha (failures (P |. n)) alpha

/- --------------------------------*
 |            variable            |
 *-------------------------------- -/

/- (*** non_expanding ***) -/

axiom continuous_failures_variable_lm {p : Type _} {α : Type _} {p0 : p} :
    non_expanding (fun M : p → domFType α => sndF (M p0))

axiom non_expanding_failures_variable {p : Type _} {α : Type _} {p0 : p} :
    non_expanding (failures (proc.Proc_name p0 : proc p α))

/- --------------------------------*
 |            Procfun             |
 *-------------------------------- -/

/- (*****************************************************************
 |                         non_expanding                         |
 *****************************************************************) -/

axiom non_expanding_failures_lm {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (failures P)

axiom non_expanding_failures {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (failures P)

/- =============================================================*
 |                          [[P]]Ff                            |
 *============================================================= -/

axiom non_expanding_semFf {p : Type _} {α : Type _} {P : proc p α} :
    noHide P → non_expanding (semFf P)

/- =============================================================*
 |                         [[P]]Ffun                           |
 *============================================================= -/

axiom non_expanding_semFfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    noHidefun Pf → non_expanding (semFfun Pf)

/- (*****************************************************************
 |                         contraction                           |
 *****************************************************************) -/

axiom contraction_alpha_failures_lm {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (failures P) (1 / 2 : ℝ)

axiom contraction_alpha_failures {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (failures P) (1 / 2 : ℝ)

/- =============================================================*
 |                          [[P]]Ff                            |
 *============================================================= -/

axiom contraction_alpha_semFf {p : Type _} {α : Type _} {P : proc p α} :
    guarded P → contraction_alpha (semFf P) (1 / 2 : ℝ)

/- =============================================================*
 |                         [[P]]Ffun                           |
 *============================================================= -/

axiom contraction_alpha_semFfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction_alpha (semFfun Pf) (1 / 2 : ℝ)

/- =============================================================*
 |                        contraction                          |
 *============================================================= -/

axiom contraction_semFfun {p : Type _} {α : Type _} {Pf : p → proc p α} :
    guardedfun Pf → contraction (semFfun Pf)

end
