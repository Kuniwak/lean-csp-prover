           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   June 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_failures

open Classical
open SumType

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.          -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

/-
(*********************************************************
                        domF
 *********************************************************)
-/

/- --------------------------------*
 |             STOP               |
 *-------------------------------- -/

/- T2 -/

axiom STOP_T2 {M : p → domFType α} :
    HC_T2 (traces proc.STOP (fstF ∘ M), failures proc.STOP M)

/- F3 -/

axiom STOP_F3 {M : p → domFType α} :
    HC_F3 (traces proc.STOP (fstF ∘ M), failures proc.STOP M)

/- T3_F4 -/

axiom STOP_T3_F4 {M : p → domFType α} :
    HC_T3_F4 (traces proc.STOP (fstF ∘ M), failures proc.STOP M)

/- (*** STOP_domF ***) -/

axiom STOP_domF {M : p → domFType α} :
    (traces proc.STOP (fstF ∘ M), failures proc.STOP M) ∈ domF (α := α)

/- --------------------------------*
 |             SKIP               |
 *-------------------------------- -/

/- T2 -/

axiom SKIP_T2 {M : p → domFType α} :
    HC_T2 (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M)

/- F3 -/

axiom SKIP_F3 {M : p → domFType α} :
    HC_F3 (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M)

/- T3_F4 -/

axiom SKIP_T3_F4 {M : p → domFType α} :
    HC_T3_F4 (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M)

/- (*** SKIP_domF ***) -/

axiom SKIP_domF {M : p → domFType α} :
    (traces proc.SKIP (fstF ∘ M), failures proc.SKIP M) ∈ domF (α := α)

/- --------------------------------*
 |              DIV               |
 *-------------------------------- -/

/- T2 -/

axiom DIV_T2 {M : p → domFType α} :
    HC_T2 (traces proc.DIV (fstF ∘ M), failures proc.DIV M)

/- F3 -/

axiom DIV_F3 {M : p → domFType α} :
    HC_F3 (traces proc.DIV (fstF ∘ M), failures proc.DIV M)

/- T3_F4 -/

axiom DIV_T3_F4 {M : p → domFType α} :
    HC_T3_F4 (traces proc.DIV (fstF ∘ M), failures proc.DIV M)

/- (*** DIV_domF ***) -/

axiom DIV_domF {M : p → domFType α} :
    (traces proc.DIV (fstF ∘ M), failures proc.DIV M) ∈ domF (α := α)

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

/- T2 -/

axiom Act_prefix_T2 {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M)

/- F3 -/

axiom Act_prefix_F3 {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M)

/- T3_F4 -/

axiom Act_prefix_T3_F4 {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M)

/- (*** Act_prefix_domF ***) -/

axiom Act_prefix_domF {a : α} {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (a ~> P) (fstF ∘ M), failures (a ~> P) M) ∈ domF (α := α)

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

/- T2 -/

axiom Ext_pre_choice_T2 {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      HC_T2 (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M), failures (proc.Ext_pre_choice X Pf) M)

/- F3 -/

axiom Ext_pre_choice_F3 {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      HC_F3 (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M), failures (proc.Ext_pre_choice X Pf) M)

/- T3_F4 -/

axiom Ext_pre_choice_T3_F4 {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      HC_T3_F4 (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M), failures (proc.Ext_pre_choice X Pf) M)

/- (*** Ext_pre_choice_domF ***) -/

axiom Ext_pre_choice_domF {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    (∀ a, (traces (Pf a) (fstF ∘ M), failures (Pf a) M) ∈ domF (α := α)) →
      (traces (proc.Ext_pre_choice X Pf) (fstF ∘ M), failures (proc.Ext_pre_choice X Pf) M) ∈
        domF (α := α)

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

/- T2 -/

axiom Ext_choice_T2 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M)

/- F3 -/

axiom Ext_choice_F3 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M)

/- T3_F4 -/

axiom Ext_choice_T3_F4 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M)

/- (*** Ext_choice_domF ***) -/

axiom Ext_choice_domF {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P [+] Q) (fstF ∘ M), failures (P [+] Q) M) ∈ domF (α := α)

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

/- T2 -/

axiom Int_choice_T2 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M)

/- F3 -/

axiom Int_choice_F3 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M)

/- T3_F4 -/

axiom Int_choice_T3_F4 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M)

/- (*** Int_choice_domF ***) -/

axiom Int_choice_domF {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P |~| Q) (fstF ∘ M), failures (P |~| Q) M) ∈ domF (α := α)

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

/- T2 -/

axiom Union_proc_T2 {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      HC_T2
        (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
          CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c))

axiom Rep_int_choice_T2 {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      HC_T2 (traces (proc.Rep_int_choice C Pf) (fstF ∘ M), failures (proc.Rep_int_choice C Pf) M)

/- F3 -/

axiom Union_proc_F3 {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      HC_F3
        (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
          CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c))

/- The Isabelle theorem `Rep_int_choice_nat` is named `Rep_int_choice_F3`
   here to avoid clashing with the existing definition `Rep_int_choice_nat`. -/
axiom Rep_int_choice_F3 {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      HC_F3 (traces (proc.Rep_int_choice C Pf) (fstF ∘ M), failures (proc.Rep_int_choice C Pf) M)

/- T3_F4 -/

axiom Union_proc_T3_F4 {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      HC_T3_F4
        (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
          CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c))

axiom Rep_int_choice_T3_F4 {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      HC_T3_F4
        (traces (proc.Rep_int_choice C Pf) (fstF ∘ M), failures (proc.Rep_int_choice C Pf) M)

/- (*** F ***) -/

axiom Union_proc_domF {ι : Type _} {C : Set ι} {Tf : ι → domTType α} {Ff : ι → setFType α} :
    (∀ c, (Tf c, Ff c) ∈ domF (α := α)) →
      (CollectT (fun t : traceType α => t = <> ∨ ∃ c, c ∈ C ∧ t :t Tf c),
        CollectF (fun f : failure α => ∃ c, c ∈ C ∧ f :f Ff c)) ∈ domF (α := α)

/- (*** Rep_int_choice_domF ***) -/

axiom Rep_int_choice_domF {C : sets_nats α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, (traces (Pf c) (fstF ∘ M), failures (Pf c) M) ∈ domF (α := α)) →
      (traces (proc.Rep_int_choice C Pf) (fstF ∘ M), failures (proc.Rep_int_choice C Pf) M) ∈
        domF (α := α)

/- --------------------------------*
 |               IF               |
 *-------------------------------- -/

/- T2 -/

axiom IF_T2 {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M)

/- F3 -/

axiom IF_F3 {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M)

/- T3_F4 -/

axiom IF_T3_F4 {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M)

/- (*** IF_domF ***) -/

axiom IF_domF {b : Bool} {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (IF b THEN P ELSE Q) (fstF ∘ M), failures (IF b THEN P ELSE Q) M) ∈ domF (α := α)

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

/- (*** T2 ***) -/

axiom Parallel_T2 {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M)

/- (*** F3 ***) -/

axiom Parallel_F3_lm1 {X1 X2 X3 X : Set α} :
    X1 ∪ (X2 ∪ X3) \ X = (X1 \ X) ∪ (X2 \ X) ∪ (X3 \ X)

axiom Parallel_F3_lm2 {X1 X2 Y1 Y2 : Set α} :
    X1 = X2 → Y1 = Y2 → X1 ∪ Y1 = X2 ∪ Y2

axiom Parallel_F3 {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M)

/- T3_F4 -/

axiom Parallel_T3_F4 {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M)

/- (*** Parallel_domF ***) -/

axiom Parallel_domF {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P |[X]| Q) (fstF ∘ M), failures (P |[X]| Q) M) ∈ domF (α := α)

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

/- (*** T2 ***) -/

axiom Hiding_T2 {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M)

/- (*** F3 ***) -/

axiom Hiding_F3 {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M)

/- T3_F4 -/

axiom Hiding_T3_F4 {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M)

/- (*** Hiding_domF ***) -/

axiom Hiding_domF {P : proc p α} {X : Set α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (proc.Hiding P X) (fstF ∘ M), failures (proc.Hiding P X) M) ∈ domF (α := α)

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

/- (*** T2 ***) -/

axiom Renaming_T2 {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M)

/- (*** F3 ***) -/

axiom Renaming_F3 {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M)

/- T3_F4 -/

axiom Renaming_T3_F4 {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M)

/- (*** Renaming_domF ***) -/

axiom Renaming_domF {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (P[[r]]) (fstF ∘ M), failures (P[[r]]) M) ∈ domF (α := α)

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

/- (*** T2 ***) -/

axiom Seq_compo_T2 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T2 (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M)

/- (*** F3 ***) -/

axiom Seq_compo_F3 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_F3 (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M)

/- T3_F4 -/

axiom Seq_compo_T3_F4 {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        HC_T3_F4 (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M)

/- (*** Seq_compo_domF ***) -/

axiom Seq_compo_domF {P Q : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces Q (fstF ∘ M), failures Q M) ∈ domF (α := α) →
        (traces (P ;; Q) (fstF ∘ M), failures (P ;; Q) M) ∈ domF (α := α)

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

/- (*** T2 ***) -/

axiom Depth_rest_T2 {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T2 (traces (P |. n) (fstF ∘ M), failures (P |. n) M)

/- (*** F3 ***) -/

axiom Depth_rest_F3 {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_F3 (traces (P |. n) (fstF ∘ M), failures (P |. n) M)

/- T3_F4 -/

axiom Depth_rest_T3_F4 {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      HC_T3_F4 (traces (P |. n) (fstF ∘ M), failures (P |. n) M)

/- (*** Depth_rest_domF ***) -/

axiom Depth_rest_domF {P : proc p α} {n : Nat} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α) →
      (traces (P |. n) (fstF ∘ M), failures (P |. n) M) ∈ domF (α := α)

/- --------------------------------*
 |        Proc_name_dom           |
 *-------------------------------- -/

/- (*** T2 ***) -/

axiom Proc_name_T2 {p0 : p} {M : p → domFType α} :
    HC_T2 (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M)

/- (*** F3 ***) -/

axiom Proc_name_F3 {p0 : p} {M : p → domFType α} :
    HC_F3 (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M)

/- T3_F4 -/

axiom Proc_name_T3_F4 {p0 : p} {M : p → domFType α} :
    HC_T3_F4 (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M)

/- (*** Proc_name_domF ***) -/

axiom Proc_name_domF {p0 : p} {M : p → domFType α} :
    (traces (proc.Proc_name p0) (fstF ∘ M), failures (proc.Proc_name p0) M) ∈ domF (α := α)

/- --------------------------------*
 |             proc               |
 *-------------------------------- -/

@[simp]
axiom proc_domF {P : proc p α} {M : p → domFType α} :
    (traces P (fstF ∘ M), failures P M) ∈ domF (α := α)

/- --------------------------------*
 |          fstF sndF             |
 *-------------------------------- -/

@[simp]
theorem fstF_proc_domF {P : proc p α} {M : p → domFType α} :
    fstF (traces P (fstF ∘ M) ,, failures P M) = traces P (fstF ∘ M) := by
  exact pairF_fstF (hSF := proc_domF (P := P) (M := M))

@[simp]
theorem sndF_proc_domF {P : proc p α} {M : p → domFType α} :
    sndF (traces P (fstF ∘ M) ,, failures P M) = failures P M := by
  exact pairF_sndF (hSF := proc_domF (P := P) (M := M))

@[simp]
axiom fstF_proc_domF2 {P : proc p α} {M : p → domFType α} :
    fstF (traces P (fun x => fstF (M x)) ,, failures P M) = traces P (fstF ∘ M)

@[simp]
axiom sndF_proc_domF2 {P : proc p α} {M : p → domFType α} :
    sndF (traces P (fun x => fstF (M x)) ,, failures P M) = failures P M

theorem fstF_proc_domF_fun {β : Type _} {f : β → proc p α} {M : p → domFType α} :
    fstF ∘ (fun p => traces (f p) (fstF ∘ M) ,, failures (f p) M) = fun p => traces (f p) (fstF ∘ M) := by
  funext p
  simp

theorem sndF_proc_domF_fun {β : Type _} {f : β → proc p α} {M : p → domFType α} :
    sndF ∘ (fun p => traces (f p) (fstF ∘ M) ,, failures (f p) M) = fun p => failures (f p) M := by
  funext p
  simp

@[simp]
theorem fstF_semFf {P : proc p α} {M : p → domFType α} :
    fstF (semFf P M) = traces P (fstF ∘ M) := by
  simp [semFf_def]

@[simp]
theorem fstF_semF [HasPNfun p α] [HasFPmode] {P : proc p α} :
    fstF (semF P) = traces P (fstF ∘ MF) := by
  simp [semF_def]

@[simp]
theorem sndF_semFf {P : proc p α} {M : p → domFType α} :
    sndF (semFf P M) = failures P M := by
  simp [semFf_def]

@[simp]
theorem sndF_semF [HasPNfun p α] [HasFPmode] {P : proc p α} :
    sndF (semF P) = failures P MF := by
  simp [semF_def]

/- (*** decomposition ***) -/

theorem semFf_decompo {P : proc p α} {M : p → domFType α} {SF : domFType α} :
    semFf P M = SF ↔ (traces P (fstF ∘ M) = fstF SF ∧ failures P M = sndF SF) := by
  constructor
  · intro h
    cases h
    simp
  · intro h
    exact (eqF_decompo (SF := semFf P M) (SE := SF)).2
      ⟨by simpa using h.1, by simpa using h.2⟩

theorem semF_decompo [HasPNfun p α] [HasFPmode] {P : proc p α} {SF : domFType α} :
    semF P = SF ↔ (traces P (fstF ∘ MF) = fstF SF ∧ failures P MF = sndF SF) := by
  simpa [semF_def] using (semFf_decompo (P := P) (M := MF) (SF := SF))

theorem semFf_decompo_fstF {P : proc p α} {M : p → domFType α} {SF : domFType α} :
    semFf P M = SF → traces P (fstF ∘ M) = fstF SF := by
  intro h
  exact (semFf_decompo (P := P) (M := M) (SF := SF)).1 h |>.1

theorem semF_decompo_fstF [HasPNfun p α] [HasFPmode] {P : proc p α} {SF : domFType α} :
    semF P = SF → traces P (fstF ∘ MF) = fstF SF := by
  intro h
  exact (semF_decompo (P := P) (SF := SF)).1 h |>.1

theorem semFf_decompo_sndF {P : proc p α} {M : p → domFType α} {SF : domFType α} :
    semFf P M = SF → failures P M = sndF SF := by
  intro h
  exact (semFf_decompo (P := P) (M := M) (SF := SF)).1 h |>.2

theorem semF_decompo_sndF [HasPNfun p α] [HasFPmode] {P : proc p α} {SF : domFType α} :
    semF P = SF → failures P MF = sndF SF := by
  intro h
  exact (semF_decompo (P := P) (SF := SF)).1 h |>.2

/- --------------------------------*
 |            [[p]]Ff            |
 *-------------------------------- -/

theorem semFf_Proc_name {p0 : p} :
    semFf (proc.Proc_name p0 : proc p α) = fun M : p → domFType α => M p0 := by
  funext M
  apply (eqF_decompo (SF := semFf (proc.Proc_name p0) M) (SE := M p0)).2
  simp [semFf, traces, failures]

/- --------------------------------*
 |          =F and <=F            |
 *-------------------------------- -/

theorem cspF_eqF_semantics {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q ↔
      (traces P (fstF ∘ M1) = traces Q (fstF ∘ M2) ∧ failures P M1 = failures Q M2) := by
  rw [eqF_def]
  exact (eqF_decompo (SF := semFf P M1) (SE := semFf Q M2)).trans <| by simp

theorem cspF_refF_semantics {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    refF P M1 M2 Q ↔
      (traces Q (fstF ∘ M2) <= traces P (fstF ∘ M1) ∧ failures Q M2 <= failures P M1) := by
  rw [refF_def]
  exact (subdomF_decompo (SF := semFf Q M2) (SE := semFf P M1)).trans <| by simp

/- The Isabelle theorem bundle `cspF_semantics` is represented by
   `cspF_eqF_semantics` and `cspF_refF_semantics`. -/

theorem cspF_cspT_eqF_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P M1 M2 Q ↔
      (eqT P (fstF ∘ M1) (fstF ∘ M2) Q ∧ failures P M1 = failures Q M2) := by
  rw [cspF_eqF_semantics, cspT_eqT_semantics]

theorem cspF_cspT_refF_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    refF P M1 M2 Q ↔
      (refT P (fstF ∘ M1) (fstF ∘ M2) Q ∧ failures Q M2 <= failures P M1) := by
  rw [cspF_refF_semantics, cspT_refT_semantics]

/- The Isabelle theorem bundle `cspF_cspT_semantics` is represented by
   `cspF_cspT_eqF_semantics` and `cspF_cspT_refF_semantics`. -/

/- --------------------------------*
 |            Timeout             |
 *-------------------------------- -/

axiom in_failures_Timeout1 {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (P [> Q) M) ↔
      (f :f failures Q M ∨
        (∃ s X, f = (s, X) ∧ s ≠ <> ∧ (s, X) :f failures P M) ∨
        ∃ X, f = (<>, X) ∧ X ⊆ Evset ∧ (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M))

theorem in_failures_Timeout2 {f : failure α} {P Q : proc p α} {M : p → domFType α} :
    (f :f failures (Timeout P Q) M) ↔
      (f :f failures Q M ∨
        (∃ s X, f = (s, X) ∧ s ≠ <> ∧ (s, X) :f failures P M) ∨
        ∃ X, f = (<>, X) ∧ X ⊆ Evset ∧ (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M)) := by
  simpa [Timeout_def] using (in_failures_Timeout1 (f := f) (P := P) (Q := Q) (M := M))

/- The Isabelle theorem bundle `in_failures_Timeout` is represented by
   `in_failures_Timeout1` and `in_failures_Timeout2`. -/

/- --------------------------------*
 |           Depth rest           |
 *-------------------------------- -/

axiom semFf_Depth_rest {P : proc p α} {n : Nat} {M : p → domFType α} :
    semFf (P |. n) M = semFf P M .|. n

theorem semF_Depth_rest [HasPNfun p α] [HasFPmode] {P : proc p α} {n : Nat} :
    semF (P |. n) = semF P .|. n := by
  simpa [semF_def] using (semFf_Depth_rest (P := P) (n := n) (M := MF))

/- ---------------------------------------------------*
 |         Healthiness conditions for proc           |
 *--------------------------------------------------- -/

axiom proc_T2 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)} :
    (s, X) :f failures P M → s :t traces P (fstF ∘ M)

axiom proc_T3 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) →
      noTick s →
        (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f failures P M

axiom proc_T3_Tick {P : proc p α} {M : p → domFType α} {X : Set (event α)} :
    (Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M) →
      ((Abs_trace [event.Tick] : traceType α), X) :f failures P M

axiom proc_F4 {P : proc p α} {M : p → domFType α} {s : traceType α} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) →
      noTick s →
        (s, Evset) :f failures P M

axiom proc_F3 {P : proc p α} {M : p → domFType α} {s : traceType α}
    {X Y : Set (event α)} :
    (s, X) :f failures P M →
      noTick s →
        (∀ a, a ∈ Y → ¬ (s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) →
          (s, X ∪ Y) :f failures P M

axiom proc_F3I {P : proc p α} {M : p → domFType α} {s : traceType α}
    {X Y Z : Set (event α)} :
    (s, X) :f failures P M →
      noTick s →
        (∀ a, a ∈ Y → ¬ (s ^^^ (Abs_trace [a] : traceType α)) :t traces P (fstF ∘ M)) →
          Z = X ∪ Y →
            (s, Z) :f failures P M

/- (*** F2_F4 ***) -/

axiom proc_F2_F4 {P : proc p α} {M : p → domFType α} {s : traceType α} {X : Set (event α)} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) →
      noTick s →
        X ⊆ Evset →
          (s, X) :f failures P M

/- (*** T2_T3 ***) -/

axiom proc_T2_T3 {P : proc p α} {M : p → domFType α} {s : traceType α}
    {X Y : Set (event α)} :
    (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f failures P M →
      noTick s →
        (s ^^^ (Abs_trace [event.Tick] : traceType α), Y) :f failures P M

/-
------------------------------------------------------*
 |   Union in domF  (used for generic internal choice   |
 *------------------------------------------------------ -/

axiom non_empty_UnionT_UnionF_T2 {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      HC_T2
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M})

axiom non_empty_UnionT_UnionF_F3 {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      HC_F3
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M})

axiom non_empty_UnionT_UnionF_T3_F4 {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      HC_T3_F4
        (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
          UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M})

axiom non_empty_UnionT_UnionF_domF {Ps : Set (proc p α)} {M : p → domFType α} :
    Ps ≠ ∅ →
      (UnionT {T : domTType α | ∃ P, P ∈ Ps ∧ T = traces P (fstF ∘ M)},
        UnionF {F : setFType α | ∃ P, P ∈ Ps ∧ F = failures P M}) ∈ domF (α := α)

/-
------------------------------------------------------*
 |   Union in domF  (used for generic internal choice   |
 *------------------------------------------------------ -/

axiom UnionT_UnionF_T2 {Ps : Set (proc p α)} {M : p → domFType α} :
    HC_T2
      (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
        CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M))

axiom UnionT_UnionF_F3 {Ps : Set (proc p α)} {M : p → domFType α} :
    HC_F3
      (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
        CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M))

axiom UnionT_UnionF_T3_F4 {Ps : Set (proc p α)} {M : p → domFType α} :
    HC_T3_F4
      (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
        CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M))

axiom UnionT_UnionF_domF {Ps : Set (proc p α)} {M : p → domFType α} :
    (CollectT (fun t : traceType α => t = <> ∨ ∃ P, P ∈ Ps ∧ t :t traces P (fstF ∘ M)),
      CollectF (fun f : failure α => ∃ P, P ∈ Ps ∧ f :f failures P M)) ∈ domF (α := α)

/- -----------------------------------------*
 |              substitution               |
 *----------------------------------------- -/

axiom semF_subst [HasPNfun q α] [HasFPmode] {P : proc p α} {f : p → proc q α} :
    semF (P << f) = semFf P (fun q => semF (f q))

axiom semF_subst_semFfun [HasPNfun q α] [HasFPmode] {Pf : p → proc p α} {f : p → proc q α} :
    (fun q => semF ((Pf q) << f)) = semFfun Pf (fun q => semF (f q))

axiom failrues_subst {P : proc p α} {f : p → proc q α} {M : q → domFType α} :
    failures (P << f) M = failures P (fun q => semFf (f q) M)

/- -----------------------------------------*
 |               semT -- semF              |
 *----------------------------------------- -/

theorem semTfun_fstF_semFf {Pf : p → proc p α} {M : p → domFType α} {p0 : p} :
    semTfun Pf (fstF ∘ M) p0 = fstF (semFf (Pf p0) M) := by
  simp [semTfun_def, semTf_def, semFf_def]

end
