           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_alpha_par
import LeanCspProver.CSP_F.CSP_F_op_rep_par
import LeanCspProver.CSP_T.CSP_T_law_rep_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `UnionT` and `InterT`.             -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq` or        -/
/-  `Inf_image_eq`, so there is nothing to disable or re-enable here.  -/

/-
(*****************************************************************

         1. associativity of [||]:I
         2. commutativity of [||]:I
         3.
         4.

 *****************************************************************)
-/

/-
(*****************************************************
   replace an index set with another equal index set
 *****************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Rep_parallel_index_eq_lm1
    [Inhabited ι]
    {I1 : Set ι} {f : ι → κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {Yf : ι → Set (event α)} :
    Set.InjOn f I1 →
      (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i) →
        Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
          S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf1 i))))} =
        Set.sUnion {S | ∃ i : κ, i ∈ f '' I1 ∧
          S =
            Set.inter
              (Yf (inv_on I1 f i))
              (Set.insert Tick (Ev '' (Prod.snd (PXf2 i))))}

axiom cspF_Rep_parallel_index_eq_lm2
    {I1 : Set ι} {f : ι → κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {Yf : κ → Set (event α)} :
    (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i) →
      Set.sUnion {S | ∃ i : κ, i ∈ f '' I1 ∧
        S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf2 i))))} =
      Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
        S = Set.inter (Yf (f i)) (Set.insert Tick (Ev '' (Prod.snd (PXf1 i))))}

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Rep_parallel_index_eq
    {I1 : Set ι} {I2 : Set κ}
    {PXf1 : ι → proc p α × Set α} {PXf2 : κ → proc p α × Set α}
    {M : p → domFType α} :
    I1.Finite →
      (∃ f : ι → κ, I2 = f '' I1 ∧ Set.InjOn f I1 ∧
        (∀ i : ι, i ∈ I1 → PXf2 (f i) = PXf1 i)) →
        eqF (Rep_parallel I1 PXf1) M M (Rep_parallel I2 PXf2)

/-
(*********************************************************
                [||]:I PXf ==> [||] PXs
 *********************************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Index_to_Inductive_parallel
    {I : Set ι} {Is : List ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite → isListOf Is I →
      eqF (Rep_parallel I PXf) M M (Inductive_parallel (List.map PXf Is))

/-
(************************************
 |       [||]:I PXf and SKIP        |
 ************************************)
-/

axiom cspF_SKIP_Rep_parallel_right_lm1
    {I : Set ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    I ≠ ∅ →
      Set.insert Tick
        (Set.sUnion {S | ∃ i : ι, i ∈ I ∧
          S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))}) =
      Set.sUnion {S | ∃ i : ι, i ∈ I ∧
        S = Set.insert Tick (Set.inter (Yf i) (Ev '' (Prod.snd (PXf i))))}

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_SKIP_Rep_parallel_right
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite →
      eqF
        ((Rep_parallel I PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' I)),
          (∅ : Set α)]| (proc.SKIP : proc p α))
        M M
        (Rep_parallel I PXf)

/-
(************************************
 |        SKIP and [||]:I PXf       |
 ************************************)
-/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

theorem cspF_SKIP_Rep_parallel_left
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite →
      eqF
        (((proc.SKIP : proc p α) |[
          (∅ : Set α),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))
        M M
        (Rep_parallel I PXf) := by
  intro hI
  exact
    cspF_trans_left_eq
      (cspF_Alpha_parallel_commut
        (P1 := (proc.SKIP : proc p α))
        (P2 := Rep_parallel I PXf)
        (X1 := (∅ : Set α))
        (X2 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (M := M))
      (cspF_SKIP_Rep_parallel_right (I := I) (PXf := PXf) (M := M) hI)

/- The Isabelle theorem bundle `cspF_SKIP_Rep_parallel` is represented by
   `cspF_SKIP_Rep_parallel_left` and `cspF_SKIP_Rep_parallel_right`. -/

/-
(************************************
 |          associativity           |
 ************************************)
-/

axiom cspF_Rep_parallel_ass_lm1
    {I : Set ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    Set.inter
      (Set.sUnion {S | ∃ i : ι, i ∈ I ∧
        S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))})
      (Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I))))) =
    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))}

axiom cspF_Rep_parallel_ass_lm2
    {I1 I2 : Set ι} {PXf : ι → proc p α × Set α}
    {Yf1 Yf2 : ι → Set (event α)} :
    I1 ∩ I2 = ∅ →
      Set.sUnion {S | ∃ i : ι, i ∈ I1 ∧
        S = Set.inter (Yf1 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∪
        Set.sUnion {S | ∃ i : ι, i ∈ I2 ∧
          S = Set.inter (Yf2 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} =
      Set.sUnion {S | (∃ i : ι, i ∈ I1 ∧
        S = Set.inter (Yf1 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))) ∨
        ∃ i : ι, i ∈ I2 ∧
          S = Set.inter (Yf2 i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))}

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_Rep_parallel_assoc
    {I1 I2 : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I1 ∩ I2 = ∅ → I1.Finite → I2.Finite →
      eqF
        (Rep_parallel (I1 ∪ I2) PXf) M M
        ((Rep_parallel I1 PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' I1)),
          Set.sUnion (Prod.snd '' (PXf '' I2))]| Rep_parallel I2 PXf)

/-
(************************************
 |             induct               |
 ************************************)
-/

/- (*------------------*
 |     csp law      |
 |   (derivable)    |
 *------------------*) -/

theorem cspF_Rep_parallel_induct
    {I : Set ι} {i : ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I.Finite → i ∉ I →
      eqF
        (Rep_parallel (Set.insert i I) PXf) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
  intro hI hiI
  have hDisj : ({i} : Set ι) ∩ I = ∅ := by
    ext x
    simp [hiI]
  have hAssoc :
      eqF
        (Rep_parallel (({i} : Set ι) ∪ I) PXf) M M
        ((Rep_parallel ({i} : Set ι) PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' ({i} : Set ι))),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
    exact cspF_Rep_parallel_assoc (I1 := ({i} : Set ι)) (I2 := I) (PXf := PXf) (M := M)
      hDisj (Set.toFinite {i}) hI
  have hAssoc' :
      eqF
        ((Rep_parallel ({i} : Set ι) PXf) |[
          Set.sUnion (Prod.snd '' (PXf '' ({i} : Set ι))),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]|
          (((proc.SKIP : proc p α) |[
            (∅ : Set α),
            Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))) := by
    simpa [Rep_parallel_one, Set.union_comm, Set.union_left_comm, Set.union_assoc]
      using
        (cspF_Alpha_parallel_assoc
          (P1 := Prod.fst (PXf i))
          (P2 := (proc.SKIP : proc p α))
          (P3 := Rep_parallel I PXf)
          (X1 := Prod.snd (PXf i))
          (X2 := (∅ : Set α))
          (X3 := Set.sUnion (Prod.snd '' (PXf '' I)))
          (M := M))
  have hCong :
      eqF
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]|
          (((proc.SKIP : proc p α) |[
            (∅ : Set α),
            Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))) M M
        ((Prod.fst (PXf i)) |[
          Prod.snd (PXf i),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf) := by
    exact
      cspF_Alpha_parallel_cong
        (X1 := Prod.snd (PXf i))
        (X2 := Prod.snd (PXf i))
        (Y1 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (Y2 := Set.sUnion (Prod.snd '' (PXf '' I)))
        (P1 := Prod.fst (PXf i))
        (Q1 := Prod.fst (PXf i))
        (P2 := ((proc.SKIP : proc p α) |[
          (∅ : Set α),
          Set.sUnion (Prod.snd '' (PXf '' I))]| Rep_parallel I PXf))
        (Q2 := Rep_parallel I PXf)
        (M1 := M)
        (M2 := M)
        rfl
        rfl
        cspF_reflex_eq_P
        (cspF_SKIP_Rep_parallel_left (I := I) (PXf := PXf) (M := M) hI)
  exact
    cspF_trans_left_eq
      (by simpa [Set.union_comm, Set.union_left_comm, Set.union_assoc] using hAssoc)
      (cspF_trans_left_eq hAssoc' hCong)

end
