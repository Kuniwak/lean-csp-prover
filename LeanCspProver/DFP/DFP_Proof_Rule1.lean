           /- -------------------------------------------*
            |                DFP package                |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DFP.DFP_Block

open Classical
open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `UnionT` and `InterT`.             -/
/-                  `Union (B \` A) = (UN x:A. B x)`                   -/
/-                  `Inter (B \` A) = (INT x:A. B x)`                  -/
/-
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
-/
/- no simp rules in Isabelle 2017
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
-/

/- Lean note:
   Isabelle's local simp-set deletion for these rules has no direct analogue
   here, so the comments are preserved without an executable command. -/

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `(notick | t = []t)`               -/
/-                                                                     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`                 -/

/- Lean note:
   Isabelle's local simp-set deletion for `disj_not1` has no direct
   counterpart in Lean. -/

/-
(*****************************************************************

         1.
         2.
         3.
         4.

 *****************************************************************)
-/

private theorem sUnion_pair_eq
    {FXf : ι → (β × Set α)} (i j : ι) :
    Set.sUnion {A | ∃ k ∈ ({i, j} : Set ι), A = Prod.snd (FXf k)} =
      Prod.snd (FXf i) ∪ Prod.snd (FXf j) := by
  ext a
  constructor
  · intro ha
    rcases Set.mem_sUnion.mp ha with ⟨A, hA, haA⟩
    rcases hA with ⟨k, hk, rfl⟩
    simp at hk
    rcases hk with rfl | rfl
    · exact Or.inl haA
    · exact Or.inr haA
  · intro ha
    rcases ha with ha | ha
    · exact Set.mem_sUnion.mpr ⟨Prod.snd (FXf i), ⟨i, by simp, rfl⟩, ha⟩
    · exact Set.mem_sUnion.mpr ⟨Prod.snd (FXf j), ⟨j, by simp, rfl⟩, ha⟩

/- --------------------------------------------------*
 |        Theorem 1 [Roscoe_Dathi_1987 P.8]         |
 *-------------------------------------------------- -/

theorem Theorem1_Roscoe_Dathi_1987 [HasPNfun p α] [HasFPmode] [Preorder π]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hTD : triple_disjoint (I, FXf))
    (hBusy : BusyNetwork (I, FXf))
    (hRank :
      ∃ f : ι → failure α → π,
        ∀ t Yf, isStateOf (t, Yf) (I, FXf) →
          ∀ i j,
            isUngrantedRequestOfwrt (I, FXf) i (t, Yf) (VocabularyOf (I, FXf)) j →
              ((f j (t rest-tr Prod.snd (FXf j), Yf j)) <
                (f i (t rest-tr Prod.snd (FXf i), Yf i)))) :
    DeadlockFreeNetwork (I, PXf) := by
  rcases hRank with ⟨f, hf⟩
  refine (DeadlockFree_notDeadlockState hI hFin hF).2 ?_
  intro sigma hDead
  rcases sigma with ⟨t, Yf⟩
  have hState : isStateOf (t, Yf) (I, FXf) := hDead.1
  have hBlocked : ∀ i ∈ I, isBlockedIn (I, FXf) i (t, Yf) :=
    (Lemma1_Roscoe_Dathi_1987 hTD hBusy hState).1 hDead
  rcases nonempty_finite_set_exists_min_fun
      (I := I) (f := fun i => f i (t rest-tr Prod.snd (FXf i), Yf i)) hFin hI with
    ⟨j, hjI, hjMin⟩
  have hBlockJ := hBlocked j hjI
  rcases hBlockJ.2.1 with ⟨k, hReq⟩
  have hkI : k ∈ I := (in_index_I1 hReq).2.1
  have hReq' : isUngrantedRequestOfwrt (I, FXf) j (t, Yf) (VocabularyOf (I, FXf)) k :=
    hBlockJ.2.2 k hReq
  exact hjMin k hkI (hf t Yf hState j k hReq')

/- --------------------------------------------------*
 |         Lemma 2 [Roscoe_Dathi_1987 P.9]          |
 *-------------------------------------------------- -/

lemma Lemma2_Roscoe_Dathi_1987 [Preorder π]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    (_hI : I ≠ ∅)
    (_hFin : I.Finite)
    (_hTD : triple_disjoint (I, FXf))
    (_hBusy : BusyNetwork (I, FXf))
    (hRank :
      ∃ f : ι → failure α → π,
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ∀ t Yf,
            isStateOf (t, Yf) (({i, j} : Set ι), FXf) →
              isUngrantedRequestOfwrt (({i, j} : Set ι), FXf) i (t, Yf)
                (VocabularyOf (I, FXf)) j →
                ((f j (t rest-tr Prod.snd (FXf j), Yf j)) <
                  (f i (t rest-tr Prod.snd (FXf i), Yf i)))) :
    ∃ f : ι → failure α → π,
      ∀ t Yf, isStateOf (t, Yf) (I, FXf) →
        ∀ i j,
          isUngrantedRequestOfwrt (I, FXf) i (t, Yf) (VocabularyOf (I, FXf)) j →
            ((f j (t rest-tr Prod.snd (FXf j), Yf j)) <
              (f i (t rest-tr Prod.snd (FXf i), Yf i))) := by
  rcases hRank with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro t Yf hState i j hReq
  have hiI : i ∈ I := (in_index_I5 hReq).1
  have hjI : j ∈ I := (in_index_I5 hReq).2.1
  have hij : i ≠ j := (in_index_I5 hReq).2.2
  have hPairSubset : ({i, j} : Set ι) ⊆ I := by
    intro k hk
    simp at hk
    rcases hk with rfl | rfl
    · exact hiI
    · exact hjI
  let X : Set α := Prod.snd (FXf i) ∪ Prod.snd (FXf j)
  have hX : X = Set.sUnion {A | ∃ k ∈ ({i, j} : Set ι), A = Prod.snd (FXf k)} := by
    dsimp [X]
    exact (sUnion_pair_eq (FXf := FXf) i j).symm
  have hStateSub : isStateOf (t rest-tr X, Yf) (({i, j} : Set ι), FXf) :=
    isStateOf_subsetI hState hPairSubset hX
  have hReqSub :
      isUngrantedRequestOfwrt (({i, j} : Set ι), FXf) i (t rest-tr X, Yf)
        (VocabularyOf (I, FXf)) j :=
    isUngrantedRequestOfwrt_subsetI hReq hPairSubset (by simp) (by simp) Set.Subset.rfl hX
  have hlt :=
    hf i hiI j hjI hij (t rest-tr X) Yf hStateSub hReqSub
  have hiSubset : Prod.snd (FXf i) ⊆ X := by
    intro a ha
    exact Or.inl ha
  have hjSubset : Prod.snd (FXf j) ⊆ X := by
    intro a ha
    exact Or.inr ha
  have hRestI :=
    (rest_tr_of_rest_tr_subset (u := t) (X := Prod.snd (FXf i)) (Y := X) hiSubset).2
  have hRestJ :=
    (rest_tr_of_rest_tr_subset (u := t) (X := Prod.snd (FXf j)) (Y := X) hjSubset).2
  simpa [X, hRestI, hRestJ] using hlt

/- --------------------------------------------------*
 |         Rule 1 [Roscoe_Dathi_1987 P.9]           |
 *-------------------------------------------------- -/

lemma Rule1_Roscoe_Dathi_1987 [HasPNfun p α] [HasFPmode] [Preorder π]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hTD : triple_disjoint (I, FXf))
    (hBusy : BusyNetwork (I, FXf))
    (hRank :
      ∃ f : ι → failure α → π,
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ∀ t Yf,
            isUngrantedRequestOfwrt (({i, j} : Set ι), FXf) i (t, Yf)
              (VocabularyOf (I, FXf)) j →
                ((f j (t rest-tr Prod.snd (FXf j), Yf j)) <
                  (f i (t rest-tr Prod.snd (FXf i), Yf i)))) :
    DeadlockFreeNetwork (I, PXf) := by
  refine Theorem1_Roscoe_Dathi_1987 (π := π) hF hI hFin hTD hBusy ?_
  refine Lemma2_Roscoe_Dathi_1987 (π := π) (I := I) (FXf := FXf) hI hFin hTD hBusy ?_
  rcases hRank with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  intro i hi j hj hij t Yf _hState hReq
  exact hf i hi j hj hij t Yf hReq

lemma Rule1_Roscoe_Dathi_1987_I [HasPNfun p α] [HasFPmode] [Preorder π]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {V : Network ι p α}
    (hF : isFailureOf (I, FXf) V)
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hTD : triple_disjoint (I, FXf))
    (hBusy : BusyNetwork (I, FXf))
    (hRank :
      ∃ f : ι → failure α → π,
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ∀ t Yf,
            isUngrantedRequestOfwrt (({i, j} : Set ι), FXf) i (t, Yf)
              (VocabularyOf (I, FXf)) j →
                ((f j (t rest-tr Prod.snd (FXf j), Yf j)) <
                  (f i (t rest-tr Prod.snd (FXf i), Yf i)))) :
    DeadlockFreeNetwork V := by
  rcases decompo_V V with ⟨Ia, PXf, rfl⟩
  dsimp [isFailureOf] at hF
  rcases hF with ⟨hIa, hSpec⟩
  subst hIa
  exact Rule1_Roscoe_Dathi_1987
    (hF := ⟨rfl, hSpec⟩)
    hI hFin hTD hBusy hRank

/- (*** looks test ***) -/

theorem Rule1_Roscoe_Dathi_1987_simp [HasPNfun p α] [HasFPmode] [Preorder π]
    {I : Set ι} {VF : NetworkF ι α} {V : Network ι p α}
    {F : ι → Set (failure α)} {P : ι → proc p α} {X : ι → Set α}
    (hVF : VF = (I, fun i => (F i, X i)))
    (hV : V = (I, fun i => (P i, X i)))
    (hF : isFailureOf VF V)
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hTD : triple_disjoint VF)
    (hBusy : BusyNetwork VF)
    (hRank :
      ∃ f : ι → failure α → π,
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ∀ t Y,
            isUngrantedRequestOfwrt (({i, j} : Set ι), fun k => (F k, X k)) i (t, Y)
              (VocabularyOf VF) j →
                ((f j (t rest-tr X j, Y j)) < (f i (t rest-tr X i, Y i)))) :
    DeadlockFreeNetwork V := by
  subst hVF
  subst hV
  exact Rule1_Roscoe_Dathi_1987_I
    (V := (I, fun i => (P i, X i)))
    hF hI hFin hTD hBusy hRank

/-(****************** to add it again ******************)

declare disj_not1   [simp]
(*
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
*)

(*
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
*)
-/

/- Lean note:
   Isabelle restored the deleted simp rules at the end of the theory. Lean has
   no corresponding local simp-set mutations to undo here. -/
