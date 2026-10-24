           /- -------------------------------------------*
            |                DFP package                |
            |                    May 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DFP.DFP_Deadlock

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

/-
(*********************************************************
                    definitions
 *********************************************************)
-/

def triple_disjoint (VF : NetworkF ι α) : Prop :=
  ∀ i ∈ VF.1, ∀ j ∈ VF.1, ∀ k ∈ VF.1,
    i ≠ j → j ≠ k → k ≠ i →
      Prod.snd (VF.2 i) ∩ Prod.snd (VF.2 j) ∩ Prod.snd (VF.2 k) = ∅

theorem triple_disjoint_def (VF : NetworkF ι α) :
    triple_disjoint VF ↔
      ∀ i ∈ VF.1, ∀ j ∈ VF.1, ∀ k ∈ VF.1,
        i ≠ j → j ≠ k → k ≠ i →
          Prod.snd (VF.2 i) ∩ Prod.snd (VF.2 j) ∩ Prod.snd (VF.2 k) = ∅ :=
  Iff.rfl

def VocabularyOf (VF : NetworkF ι α) : Set α :=
  Set.sUnion {X | ∃ i ∈ VF.1, ∃ j ∈ VF.1, i ≠ j ∧
    X = Prod.snd (VF.2 i) ∩ Prod.snd (VF.2 j)}
    /- internal communication -/

theorem VocabularyOf_def (VF : NetworkF ι α) :
    VocabularyOf VF =
      Set.sUnion {X | ∃ i ∈ VF.1, ∃ j ∈ VF.1, i ≠ j ∧
        X = Prod.snd (VF.2 i) ∩ Prod.snd (VF.2 j)} :=
  rfl

def BusyNetworkP [HasPNfun p α] [HasFPmode] (V : Network ι p α) : Prop :=
  ∀ i ∈ V.1, DeadlockFreeNetwork ({i}, V.2)

theorem BusyNetworkP_def [HasPNfun p α] [HasFPmode] (V : Network ι p α) :
    BusyNetworkP V ↔ ∀ i ∈ V.1, DeadlockFreeNetwork ({i}, V.2) :=
  Iff.rfl

def BusyNetwork (VF : NetworkF ι α) : Prop :=
  ∀ i ∈ VF.1, ∀ sigma, ¬ isDeadlockStateOf sigma ({i}, VF.2)

theorem BusyNetwork_def (VF : NetworkF ι α) :
    BusyNetwork VF ↔ ∀ i ∈ VF.1, ∀ sigma, ¬ isDeadlockStateOf sigma ({i}, VF.2) :=
  Iff.rfl

def isRequestOf (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) : Prop :=
  isStateOf sigma VF ∧
    i ≠ j ∧ i ∈ VF.1 ∧ j ∈ VF.1 ∧
      ((Ev '' Prod.snd (VF.2 i)) \ sigma.2 i) ∩ (Ev '' Prod.snd (VF.2 j)) ≠ ∅

theorem isRequestOf_def (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) :
    isRequestOf VF i sigma j ↔
      isStateOf sigma VF ∧
        i ≠ j ∧ i ∈ VF.1 ∧ j ∈ VF.1 ∧
          ((Ev '' Prod.snd (VF.2 i)) \ sigma.2 i) ∩ (Ev '' Prod.snd (VF.2 j)) ≠ ∅ :=
  Iff.rfl

def isStrongRequestOf (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) : Prop :=
  isStateOf sigma VF ∧
    i ≠ j ∧ i ∈ VF.1 ∧ j ∈ VF.1 ∧
      (Ev '' Prod.snd (VF.2 i)) \ sigma.2 i ≠ ∅ ∧
      (Ev '' Prod.snd (VF.2 i)) \ sigma.2 i ⊆ Ev '' Prod.snd (VF.2 j)

theorem isStrongRequestOf_def (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) :
    isStrongRequestOf VF i sigma j ↔
      isStateOf sigma VF ∧
        i ≠ j ∧ i ∈ VF.1 ∧ j ∈ VF.1 ∧
          (Ev '' Prod.snd (VF.2 i)) \ sigma.2 i ≠ ∅ ∧
          (Ev '' Prod.snd (VF.2 i)) \ sigma.2 i ⊆ Ev '' Prod.snd (VF.2 j) :=
  Iff.rfl

def isUngrantedRequestOf (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) : Prop :=
  isRequestOf VF i sigma j ∧
    Ev '' Prod.snd (VF.2 i) ∩ Ev '' Prod.snd (VF.2 j) ⊆ sigma.2 i ∪ sigma.2 j

theorem isUngrantedRequestOf_def (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) :
    isUngrantedRequestOf VF i sigma j ↔
      isRequestOf VF i sigma j ∧
        Ev '' Prod.snd (VF.2 i) ∩ Ev '' Prod.snd (VF.2 j) ⊆ sigma.2 i ∪ sigma.2 j :=
  Iff.rfl

def isUngrantedStrongRequestOf
    (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) : Prop :=
  isStrongRequestOf VF i sigma j ∧
    Ev '' Prod.snd (VF.2 i) ∩ Ev '' Prod.snd (VF.2 j) ⊆ sigma.2 i ∪ sigma.2 j

theorem isUngrantedStrongRequestOf_def
    (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (j : ι) :
    isUngrantedStrongRequestOf VF i sigma j ↔
      isStrongRequestOf VF i sigma j ∧
        Ev '' Prod.snd (VF.2 i) ∩ Ev '' Prod.snd (VF.2 j) ⊆ sigma.2 i ∪ sigma.2 j :=
  Iff.rfl

def isUngrantedRequestOfwrt
    (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (Lambda : Set α) (j : ι) : Prop :=
  isUngrantedRequestOf VF i sigma j ∧
    (((Ev '' Prod.snd (VF.2 i)) \ sigma.2 i) ∪
      ((Ev '' Prod.snd (VF.2 j)) \ sigma.2 j)) ⊆ Ev '' Lambda

theorem isUngrantedRequestOfwrt_def
    (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) (Lambda : Set α) (j : ι) :
    isUngrantedRequestOfwrt VF i sigma Lambda j ↔
      isUngrantedRequestOf VF i sigma j ∧
        (((Ev '' Prod.snd (VF.2 i)) \ sigma.2 i) ∪
          ((Ev '' Prod.snd (VF.2 j)) \ sigma.2 j)) ⊆ Ev '' Lambda :=
  Iff.rfl

/- (*** Block ***) -/

def isBlockedIn (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) : Prop :=
  triple_disjoint VF ∧
    (∃ j, isRequestOf VF i sigma j) ∧
      ∀ j, isRequestOf VF i sigma j →
        isUngrantedRequestOfwrt VF i sigma (VocabularyOf VF) j

theorem isBlockedIn_def (VF : NetworkF ι α) (i : ι) (sigma : net_state ι α) :
    isBlockedIn VF i sigma ↔
      triple_disjoint VF ∧
        (∃ j, isRequestOf VF i sigma j) ∧
          ∀ j, isRequestOf VF i sigma j →
            isUngrantedRequestOfwrt VF i sigma (VocabularyOf VF) j :=
  Iff.rfl

/-
(*********************************************************
                  BusyNetwork lemmas
 *********************************************************)
-/

private theorem ALP_singleton (FXf : ι → (β × Set α)) (i : ι) :
    ALP (({i} : Set ι), FXf) = Prod.snd (FXf i) := by
  ext a
  constructor
  · rintro ⟨j, hj, ha⟩
    have : j = i := by simpa using hj
    simpa [this] using ha
  · intro ha
    exact ⟨i, by simp, ha⟩

private theorem isDeadlockStateOf_singleton_iff
    {FXf : ι → (Set (failure α) × Set α)} {t : traceType α} {Yf : ι → Set (event α)} {i : ι} :
    isDeadlockStateOf (t, Yf) (({i} : Set ι), FXf) ↔
      isStateOf (t, Yf) (({i} : Set ι), FXf) ∧ Yf i = Ev '' Prod.snd (FXf i) := by
  rw [isDeadlockStateOf_def]
  simp [ALP_singleton]

theorem BusyNetwork_BusyNetworkP [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hF : isFailureOf (I, FXf) (I, PXf)) :
    BusyNetwork (I, FXf) ↔ BusyNetworkP (I, PXf) := by
  let _ := hI
  let _ := hFin
  constructor
  · intro hBusy i hi
    have hFi : isFailureOf (({i} : Set ι), FXf) (({i} : Set ι), PXf) := by
      exact isFailureOf_subset_index hF (by
        intro j hj
        have : j = i := by simpa using hj
        simpa [this] using hi)
    have hDead :
        ∀ sigma, ¬ isDeadlockStateOf sigma (({i} : Set ι), FXf) := by
      intro sigma hSigma
      exact hBusy i hi sigma hSigma
    exact (DeadlockFree_notDeadlockState
      (I := ({i} : Set ι)) (FXf := FXf) (PXf := PXf) (by simp) (by simp) hFi).2 hDead
  · intro hBusyP i hi sigma hSigma
    have hFi : isFailureOf (({i} : Set ι), FXf) (({i} : Set ι), PXf) := by
      exact isFailureOf_subset_index hF (by
        intro j hj
        have : j = i := by simpa using hj
        simpa [this] using hi)
    have hNoDead :=
      (DeadlockFree_notDeadlockState
        (I := ({i} : Set ι)) (FXf := FXf) (PXf := PXf) (by simp) (by simp) hFi).1
        (hBusyP i hi)
    exact hNoDead sigma hSigma

/- -----------------------------------*
 |     How to check BusyNetworkF     |
 *----------------------------------- -/

theorem check_BusyNetwork
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    (hAll : ∀ i ∈ I, ∀ s Y, (s, Y) ∈ Prod.fst (FXf i) → Y ≠ Ev '' Prod.snd (FXf i)) :
    BusyNetwork (I, FXf) := by
  intro i hi sigma hDead
  rcases sigma with ⟨s, Yf⟩
  have hState : isStateOf (s, Yf) (({i} : Set ι), FXf) :=
    (isDeadlockStateOf_singleton_iff.mp hDead).1
  have hMem : (s rest-tr Prod.snd (FXf i), Yf i) ∈ Prod.fst (FXf i) := by
    exact (hState.2 i (by simp)).1
  have hNe := hAll i hi (s rest-tr Prod.snd (FXf i)) (Yf i) hMem
  have hEq : Yf i = Ev '' Prod.snd (FXf i) := (isDeadlockStateOf_singleton_iff.mp hDead).2
  exact hNe hEq

/-
(*********************************************************
                     in index I
 *********************************************************)
-/

theorem in_index_I1 {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {sigma : net_state ι α} :
    isRequestOf (I, FXf) i sigma j → i ∈ I ∧ j ∈ I ∧ i ≠ j := by
  intro h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.1⟩

theorem in_index_I2 {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {sigma : net_state ι α} :
    isStrongRequestOf (I, FXf) i sigma j → i ∈ I ∧ j ∈ I ∧ i ≠ j := by
  intro h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.1⟩

theorem in_index_I3 {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {sigma : net_state ι α} :
    isUngrantedRequestOf (I, FXf) i sigma j → i ∈ I ∧ j ∈ I ∧ i ≠ j := by
  intro h
  exact in_index_I1 h.1

theorem in_index_I4 {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {sigma : net_state ι α} :
    isUngrantedStrongRequestOf (I, FXf) i sigma j → i ∈ I ∧ j ∈ I ∧ i ≠ j := by
  intro h
  exact in_index_I2 h.1

theorem in_index_I5 {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {sigma : net_state ι α} {Lambda : Set α} :
    isUngrantedRequestOfwrt (I, FXf) i sigma Lambda j → i ∈ I ∧ j ∈ I ∧ i ≠ j := by
  intro h
  exact in_index_I3 h.1

/-
(*********************************************************
                       note (P.7)
 *********************************************************)
-/

theorem isUngrantedRequestOfwrt_note1
    {VF : NetworkF ι α} {i j : ι} {sigma : net_state ι α} {Lambda1 Lambda2 : Set α}
    (hLambda : Lambda1 ⊆ Lambda2)
    (hReq : isUngrantedRequestOfwrt VF i sigma Lambda1 j) :
    isUngrantedRequestOfwrt VF i sigma Lambda2 j := by
  refine ⟨hReq.1, ?_⟩
  intro e he
  rcases hReq.2 he with ⟨a, ha, rfl⟩
  exact ⟨a, hLambda ha, rfl⟩

theorem isUngrantedRequestOfwrt_note2
    {VF : NetworkF ι α} {i j : ι} {sigma : net_state ι α} {Lambda : Set α}
    (hLambda : Prod.snd (VF.2 i) ∪ Prod.snd (VF.2 j) ⊆ Lambda) :
    isUngrantedRequestOfwrt VF i sigma Lambda j ↔
      isUngrantedRequestOf VF i sigma j := by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_⟩
    intro e he
    have he' :
        e ∈ (Ev '' Prod.snd (VF.2 i) \ sigma.2 i) ∨
          e ∈ (Ev '' Prod.snd (VF.2 j) \ sigma.2 j) := by
      simpa [Set.mem_union] using he
    rcases he' with hi | hj
    · rcases hi with ⟨heAi, _⟩
      rcases heAi with ⟨a, ha, rfl⟩
      exact ⟨a, hLambda (Or.inl ha), rfl⟩
    · rcases hj with ⟨heAj, _⟩
      rcases heAj with ⟨a, ha, rfl⟩
      exact ⟨a, hLambda (Or.inr ha), rfl⟩

/-
(*********************************************************
                     sub request
 *********************************************************)
-/

theorem isRequestOf_subsetI
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {t : traceType α} {Yf : ι → Set (event α)} {X : Set α}
    (hReq : isRequestOf (I, FXf) i (t, Yf) j)
    (hJ : J ⊆ I)
    (hi : i ∈ J)
    (hj : j ∈ J)
    (hX : X = Set.sUnion {A | ∃ i ∈ J, A = Prod.snd (FXf i)}) :
    isRequestOf (J, FXf) i (t rest-tr X, Yf) j := by
  refine ⟨isStateOf_subsetI hReq.1 hJ hX, hReq.2.1, hi, hj, ?_⟩
  simpa using hReq.2.2.2.2

theorem isStrongRequestOf_subsetI
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {t : traceType α} {Yf : ι → Set (event α)} {X : Set α}
    (hReq : isStrongRequestOf (I, FXf) i (t, Yf) j)
    (hJ : J ⊆ I)
    (hi : i ∈ J)
    (hj : j ∈ J)
    (hX : X = Set.sUnion {A | ∃ i ∈ J, A = Prod.snd (FXf i)}) :
    isStrongRequestOf (J, FXf) i (t rest-tr X, Yf) j := by
  refine ⟨isStateOf_subsetI hReq.1 hJ hX, hReq.2.1, hi, hj, hReq.2.2.2.2.1, hReq.2.2.2.2.2⟩

theorem isUngrantedRequestOf_subsetI
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {t : traceType α} {Yf : ι → Set (event α)} {X : Set α}
    (hReq : isUngrantedRequestOf (I, FXf) i (t, Yf) j)
    (hJ : J ⊆ I)
    (hi : i ∈ J)
    (hj : j ∈ J)
    (hX : X = Set.sUnion {A | ∃ i ∈ J, A = Prod.snd (FXf i)}) :
    isUngrantedRequestOf (J, FXf) i (t rest-tr X, Yf) j := by
  exact ⟨isRequestOf_subsetI hReq.1 hJ hi hj hX, hReq.2⟩

theorem isUngrantedStrongRequestOf_subsetI
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {t : traceType α} {Yf : ι → Set (event α)} {X : Set α}
    (hReq : isUngrantedStrongRequestOf (I, FXf) i (t, Yf) j)
    (hJ : J ⊆ I)
    (hi : i ∈ J)
    (hj : j ∈ J)
    (hX : X = Set.sUnion {A | ∃ i ∈ J, A = Prod.snd (FXf i)}) :
    isUngrantedStrongRequestOf (J, FXf) i (t rest-tr X, Yf) j := by
  exact ⟨isStrongRequestOf_subsetI hReq.1 hJ hi hj hX, hReq.2⟩

theorem isUngrantedRequestOfwrt_subsetI
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {i j : ι} {t : traceType α} {Yf : ι → Set (event α)} {Lambda1 Lambda2 X : Set α}
    (hReq : isUngrantedRequestOfwrt (I, FXf) i (t, Yf) Lambda1 j)
    (hJ : J ⊆ I)
    (hi : i ∈ J)
    (hj : j ∈ J)
    (hLambda : Lambda1 ⊆ Lambda2)
    (hX : X = Set.sUnion {A | ∃ i ∈ J, A = Prod.snd (FXf i)}) :
    isUngrantedRequestOfwrt (J, FXf) i (t rest-tr X, Yf) Lambda2 j := by
  exact isUngrantedRequestOfwrt_note1 hLambda
    ⟨isUngrantedRequestOf_subsetI hReq.1 hJ hi hj hX, hReq.2⟩

/-
(*********************************************************
                      blocked
 *********************************************************)
-/

private theorem mem_VocabularyOf_iff {VF : NetworkF ι α} {a : α} :
    a ∈ VocabularyOf VF ↔
      ∃ i ∈ VF.1, ∃ j ∈ VF.1, i ≠ j ∧
        a ∈ Prod.snd (VF.2 i) ∧ a ∈ Prod.snd (VF.2 j) := by
  constructor
  · intro ha
    rcases Set.mem_sUnion.mp ha with ⟨X, hX, haX⟩
    rcases hX with ⟨i, hi, j, hj, hij, rfl⟩
    exact ⟨i, hi, j, hj, hij, haX.1, haX.2⟩
  · rintro ⟨i, hi, j, hj, hij, hai, haj⟩
    exact Set.mem_sUnion.mpr
      ⟨Prod.snd (VF.2 i) ∩ Prod.snd (VF.2 j), ⟨i, hi, j, hj, hij, rfl⟩, ⟨hai, haj⟩⟩

private theorem triple_disjoint_no_common
    {VF : NetworkF ι α} (hTD : triple_disjoint VF)
    {i j k : ι} (hi : i ∈ VF.1) (hj : j ∈ VF.1) (hk : k ∈ VF.1)
    (hij : i ≠ j) (hjk : j ≠ k) (hki : k ≠ i)
    {a : α}
    (hai : a ∈ Prod.snd (VF.2 i))
    (haj : a ∈ Prod.snd (VF.2 j))
    (hak : a ∈ Prod.snd (VF.2 k)) :
    False := by
  have hEmpty := hTD i hi j hj k hk hij hjk hki
  have : a ∈ Prod.snd (VF.2 i) ∩ Prod.snd (VF.2 j) ∩ Prod.snd (VF.2 k) := by
    exact ⟨⟨hai, haj⟩, hak⟩
  simp [hEmpty] at this

private theorem mem_union_of_deadlock
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {e : event α}
    (hDead : isDeadlockStateOf (t, Yf) (I, FXf))
    (he : e ∈ Ev '' ALP (I, FXf)) :
    e ∈ Set.sUnion (Yf '' I) := by
  rw [hDead.2]
  exact he

private theorem mem_alpha_of_state
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {i : ι} {e : event α}
    (hState : isStateOf (t, Yf) (I, FXf))
    (hi : i ∈ I)
    (he : e ∈ Yf i) :
    e ∈ Ev '' Prod.snd (FXf i) :=
  (hState.2 i hi).2 he

/- ---------------------------------*
 | lemma 1 [Roscoe_Dathi_1987 P.7] |
 *--------------------------------- -/

private theorem mem_Yf_of_mem_ALP_of_deadlock
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {e : event α}
    (hDead : isDeadlockStateOf (t, Yf) (I, FXf))
    (he : e ∈ Ev '' ALP (I, FXf)) :
    ∃ k ∈ I, e ∈ Yf k := by
  have hmem : e ∈ Set.sUnion (Yf '' I) := mem_union_of_deadlock hDead he
  rcases Set.mem_sUnion.mp hmem with ⟨S, ⟨k, hk, rfl⟩, heS⟩
  exact ⟨k, hk, heS⟩

private theorem mem_alpha_of_state_inj
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {k : ι} {a : α}
    (hState : isStateOf (t, Yf) (I, FXf))
    (hk : k ∈ I)
    (he : Ev a ∈ Yf k) :
    a ∈ Prod.snd (FXf k) := by
  rcases (hState.2 k hk).2 he with ⟨b, hb, hEq⟩
  obtain rfl : b = a := Ev.inj hEq
  exact hb

/- (*** only if ***) -/

theorem Lemma1_Roscoe_Dathi_1987_only_if
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)}
    (hTD : triple_disjoint (I, FXf))
    (hBusy : BusyNetwork (I, FXf))
    (hDead : isDeadlockStateOf (t, Yf) (I, FXf)) :
    ∀ i ∈ I, isBlockedIn (I, FXf) i (t, Yf) := by
  intro i hi
  have hState : isStateOf (t, Yf) (I, FXf) := hDead.1
  refine ⟨hTD, ?_, ?_⟩
  · /- (* 1 *) : busy --> i is deadlock-free --> EX j -/
    have hStateI : isStateOf (t rest-tr Prod.snd (FXf i), Yf) (({i} : Set ι), FXf) :=
      isStateOf_each_element hState hi
    have hNotDead := hBusy i hi (t rest-tr Prod.snd (FXf i), Yf)
    have hNe : Yf i ≠ Ev '' Prod.snd (FXf i) := by
      intro hEq
      exact hNotDead (isDeadlockStateOf_singleton_iff.mpr ⟨hStateI, hEq⟩)
    have hSub : Yf i ⊆ Ev '' Prod.snd (FXf i) := (hState.2 i hi).2
    have hExists : ∃ e, e ∈ Ev '' Prod.snd (FXf i) ∧ e ∉ Yf i := by
      by_contra hAll
      push_neg at hAll
      exact hNe (Set.Subset.antisymm hSub (fun e he => hAll e he))
    rcases hExists with ⟨e, heA, heY⟩
    rcases heA with ⟨a, ha, rfl⟩
    obtain ⟨j, hj, hEvYj⟩ :=
      mem_Yf_of_mem_ALP_of_deadlock hDead ⟨a, ⟨i, hi, ha⟩, rfl⟩
    have hij : i ≠ j := by
      intro h
      exact heY (h ▸ hEvYj)
    refine ⟨j, hState, hij, hi, hj, ?_⟩
    exact Set.nonempty_iff_ne_empty.mp
      ⟨Ev a, ⟨⟨a, ha, rfl⟩, heY⟩, (hState.2 j hj).2 hEvYj⟩
  · /- (* 2 *) : every request of i is ungranted wrt the vocabulary -/
    intro j hReq
    have hij : i ≠ j := hReq.2.1
    have hjI : j ∈ I := hReq.2.2.2.1
    refine ⟨⟨hReq, ?_⟩, ?_⟩
    · /- (* 2-1 *) -/
      rintro e ⟨⟨a, hai, rfl⟩, hEvj⟩
      have haj : a ∈ Prod.snd (FXf j) := by
        rcases hEvj with ⟨b, hb, hEq⟩
        obtain rfl : b = a := Ev.inj hEq
        exact hb
      obtain ⟨k, hk, hEvYk⟩ :=
        mem_Yf_of_mem_ALP_of_deadlock hDead ⟨a, ⟨i, hi, hai⟩, rfl⟩
      by_cases hki : k = i
      · subst hki
        exact Or.inl hEvYk
      · by_cases hkj : k = j
        · subst hkj
          exact Or.inr hEvYk
        · exact absurd (mem_alpha_of_state_inj hState hk hEvYk)
            (fun hak => triple_disjoint_no_common hTD hi hjI hk
              hij (fun h => hkj h.symm) hki hai haj hak)
    · /- (* 2-2 *) -/
      rintro e (⟨⟨a, hai, rfl⟩, heY⟩ | ⟨⟨a, haj, rfl⟩, heY⟩)
      · obtain ⟨k, hk, hEvYk⟩ :=
          mem_Yf_of_mem_ALP_of_deadlock hDead ⟨a, ⟨i, hi, hai⟩, rfl⟩
        have hki : k ≠ i := by
          intro h
          exact heY (h ▸ hEvYk)
        have hak : a ∈ Prod.snd (FXf k) := mem_alpha_of_state_inj hState hk hEvYk
        exact ⟨a, mem_VocabularyOf_iff.mpr
          ⟨i, hi, k, hk, fun h => hki h.symm, hai, hak⟩, rfl⟩
      · obtain ⟨k, hk, hEvYk⟩ :=
          mem_Yf_of_mem_ALP_of_deadlock hDead ⟨a, ⟨j, hjI, haj⟩, rfl⟩
        have hkj : k ≠ j := by
          intro h
          exact heY (h ▸ hEvYk)
        have hak : a ∈ Prod.snd (FXf k) := mem_alpha_of_state_inj hState hk hEvYk
        exact ⟨a, mem_VocabularyOf_iff.mpr
          ⟨j, hjI, k, hk, fun h => hkj h.symm, haj, hak⟩, rfl⟩

/- (*** if ***) -/

theorem Lemma1_Roscoe_Dathi_1987_if
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)}
    (hTD : triple_disjoint (I, FXf))
    (hBusy : BusyNetwork (I, FXf))
    (hState : isStateOf (t, Yf) (I, FXf))
    (hBlocked : ∀ i ∈ I, isBlockedIn (I, FXf) i (t, Yf)) :
    isDeadlockStateOf (t, Yf) (I, FXf) := by
  let _ := hBusy
  refine ⟨hState, ?_⟩
  apply Set.Subset.antisymm
  · /- (* <= *) -/
    rintro e ⟨S, ⟨k, hk, rfl⟩, heS⟩
    rcases (hState.2 k hk).2 heS with ⟨a, ha, rfl⟩
    exact ⟨a, ⟨k, hk, ha⟩, rfl⟩
  · /- (* => *) -/
    rintro e ⟨a, ⟨i, hi, hai⟩, rfl⟩
    by_cases hYi : Ev a ∈ Yf i
    · exact Set.mem_sUnion.mpr ⟨Yf i, ⟨i, hi, rfl⟩, hYi⟩
    · obtain ⟨-, ⟨j0, hReq0⟩, hAll⟩ := hBlocked i hi
      have hVocab : Ev a ∈ Ev '' VocabularyOf (I, FXf) :=
        (hAll j0 hReq0).2 (Or.inl ⟨⟨a, hai, rfl⟩, hYi⟩)
      rcases hVocab with ⟨b, hb, hEq⟩
      rw [Ev.inj hEq] at hb
      rcases mem_VocabularyOf_iff.mp hb with ⟨ia, hia, jb, hjb, hne, haia, hajb⟩
      by_cases h1 : ia = i
      · subst h1
        have hReq : isRequestOf (I, FXf) ia (t, Yf) jb :=
          ⟨hState, hne, hia, hjb,
            Set.nonempty_iff_ne_empty.mp
              ⟨Ev a, ⟨⟨a, hai, rfl⟩, hYi⟩, ⟨a, hajb, rfl⟩⟩⟩
        have hmem : Ev a ∈ Yf ia ∪ Yf jb :=
          (hAll jb hReq).1.2 ⟨⟨a, hai, rfl⟩, ⟨a, hajb, rfl⟩⟩
        rcases hmem with h | h
        · exact absurd h hYi
        · exact Set.mem_sUnion.mpr ⟨Yf jb, ⟨jb, hjb, rfl⟩, h⟩
      · by_cases h2 : jb = i
        · subst h2
          have hReq : isRequestOf (I, FXf) jb (t, Yf) ia :=
            ⟨hState, fun h => hne h.symm, hjb, hia,
              Set.nonempty_iff_ne_empty.mp
                ⟨Ev a, ⟨⟨a, hai, rfl⟩, hYi⟩, ⟨a, haia, rfl⟩⟩⟩
          have hmem : Ev a ∈ Yf jb ∪ Yf ia :=
            (hAll ia hReq).1.2 ⟨⟨a, hai, rfl⟩, ⟨a, haia, rfl⟩⟩
          rcases hmem with h | h
          · exact absurd h hYi
          · exact Set.mem_sUnion.mpr ⟨Yf ia, ⟨ia, hia, rfl⟩, h⟩
        · exact absurd hajb
            (fun hak => triple_disjoint_no_common hTD hi hia hjb
              (fun h => h1 h.symm) hne h2 hai haia hak)

theorem Lemma1_Roscoe_Dathi_1987
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)}
    (hTD : triple_disjoint (I, FXf))
    (hBusy : BusyNetwork (I, FXf))
    (hState : isStateOf (t, Yf) (I, FXf)) :
    isDeadlockStateOf (t, Yf) (I, FXf) ↔
      ∀ i ∈ I, isBlockedIn (I, FXf) i (t, Yf) := by
  let _ := hState
  constructor
  · intro hDead
    exact Lemma1_Roscoe_Dathi_1987_only_if hTD hBusy hDead
  · intro hBlocked
    exact Lemma1_Roscoe_Dathi_1987_if hTD hBusy hState hBlocked

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
