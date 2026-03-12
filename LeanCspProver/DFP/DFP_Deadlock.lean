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

import LeanCspProver.DFP.DFP_Network

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

def DeadlockFree [HasPNfun p α] [HasFPmode] (X : Set (event α)) (P : proc p α) : Prop :=
  ∀ s, Tick ∉ sett s → ¬ ((s, X) :f failures P MF)

theorem DeadlockFree_def [HasPNfun p α] [HasFPmode] (X : Set (event α)) (P : proc p α) :
    DeadlockFree X P ↔ ∀ s, Tick ∉ sett s → ¬ ((s, X) :f failures P MF) :=
  Iff.rfl

def DeadlockFreeNetwork [HasPNfun p α] [HasFPmode] (V : Network ι p α) : Prop :=
  DeadlockFree (Ev '' ALP V) (PAR V)

theorem DeadlockFreeNetwork_def [HasPNfun p α] [HasFPmode] (V : Network ι p α) :
    DeadlockFreeNetwork V ↔ DeadlockFree (Ev '' ALP V) (PAR V) :=
  Iff.rfl

/- (*** UNIV deadlockfree ***) -/

def isDeadlockFree [HasPNfun p α] [HasFPmode] (P : proc p α) : Prop :=
  DeadlockFree Set.univ P

theorem isDeadlockFree_def [HasPNfun p α] [HasFPmode] (P : proc p α) :
    isDeadlockFree P ↔ DeadlockFree Set.univ P :=
  Iff.rfl

def isDeadlockStateOf (sigma : net_state ι α) (VF : NetworkF ι α) : Prop :=
  isStateOf sigma VF ∧ Set.sUnion (sigma.2 '' VF.1) = Ev '' ALP VF

theorem isDeadlockStateOf_def (sigma : net_state ι α) (VF : NetworkF ι α) :
    isDeadlockStateOf sigma VF ↔
      isStateOf sigma VF ∧ Set.sUnion (sigma.2 '' VF.1) = Ev '' ALP VF :=
  Iff.rfl

/-
(*********************************************************
           isDeadlockStateOf subset alpha
 *********************************************************)
-/

theorem isDeadlockStateOf_subset_alpha1 [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {i : ι} {e : event α}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hD : isDeadlockStateOf (t, Yf) (I, FXf))
    (hi : i ∈ I)
    (he : e ∈ Yf i) :
    e ∈ Ev '' Prod.snd (PXf i) := by
  exact isStateOf_subset_alpha1 hF hD.1 hi he

theorem isDeadlockStateOf_subset_alpha2 [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {i : ι} {e : event α}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hD : isDeadlockStateOf (t, Yf) (I, FXf))
    (hi : i ∈ I)
    (he : e ∈ Yf i) :
    e ∈ Ev '' Prod.snd (FXf i) := by
  exact isStateOf_subset_alpha2 hF hD.1 hi he

/- The Isabelle theorem bundle `isDeadlockStateOf_subset_alpha` is represented
   by `isDeadlockStateOf_subset_alpha1` and
   `isDeadlockStateOf_subset_alpha2`. -/

/-
(*********************************************************
             Deadlock and Deadlock freedom
 *********************************************************)
-/

private theorem ALP_eq_sUnion {V : Set ι × (ι → (β × Set α))} :
    ALP V = Set.sUnion (Prod.snd '' (V.2 '' V.1)) := by
  ext a
  constructor
  · rintro ⟨i, hi, ha⟩
    exact Set.mem_sUnion.mpr ⟨Prod.snd (V.2 i), ⟨V.2 i, ⟨i, hi, rfl⟩, rfl⟩, ha⟩
  · intro ha
    rcases Set.mem_sUnion.mp ha with ⟨A, hA, haA⟩
    rcases hA with ⟨p, hp, hEqA⟩
    rcases hp with ⟨i, hi, hEqp⟩
    subst hEqA
    subst hEqp
    exact ⟨i, hi, haA⟩

private theorem ALP_eq_of_isFailureOf [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hF : isFailureOf (I, FXf) (I, PXf)) :
    ALP (I, FXf) = ALP (I, PXf) := by
  ext a
  constructor <;> intro ha
  · rcases ha with ⟨i, hi, ha⟩
    exact ⟨i, hi, by simpa [isFailureOf_same_alpha hF i hi] using ha⟩
  · rcases ha with ⟨i, hi, ha⟩
    exact ⟨i, hi, by simpa [isFailureOf_same_alpha hF i hi] using ha⟩

private theorem image_inter_insert_Ev (A : Set α) :
    Ev '' A ∩ Set.insert Tick (Ev '' A) = Ev '' A := by
  simpa using (Int_insert_eq (A := Ev '' A) (x := Tick))

private theorem subset_inter_insert_Ev_eq {X : Set α} {Y : Set (event α)}
    (hY : Y ⊆ Ev '' X) :
    Y ∩ Set.insert Tick (Ev '' X) = Y := by
  ext e
  constructor
  · intro h
    exact h.1
  · intro he
    exact ⟨he, Or.inr (hY he)⟩

private theorem family_set_eq_image {I : Set ι} {F : ι → Set β} :
    {S | ∃ i : ι, i ∈ I ∧ S = F i} = F '' I := by
  ext S
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

private theorem image_eq_of_pointwise {I : Set ι} {F G : ι → β}
    (hFG : ∀ i ∈ I, F i = G i) :
    F '' I = G '' I := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by simp [hFG i hi]⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, by simp [hFG i hi]⟩

/- (*** Existency ***) -/

theorem DeadlockState_notDeadlockFree_only_if_lmEX_lm
    {s : traceType α} {F : Set (failure α)} {A Y : Set (event α)}
    (hEx : ∃ Z, (s, Z) ∈ F ∧ Y ⊆ Z ∧ Z ⊆ A) :
    (s, Classical.choose hEx) ∈ F ∧
      Y ⊆ Classical.choose hEx ∧
      Classical.choose hEx ⊆ A := by
  exact Classical.choose_spec hEx

theorem DeadlockState_notDeadlockFree_only_if_lmEX [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {s : traceType α} {Yf : ι → Set (event α)}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hAll : ∀ i ∈ I, (s rest-tr Prod.snd (PXf i), Yf i) :f failures (Prod.fst (PXf i)) MF) :
    ∃ Zf : ι → Set (event α), ∀ i ∈ I,
      (s rest-tr Prod.snd (FXf i), Zf i) ∈ Prod.fst (FXf i) ∧
        Yf i ∩ Ev '' Prod.snd (FXf i) ⊆ Zf i ∧
        Zf i ⊆ Ev '' Prod.snd (FXf i) := by
  classical
  have hEx :
      ∀ i ∈ I,
        ∃ Z,
          (s rest-tr Prod.snd (FXf i), Z) ∈ Prod.fst (FXf i) ∧
            Yf i ∩ Ev '' Prod.snd (FXf i) ⊆ Z ∧
            Z ⊆ Ev '' Prod.snd (FXf i) := by
    intro i hi
    have hiSpec := hF.2 i hi
    have hProc : (s rest-tr Prod.snd (FXf i), Yf i) :f failures (Prod.fst (PXf i)) MF := by
      rw [← hiSpec.2]
      exact hAll i hi
    rcases (subseteqEX_restRefusal_iff.mp hiSpec.1).2
        (s rest-tr Prod.snd (FXf i)) (Yf i) hProc with ⟨Z, hZF, hYZ⟩
    have hRest :
        (s rest-tr Prod.snd (FXf i), Z) ∈
          restRefusal (failures (Prod.fst (PXf i)) MF) (Ev '' Prod.snd (FXf i)) :=
      hiSpec.1.1 hZF
    exact ⟨Z, hZF, hYZ, hRest.2⟩
  let Zf : ι → Set (event α) := fun i =>
    if hi : i ∈ I then
      Classical.choose (hEx i hi)
    else
      ∅
  refine ⟨Zf, ?_⟩
  intro i hi
  have hChosen := DeadlockState_notDeadlockFree_only_if_lmEX_lm (hEx i hi)
  simp [Zf, hi, hChosen]

/- only if part -/

theorem DeadlockState_notDeadlockFree_only_if [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hNotDF : ¬ DeadlockFreeNetwork (I, PXf)) :
    ∃ sigma, isDeadlockStateOf sigma (I, FXf) := by
  classical
  let _ := hI
  let _ := hFin
  have hCounter :
      ∃ s, Tick ∉ sett s ∧ ((s, Ev '' ALP (I, PXf)) :f failures (PAR (I, PXf)) MF) := by
    simpa [DeadlockFreeNetwork_def, DeadlockFree_def] using hNotDF
  rcases hCounter with ⟨s, hNoTick, hsFail⟩
  have hsFailRep :
      ((s, Ev '' ALP (I, PXf)) :f failures (Rep_parallel I PXf) MF) := by
    simpa [PAR_def] using hsFail
  have hRep :
      I ≠ ∅ → I.Finite →
        ((s, Ev '' ALP (I, PXf)) :f failures (Rep_parallel I PXf) MF) := by
    intro _ _
    exact hsFailRep
  have hRepIff :=
    in_failures_Rep_parallel
      (I := I) (PXf := PXf) (f := (s, Ev '' ALP (I, PXf))) (M := MF)
  rcases hRepIff.1 hRep with
      ⟨u, huSubset, Z, hPair, Yf, hUnion, hAll⟩
  rcases Prod.mk.inj hPair with ⟨rfl, rfl⟩
  rcases DeadlockState_notDeadlockFree_only_if_lmEX hF hAll with ⟨Zf, hZf⟩
  have hSettPX : sett s ⊆ Ev '' ALP (I, PXf) := by
    intro e he
    have heIns : e ∈ Set.insert Tick (Ev '' Set.sUnion (Prod.snd '' (PXf '' I))) := huSubset he
    have heOr : e = Tick ∨ e ∈ Ev '' Set.sUnion (Prod.snd '' (PXf '' I)) :=
      Set.mem_insert_iff.mp heIns
    cases heOr with
    | inl hTick =>
        exact False.elim (hNoTick (hTick ▸ he))
    | inr heEv =>
        simpa [ALP_eq_sUnion] using heEv
  have hSettFX : sett s ⊆ Ev '' ALP (I, FXf) := by
    simpa [ALP_eq_of_isFailureOf hF] using hSettPX
  have hUnionZLeft : Set.sUnion (Zf '' I) ⊆ Ev '' ALP (I, FXf) := by
    intro e he
    rcases Set.mem_sUnion.mp he with ⟨Z', hZ', heZ⟩
    rcases hZ' with ⟨i, hi, rfl⟩
    rcases (hZf i hi).2.2 heZ with ⟨a, ha, rfl⟩
    exact ⟨a, ⟨i, hi, ha⟩, rfl⟩
  have hUnionZRight : Ev '' ALP (I, FXf) ⊆ Set.sUnion (Zf '' I) := by
    intro e he
    have hePX : e ∈ Ev '' ALP (I, PXf) := by
      simpa [ALP_eq_of_isFailureOf hF] using he
    have heIns : e ∈ Set.insert Tick (Ev '' Set.sUnion (Prod.snd '' (PXf '' I))) := by
      have heUnion : e ∈ Ev '' Set.sUnion (Prod.snd '' (PXf '' I)) := by
        simpa [ALP_eq_sUnion] using hePX
      exact Or.inr heUnion
    have heFam :
        e ∈ Set.sUnion {S | ∃ i : ι, i ∈ I ∧
          S = Yf i ∩ Set.insert Tick (Ev '' Prod.snd (PXf i))} := by
      exact hUnion ▸ ⟨hePX, heIns⟩
    rcases Set.mem_sUnion.mp heFam with ⟨S, hS, heS⟩
    rcases hS with ⟨i, hi, rfl⟩
    have heY : e ∈ Yf i := heS.1
    have heOr : e = Tick ∨ e ∈ Ev '' Prod.snd (PXf i) :=
      Set.mem_insert_iff.mp heS.2
    have hePXi : e ∈ Ev '' Prod.snd (PXf i) := by
      cases heOr with
      | inl hTick =>
          rcases hePX with ⟨a, _, hEq⟩
          have : Ev a = Tick := hEq.trans hTick
          cases this
      | inr he' =>
          exact he'
    have heFXi : e ∈ Ev '' Prod.snd (FXf i) := by
      simpa [isFailureOf_same_alpha hF i hi] using hePXi
    have heZ : e ∈ Zf i := (hZf i hi).2.1 ⟨heY, heFXi⟩
    exact Set.mem_sUnion.mpr ⟨Zf i, ⟨i, hi, rfl⟩, heZ⟩
  refine ⟨(s, Zf), ?_⟩
  constructor
  · constructor
    · exact hSettFX
    · intro i hi
      exact ⟨(hZf i hi).1, (hZf i hi).2.2⟩
  · exact Set.Subset.antisymm hUnionZLeft hUnionZRight

/- (*** if part ***) -/

theorem DeadlockState_notDeadlockFree_if [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hDead : ∃ sigma, isDeadlockStateOf sigma (I, FXf)) :
    ¬ DeadlockFreeNetwork (I, PXf) := by
  classical
  rcases hDead with ⟨⟨t, Yf⟩, hDead⟩
  have hState : isStateOf (t, Yf) (I, FXf) := hDead.1
  have hUnionState : Set.sUnion (Yf '' I) = Ev '' ALP (I, FXf) := hDead.2
  have hNoTick : Tick ∉ sett t := by
    intro hTick
    rcases hState.1 hTick with ⟨a, _, hEq⟩
    cases hEq
  have hYSubsetFX : ∀ i ∈ I, Yf i ⊆ Ev '' Prod.snd (FXf i) := by
    intro i hi
    exact (hState.2 i hi).2
  have hYSubsetPX : ∀ i ∈ I, Yf i ⊆ Ev '' Prod.snd (PXf i) := by
    intro i hi
    simpa [isFailureOf_same_alpha hF i hi] using hYSubsetFX i hi
  have hLocalFail :
      ∀ i ∈ I, (t rest-tr Prod.snd (PXf i), Yf i) :f failures (Prod.fst (PXf i)) MF := by
    intro i hi
    have hRest :
        (t rest-tr Prod.snd (FXf i), Yf i) ∈
          restRefusal (failures (Prod.fst (PXf i)) MF) (Ev '' Prod.snd (FXf i)) :=
      ((hF.2 i hi).1).1 ((hState.2 i hi).1)
    have hRest' := hRest.1
    rw [← (hF.2 i hi).2] at hRest'
    exact hRest'
  have hIntersectEq :
      ∀ i ∈ I,
        Yf i ∩ Set.insert Tick (Ev '' Prod.snd (PXf i)) = Yf i := by
    intro i hi
    exact subset_inter_insert_Ev_eq (hYSubsetPX i hi)
  have hImageEq :
      ((fun i => Yf i ∩ Set.insert Tick (Ev '' Prod.snd (PXf i))) '' I) = Yf '' I := by
    exact image_eq_of_pointwise hIntersectEq
  have hLeftEq :
      Ev '' ALP (I, PXf) ∩ Set.insert Tick (Ev '' Set.sUnion (Prod.snd '' (PXf '' I))) =
        Ev '' ALP (I, PXf) := by
    rw [ALP_eq_sUnion]
    simpa using image_inter_insert_Ev (A := Set.sUnion (Prod.snd '' (PXf '' I)))
  have hFailRep :
      ((t, Ev '' ALP (I, PXf)) :f failures (Rep_parallel I PXf) MF) := by
    have hRepIff :=
      in_failures_Rep_parallel
        (I := I) (PXf := PXf) (f := (t, Ev '' ALP (I, PXf))) (M := MF)
    have hRep :
        I ≠ ∅ → I.Finite →
          ((t, Ev '' ALP (I, PXf)) :f failures (Rep_parallel I PXf) MF) :=
      hRepIff.2
        (by
      refine ⟨t, ?_, Ev '' ALP (I, PXf), rfl, Yf, ?_, hLocalFail⟩
      · intro e he
        have heFX : e ∈ Ev '' ALP (I, FXf) := hState.1 he
        have hePX : e ∈ Ev '' ALP (I, PXf) := by
          simpa [ALP_eq_of_isFailureOf hF] using heFX
        have heUnion : e ∈ Ev '' Set.sUnion (Prod.snd '' (PXf '' I)) := by
          simpa [ALP_eq_sUnion] using hePX
        change e = Tick ∨ e ∈ Ev '' Set.sUnion (Prod.snd '' (PXf '' I))
        exact Or.inr heUnion
      · calc
          Ev '' ALP (I, PXf) ∩ Set.insert Tick (Ev '' Set.sUnion (Prod.snd '' (PXf '' I)))
              = Ev '' ALP (I, PXf) := hLeftEq
          _ = Ev '' ALP (I, FXf) := by
            simp [ALP_eq_of_isFailureOf hF]
          _ = Set.sUnion (Yf '' I) := hUnionState.symm
          _ = Set.sUnion ((fun i => Yf i ∩ Set.insert Tick (Ev '' Prod.snd (PXf i))) '' I) := by
            simp [hImageEq]
          _ =
              Set.sUnion {S | ∃ i : ι, i ∈ I ∧
                S = Yf i ∩ Set.insert Tick (Ev '' Prod.snd (PXf i))} := by
            rw [family_set_eq_image])
    exact hRep hI hFin
  have hFailPAR :
      ((t, Ev '' ALP (I, PXf)) :f failures (PAR (I, PXf)) MF) := by
    simpa [PAR_def] using hFailRep
  intro hDF
  exact (hDF t hNoTick) hFailPAR

/- (*** iff ***) -/

theorem DeadlockState_notDeadlockFree [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hF : isFailureOf (I, FXf) (I, PXf)) :
    (¬ DeadlockFreeNetwork (I, PXf)) ↔ ∃ sigma, isDeadlockStateOf sigma (I, FXf) := by
  constructor
  · exact DeadlockState_notDeadlockFree_only_if hI hFin hF
  · exact DeadlockState_notDeadlockFree_if hI hFin hF

/- (*** DeadlockFree ***) -/

theorem DeadlockFree_notDeadlockState [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hI : I ≠ ∅)
    (hFin : I.Finite)
    (hF : isFailureOf (I, FXf) (I, PXf)) :
    DeadlockFreeNetwork (I, PXf) ↔ ∀ sigma, ¬ isDeadlockStateOf sigma (I, FXf) := by
  constructor
  · intro hDF sigma hSigma
    exact (DeadlockState_notDeadlockFree_if hI hFin hF ⟨sigma, hSigma⟩) hDF
  · intro hAll
    by_contra hDF
    rcases DeadlockState_notDeadlockFree_only_if hI hFin hF hDF with ⟨sigma, hSigma⟩
    exact hAll sigma hSigma

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
