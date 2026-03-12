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

import LeanCspProver.DFP.DFP_subseteqEX
import LeanCspProver.CSP_F.CSP_F_law_rep_par
import LeanCspProver.CSP_T.CSP_T_law_rep_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `UnionT` and `InterT`.             -/
/-                  `Union (B \` A) = (UN x:A. B x)`                   -/
/-                  `Inter (B \` A) = (INT x:A. B x)`                  -/

/- Lean note:
   Isabelle's local simp-set deletion for these rules has no direct analogue
   here, so the comments are preserved without an executable command. -/

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `(notick | t = []t)`              -/
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

/- (*** network ***) -/

abbrev Network (ι : Type _) (p : Type _) (α : Type _) :=
  Set ι × (ι → (proc p α × Set α))

def PAR (V : Network ι p α) : proc p α :=
  Rep_parallel V.1 V.2

theorem PAR_def (V : Network ι p α) :
    PAR V = Rep_parallel V.1 V.2 :=
  rfl

/- Isabelle's `syntax`/`translations` block for `{ PX | i:I }net` is encoded
   directly by the underlying pair `(I, fun i => PX)` in Lean. -/

/- (*** failure set of network ***) -/

abbrev NetworkF (ι : Type _) (α : Type _) :=
  Set ι × (ι → (Set (failure α) × Set α))

/- Isabelle's `syntax`/`translations` block for `{ FX | i:I }Fnet` is encoded
   directly by the underlying pair `(I, fun i => FX)` in Lean. -/

/- (*** Network and NetworkF ***) -/

abbrev Network_pro (V : Set ι × (ι → (β × Set α))) (i : ι) : β :=
  Prod.fst (V.2 i)

abbrev Network_alp (V : Set ι × (ι → (β × Set α))) (i : ι) : Set α :=
  Prod.snd (V.2 i)

def isFailureOf [HasPNfun p α] [HasFPmode] (VF : NetworkF ι α) (V : Network ι p α) : Prop :=
  V.1 = VF.1 ∧
    ∀ i ∈ VF.1,
      Prod.fst (VF.2 i) <=EX
          restRefusal (failures (Prod.fst (V.2 i)) MF) (Ev '' Prod.snd (VF.2 i)) ∧
        Prod.snd (V.2 i) = Prod.snd (VF.2 i)

theorem isFailureOf_def [HasPNfun p α] [HasFPmode] (VF : NetworkF ι α) (V : Network ι p α) :
    isFailureOf VF V ↔
      V.1 = VF.1 ∧
        ∀ i ∈ VF.1,
          Prod.fst (VF.2 i) <=EX
              restRefusal (failures (Prod.fst (V.2 i)) MF) (Ev '' Prod.snd (VF.2 i)) ∧
            Prod.snd (V.2 i) = Prod.snd (VF.2 i) :=
  Iff.rfl

/- (*** short notations ***) -/

def ALP (V : Set ι × (ι → (β × Set α))) : Set α :=
  {a | ∃ i ∈ V.1, a ∈ Prod.snd (V.2 i)}

theorem ALP_def (V : Set ι × (ι → (β × Set α))) :
    ALP V = {a | ∃ i ∈ V.1, a ∈ Prod.snd (V.2 i)} :=
  rfl

/- (*** state ***) -/

abbrev net_state (ι : Type _) (α : Type _) :=
  traceType α × (ι → Set (event α))

def isStateOf (sigma : net_state ι α) (VF : NetworkF ι α) : Prop :=
  sett sigma.1 ⊆ Ev '' ALP VF ∧
    ∀ i ∈ VF.1,
      (sigma.1 rest-tr Prod.snd (VF.2 i), sigma.2 i) ∈ Prod.fst (VF.2 i) ∧
        sigma.2 i ⊆ Ev '' Prod.snd (VF.2 i)

theorem isStateOf_def (sigma : net_state ι α) (VF : NetworkF ι α) :
    isStateOf sigma VF ↔
      sett sigma.1 ⊆ Ev '' ALP VF ∧
        ∀ i ∈ VF.1,
          (sigma.1 rest-tr Prod.snd (VF.2 i), sigma.2 i) ∈ Prod.fst (VF.2 i) ∧
            sigma.2 i ⊆ Ev '' Prod.snd (VF.2 i) :=
  Iff.rfl

/-
(*********************************************************
                    small lemmas
 *********************************************************)
-/

theorem decompo_V (V : Network ι p α) :
    ∃ I PXf, V = (I, PXf) := by
  exact ⟨V.1, V.2, rfl⟩

theorem isFailureOf_subset_index [HasPNfun p α] [HasFPmode]
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hF : isFailureOf (I, FXf) (I, PXf)) (hJ : J ⊆ I) :
    isFailureOf (J, FXf) (J, PXf) := by
  constructor
  · rfl
  · intro i hi
    exact hF.2 i (hJ hi)

theorem isFailureOf_subset_alpha1 [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {i : ι} {s : traceType α} {Y : Set (event α)} {e : event α}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hi : i ∈ I)
    (hsY : (s, Y) ∈ Prod.fst (FXf i))
    (he : e ∈ Y) :
    e ∈ Ev '' Prod.snd (PXf i) := by
  have hiSpec := hF.2 i hi
  have hsRest : (s, Y) ∈ restRefusal (failures (Prod.fst (PXf i)) MF) (Ev '' Prod.snd (FXf i)) :=
    hiSpec.1.1 hsY
  rw [restRefusal_def] at hsRest
  have heFX : e ∈ Ev '' Prod.snd (FXf i) := hsRest.2 he
  rw [hiSpec.2]
  exact heFX

theorem isFailureOf_subset_alpha2 [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {i : ι} {s : traceType α} {Y : Set (event α)} {e : event α}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hi : i ∈ I)
    (hsY : (s, Y) ∈ Prod.fst (FXf i))
    (he : e ∈ Y) :
    e ∈ Ev '' Prod.snd (FXf i) := by
  have hiSpec := hF.2 i hi
  have hsRest : (s, Y) ∈ restRefusal (failures (Prod.fst (PXf i)) MF) (Ev '' Prod.snd (FXf i)) :=
    hiSpec.1.1 hsY
  rw [restRefusal_def] at hsRest
  exact hsRest.2 he

theorem isFailureOf_not_Tick [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {i : ι} {s : traceType α} {Y : Set (event α)}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hi : i ∈ I)
    (hsY : (s, Y) ∈ Prod.fst (FXf i)) :
    Tick ∉ Y := by
  have hiSpec := hF.2 i hi
  have hsRest : (s, Y) ∈ restRefusal (failures (Prod.fst (PXf i)) MF) (Ev '' Prod.snd (FXf i)) :=
    hiSpec.1.1 hsY
  rw [restRefusal_def] at hsRest
  intro hTick
  rcases hsRest.2 hTick with ⟨a, _, hEq⟩
  cases hEq

theorem isFailureOf_same_alpha [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    (hF : isFailureOf (I, FXf) (I, PXf)) :
    ∀ i ∈ I, Prod.snd (PXf i) = Prod.snd (FXf i) :=
  fun i hi => (hF.2 i hi).2

/-
(*********************************************************
                 StateOf subset
 *********************************************************)
-/

theorem isStateOf_subset_alpha1 [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {i : ι} {e : event α}
    (hF : isFailureOf (I, FXf) (I, PXf))
    (hS : isStateOf (t, Yf) (I, FXf))
    (hi : i ∈ I)
    (he : e ∈ Yf i) :
    e ∈ Ev '' Prod.snd (PXf i) := by
  have hY := (hS.2 i hi).2 he
  simpa [isFailureOf_same_alpha hF i hi] using hY

theorem isStateOf_subset_alpha2 [HasPNfun p α] [HasFPmode]
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {PXf : ι → (proc p α × Set α)}
    {t : traceType α} {Yf : ι → Set (event α)} {i : ι} {e : event α}
    (_hF : isFailureOf (I, FXf) (I, PXf))
    (hS : isStateOf (t, Yf) (I, FXf))
    (hi : i ∈ I)
    (he : e ∈ Yf i) :
    e ∈ Ev '' Prod.snd (FXf i) := by
  exact (hS.2 i hi).2 he

theorem isStateOf_each_element
    {I : Set ι} {FXf : ι → (Set (failure α) × Set α)} {t : traceType α} {Yf : ι → Set (event α)}
    {i : ι}
    (hS : isStateOf (t, Yf) (I, FXf))
    (hi : i ∈ I) :
    isStateOf (t rest-tr Prod.snd (FXf i), Yf) ({i}, FXf) := by
  constructor
  · have hSubsetTick :
        sett (t rest-tr Prod.snd (FXf i)) ⊆ Set.insert Tick (Ev '' Prod.snd (FXf i)) :=
      rest_tr_subset_event
    have hNoTickT : noTick t := by
      intro hTick
      have hMem : Tick ∈ Ev '' ALP (I, FXf) := hS.1 hTick
      rcases hMem with ⟨a, _, hEq⟩
      cases hEq
    have hNoTickRest : noTick (t rest-tr Prod.snd (FXf i)) := by
      simpa [noTick] using ((rest_tr_noTick (s := t) (X := Prod.snd (FXf i))).2 hNoTickT)
    intro e he
    have heTickOr : e = Tick ∨ e ∈ Ev '' Prod.snd (FXf i) := by
      simpa [Set.mem_insert_iff] using hSubsetTick he
    cases heTickOr with
    | inl hTick =>
        exfalso
        exact hNoTickRest (hTick ▸ he)
    | inr heEv =>
        rcases heEv with ⟨a, ha, rfl⟩
        exact ⟨a, ⟨i, by simp, ha⟩, rfl⟩
  · intro j hj
    have hjEq : j = i := by simpa using hj
    subst j
    constructor
    · have hRestEq :=
        (rest_tr_of_rest_tr_subset
          (u := t)
          (X := Prod.snd (FXf i))
          (Y := Prod.snd (FXf i))
          (by intro a ha; exact ha)).1
      simpa [hRestEq] using (hS.2 i hi).1
    · simpa using (hS.2 i hi).2

/-
(*********************************************************
                        PAR
 *********************************************************)
-/

/- *---------------------------------*
 |           flattening            |
 *---------------------------------* -/

/- (*** SF ***) -/

/- lemmas -/

axiom domSF_PAR_flattening_lm1
    {κ : Type _} {x : κ} {V : κ → Network ι p α} :
    ALP (V x) =
      Set.sUnion
        (Prod.snd ''
          ((fun ij : ι × κ => (V ij.2).2 ij.1) ''
            {ij : ι × κ | ij.1 ∈ (V x).1 ∧ ij.2 = x}))

axiom domSF_PAR_flattening_lm2
    {κ : Type _} {F : Set κ} {V : κ → Network ι p α} :
    Set.sUnion (Prod.snd '' ((fun i : κ => (PAR (V i), ALP (V i))) '' F)) =
      Set.sUnion
        (Prod.snd ''
          ((fun ij : ι × κ => (V ij.2).2 ij.1) ''
            {ij : ι × κ | ij.2 ∈ F ∧ ij.1 ∈ (V ij.2).1}))

/- main -/

/- (*------------------*
 |      csp law     |
 *------------------*) -/

axiom cspF_PAR_flattening
    {κ : Type _} {J : Set κ} {V : κ → Network ι p α} {M : p → domFType α} :
    J.Finite →
      (∀ j ∈ J, ((V j).1).Finite) →
        eqF
          (PAR ({j | j ∈ J}, fun j => (PAR (V j), ALP (V j))))
          M M
          (PAR ({ij : ι × κ | ij.2 ∈ J ∧ ij.1 ∈ (V ij.2).1}, fun ij => (V ij.2).2 ij.1))

/- (*** T and F ***) -/

theorem traces_PAR_flattening
    {κ : Type _} {J : Set κ} {V : κ → Network ι p α} {M : p → domTType α}
    (hJ : J.Finite)
    (hV : ∀ j ∈ J, ((V j).1).Finite) :
    traces (PAR ({j | j ∈ J}, fun j => (PAR (V j), ALP (V j)))) M =
      traces (PAR ({ij : ι × κ | ij.2 ∈ J ∧ ij.1 ∈ (V ij.2).1}, fun ij => (V ij.2).2 ij.1)) M := by
  let MF' : p → domFType α := fun p => M p ,, maxFof (M p)
  have hEq :=
    cspF_PAR_flattening (J := J) (V := V) (M := MF') hJ hV
  have hSem :=
    (cspF_eqF_semantics
      (P := PAR ({j | j ∈ J}, fun j => (PAR (V j), ALP (V j))))
      (Q := PAR ({ij : ι × κ | ij.2 ∈ J ∧ ij.1 ∈ (V ij.2).1}, fun ij => (V ij.2).2 ij.1))
      (M1 := MF')
      (M2 := MF')).1 hEq
  have hfst : fstF ∘ MF' = M := by
    funext p
    exact pairF_fstF (hSF := maxFof_domF (T := M p))
  simpa [MF', hfst] using hSem.1

theorem failures_PAR_flattening
    {κ : Type _} {J : Set κ} {V : κ → Network ι p α} {M : p → domFType α}
    (hJ : J.Finite)
    (hV : ∀ j ∈ J, ((V j).1).Finite) :
    failures (PAR ({j | j ∈ J}, fun j => (PAR (V j), ALP (V j)))) M =
      failures
        (PAR ({ij : ι × κ | ij.2 ∈ J ∧ ij.1 ∈ (V ij.2).1}, fun ij => (V ij.2).2 ij.1))
        M := by
  exact
    (cspF_eqF_semantics
      (P := PAR ({j | j ∈ J}, fun j => (PAR (V j), ALP (V j))))
      (Q := PAR ({ij : ι × κ | ij.2 ∈ J ∧ ij.1 ∈ (V ij.2).1}, fun ij => (V ij.2).2 ij.1))
      (M1 := M)
      (M2 := M)).1 (cspF_PAR_flattening (J := J) (V := V) (M := M) hJ hV) |>.2

/-
(*********************************************************
                      sub network
 *********************************************************)
-/

/- (*** state ***) -/

theorem isStateOf_subset
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)} {t : traceType α} {Yf : ι → Set (event α)}
    {X : Set α}
    (hS : isStateOf (t, Yf) (I, FXf))
    (hJ : J ⊆ I)
    (hX : X = {sY | ∃ i ∈ J, sY ∈ Prod.snd (FXf i)}) :
    isStateOf (t rest-tr X, Yf) (J, FXf) := by
  constructor
  · have hSubsetTick : sett (t rest-tr X) ⊆ Set.insert Tick (Ev '' X) := rest_tr_subset_event
    have hNoTickT : noTick t := by
      intro hTick
      have hMem : Tick ∈ Ev '' ALP (I, FXf) := hS.1 hTick
      rcases hMem with ⟨a, _, hEq⟩
      cases hEq
    have hNoTickRest : noTick (t rest-tr X) := by
      simpa [noTick] using ((rest_tr_noTick (s := t) (X := X)).2 hNoTickT)
    intro e he
    have heTickOr : e = Tick ∨ e ∈ Ev '' X := by
      simpa [Set.mem_insert_iff] using hSubsetTick he
    cases heTickOr with
    | inl hTick =>
        exfalso
        exact hNoTickRest (hTick ▸ he)
    | inr heX =>
        rcases heX with ⟨a, haX, rfl⟩
        rw [hX] at haX
        rcases haX with ⟨i, hiJ, ha⟩
        exact ⟨a, ⟨i, hiJ, ha⟩, rfl⟩
  · intro i hiJ
    have hiI : i ∈ I := hJ hiJ
    have hFXsubset : Prod.snd (FXf i) ⊆ X := by
      rw [hX]
      intro a ha
      exact ⟨i, hiJ, ha⟩
    constructor
    · have hRestEq :=
        (rest_tr_of_rest_tr_subset (u := t) (X := Prod.snd (FXf i)) (Y := X) hFXsubset).2
      rw [hRestEq]
      exact (hS.2 i hiI).1
    · exact (hS.2 i hiI).2

theorem isStateOf_subsetI
    {I J : Set ι} {FXf : ι → (Set (failure α) × Set α)} {t : traceType α} {Yf : ι → Set (event α)}
    {X : Set α}
    (hS : isStateOf (t, Yf) (I, FXf))
    (hJ : J ⊆ I)
    (hX : X = Set.sUnion {A | ∃ i ∈ J, A = Prod.snd (FXf i)}) :
    isStateOf (t rest-tr X, Yf) (J, FXf) := by
  have hX' : X = {sY | ∃ i ∈ J, sY ∈ Prod.snd (FXf i)} := by
    rw [hX]
    ext a
    constructor
    · intro ha
      rcases Set.mem_sUnion.mp ha with ⟨A, hA, haA⟩
      rcases hA with ⟨i, hiJ, rfl⟩
      exact ⟨i, hiJ, haA⟩
    · rintro ⟨i, hiJ, ha⟩
      exact Set.mem_sUnion.mpr ⟨Prod.snd (FXf i), ⟨i, hiJ, rfl⟩, ha⟩
  exact isStateOf_subset (hS := hS) (hJ := hJ) (hX := hX')

/-
(*********************************************************
                      isFailureOf
 *********************************************************)
-/

theorem isFailureOf_largest [HasPNfun p α] [HasFPmode]
    {I : Set ι} {PXf : ι → (proc p α × Set α)} :
    isFailureOf
      (I, fun i =>
        ({f | ∃ s Y, f = (s, Y ∩ (Ev '' Prod.snd (PXf i))) ∧
            (s, Y) :f failures (Prod.fst (PXf i)) MF},
          Prod.snd (PXf i)))
      (I, PXf) := by
  constructor
  · rfl
  · intro i hi
    constructor
    · rw [subseteqEX_Int]
      exact subseteqEX_reflex
    · rfl

theorem isFailureOf_EX [HasPNfun p α] [HasFPmode] (V : Network ι p α) :
    ∃ VF, isFailureOf VF V := by
  refine ⟨(V.1, fun i =>
    ({f | ∃ s Y, f = (s, Y ∩ (Ev '' Prod.snd (V.2 i))) ∧
        (s, Y) :f failures (Prod.fst (V.2 i)) MF},
      Prod.snd (V.2 i))), ?_⟩
  simpa using (isFailureOf_largest (I := V.1) (PXf := V.2))

/- Lean note:
   Isabelle restored the deleted simp rules at the end of the theory. Lean has
   no corresponding local simp-set mutations to undo here. -/
