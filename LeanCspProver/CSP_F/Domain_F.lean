           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.Domain_T
import LeanCspProver.CSP_F.Set_F

noncomputable section

/-
(*****************************************************************

         1.
         2.
         3.
         4.

 *****************************************************************)
-/

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.        -/
/-                  `Union (B \` A) = (UN x:A. B x)`                -/
/-                  `Inter (B \` A) = (INT x:A. B x)`               -/

/- no simp rules in Isabelle 2017 -/

/-
(***********************************************************
                 type def (Stable Failure)
 ***********************************************************)
-/

abbrev domTsetF (α : Type u) := domTType α × setFType α

private abbrev Tickt : traceType α := (Abs_trace [event.Tick] : traceType α)

def HC_T2 (TF : domTsetF α) : Prop :=
  ∀ s X, (s, X) :f TF.2 → memT s TF.1

theorem HC_T2_def {TF : domTsetF α} :
    HC_T2 TF ↔ ∀ s X, (s, X) :f TF.2 → memT s TF.1 :=
  Iff.rfl

def HC_T3 (TF : domTsetF α) : Prop :=
  ∀ s, memT (s ^^^ Tickt (α := α)) TF.1 ∧ noTick s →
    ∀ X, (s ^^^ Tickt (α := α), X) :f TF.2

theorem HC_T3_def {TF : domTsetF α} :
    HC_T3 TF ↔
      ∀ s, memT (s ^^^ Tickt (α := α)) TF.1 ∧ noTick s →
        ∀ X, (s ^^^ Tickt (α := α), X) :f TF.2 :=
  Iff.rfl

def HC_F3 (TF : domTsetF α) : Prop :=
  ∀ s X Y, (s, X) :f TF.2 → noTick s →
    (∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) TF.1) →
      (s, X ∪ Y) :f TF.2

theorem HC_F3_def {TF : domTsetF α} :
    HC_F3 TF ↔
      ∀ s X Y, (s, X) :f TF.2 → noTick s →
        (∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) TF.1) →
          (s, X ∪ Y) :f TF.2 :=
  Iff.rfl

def HC_F4 (TF : domTsetF α) : Prop :=
  ∀ s, memT (s ^^^ Tickt (α := α)) TF.1 ∧ noTick s → (s, Evset) :f TF.2

theorem HC_F4_def {TF : domTsetF α} :
    HC_F4 TF ↔
      ∀ s, memT (s ^^^ Tickt (α := α)) TF.1 ∧ noTick s → (s, Evset) :f TF.2 :=
  Iff.rfl

def HC_T3_F4 (TF : domTsetF α) : Prop :=
  ∀ s, memT (s ^^^ Tickt (α := α)) TF.1 ∧ noTick s →
    ((s, Evset) :f TF.2 ∧ ∀ X, (s ^^^ Tickt (α := α), X) :f TF.2)

theorem HC_T3_F4_def {TF : domTsetF α} :
    HC_T3_F4 TF ↔
      ∀ s, memT (s ^^^ Tickt (α := α)) TF.1 ∧ noTick s →
        ((s, Evset) :f TF.2 ∧ ∀ X, (s ^^^ Tickt (α := α), X) :f TF.2) :=
  Iff.rfl

theorem HC_T3_F4_iff {TF : domTsetF α} :
    HC_T3_F4 TF ↔ (HC_T3 TF ∧ HC_F4 TF) := by
  constructor
  · intro hTF
    constructor
    · intro s hs X
      exact (hTF s hs).2 X
    · intro s hs
      exact (hTF s hs).1
  · rintro ⟨hT3, hF4⟩
    intro s hs
    exact ⟨hF4 s hs, hT3 s hs⟩

/- (*** BOT in domF ***) -/

theorem BOT_T2_T3_F3_F4 :
    HC_T2 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) ∧
      HC_F3 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) ∧
      HC_T3_F4 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) := by
  constructor
  · intro s X hsX
    exact False.elim ((memF_empF (sX := (s, X))) hsX)
  constructor
  · intro s X Y hsX _ _
    exact False.elim ((memF_empF (sX := (s, X))) hsX)
  · intro s hs
    have hFalse : False := by
      have hEq : s ^^^ Tickt (α := α) = <> := memT_nilt.mp hs.1
      have hNil := (appt_nil hs.2).mp hEq
      simpa using hNil.2
    exact False.elim hFalse

/-
(**************************************************
           Type domF (Stable-Failures model)
 **************************************************)
-/

def domF : Set (domTsetF α) :=
  {SF | HC_T2 SF ∧ HC_T3 SF ∧ HC_F3 SF ∧ HC_F4 SF}

theorem domF_def {SF : domTsetF α} :
    SF ∈ domF (α := α) ↔ HC_T2 SF ∧ HC_T3 SF ∧ HC_F3 SF ∧ HC_F4 SF :=
  Iff.rfl

abbrev domFType (α : Type u) := {SF : domTsetF α // SF ∈ domF (α := α)}

def Rep_domF (SF : domFType α) : domTsetF α := SF.1

open Classical in
noncomputable def Abs_domF (SF : domTsetF α) : domFType α :=
  if h : SF ∈ domF (α := α) then
    ⟨SF, h⟩
  else
    ⟨((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)), by
      change
        HC_T2 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) ∧
          HC_T3 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) ∧
          HC_F3 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) ∧
          HC_F4 ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α))
      rcases BOT_T2_T3_F3_F4 (α := α) with ⟨hT2, hF3, hT3F4⟩
      rcases
          (HC_T3_F4_iff
            (TF := ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)))).mp hT3F4
        with
        ⟨hT3, hF4⟩
      exact ⟨hT2, hT3, hF3, hF4⟩⟩

@[simp]
theorem Rep_domF_mk {SF : domTsetF α} {h : SF ∈ domF (α := α)} :
    Rep_domF (Subtype.mk SF h : domFType α) = SF :=
  rfl

@[simp]
theorem Abs_domF_inverse {SF : domTsetF α} (hSF : SF ∈ domF (α := α)) :
    Rep_domF (Abs_domF SF) = SF := by
  simp [Abs_domF, hSF]

@[simp]
theorem Rep_domF_inverse (SF : domFType α) : Abs_domF (Rep_domF SF) = SF := by
  cases SF with
  | mk SF hSF =>
      simp [Abs_domF, hSF]

theorem Rep_domF_inject {SF SE : domFType α} :
    Rep_domF SF = Rep_domF SE ↔ SF = SE := by
  constructor
  · intro h
    cases SF
    cases SE
    cases h
    rfl
  · intro h
    cases h
    rfl

private theorem mem_domF_iff {SF : domTsetF α} :
    SF ∈ domF (α := α) ↔ HC_T2 SF ∧ HC_F3 SF ∧ HC_T3_F4 SF := by
  constructor
  · intro hSF
    exact ⟨hSF.1, hSF.2.2.1, (HC_T3_F4_iff (TF := SF)).2 ⟨hSF.2.1, hSF.2.2.2⟩⟩
  · intro hSF
    rcases (HC_T3_F4_iff (TF := SF)).1 hSF.2.2 with ⟨hT3, hF4⟩
    exact ⟨hSF.1, hT3, hSF.2.1, hF4⟩

theorem domF_iff :
    domF (α := α) = {SF | HC_T2 SF ∧ HC_F3 SF ∧ HC_T3_F4 SF} := by
  ext SF
  exact mem_domF_iff (SF := SF)

/-
(*********************************************************
          The relation (<=) is defined over domF
 *********************************************************)
-/

instance : LE (domFType α) where
  le SF SE := Rep_domF SF <= Rep_domF SE

theorem subdomF_def {SF SE : domFType α} :
    SF <= SE ↔ Rep_domF SF <= Rep_domF SE :=
  Iff.rfl

theorem psubdomF_def {SF SE : domFType α} :
    LT.lt SF SE ↔ LT.lt (Rep_domF SF) (Rep_domF SE) :=
  Iff.rfl

/-
(*********************************************************
          The relation (<=) is a partial order
 *********************************************************)
-/

instance : PartialOrder (domFType α) where
  le SF SE := Rep_domF SF <= Rep_domF SE
  le_refl := by
    intro SF
    exact le_rfl
  le_trans := by
    intro SF SE ST hFS hES
    exact le_trans hFS hES
  le_antisymm := by
    intro SF SE hFS hES
    apply (Rep_domF_inject).mp
    exact le_antisymm hFS hES

/-
(***********************************************************
                          lemmas
 ***********************************************************)
-/

/-
(*******************************
              basic
 *******************************)
-/

/- (*** T2 ***) -/

theorem domTsetF_T2 {TF : domTsetF α}
    (hTF : TF ∈ domF (α := α)) (hsX : (s, X) :f TF.2) :
    memT s TF.1 := by
  exact hTF.1 s X hsX

theorem domF_T2 {T : domTType α} {F : setFType α}
    (hTF : (T, F) ∈ domF (α := α)) (hsX : (s, X) :f F) :
    memT s T := by
  exact domTsetF_T2 (TF := (T, F)) hTF hsX

/- (*** T3 ***) -/

theorem domTsetF_T3 {TF : domTsetF α}
    (hTF : TF ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) TF.1) (hNo : noTick s) :
    (s ^^^ Tickt (α := α), X) :f TF.2 := by
  exact hTF.2.1 s ⟨hTick, hNo⟩ X

theorem domF_T3 {T : domTType α} {F : setFType α}
    (hTF : (T, F) ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) T) (hNo : noTick s) :
    (s ^^^ Tickt (α := α), X) :f F := by
  exact domTsetF_T3 (TF := (T, F)) hTF hTick hNo

/- (*** F3 ***) -/

theorem domTsetF_F3 {TF : domTsetF α}
    (hTF : TF ∈ domF (α := α)) (hsX : (s, X) :f TF.2) (hNo : noTick s)
    (hY : ∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) TF.1) :
    (s, X ∪ Y) :f TF.2 := by
  exact hTF.2.2.1 s X Y hsX hNo hY

theorem domF_F3 {T : domTType α} {F : setFType α}
    (hTF : (T, F) ∈ domF (α := α)) (hsX : (s, X) :f F) (hNo : noTick s)
    (hY : ∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) T) :
    (s, X ∪ Y) :f F := by
  exact domTsetF_F3 (TF := (T, F)) hTF hsX hNo hY

/- (*** F4 ***) -/

theorem domTsetF_F4 {TF : domTsetF α}
    (hTF : TF ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) TF.1) (hNo : noTick s) :
    (s, Evset) :f TF.2 := by
  exact hTF.2.2.2 s ⟨hTick, hNo⟩

theorem domF_F4 {T : domTType α} {F : setFType α}
    (hTF : (T, F) ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) T) (hNo : noTick s) :
    (s, Evset) :f F := by
  exact domTsetF_F4 (TF := (T, F)) hTF hTick hNo

/- (*** T3_F4 ***) -/

theorem domTsetF_T3_F4 {TF : domTsetF α}
    (hTF : TF ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) TF.1) (hNo : noTick s) :
    (s, Evset) :f TF.2 ∧ ∀ X, (s ^^^ Tickt (α := α), X) :f TF.2 := by
  exact (mem_domF_iff (SF := TF)).mp hTF |>.2.2 s ⟨hTick, hNo⟩

theorem domF_T3_F4 {T : domTType α} {F : setFType α}
    (hTF : (T, F) ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) T) (hNo : noTick s) :
    (s, Evset) :f F ∧ ∀ X, (s ^^^ Tickt (α := α), X) :f F := by
  exact domTsetF_T3_F4 (TF := (T, F)) hTF hTick hNo

/- (*** F2_F4 ***) -/

theorem domTsetF_F2_F4 {TF : domTsetF α}
    (hTF : TF ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) TF.1) (hNo : noTick s)
    (hX : X ⊆ Evset) :
    (s, X) :f TF.2 := by
  exact memF_F2 (domTsetF_F4 (TF := TF) hTF hTick hNo) hX

theorem domF_F2_F4 {T : domTType α} {F : setFType α}
    (hTF : (T, F) ∈ domF (α := α))
    (hTick : memT (s ^^^ Tickt (α := α)) T) (hNo : noTick s)
    (hX : X ⊆ Evset) :
    (s, X) :f F := by
  exact domTsetF_F2_F4 (TF := (T, F)) hTF hTick hNo hX

/-
(*******************************
         check in domF
 *******************************)
-/

/- (*** ({<>}t, {}f) ***) -/

@[simp]
theorem BOT_in_domF :
    ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) ∈ domF (α := α) := by
  exact (mem_domF_iff
    (SF := ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)))).2
      (BOT_T2_T3_F3_F4 (α := α))

/-
(*******************************
       BOT is the bottom
 *******************************)
-/

@[simp]
theorem BOT_is_bottom_domF {SF : domFType α} :
    Abs_domF ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) <= SF := by
  rw [subdomF_def]
  have hbot :
      ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α)) <= Rep_domF SF :=
    order_pair_def.mpr
      ⟨BOT_is_bottom_domT, fun sX hsX => False.elim ((memF_empF (sX := sX)) hsX)⟩
  simpa [BOT_in_domF] using hbot

/-
(***********************************************************
                   operators on domF
 ***********************************************************)
-/

def pairF (T : domTType α) (F : setFType α) : domFType α :=
  Abs_domF (T, F)

infixr:52 " ,, " => pairF

def fstF (SF : domFType α) : domTType α :=
  Prod.fst (Rep_domF SF)

def sndF (SF : domFType α) : setFType α :=
  Prod.snd (Rep_domF SF)

/-
(***********************************************************
                     pairSF lemmas
 ***********************************************************)
-/

theorem fold_fstF {SF : domFType α} :
    Prod.fst (Rep_domF SF) = fstF SF :=
  rfl

theorem fold_sndF {SF : domFType α} :
    Prod.snd (Rep_domF SF) = sndF SF :=
  rfl

theorem pairF_fstF {S : domTType α} {F : setFType α}
    (hSF : (S, F) ∈ domF (α := α)) :
    fstF (S ,, F) = S := by
  simp [pairF, fstF, hSF]

theorem pairF_sndF {S : domTType α} {F : setFType α}
    (hSF : (S, F) ∈ domF (α := α)) :
    sndF (S ,, F) = F := by
  simp [pairF, sndF, hSF]

theorem eqF_decompo {SF SE : domFType α} :
    SF = SE ↔ (fstF SF = fstF SE ∧ sndF SF = sndF SE) := by
  constructor
  · intro h
    cases h
    simp [fstF, sndF]
  · intro h
    apply (Rep_domF_inject).mp
    exact Prod.ext h.1 h.2

theorem mono_fstF {α : Type u} : mono (fstF (α := α)) := by
  intro SF SE hSE
  exact (order_pair_def.mp (subdomF_def.mp hSE)).1

theorem mono_sndF {α : Type u} : mono (sndF (α := α)) := by
  intro SF SE hSE
  exact (order_pair_def.mp (subdomF_def.mp hSE)).2

/-
(*********************************************************
           Healthiness conditions for pairF
 *********************************************************)
-/

theorem pairF_domF_T2 {SF : domFType α} (hsX : (s, X) :f sndF SF) :
    memT s (fstF SF) := by
  cases SF with
  | mk SF hSF =>
      simpa [fstF, sndF, Rep_domF] using
        (domF_T2 (T := SF.1) (F := SF.2) hSF hsX)

theorem pairF_domF_T3 {SF : domFType α}
    (hTick : memT (s ^^^ Tickt (α := α)) (fstF SF)) (hNo : noTick s) :
    (s ^^^ Tickt (α := α), X) :f sndF SF := by
  cases SF with
  | mk SF hSF =>
      simpa [fstF, sndF, Rep_domF] using
        (domF_T3 (T := SF.1) (F := SF.2) hSF hTick hNo)

theorem pairF_domF_T3_Tick {SF : domFType α}
    (hTick : memT (Tickt (α := α)) (fstF SF)) :
    (Tickt (α := α), X) :f sndF SF := by
  have hTick' : memT (<> ^^^ Tickt (α := α)) (fstF SF) := by
    simpa using hTick
  simpa using pairF_domF_T3 (SF := SF) (s := <>) (X := X) hTick' noTick_nil

theorem pairF_domF_F4 {SF : domFType α}
    (hTick : memT (s ^^^ Tickt (α := α)) (fstF SF)) (hNo : noTick s) :
    (s, Evset) :f sndF SF := by
  cases SF with
  | mk SF hSF =>
      simpa [fstF, sndF, Rep_domF] using
        (domF_F4 (T := SF.1) (F := SF.2) hSF hTick hNo)

theorem pairF_domF_F3 {SF : domFType α}
    (hsX : (s, X) :f sndF SF) (hNo : noTick s)
    (hY : ∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) (fstF SF)) :
    (s, X ∪ Y) :f sndF SF := by
  cases SF with
  | mk SF hSF =>
      simpa [fstF, sndF, Rep_domF] using
        (domF_F3 (T := SF.1) (F := SF.2) hSF hsX hNo hY)

theorem pairF_domF_F3I {SF : domFType α}
    (hsX : (s, X) :f sndF SF) (hNo : noTick s)
    (hY : ∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) (fstF SF)) (hZ : Z = X ∪ Y) :
    (s, Z) :f sndF SF := by
  simpa [hZ] using pairF_domF_F3 (SF := SF) hsX hNo hY

/- (*** F2_F4 ***) -/

theorem pairF_domF_F2_F4 {SF : domFType α}
    (hTick : memT (s ^^^ Tickt (α := α)) (fstF SF)) (hNo : noTick s) (hX : X ⊆ Evset) :
    (s, X) :f sndF SF := by
  exact memF_F2 (pairF_domF_F4 (SF := SF) hTick hNo) hX

/- (*** T2_T3 ***) -/

theorem pairF_domF_T2_T3 {SF : domFType α}
    (hsX : (s ^^^ Tickt (α := α), X) :f sndF SF) (hNo : noTick s) :
    (s ^^^ Tickt (α := α), Y) :f sndF SF := by
  exact pairF_domF_T3 (SF := SF) (X := Y) (pairF_domF_T2 (SF := SF) hsX) hNo

/-
(*********************************************************
                     fstF and sndF
 *********************************************************)
-/

@[simp]
theorem fstF_sndF_in_domF {SF : domFType α} :
    (fstF SF, sndF SF) ∈ domF (α := α) := by
  cases SF with
  | mk SF hSF =>
      simpa [fstF, sndF, Rep_domF] using hSF

@[simp]
theorem fstF_sndF_domF (SF : domFType α) :
    (fstF SF ,, sndF SF) = SF := by
  apply (Rep_domF_inject).mp
  simp [pairF, fstF, sndF]

/-
(*********************************************************
                      subdomF
 *********************************************************)
-/

theorem subdomF_decompo {SF SE : domFType α} :
    (SF <= SE) ↔ (fstF SF <= fstF SE ∧ sndF SF <= sndF SE) := by
  simpa [subdomF_def, fstF, sndF] using (order_pair_def (xc := Rep_domF SF) (yc := Rep_domF SE))

/-
(*********************************************************
                define max F from T
 *********************************************************)
-/

def maxFof (T : domTType α) : setFType α :=
  Abs_setF {f | ∃ s, (∃ X, f = (s, X)) ∧ memT s T}

theorem maxFof_def {T : domTType α} :
    maxFof T = Abs_setF {f | ∃ s, (∃ X, f = (s, X)) ∧ memT s T} :=
  rfl

/- (* in setF *) -/

theorem maxFof_setF {T : domTType α} :
    ({f : failure α | ∃ s, (∃ X, f = (s, X)) ∧ memT s T} : Set (failure α)) ∈ setF (α := α) := by
  intro s X Y hs _
  rcases hs with ⟨s', hs'⟩
  rcases hs' with ⟨⟨X', hEq⟩, hsT⟩
  cases hEq
  exact ⟨s, ⟨Y, rfl⟩, hsT⟩

/- (* in maxFof *) -/

theorem in_maxFof {T : domTType α} {f : failure α} :
    (f :f maxFof T) ↔ ∃ s, (∃ X, f = (s, X)) ∧ memT s T := by
  change f ∈ Rep_setF (Abs_setF {f | ∃ s, (∃ X, f = (s, X)) ∧ memT s T}) ↔
    ∃ s, (∃ X, f = (s, X)) ∧ memT s T
  rw [Abs_setF_inverse (F := {f | ∃ s, (∃ X, f = (s, X)) ∧ memT s T}) maxFof_setF]
  rfl

/- (* in domF *) -/

theorem maxFof_domF {T : domTType α} :
    (T, maxFof T) ∈ domF (α := α) := by
  apply (mem_domF_iff (SF := (T, maxFof T))).2
  constructor
  · intro s X hsX
    rcases (in_maxFof (T := T) (f := (s, X))).1 hsX with ⟨s', hs'⟩
    rcases hs' with ⟨⟨X', hEq⟩, hsT⟩
    cases hEq
    exact hsT
  constructor
  · intro s X Y hsX _ _
    rcases (in_maxFof (T := T) (f := (s, X))).1 hsX with ⟨s', hs'⟩
    rcases hs' with ⟨⟨X', hEq⟩, hsT⟩
    cases hEq
    exact (in_maxFof (T := T) (f := (s, X ∪ Y))).2 ⟨s, ⟨X ∪ Y, rfl⟩, hsT⟩
  · intro s hs
    have hsT : memT s T := by
      exact memT_prefix_closed hs.1 (prefix_appt_simp (s := s) (t := Tickt (α := α)) (Or.inl hs.2))
    constructor
    · exact (in_maxFof (T := T) (f := (s, Evset))).2 ⟨s, ⟨Evset, rfl⟩, hsT⟩
    · intro X
      exact (in_maxFof (T := T) (f := (s ^^^ Tickt (α := α), X))).2
        ⟨s ^^^ Tickt (α := α), ⟨X, rfl⟩, hs.1⟩

/- (* max *) -/

theorem maxFof_max {T : domTType α} (hs : memT s T) :
    (s, X) :f maxFof T := by
  exact (in_maxFof (T := T) (f := (s, X))).2 ⟨s, ⟨X, rfl⟩, hs⟩

end
