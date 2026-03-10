           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Trace

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

/-
(***********************************************************
                 type def (Failure Part)
 ***********************************************************)
-/

abbrev failure (α : Type u) := traceType α × Set (event α)

def HC_F2 (F : Set (failure α)) : Prop :=
  ∀ s X Y, (s, X) ∈ F → Y ⊆ X → (s, Y) ∈ F

def setF : Set (Set (failure α)) := {F | HC_F2 F}

abbrev setFType (α : Type u) := {F : Set (failure α) // F ∈ setF (α := α)}

def Rep_setF (F : setFType α) : Set (failure α) := F.1

open Classical in
noncomputable def Abs_setF (F : Set (failure α)) : setFType α :=
  if h : F ∈ setF (α := α) then ⟨F, h⟩ else ⟨∅, by simp [setF, HC_F2]⟩

@[simp]
theorem Rep_setF_mk {F : Set (failure α)} {h : F ∈ setF (α := α)} :
    Rep_setF (Subtype.mk F h : setFType α) = F := rfl

@[simp]
theorem Abs_setF_inverse {F : Set (failure α)} (hF : F ∈ setF (α := α)) :
    Rep_setF (Abs_setF F) = F := by
  classical
  simp [Abs_setF, hF]

@[simp]
theorem Rep_setF_inverse (F : setFType α) : Abs_setF (Rep_setF F) = F := by
  classical
  cases F with
  | mk F hF =>
      simp [Abs_setF, hF]

theorem Rep_setF_inject {F E : setFType α} : Rep_setF F = Rep_setF E ↔ F = E := by
  constructor
  · intro h
    cases F
    cases E
    cases h
    rfl
  · intro h
    cases h
    rfl

instance : SetLike (setFType α) (failure α) where
  coe := Rep_setF
  coe_injective' := fun _ _ h => (Rep_setF_inject).mp h

/-
(***********************************************************
                   operators on setF
 ***********************************************************)
-/

def memF (x : failure α) (F : setFType α) : Prop := x ∈ Rep_setF F

infix:50 " :f " => memF
notation:50 x " ~:f " F => ¬ memF x F

def CollectF (P : failure α → Prop) : setFType α := Abs_setF {x | P x}

def UnionF (Fs : Set (setFType α)) : setFType α := Abs_setF (⋃₀ (Rep_setF '' Fs))

def InterF (Fs : Set (setFType α)) : setFType α := Abs_setF (⋂₀ (Rep_setF '' Fs))

def empF : setFType α := Abs_setF ∅

def UNIVF : setFType α := Abs_setF Set.univ

notation "{}f" => empF
notation "UNIVf" => UNIVF

def UnF (F E : setFType α) : setFType α := UnionF ({F, E} : Set (setFType α))

def IntF (F E : setFType α) : setFType α := InterF ({F, E} : Set (setFType α))

infixl:65 " UnF " => UnF
infixl:70 " IntF " => IntF

/-
(*********************************************************
          The relation (<=) is defined over setF
 *********************************************************)
-/

instance : LE (setFType α) where
  le F E := Rep_setF F ⊆ Rep_setF E

theorem subsetF_def {F E : setFType α} :
    F ≤ E ↔ Rep_setF F ⊆ Rep_setF E :=
  Iff.rfl

/-
(*********************************************************
          The relation (<=) is a partial order
 *********************************************************)
-/

instance : PartialOrder (setFType α) where
  le F E := Rep_setF F ⊆ Rep_setF E
  le_refl := by
    intro F
    exact Set.Subset.refl _
  le_trans := by
    intro F E G hFE hEG
    exact Set.Subset.trans hFE hEG
  le_antisymm := by
    intro F E hFE hEF
    apply (Rep_setF_inject).mp
    ext x
    constructor
    · intro hx
      exact hFE hx
    · intro hx
      exact hEF hx
theorem psubsetF_def {F E : setFType α} :
    LT.lt F E ↔ LT.lt (Rep_setF F) (Rep_setF E) :=
  Iff.rfl

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

theorem setF_F2 {F : Set (failure α)} (hF : F ∈ setF (α := α))
    (hmem : (s, X) ∈ F) (hYX : Y ⊆ X) :
    (s, Y) ∈ F := by
  exact hF s X Y hmem hYX

/- *** {} in setF *** -/

@[simp]
theorem emptyset_in_setF : (∅ : Set (failure α)) ∈ setF (α := α) := by
  simp [setF, HC_F2]

/-
(*******************************
         check in setF
 *******************************)
-/

/- *** [] (for STOP) *** -/

@[simp]
theorem nilt_in_setF :
    {u : failure α | u.1 = <> ∧ u.2 ⊆ EvsetTick} ∈ setF (α := α) := by
  intro s X Y hs hYX
  exact ⟨hs.1, Set.Subset.trans hYX hs.2⟩

/- *** [Tick] (for SKIP) *** -/

@[simp]
theorem nilt_Tick_in_setF :
    ({u : failure α | u.1 = <> ∧ u.2 ⊆ Evset} ∪
      {u : failure α | u.1 = Abs_trace [event.Tick] ∧ u.2 ⊆ EvsetTick}) ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs
  · exact Or.inl ⟨hs.1, Set.Subset.trans hYX hs.2⟩
  · exact Or.inr ⟨hs.1, Set.Subset.trans hYX hs.2⟩

/- *** Union *** -/

theorem setF_Union_in_setF {Fs : Set (setFType α)} :
    (⋃₀ (Rep_setF '' Fs) : Set (failure α)) ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases Set.mem_sUnion.mp hs with ⟨F, hFimg, hsF⟩
  rcases hFimg with ⟨F', hF', rfl⟩
  exact Set.mem_sUnion.mpr ⟨Rep_setF F', ⟨F', hF', rfl⟩, setF_F2 F'.2 hsF hYX⟩

/- *** Un *** -/

theorem setF_Un_in_setF {F E : setFType α} :
    (Rep_setF F ∪ Rep_setF E : Set (failure α)) ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs
  · exact Or.inl <| setF_F2 F.2 hs hYX
  · exact Or.inr <| setF_F2 E.2 hs hYX

/- *** Inter *** -/

theorem setF_Inter_in_setF {Fs : Set (setFType α)} :
    (⋂₀ (Rep_setF '' Fs) : Set (failure α)) ∈ setF (α := α) := by
  intro s X Y hs hYX
  rw [Set.mem_sInter] at hs ⊢
  intro A hA
  rcases hA with ⟨F, hF, rfl⟩
  exact setF_F2 F.2 (hs (Rep_setF F) ⟨F, hF, rfl⟩) hYX

/- *** Int *** -/

theorem setF_Int_in_setF {F E : setFType α} :
    (Rep_setF F ∩ Rep_setF E : Set (failure α)) ∈ setF (α := α) := by
  intro s X Y hs hYX
  exact ⟨setF_F2 F.2 hs.1 hYX, setF_F2 E.2 hs.2 hYX⟩

/-
The Isabelle lemma bundle `in_setF` is represented by the theorems
`setF_Union_in_setF`, `setF_Un_in_setF`, `setF_Inter_in_setF`, and `setF_Int_in_setF`.
-/

/-
(*******************************
     setF type --> set type
 *******************************)
-/

/- *** UnionF *** -/

theorem setF_UnionF_Rep {Fs : Set (setFType α)} :
    Rep_setF (UnionF Fs) = ⋃₀ (Rep_setF '' Fs) := by
  have hUnion : (⋃₀ (Rep_setF '' Fs) : Set (failure α)) ∈ setF (α := α) :=
    setF_Union_in_setF
  simpa [UnionF] using
    (Abs_setF_inverse (F := ⋃₀ (Rep_setF '' Fs)) hUnion)

/- *** UnF *** -/

theorem setF_UnF_Rep {F E : setFType α} :
    Rep_setF (F UnF E) = Rep_setF F ∪ Rep_setF E := by
  change Rep_setF (UnionF ({F, E} : Set (setFType α))) = Rep_setF F ∪ Rep_setF E
  ext x
  simp [setF_UnionF_Rep]

/- *** InterF *** -/

theorem setF_InterF_Rep {Fs : Set (setFType α)} :
    Rep_setF (InterF Fs) = ⋂₀ (Rep_setF '' Fs) := by
  have hInter : (⋂₀ (Rep_setF '' Fs) : Set (failure α)) ∈ setF (α := α) :=
    setF_Inter_in_setF
  simpa [InterF] using
    (Abs_setF_inverse (F := ⋂₀ (Rep_setF '' Fs)) hInter)

/- *** IntF *** -/

theorem setF_IntF_Rep {F E : setFType α} :
    Rep_setF (F IntF E) = Rep_setF F ∩ Rep_setF E := by
  change Rep_setF (InterF ({F, E} : Set (setFType α))) = Rep_setF F ∩ Rep_setF E
  ext x
  simp [setF_InterF_Rep]

/-
(*********************************************************
                       memF
 *********************************************************)
-/

/- memF_F2 -/

theorem memF_F2 (hmem : (s, X) :f F) (hYX : Y ⊆ X) :
    (s, Y) :f F := by
  exact setF_F2 F.2 hmem hYX

/- UnionF -/

theorem memF_UnionF_only_if {sX : failure α} {Fs : Set (setFType α)}
    (hsX : sX :f UnionF Fs) : ∃ F ∈ Fs, sX :f F := by
  simpa [memF, setF_UnionF_Rep] using hsX

theorem memF_UnionF_if {sX : failure α} {Fs : Set (setFType α)}
    {F : setFType α} (hF : F ∈ Fs) (hsX : sX :f F) : sX :f UnionF Fs := by
  rw [memF, setF_UnionF_Rep]
  exact Set.mem_sUnion.mpr ⟨Rep_setF F, ⟨F, hF, rfl⟩, hsX⟩

@[simp]
theorem memF_UnionF {sX : failure α} {Fs : Set (setFType α)} :
    sX :f UnionF Fs ↔ ∃ F ∈ Fs, sX :f F := by
  constructor
  · exact memF_UnionF_only_if
  · rintro ⟨F, hF, hsX⟩
    exact memF_UnionF_if hF hsX

/- InterF -/

theorem memF_InterF_only_if {sX : failure α} {Fs : Set (setFType α)}
    (hsX : sX :f InterF Fs) : ∀ F ∈ Fs, sX :f F := by
  rw [memF, setF_InterF_Rep, Set.mem_sInter] at hsX
  intro F hF
  exact hsX (Rep_setF F) ⟨F, hF, rfl⟩

theorem memF_InterF_if {sX : failure α} {Fs : Set (setFType α)}
    (hsX : ∀ F ∈ Fs, sX :f F) : sX :f InterF Fs := by
  rw [memF, setF_InterF_Rep, Set.mem_sInter]
  intro A hA
  rcases hA with ⟨F, hF, rfl⟩
  exact hsX F hF

@[simp]
theorem memF_InterF {sX : failure α} {Fs : Set (setFType α)} :
    sX :f InterF Fs ↔ ∀ F ∈ Fs, sX :f F := by
  constructor
  · exact memF_InterF_only_if
  · exact memF_InterF_if

/- empty -/

@[simp]
theorem memF_empF {sX : failure α} : sX ~:f {}f := by
  simp [memF, empF, Abs_setF_inverse]

/- pair -/

theorem memF_pair_iff : (f :f F) ↔ ∃ s X, f = (s, X) ∧ (s, X) :f F := by
  rcases f with ⟨s, X⟩
  constructor
  · intro hf
    exact ⟨s, X, rfl, hf⟩
  · rintro ⟨s', X', hEq, hsX⟩
    simpa [hEq] using hsX

theorem memF_pairI (h : ∃ s X, f = (s, X) ∧ (s, X) :f F) : f :f F := by
  exact (memF_pair_iff).2 h

theorem memF_pairE_lm {R : Prop} (hf : f :f F)
    (hR : (∃ s X, f = (s, X) ∧ (s, X) :f F) → R) : R := by
  exact hR ((memF_pair_iff).1 hf)

theorem memF_pairE {R : Prop} (hf : f :f F)
    (hR : ∀ s X, f = (s, X) → (s, X) :f F → R) : R := by
  rcases (memF_pair_iff).1 hf with ⟨s, X, hEq, hsX⟩
  exact hR s X hEq hsX

/-
(*********************************************************
                       subsetF
 *********************************************************)
-/

theorem subsetFI (hEF : ∀ s X, (s, X) :f E → (s, X) :f F) : E ≤ F := by
  intro x hx
  rcases x with ⟨s, X⟩
  exact hEF s X hx

theorem subsetFE {R : Prop} (hEF : E ≤ F)
    (hR : (∀ s X, (s, X) :f E → (s, X) :f F) → R) : R := by
  exact hR (fun s X hsX => hEF hsX)

theorem subsetFE_ALL {R : Prop} (hEF : E ≤ F)
    (hR : (∀ s X, (s, X) :f E → (s, X) :f F) → R) : R := by
  exact subsetFE hEF hR

theorem subsetF_iff : (E ≤ F) ↔ ∀ s X, (s, X) :f E → (s, X) :f F := by
  constructor
  · intro hEF s X hsX
    exact hEF hsX
  · intro hEF
    exact subsetFI hEF

/- *** {}f is bottom *** -/

@[simp]
theorem BOT_is_bottom_setF : {}f ≤ F := by
  intro x hx
  simp [empF] at hx

theorem memF_subsetF (hsX : (s, X) :f E) (hEF : E ≤ F) : (s, X) :f F := by
  exact hEF hsX

/-
(*********************************************************
                         UnF
 *********************************************************)
-/

theorem UnF_commut : E UnF F = F UnF E := by
  apply (Rep_setF_inject).mp
  ext x
  simp [setF_UnF_Rep, Set.union_comm]

theorem UnF_assoc : (E UnF F) UnF R = E UnF (F UnF R) := by
  apply (Rep_setF_inject).mp
  ext x
  simp [setF_UnF_Rep, Set.union_assoc]

theorem UnF_left_commut : E UnF (F UnF R) = F UnF (E UnF R) := by
  apply (Rep_setF_inject).mp
  ext x
  simp [setF_UnF_Rep, Set.union_left_comm]

/-
The Isabelle lemma bundle `UnF_rules` is represented by
`UnF_commut`, `UnF_assoc`, and `UnF_left_commut`.
-/

/-
(*********************************************************
                         IntF
 *********************************************************)
-/

theorem IntF_commut : E IntF F = F IntF E := by
  apply (Rep_setF_inject).mp
  ext x
  simp [setF_IntF_Rep, Set.inter_comm]

theorem IntF_assoc : (E IntF F) IntF R = E IntF (F IntF R) := by
  apply (Rep_setF_inject).mp
  ext x
  simp [setF_IntF_Rep, Set.inter_assoc]

theorem IntF_left_commut : E IntF (F IntF R) = F IntF (E IntF R) := by
  apply (Rep_setF_inject).mp
  ext x
  simp [setF_IntF_Rep, Set.inter_left_comm]

/-
The Isabelle lemma bundle `IntF_rules` is represented by
`IntF_commut`, `IntF_assoc`, and `IntF_left_commut`.
-/

/-
(*********************************************************
                         CollectT
 *********************************************************)
-/

/- *** open *** -/

@[simp]
theorem CollectF_open {F : setFType α} : CollectF (fun u => u :f F) = F := by
  apply (Rep_setF_inject).mp
  have hCollect : ({u : _root_.failure α | u :f F} : Set (_root_.failure α)) = Rep_setF F := by
    ext u
    rfl
  rw [CollectF, hCollect]
  simp

theorem CollectF_open_memF {P : _root_.failure α → Prop} {f : _root_.failure α}
    (hP : {f | P f} ∈ setF (α := α)) :
    f :f CollectF P ↔ P f := by
  simp [CollectF, memF, Abs_setF_inverse, hP]

/- *** implies {  }f *** -/

theorem set_CollectF_eq {Pr1 Pr2 : _root_.failure α → Prop}
    (hEq : {f : _root_.failure α | Pr1 f} = {f : _root_.failure α | Pr2 f}) :
    CollectF Pr1 = CollectF Pr2 := by
  simp [CollectF, hEq]

theorem CollectF_eq {Pr1 Pr2 : _root_.failure α → Prop}
    (hEq : ∀ f : _root_.failure α, Pr1 f = Pr2 f) :
    CollectF Pr1 = CollectF Pr2 := by
  apply set_CollectF_eq
  ext f
  simp [hEq f]

end
