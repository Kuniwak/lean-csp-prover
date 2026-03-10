           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Prefix

open Classical

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
                 type def (Trace Part)
 ***********************************************************)
-/

def HC_T1 (T : Set (traceType α)) : Prop :=
  T ≠ ∅ ∧ prefix_closed T

theorem HC_T1_def {T : Set (traceType α)} :
    HC_T1 T ↔ T ≠ ∅ ∧ prefix_closed T :=
  Iff.rfl

def domT : Set (Set (traceType α)) := {T | HC_T1 T}

theorem domT_def {T : Set (traceType α)} :
    T ∈ domT (α := α) ↔ HC_T1 T :=
  Iff.rfl

abbrev domTType (α : Type u) := {T : Set (traceType α) // T ∈ domT (α := α)}

def Rep_domT (T : domTType α) : Set (traceType α) := T.1

theorem HC_T1_nilt : HC_T1 ({<>} : Set (traceType α)) := by
  constructor
  · simp
  · intro s t hst
    rcases hst with ⟨ht, hp⟩
    simp at ht
    subst ht
    simpa [prefix_of_nil.mp hp]

noncomputable def Abs_domT (T : Set (traceType α)) : domTType α :=
  if h : T ∈ domT (α := α) then ⟨T, h⟩ else ⟨{<>}, by simpa [domT] using HC_T1_nilt (α := α)⟩

@[simp]
theorem Rep_domT_mk {T : Set (traceType α)} {h : T ∈ domT (α := α)} :
    Rep_domT (Subtype.mk T h : domTType α) = T := rfl

@[simp]
theorem Abs_domT_inverse {T : Set (traceType α)} (hT : T ∈ domT (α := α)) :
    Rep_domT (Abs_domT T) = T := by
  simp [Abs_domT, hT]

@[simp]
theorem Rep_domT_inverse (T : domTType α) : Abs_domT (Rep_domT T) = T := by
  cases T with
  | mk T hT =>
      simp [Abs_domT, hT]

theorem Rep_domT_inject {S T : domTType α} : Rep_domT S = Rep_domT T ↔ S = T := by
  constructor
  · intro h
    cases S
    cases T
    cases h
    rfl
  · intro h
    cases h
    rfl

instance : SetLike (domTType α) (traceType α) where
  coe := Rep_domT
  coe_injective' := fun _ _ h => (Rep_domT_inject).mp h

/-
(***********************************************************
                   operators on domT
 ***********************************************************)
-/

def memT (x : traceType α) (T : domTType α) : Prop := x ∈ Rep_domT T

infix:50 " :t " => memT
notation:50 x " ~:t " T => ¬ memT x T

def CollectT (P : traceType α → Prop) : domTType α := Abs_domT {x | P x}

def UnionT (Ts : Set (domTType α)) : domTType α := Abs_domT (⋃₀ (Rep_domT '' Ts))

def InterT (Ts : Set (domTType α)) : domTType α := Abs_domT (⋂₀ (Rep_domT '' Ts))

def empT : domTType α := Abs_domT ∅

def UNIVT : domTType α := Abs_domT Set.univ

notation "{}t" => empT
notation "UNIVt" => UNIVT

def UnT (T S : domTType α) : domTType α := UnionT ({T, S} : Set (domTType α))

def IntT (T S : domTType α) : domTType α := InterT ({T, S} : Set (domTType α))

infixl:65 " UnT " => UnT
infixl:70 " IntT " => IntT

/-
(*********************************************************
          The relation (<=) is defined over domT
 *********************************************************)
-/

instance : LE (domTType α) where
  le T S := Rep_domT T ⊆ Rep_domT S

theorem subdomT_def {T S : domTType α} :
    T ≤ S ↔ Rep_domT T ⊆ Rep_domT S :=
  Iff.rfl

theorem psubdomT_def {T S : domTType α} :
    LT.lt T S ↔ LT.lt (Rep_domT T) (Rep_domT S) :=
  Iff.rfl

/-
(*********************************************************
          The relation (<=) is a partial order
 *********************************************************)
-/

instance : PartialOrder (domTType α) where
  le T S := Rep_domT T ⊆ Rep_domT S
  le_refl := by
    intro T
    exact Set.Subset.refl _
  le_trans := by
    intro T S R hTS hSR
    exact Set.Subset.trans hTS hSR
  le_antisymm := by
    intro T S hTS hST
    apply (Rep_domT_inject).mp
    ext t
    constructor
    · intro ht
      exact hTS ht
    · intro ht
      exact hST ht

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

theorem domT_is_non_empty {T : Set (traceType α)} (hT : T ∈ domT (α := α)) :
    T ≠ ∅ := by
  simpa [domT, HC_T1] using hT.1

theorem domT_is_prefix_closed {T : Set (traceType α)} (hT : T ∈ domT (α := α)) :
    prefix_closed T := by
  simpa [domT, HC_T1] using hT.2

theorem domT_is_prefix_closed_unfold {T : Set (traceType α)}
    (hT : T ∈ domT (α := α)) (ht : t ∈ T) (hp : «prefix» s t) :
    s ∈ T := by
  exact prefix_closed_iff ht hp (domT_is_prefix_closed hT)

/- *** {<>} in domT *** -/

@[simp]
theorem nilt_set_in : ({<>} : Set (traceType α)) ∈ domT (α := α) := by
  simpa [domT] using HC_T1_nilt (α := α)

/- *** {<>, <a>} in domT *** -/

@[simp]
theorem one_t_set_in {a : event α} :
    (({<>} : Set (traceType α)) ∪ ({Abs_trace [a]} : Set (traceType α))) ∈ domT (α := α) := by
  change HC_T1 (({<>} : Set (traceType α)) ∪ ({Abs_trace [a]} : Set (traceType α)))
  constructor
  · intro hEmpty
    have hNil : <> ∈ (({<>} : Set (traceType α)) ∪ ({Abs_trace [a]} : Set (traceType α))) := by
      simp
    simpa [hEmpty] using hNil
  · intro s t hst
    rcases hst with ⟨ht, hp⟩
    simp only [Set.mem_union, Set.mem_singleton_iff] at ht ⊢
    rcases ht with rfl | rfl
    · left
      exact prefix_of_nil.mp hp
    · exact prefix_of_one.mp hp

/- <> is contained in all domT -/

theorem nilt_in_all_dom {T : Set (traceType α)} (hT : T ∈ domT (α := α)) :
    <> ∈ T := by
  have hne : ∃ t, t ∈ T := by
    by_contra hne
    apply domT_is_non_empty hT
    ext t
    constructor
    · intro ht
      exact False.elim (hne ⟨t, ht⟩)
    · intro ht
      cases ht
  rcases hne with ⟨t, ht⟩
  exact domT_is_prefix_closed_unfold hT ht nil_is_prefix

/-
(*******************************
        check in domT
 *******************************)
-/

/- *** Union *** -/

theorem domT_Union_in_domT {Ts : Set (domTType α)} (hTs : Ts ≠ ∅) :
    (⋃₀ (Rep_domT '' Ts) : Set (traceType α)) ∈ domT (α := α) := by
  change HC_T1 (⋃₀ (Rep_domT '' Ts))
  constructor
  · intro hEmpty
    have hne : ∃ T, T ∈ Ts := by
      by_contra hne
      apply hTs
      ext T
      constructor
      · intro hT
        exact False.elim (hne ⟨T, hT⟩)
      · intro hT
        cases hT
    rcases hne with ⟨T, hT⟩
    have hnil : <> ∈ ⋃₀ (Rep_domT '' Ts) := by
      exact Set.mem_sUnion.mpr ⟨Rep_domT T, ⟨T, hT, rfl⟩, nilt_in_all_dom T.2⟩
    simpa [hEmpty] using hnil
  · intro s t hst
    rcases Set.mem_sUnion.mp hst.1 with ⟨T', hT'img, ht⟩
    rcases hT'img with ⟨T, hT, rfl⟩
    exact Set.mem_sUnion.mpr ⟨Rep_domT T, ⟨T, hT, rfl⟩, domT_is_prefix_closed_unfold T.2 ht hst.2⟩

/- *** Un *** -/

theorem domT_Un_in_domT {T S : domTType α} :
    (Rep_domT T ∪ Rep_domT S : Set (traceType α)) ∈ domT (α := α) := by
  have hTs : ({T, S} : Set (domTType α)) ≠ ∅ := by
    intro hEmpty
    have hT : T ∈ ({T, S} : Set (domTType α)) := by simp
    simpa [hEmpty] using hT
  simpa using domT_Union_in_domT (Ts := ({T, S} : Set (domTType α))) hTs

/- *** Inter *** -/

theorem domT_Inter_in_domT {Ts : Set (domTType α)} :
    (⋂₀ (Rep_domT '' Ts) : Set (traceType α)) ∈ domT (α := α) := by
  change HC_T1 (⋂₀ (Rep_domT '' Ts))
  constructor
  · intro hEmpty
    have hnil : <> ∈ (⋂₀ (Rep_domT '' Ts) : Set (traceType α)) := by
      rw [Set.mem_sInter]
      intro A hA
      rcases hA with ⟨T, hT, rfl⟩
      exact nilt_in_all_dom T.2
    simpa [hEmpty] using hnil
  · intro s t hst
    rw [Set.mem_sInter] at hst ⊢
    intro A hA
    rcases hA with ⟨T, hT, rfl⟩
    exact domT_is_prefix_closed_unfold T.2 (hst.1 _ ⟨T, hT, rfl⟩) hst.2

/- *** Int *** -/

theorem domT_Int_in_domT {T S : domTType α} :
    (Rep_domT T ∩ Rep_domT S : Set (traceType α)) ∈ domT (α := α) := by
  simpa using domT_Inter_in_domT (Ts := ({T, S} : Set (domTType α)))

/- The Isabelle lemma bundle `in_domT` is represented by the theorems
   `domT_Union_in_domT`, `domT_Un_in_domT`, `domT_Inter_in_domT`, and
   `domT_Int_in_domT`. -/

/-
(*******************************
    domT type --> set type
 *******************************)
-/

/- *** UnionT *** -/

theorem domT_UnionT_Rep {Ts : Set (domTType α)} (hTs : Ts ≠ ∅) :
    Rep_domT (UnionT Ts) = ⋃₀ (Rep_domT '' Ts) := by
  simpa [UnionT] using Abs_domT_inverse (T := ⋃₀ (Rep_domT '' Ts)) (domT_Union_in_domT hTs)

/- *** UnT *** -/

theorem domT_UnT_Rep {T S : domTType α} :
    Rep_domT (T UnT S) = Rep_domT T ∪ Rep_domT S := by
  have hTs : ({T, S} : Set (domTType α)) ≠ ∅ := by
    intro hEmpty
    have hT : T ∈ ({T, S} : Set (domTType α)) := by simp
    simpa [hEmpty] using hT
  change Rep_domT (UnionT ({T, S} : Set (domTType α))) = Rep_domT T ∪ Rep_domT S
  rw [domT_UnionT_Rep hTs]
  ext t
  simp

/- *** InterT *** -/

theorem domT_InterT_Rep {Ts : Set (domTType α)} :
    Rep_domT (InterT Ts) = ⋂₀ (Rep_domT '' Ts) := by
  simpa [InterT] using Abs_domT_inverse (T := ⋂₀ (Rep_domT '' Ts)) (domT_Inter_in_domT (Ts := Ts))

/- *** IntT *** -/

theorem domT_IntT_Rep {T S : domTType α} :
    Rep_domT (T IntT S) = Rep_domT T ∩ Rep_domT S := by
  change Rep_domT (InterT ({T, S} : Set (domTType α))) = Rep_domT T ∩ Rep_domT S
  ext t
  simp [domT_InterT_Rep]

/-
(*********************************************************
                       memT
 *********************************************************)
-/

/- prefix closed -/

theorem memT_prefix_closed {t : traceType α} {T : domTType α}
    (ht : t :t T) (hp : «prefix» s t) : s :t T := by
  exact domT_is_prefix_closed_unfold T.2 ht hp

/- <> -/

@[simp]
theorem nilt_in_T {T : domTType α} : <> :t T := by
  exact nilt_in_all_dom T.2

/- UnionT -/

theorem memT_UnionT_only_if {Ts : Set (domTType α)} {t : traceType α}
    (hTs : Ts ≠ ∅) (ht : t :t UnionT Ts) : ∃ T ∈ Ts, t :t T := by
  simpa [memT, domT_UnionT_Rep hTs] using ht

theorem memT_UnionT_if {Ts : Set (domTType α)} {T : domTType α} {t : traceType α}
    (hT : T ∈ Ts) (ht : t :t T) : t :t UnionT Ts := by
  have hTs : Ts ≠ ∅ := by
    intro hEmpty
    exact (by simpa [hEmpty] using hT)
  rw [memT, domT_UnionT_Rep hTs]
  exact Set.mem_sUnion.mpr ⟨Rep_domT T, ⟨T, hT, rfl⟩, ht⟩

@[simp]
theorem memT_UnionT {Ts : Set (domTType α)} {t : traceType α} (hTs : Ts ≠ ∅) :
    t :t UnionT Ts ↔ ∃ T ∈ Ts, t :t T := by
  constructor
  · exact memT_UnionT_only_if hTs
  · rintro ⟨T, hT, ht⟩
    exact memT_UnionT_if hT ht

/- InterT -/

theorem memT_InterT_only_if {Ts : Set (domTType α)} {t : traceType α}
    (ht : t :t InterT Ts) : ∀ T ∈ Ts, t :t T := by
  rw [memT, domT_InterT_Rep, Set.mem_sInter] at ht
  intro T hT
  exact ht (Rep_domT T) ⟨T, hT, rfl⟩

theorem memT_InterT_if {Ts : Set (domTType α)} {t : traceType α}
    (ht : ∀ T ∈ Ts, t :t T) : t :t InterT Ts := by
  rw [memT, domT_InterT_Rep, Set.mem_sInter]
  intro A hA
  rcases hA with ⟨T, hT, rfl⟩
  exact ht T hT

@[simp]
theorem memT_InterT {Ts : Set (domTType α)} {t : traceType α} :
    t :t InterT Ts ↔ ∀ T ∈ Ts, t :t T := by
  constructor
  · exact memT_InterT_only_if
  · exact memT_InterT_if

/- <> -/

@[simp]
theorem memT_nilt {t : traceType α} :
    t :t (Abs_domT ({<>} : Set (traceType α))) ↔ t = <> := by
  simp [memT, Abs_domT, nilt_set_in]

/- [e]t, <> -/

@[simp]
theorem memT_nilt_one {t : traceType α} {a : event α} :
    t :t (Abs_domT (({<>} : Set (traceType α)) ∪ ({Abs_trace [a]} : Set (traceType α)))) ↔
      (t = <> ∨ t = Abs_trace [a]) := by
  have hPair :
      (({<>} : Set (traceType α)) ∪ ({Abs_trace [a]} : Set (traceType α))) ∈ domT (α := α) :=
    one_t_set_in (a := a)
  rw [memT, Abs_domT_inverse (T := (({<>} : Set (traceType α)) ∪ ({Abs_trace [a]} : Set (traceType α)))) hPair]
  simp only [Set.mem_union, Set.mem_singleton_iff]

/-
(*********************************************************
                       subdomT
 *********************************************************)
-/

theorem subdomTI {S T : domTType α} (hST : ∀ t, t :t S → t :t T) : S ≤ T := by
  intro t ht
  exact hST t ht

theorem subdomTE {R : Prop} {S T : domTType α} (hST : S ≤ T)
    (hR : (∀ t, t :t S → t :t T) → R) : R := by
  exact hR (fun t ht => hST ht)

theorem subdomTE_ALL {R : Prop} {S T : domTType α} (hST : S ≤ T)
    (hR : (∀ t, t :t S → t :t T) → R) : R := by
  exact subdomTE hST hR

theorem subdomT_iff {S T : domTType α} :
    S ≤ T ↔ ∀ t, t :t S → t :t T := by
  constructor
  · intro hST t ht
    exact hST ht
  · intro hST t ht
    exact hST t ht

/- *** {<>}t is bottom *** -/

@[simp]
theorem BOT_is_bottom_domT {T : domTType α} :
    (Abs_domT ({<>} : Set (traceType α))) ≤ T := by
  intro t ht
  have hEq : t = <> := memT_nilt.mp ht
  simpa [memT, hEq] using (nilt_in_T (T := T))

theorem memT_subdomT {t : traceType α} {S T : domTType α}
    (ht : t :t S) (hST : S ≤ T) : t :t T := by
  exact hST ht

/-
(*********************************************************
                         UnT
 *********************************************************)
-/

theorem UnT_commut {S T : domTType α} : S UnT T = T UnT S := by
  apply (Rep_domT_inject).mp
  ext t
  simp [domT_UnT_Rep, Set.union_comm]

theorem UnT_assoc {S T R : domTType α} : (S UnT T) UnT R = S UnT (T UnT R) := by
  apply (Rep_domT_inject).mp
  ext t
  simp [domT_UnT_Rep, Set.union_assoc]

theorem UnT_left_commut {S T R : domTType α} : S UnT (T UnT R) = T UnT (S UnT R) := by
  apply (Rep_domT_inject).mp
  ext t
  simp [domT_UnT_Rep, Set.union_left_comm]

/- The Isabelle lemma bundle `UnT_rules` is represented by
   `UnT_commut`, `UnT_assoc`, and `UnT_left_commut`. -/

@[simp]
theorem UnT_nilt_left {T : domTType α} :
    (Abs_domT ({<>} : Set (traceType α))) UnT T = T := by
  apply (Rep_domT_inject).mp
  ext t
  constructor
  · intro ht
    simp [domT_UnT_Rep] at ht
    rcases ht with ht | ht
    · simpa [memT, ht] using (nilt_in_T (T := T))
    · exact ht
  · intro ht
    simp [domT_UnT_Rep, ht]

@[simp]
theorem UnT_nilt_right {T : domTType α} :
    T UnT (Abs_domT ({<>} : Set (traceType α))) = T := by
  rw [UnT_commut, UnT_nilt_left]

/-
(*********************************************************
                         IntT
 *********************************************************)
-/

theorem IntT_commut {S T : domTType α} : S IntT T = T IntT S := by
  apply (Rep_domT_inject).mp
  ext t
  simp [domT_IntT_Rep, Set.inter_comm]

theorem IntT_assoc {S T R : domTType α} : (S IntT T) IntT R = S IntT (T IntT R) := by
  apply (Rep_domT_inject).mp
  ext t
  simp [domT_IntT_Rep, Set.inter_assoc]

theorem IntT_left_commut {S T R : domTType α} : S IntT (T IntT R) = T IntT (S IntT R) := by
  apply (Rep_domT_inject).mp
  ext t
  simp [domT_IntT_Rep, Set.inter_left_comm]

/- The Isabelle lemma bundle `IntT_rules` is represented by
   `IntT_commut`, `IntT_assoc`, and `IntT_left_commut`. -/

/-
(*********************************************************
                         CollectT
 *********************************************************)
-/

/- *** open *** -/

@[simp]
theorem CollectT_open {T : domTType α} : CollectT (fun u => u :t T) = T := by
  apply (Rep_domT_inject).mp
  have hCollect : ({u : traceType α | u :t T} : Set (traceType α)) = Rep_domT T := by
    ext u
    rfl
  rw [CollectT, hCollect]
  simp

theorem CollectT_open_memT {P : traceType α → Prop} {t : traceType α}
    (hP : {t | P t} ∈ domT (α := α)) :
    t :t CollectT P ↔ P t := by
  simp [CollectT, memT, Abs_domT, hP]

/- *** implies {  }t *** -/

theorem set_CollectT_eq {Pr1 Pr2 : traceType α → Prop}
    (hEq : {t : traceType α | Pr1 t} = {t : traceType α | Pr2 t}) :
    CollectT Pr1 = CollectT Pr2 := by
  simp [CollectT, hEq]

theorem CollectT_eq {Pr1 Pr2 : traceType α → Prop}
    (hEq : ∀ t : traceType α, Pr1 t = Pr2 t) :
    CollectT Pr1 = CollectT Pr2 := by
  apply set_CollectT_eq
  ext t
  simp [hEq t]

end
