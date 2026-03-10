           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2013         |
            |                   June 2013  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_list
import LeanCspProver.CSP.Infra_order

open Function

/-
(*****************************************************
               Small lemmas for Set
 *****************************************************)
-/

theorem notin_subset {S T : Set α} {a : α} : S <= T → a ∉ T → a ∉ S := by
  intro hST haT haS
  exact haT (hST haS)

theorem notin_set_butlast {a : α} {s : List α} : a ∉ set s → a ∉ set (butlast s) := by
  exact notin_subset butlast_subseteq

theorem in_set_butlast {a : α} {s : List α} : a ∈ set (butlast s) → a ∈ set s := by
  intro ha
  exact butlast_subseteq ha

theorem in_image_set {f : α → β} {x : β} {X : Set α} :
    x ∈ f '' X ↔ ∃ y, x = f y ∧ y ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl, hy⟩
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y, hy, rfl⟩

theorem inj_image_diff_dist {f : α → β} (hf : Injective f) {A B : Set α} :
    f '' (A \ B) = f '' A \ f '' B := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, ?_⟩
    rintro ⟨z, hzB, hzEq⟩
    exact hyB (hf hzEq ▸ hzB)
  · rintro ⟨⟨y, hyA, rfl⟩, hxB⟩
    refine ⟨y, ⟨hyA, ?_⟩, rfl⟩
    intro hyB
    exact hxB ⟨y, hyB, rfl⟩

theorem inj_image_Int_dist {f : α → β} (hf : Injective f) {A B : Set α} :
    f '' (A ∩ B) = f '' A ∩ f '' B := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    exact ⟨⟨y, hyA, rfl⟩, ⟨y, hyB, rfl⟩⟩
  · rintro ⟨⟨y, hyA, hxy⟩, ⟨z, hzB, hxz⟩⟩
    have : y = z := hf (hxy.trans hxz.symm)
    subst this
    exact ⟨y, ⟨hyA, hzB⟩, hxy⟩

theorem subsetE {A B : Set α} {R : Prop} : A <= B → ((∀ x ∈ A, x ∈ B) → R) → R := by
  intro hAB hR
  exact hR (fun x hx => hAB hx)

theorem Un_sym {X Y : Set α} : X ∪ Y = Y ∪ X := by
  ext x
  simp [or_comm]

theorem Int_subset_eq {A B : Set α} : A <= B → A ∩ B = A := by
  intro hAB
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, hAB hx⟩

theorem Int_insert_eq {A : Set α} {x : α} : A ∩ Set.insert x A = A := by
  ext y
  constructor
  · intro hy
    exact hy.1
  · intro hy
    exact ⟨hy, Or.inr hy⟩

theorem in_Union_EX {x : α} {Xs : Set (Set α)} :
    x ∈ Set.sUnion Xs ↔ ∃ X, x ∈ X ∧ X ∈ Xs := by
  constructor
  · rintro ⟨X, hX, hxX⟩
    exact ⟨X, hxX, hX⟩
  · rintro ⟨X, hxX, hX⟩
    exact ⟨X, hX, hxX⟩

theorem subset_or_not_subset :
    ∀ A B : Set α,
      A <= B ∨ B <= A ∨ ∃ a b, a ∈ A ∧ a ∉ B ∧ b ∉ A ∧ b ∈ B := by
  intro A B
  by_cases hAB : A <= B
  · exact Or.inl hAB
  · by_cases hBA : B <= A
    · exact Or.inr <| Or.inl hBA
    · have hA : ∃ a, a ∈ A ∧ a ∉ B := by
        simpa [Set.not_subset] using hAB
      have hB : ∃ b, b ∈ B ∧ b ∉ A := by
        simpa [Set.not_subset] using hBA
      rcases hA with ⟨a, haA, haB⟩
      rcases hB with ⟨b, hbB, hbA⟩
      exact Or.inr <| Or.inr ⟨a, b, haA, haB, hbA, hbB⟩

theorem not_subset_iff {A B : Set α} :
    (¬ (A < B)) ↔ (B <= A ∨ ∃ a b, a ∈ A ∧ a ∉ B ∧ b ∉ A ∧ b ∈ B) := by
  constructor
  · intro h
    by_cases hBA : B <= A
    · exact Or.inl hBA
    · have hAB : ¬ A <= B := by
        intro hAB
        exact h ⟨hAB, hBA⟩
      rcases (show ∃ a, a ∈ A ∧ a ∉ B by simpa [Set.not_subset] using hAB) with ⟨a, haA, haB⟩
      rcases (show ∃ b, b ∈ B ∧ b ∉ A by simpa [Set.not_subset] using hBA) with ⟨b, hbB, hbA⟩
      exact Or.inr ⟨a, b, haA, haB, hbA, hbB⟩
  · rintro (hBA | ⟨a, b, haA, haB, hbA, hbB⟩) hAB
    · exact hAB.2 hBA
    · exact haB (hAB.1 haA)

theorem Union_snd_Un {f : α → β × Set γ} {I1 I2 : Set α} :
    Set.sUnion (Prod.snd '' (f '' (I1 ∪ I2))) =
      Set.sUnion (Prod.snd '' (f '' I1)) ∪ Set.sUnion (Prod.snd '' (f '' I2)) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
    rcases hX with ⟨p, hp, rfl⟩
    rcases hp with ⟨i, hi, rfl⟩
    cases hi with
    | inl hi =>
        exact Or.inl <| Set.mem_sUnion.mpr ⟨(f i).2, ⟨f i, ⟨i, hi, rfl⟩, rfl⟩, hxX⟩
    | inr hi =>
        exact Or.inr <| Set.mem_sUnion.mpr ⟨(f i).2, ⟨f i, ⟨i, hi, rfl⟩, rfl⟩, hxX⟩
  · intro hx
    rcases hx with hx | hx
    · rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
      rcases hX with ⟨p, hp, rfl⟩
      rcases hp with ⟨i, hi, rfl⟩
      exact Set.mem_sUnion.mpr ⟨(f i).2, ⟨f i, ⟨i, Or.inl hi, rfl⟩, rfl⟩, hxX⟩
    · rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
      rcases hX with ⟨p, hp, rfl⟩
      rcases hp with ⟨i, hi, rfl⟩
      exact Set.mem_sUnion.mpr ⟨(f i).2, ⟨f i, ⟨i, Or.inr hi, rfl⟩, rfl⟩, hxX⟩

theorem Union_snd_set_Un {s t : List (α × Set β)} :
    Set.sUnion (Prod.snd '' (set s ∪ set t)) =
      Set.sUnion (Prod.snd '' set s) ∪ Set.sUnion (Prod.snd '' set t) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
    rcases hX with ⟨p, hp, rfl⟩
    cases hp with
    | inl hp =>
        exact Or.inl <| Set.mem_sUnion.mpr ⟨p.2, ⟨p, hp, rfl⟩, hxX⟩
    | inr hp =>
        exact Or.inr <| Set.mem_sUnion.mpr ⟨p.2, ⟨p, hp, rfl⟩, hxX⟩
  · intro hx
    rcases hx with hx | hx
    · rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
      rcases hX with ⟨p, hp, rfl⟩
      exact Set.mem_sUnion.mpr ⟨p.2, ⟨p, Or.inl hp, rfl⟩, hxX⟩
    · rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
      rcases hX with ⟨p, hp, rfl⟩
      exact Set.mem_sUnion.mpr ⟨p.2, ⟨p, Or.inr hp, rfl⟩, hxX⟩

theorem neq_Set_EX1 {A B : Set α} : (∃ a, a ∈ A ∧ a ∉ B) → A ≠ B := by
  rintro ⟨a, haA, haB⟩ hEq
  exact haB (hEq ▸ haA)

theorem neq_Set_EX2 {A B : Set α} : (∃ a, a ∈ A ∧ a ∉ B) → B ≠ A := by
  rintro ⟨a, haA, haB⟩ hEq
  exact haB (hEq.symm ▸ haA)

/-
(*****************************
          finite set
 *****************************)
-/

theorem Union_index_fun {I1 : Set α} {f : α → β} {PXf1 : α → γ × Set δ} {PXf2 : β → γ × Set δ}
    (hPX : ∀ i ∈ I1, PXf2 (f i) = PXf1 i) :
    Set.sUnion (Prod.snd '' (PXf2 '' (f '' I1))) = Set.sUnion (Prod.snd '' (PXf1 '' I1)) := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
    rcases hX with ⟨p, hp, rfl⟩
    rcases hp with ⟨b, hb, rfl⟩
    rcases hb with ⟨i, hi, rfl⟩
    exact Set.mem_sUnion.mpr
      ⟨Prod.snd (PXf1 i), ⟨PXf1 i, ⟨i, hi, rfl⟩, rfl⟩, by simpa [hPX i hi] using hxX⟩
  · intro hx
    rcases Set.mem_sUnion.mp hx with ⟨X, hX, hxX⟩
    rcases hX with ⟨p, hp, rfl⟩
    rcases hp with ⟨i, hi, rfl⟩
    exact Set.mem_sUnion.mpr
      ⟨Prod.snd (PXf2 (f i)), ⟨PXf2 (f i), ⟨f i, ⟨i, hi, rfl⟩, rfl⟩, rfl⟩,
        by simpa [hPX i hi] using hxX⟩

theorem finite_pair_set1 {F1 : Set β} {F2 : β → Set α}
    (hF1 : F1.Finite) (hF2 : ∀ j ∈ F1, (F2 j).Finite) :
    {p : α × β | p.2 ∈ F1 ∧ p.1 ∈ F2 p.2}.Finite := by
  refine (hF1.biUnion fun j hj => (hF2 j hj).image (fun i => (i, j))).subset ?_
  intro p hp
  refine Set.mem_iUnion.mpr ?_
  refine ⟨p.2, Set.mem_iUnion.mpr ?_⟩
  refine ⟨hp.1, ?_⟩
  exact ⟨p.1, hp.2, by cases p; rfl⟩

theorem finite_pair_set2 {F1 : Set β} {F2 : β → Set α}
    (hF1 : F1.Finite) (hF2 : ∀ j ∈ F1, (F2 j).Finite) :
    {p : α × β | p.1 ∈ F2 p.2 ∧ p.2 ∈ F1}.Finite := by
  simpa [and_comm] using finite_pair_set1 hF1 hF2

theorem finite_pair_set {F1 : Set β} {F2 : β → Set α}
    (hF1 : F1.Finite) (hF2 : ∀ j ∈ F1, (F2 j).Finite) :
    {p : α × β | p.2 ∈ F1 ∧ p.1 ∈ F2 p.2}.Finite :=
  finite_pair_set1 hF1 hF2

theorem nonempty_finite_set_exists_max_fun_subset {I : Set α} {f : α → β} [Preorder β]
    (hI : I.Finite) (hNe : I ≠ ∅) :
    ∃ J, J <= I ∧ J ≠ ∅ ∧ ∀ j ∈ J, ∀ i ∈ I, ¬ f j < f i := by
  rcases hI.exists_maximalFor f I (Set.nonempty_iff_ne_empty.mpr hNe) with ⟨j, hj⟩
  refine ⟨{j}, by simp [hj.1], by simp, ?_⟩
  intro k hk i hi hlt
  have hk' : k = j := by simpa using hk
  subst hk'
  exact not_le_of_gt hlt (hj.2 hi hlt.le)

theorem nonempty_finite_set_exists_max_fun {I : Set α} {f : α → β} [Preorder β]
    (hI : I.Finite) (hNe : I ≠ ∅) :
    ∃ j ∈ I, ∀ i ∈ I, ¬ f j < f i := by
  rcases hI.exists_maximalFor f I (Set.nonempty_iff_ne_empty.mpr hNe) with ⟨j, hj⟩
  exact ⟨j, hj.1, fun i hi hlt => not_le_of_gt hlt (hj.2 hi hlt.le)⟩

theorem nonempty_finite_set_exists_min_fun_subset {I : Set α} {f : α → β} [Preorder β]
    (hI : I.Finite) (hNe : I ≠ ∅) :
    ∃ J, J <= I ∧ J ≠ ∅ ∧ ∀ j ∈ J, ∀ i ∈ I, ¬ f i < f j := by
  rcases hI.exists_minimalFor f I (Set.nonempty_iff_ne_empty.mpr hNe) with ⟨j, hj⟩
  refine ⟨{j}, by simp [hj.1], by simp, ?_⟩
  intro k hk i hi hlt
  have hk' : k = j := by simpa using hk
  subst hk'
  exact not_le_of_gt hlt (hj.2 hi hlt.le)

theorem nonempty_finite_set_exists_min_fun {I : Set α} {f : α → β} [Preorder β]
    (hI : I.Finite) (hNe : I ≠ ∅) :
    ∃ j ∈ I, ∀ i ∈ I, ¬ f i < f j := by
  rcases hI.exists_minimalFor f I (Set.nonempty_iff_ne_empty.mpr hNe) with ⟨j, hj⟩
  exact ⟨j, hj.1, fun i hi hlt => not_le_of_gt hlt (hj.2 hi hlt.le)⟩

/-
(*** cardinality of the set of a list ***)
-/

private theorem card_set_le_length {s : List α} : card (_root_.set s) <= s.length := by
  classical
  have htoFinset : (List.finite_toSet s).toFinset = s.toFinset := by
    ext x
    simp [_root_.set]
  calc
    card (_root_.set s) = (List.finite_toSet s).toFinset.card := by
      simpa [card] using (Set.ncard_eq_toFinset_card (_root_.set s) (List.finite_toSet s))
    _ = s.toFinset.card := by simpa [htoFinset]
    _ <= s.length := List.toFinset_card_le s

private theorem card_set_eq_length_iff_nodup {s : List α} : card (_root_.set s) = s.length ↔ s.Nodup := by
  classical
  induction s with
  | nil =>
      simp [card, _root_.set]
  | cons a s ih =>
      by_cases ha : a ∈ _root_.set s
      · constructor
        · intro hEq
          have hEq' : Set.ncard (Set.insert a (_root_.set s)) = s.length + 1 := by
            simpa [set_cons, card] using hEq
          have hInsert : Set.ncard (Set.insert a (_root_.set s)) = card (_root_.set s) := by
            simpa [card] using (Set.ncard_insert_of_mem ha : Set.ncard (Set.insert a (_root_.set s)) = Set.ncard (_root_.set s))
          rw [hInsert] at hEq'
          have hle : card (_root_.set s) <= s.length := card_set_le_length
          omega
        · intro hNodup
          exact False.elim ((List.not_nodup_cons_of_mem (by simpa using ha)) hNodup)
      · constructor
        · intro hEq
          have hs : card (_root_.set s) = s.length := by
            have hEq' : Set.ncard (Set.insert a (_root_.set s)) = s.length + 1 := by
              simpa [set_cons, card] using hEq
            have hInsert : Set.ncard (Set.insert a (_root_.set s)) = card (_root_.set s) + 1 := by
              simpa [card] using
                (Set.ncard_insert_of_notMem ha (List.finite_toSet s) :
                  Set.ncard (Set.insert a (_root_.set s)) = Set.ncard (_root_.set s) + 1)
            rw [hInsert] at hEq'
            omega
          exact List.Nodup.cons (by simpa using ha) (ih.mp hs)
        · intro hNodup
          have hs : card (_root_.set s) = s.length := ih.mpr hNodup.of_cons
          have : Set.ncard (Set.insert a (_root_.set s)) = s.length + 1 := by
            have hInsert : Set.ncard (Set.insert a (_root_.set s)) = card (_root_.set s) + 1 := by
              simpa [card] using
                (Set.ncard_insert_of_notMem ha (List.finite_toSet s) :
                  Set.ncard (Set.insert a (_root_.set s)) = Set.ncard (_root_.set s) + 1)
            simpa [hInsert, hs]
          simpa [set_cons, card] using this

private theorem nodup_iff_injective_nth [Inhabited α] {s : List α} :
    s.Nodup ↔ ∀ i, i < s.length → ∀ j, j < s.length → nth s i = nth s j → i = j := by
  constructor
  · intro h i hi j hj hij
    have hi' : i < s.length := hi
    have hj' : j < s.length := hj
    have hij' : s[i] = s[j] := by
      rw [← List.getD_eq_getElem (l := s) (d := default) hi',
        ← List.getD_eq_getElem (l := s) (d := default) hj']
      simpa [nth] using hij
    exact h.getElem_inj_iff.mp hij'
  · intro h
    refine List.nodup_iff_injective_getElem.mpr ?_
    intro i j hij
    apply Fin.ext
    exact h i.1 i.2 j.1 j.2 <| by
      rw [nth, List.getD_eq_getElem (l := s) (d := default) i.2,
        nth, List.getD_eq_getElem (l := s) (d := default) j.2]
      exact hij

theorem card_set_eq_length [Inhabited α] {s : List α} :
    (card (_root_.set s) = s.length) ↔
      (∀ i, i < s.length → ∀ j, j < s.length → nth s i = nth s j → i = j) := by
  rw [card_set_eq_length_iff_nodup, nodup_iff_injective_nth]

/-
(*****************************************************
   Small lemmas for isListOf (Finite Set <--> List)
 *****************************************************)
-/

def isListOf (s : List α) (X : Set α) : Prop :=
  X = _root_.set s ∧ card (_root_.set s) = s.length

theorem isListOf_EX {X : Set α} : X.Finite → ∃ s, isListOf s X := by
  intro hX
  classical
  refine ⟨hX.toFinset.toList, ?_⟩
  constructor
  · ext x
    simp [_root_.set]
  · exact card_set_eq_length_iff_nodup.mpr hX.toFinset.nodup_toList

theorem isListOf_set_eq {x : List α} {X : Set α} : isListOf x X → _root_.set x = X := by
  intro hx
  exact hx.1.symm

theorem set_SOME_isListOf {S : Set α} :
    S.Finite → _root_.set (SOME (fun t : List α => isListOf t S)) = S := by
  intro hS
  have hs : ∃ t : List α, isListOf t S := isListOf_EX hS
  exact isListOf_set_eq (chooseOrDefault_spec hs)

theorem isListOf_nonemptyset {X : Set α} {x : List α} : X ≠ ∅ → isListOf x X → x ≠ [] := by
  intro hX hx hNil
  apply hX
  rw [hx.1, hNil]
  simp

theorem isListOf_index_to_nth [Inhabited α] {Is : List α} {I : Set α} :
    isListOf Is I → ∀ i ∈ I, ∃ n, n < Is.length ∧ i = nth Is n := by
  intro hIs i hi
  have hi' : i ∈ _root_.set Is := by simpa [hIs.1] using hi
  exact set_nth.mp hi'

theorem isListOf_nth_in_index [Inhabited α] {Is : List α} {I : Set α} :
    isListOf Is I → ∀ {n}, n < Is.length → nth Is n ∈ I := by
  intro hIs n hn
  have hn' : nth Is n ∈ _root_.set Is := by
    exact (set_nth).mpr ⟨n, hn, rfl⟩
  simpa [hIs.1] using hn'

theorem isListOf_index_to_nthE [Inhabited α] {Is : List α} {I : Set α} {R : Prop} :
    isListOf Is I →
      (isListOf Is I →
        (∀ i ∈ I, ∃ n, n < Is.length ∧ i = nth Is n) → R) →
      R := by
  intro hIs hR
  exact hR hIs (isListOf_index_to_nth hIs)

theorem isListOf_nth_in_indexE [Inhabited α] {Is : List α} {I : Set α} {R : Prop} :
    isListOf Is I →
      (isListOf Is I → (∀ n, n < Is.length → nth Is n ∈ I) → R) →
      R := by
  intro hIs hR
  exact hR hIs fun n hn => isListOf_nth_in_index hIs hn

theorem isListOf_THE_nth [Inhabited α] {Is : List α} {I : Set α} {n : Nat} :
    isListOf Is I → n < Is.length →
      THE (fun m : Nat => nth Is m = nth Is n ∧ m < Is.length) = n := by
  intro hIs hn
  apply chooseOrDefault_eq
  · exact ⟨rfl, hn⟩
  · intro m hm
    exact (card_set_eq_length.mp hIs.2) m hm.2 n hn hm.1

@[simp]
theorem isListOf_emptyset_to_nil {Is : List α} : isListOf Is {} ↔ Is = [] := by
  constructor
  · intro hIs
    exact emptyset_to_nil.mp hIs.1
  · intro hIs
    subst hIs
    simp [isListOf, card, _root_.set]

@[simp]
theorem isListOf_nil_to_emptyset {X : Set α} : isListOf ([] : List α) X ↔ X = {} := by
  simp [isListOf, card, _root_.set]

theorem isListOf_oneset_to_onelist_ALL : ∀ t a, isListOf t ({a} : Set α) → t = [a] := by
  intro t a ht
  have hcard1 : card (_root_.set t) = 1 := by
    rw [← ht.1]
    simp [card]
  have hlen : t.length = 1 := by
    have : card (_root_.set t) = t.length := ht.2
    omega
  rcases list_length_one.mp hlen with ⟨b, rfl⟩
  have ha : a ∈ (_root_.set [b] : Set α) := by
    have : a ∈ ({a} : Set α) := by simp
    simpa [ht.1] using this
  have hab : a = b := by simpa [_root_.set] using ha
  simpa [hab]

@[simp]
theorem isListOf_oneset_to_onelist {t : List α} {a : α} :
    isListOf t ({a} : Set α) ↔ t = [a] := by
  constructor
  · exact isListOf_oneset_to_onelist_ALL t a
  · intro ht
    subst ht
    simp [isListOf, card, _root_.set]

@[simp]
theorem isListOf_onelist_to_oneset {a : α} {X : Set α} :
    isListOf ([a] : List α) X ↔ X = ({a} : Set α) := by
  constructor
  · intro hX
    simpa [_root_.set] using hX.1
  · intro hX
    subst hX
    simp [isListOf, card, _root_.set]

/- --------------------------------------------------- *
               addition for CSP-Prover 5
 * --------------------------------------------------- -/

/- --------------------------------------------------- *
   convenient lemmas for practical verification in CSP
 * --------------------------------------------------- -/

/- -------------------------------------------- *
                      in
 * -------------------------------------------- -/

theorem event_notin_channel_map {a : β} {c : α → β} {X : Set α} :
    (∀ x ∈ X, a ≠ c x) → a ∉ c '' X := by
  intro h x
  rcases x with ⟨y, hy, rfl⟩
  exact h y hy rfl

theorem event_in_channel_map_inj {c : α → β} {v : α} {X : Set α} (hc : Injective c) :
    (c v ∈ c '' X) ↔ v ∈ X := by
  constructor
  · rintro ⟨x, hx, hxv⟩
    have : x = v := hc hxv
    subst this
    exact hx
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem event_in_channel_map {c : α → β} {v : α} {X : Set α} :
    v ∈ X → c v ∈ c '' X := by
  intro hv
  exact ⟨v, hv, rfl⟩

theorem event_notin_channel_range {a : β} {c : α → β} :
    (∀ x, a ≠ c x) → a ∉ Set.range c := by
  intro h
  rintro ⟨x, rfl⟩
  exact h x rfl

theorem event_in_channel_range {c : α → β} {v : α} : c v ∈ Set.range c := by
  exact ⟨v, rfl⟩

/- -------------------------------------------- *
                        Int
 * -------------------------------------------- -/

theorem channel_Int_event_eq_map_left {c : α → β} {X : Set α} {v : α} (hc : Injective c) :
    (c '' X) ∩ ({c v} : Set β) = c '' (X ∩ ({v} : Set α)) := by
  ext x
  constructor
  · rintro ⟨⟨y, hyX, rfl⟩, hxv⟩
    have hyv : y = v := hc hxv
    subst y
    exact ⟨v, by simp [hyX], rfl⟩
  · rintro ⟨y, ⟨hyX, hyv⟩, rfl⟩
    have : y = v := by simpa using hyv
    subst y
    exact ⟨⟨v, hyX, rfl⟩, by simp⟩

theorem channel_Int_event_eq_map_right {c : α → β} {X : Set α} {v : α} (hc : Injective c) :
    ({c v} : Set β) ∩ (c '' X) = c '' (({v} : Set α) ∩ X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxv, ⟨y, hyX, hyEq⟩⟩
    have hxEq : x = c v := by simpa using hxv
    have hyv : y = v := hc (hyEq.trans hxEq)
    subst y
    exact ⟨v, by simp [hyX, hxEq]⟩
  · intro hx
    rcases hx with ⟨y, ⟨hyv, hyX⟩, rfl⟩
    have : y = v := by simpa using hyv
    subst y
    exact ⟨by simp, ⟨v, hyX, rfl⟩⟩

theorem set_Int_single_in_left {A : Set α} {a : α} : a ∈ A → A ∩ ({a} : Set α) = {a} := by
  intro ha
  ext x
  simp [ha, eq_comm]

theorem set_Int_single_in_right {A : Set α} {a : α} : a ∈ A → ({a} : Set α) ∩ A = {a} := by
  intro ha
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, hx ▸ ha⟩

theorem set_Int_single_notin_left {A : Set α} {a : α} : a ∉ A → A ∩ ({a} : Set α) = {} := by
  intro ha
  ext x
  constructor <;> intro hx <;> aesop

theorem set_Int_single_notin_right {A : Set α} {a : α} : a ∉ A → ({a} : Set α) ∩ A = {} := by
  intro ha
  ext x
  constructor
  · intro hx
    have : x = a := by simpa using hx.1
    exact False.elim (ha (this ▸ hx.2))
  · intro hx
    exact False.elim hx

theorem channel_Int_channel_eq {c : α → β} {X Y : Set α} (hc : Injective c) :
    (c '' X) ∩ (c '' Y) = c '' (X ∩ Y) := by
  simpa using (inj_image_Int_dist hc (A := X) (B := Y)).symm

theorem channel_Int_channel_neq_map {a : α → γ} {b : β → γ} {X : Set α} {Y : Set β} :
    (∀ x ∈ X, ∀ y ∈ Y, a x ≠ b y) → (a '' X) ∩ (b '' Y) = {} := by
  intro h
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    exact False.elim (h x hx y hy hxy.symm)
  · intro hz
    exact False.elim hz

theorem channel_Int_channel_neq_range {a : α → γ} {b : β → γ} :
    (∀ x y, a x ≠ b y) → Set.range a ∩ Set.range b = {} := by
  intro h
  ext z
  constructor
  · rintro ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    exact False.elim (h x y hy.symm)
  · intro hz
    exact False.elim hz

/- -------------------------------------------- *
                        Un
 * -------------------------------------------- -/

theorem channel_Un_channel {c : α → β} {X Y : Set α} (hc : Injective c) :
    (c '' X) ∪ (c '' Y) = c '' (X ∪ Y) := by
  ext x
  constructor
  · rintro (hx | hy)
    · rcases hx with ⟨a, ha, rfl⟩
      exact ⟨a, Or.inl ha, rfl⟩
    · rcases hy with ⟨a, ha, rfl⟩
      exact ⟨a, Or.inr ha, rfl⟩
  · rintro ⟨a, (ha | ha), rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨a, ha, rfl⟩

/- -------------------------------------------- *
                  Insert Int
 * -------------------------------------------- -/

theorem event_insert_Int_event_left {A : Set α} {a b : α} :
    (a ≠ b ∨ b ≠ a) → (Set.insert a A) ∩ ({b} : Set α) = A ∩ ({b} : Set α) := by
  intro hne
  have hab : a ≠ b := by
    cases hne with
    | inl hab => exact hab
    | inr hba => exact fun hab => hba hab.symm
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxL, hxR⟩
    have hxb : x = b := by simpa using hxR
    have hxA : x ∈ A := by
      rcases hxL with rfl | hxA
      · exact False.elim (hab hxb)
      · exact hxA
    exact ⟨hxA, hxR⟩
  · intro hx
    exact ⟨Or.inr hx.1, hx.2⟩

theorem event_insert_Int_event_right {A : Set α} {a b : α} :
    (a ≠ b ∨ b ≠ a) → ({b} : Set α) ∩ Set.insert a A = ({b} : Set α) ∩ A := by
  intro hne
  have hab : a ≠ b := by
    cases hne with
    | inl hab => exact hab
    | inr hba => exact fun hab => hba hab.symm
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxL, hxR⟩
    have hxb : x = b := by simpa using hxL
    have hxA : x ∈ A := by
      rcases hxR with rfl | hxA
      · subst x
        exact False.elim (hab hxb)
      · exact hxA
    exact ⟨hxL, hxA⟩
  · intro hx
    exact ⟨hx.1, Or.inr hx.2⟩

theorem event_insert_Int_channel_notin_left {A B : Set α} {a : α} :
    a ∉ B → Set.insert a A ∩ B = A ∩ B := by
  intro ha
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨hxL, hxR⟩
    have hxA : x ∈ A := by
      rcases hxL with rfl | hxA
      · exact False.elim (ha hxR)
      · exact hxA
    exact ⟨hxA, hxR⟩
  · exact ⟨Or.inr hx.1, hx.2⟩

theorem event_insert_Int_channel_notin_right {A B : Set α} {a : α} :
    a ∉ B → B ∩ Set.insert a A = B ∩ A := by
  intro ha
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxB, hxIns⟩
    have hxA : x ∈ A := by
      rcases hxIns with rfl | hxA
      · exact False.elim (ha hxB)
      · exact hxA
    exact ⟨hxB, hxA⟩
  · intro hx
    exact ⟨hx.1, Or.inr hx.2⟩

theorem event_insert_Int_channel_in_left {A B : Set α} {a : α} :
    a ∈ B → Set.insert a A ∩ B = Set.insert a (A ∩ B) := by
  intro ha
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨hxL, hxR⟩
    rcases hxL with rfl | hxA
    · exact Or.inl rfl
    · exact Or.inr ⟨hxA, hxR⟩
  · rcases hx with rfl | hx
    · exact ⟨Or.inl rfl, ha⟩
    · exact ⟨Or.inr hx.1, hx.2⟩

theorem event_insert_Int_channel_in_right {A B : Set α} {a : α} :
    a ∈ B → B ∩ Set.insert a A = Set.insert a (B ∩ A) := by
  intro ha
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxB, hxIns⟩
    rcases hxIns with rfl | hxA
    · exact Or.inl rfl
    · exact Or.inr ⟨hxB, hxA⟩
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨ha, Or.inl rfl⟩
    · exact ⟨hx.1, Or.inr hx.2⟩

theorem event_insert_Int_insert_channel_in {A B : Set α} {a b : α} :
    a ∈ B →
      Set.insert a A ∩ Set.insert b B = Set.insert a (A ∩ Set.insert b B) := by
  intro ha
  have ha' : a ∈ Set.insert b B := Or.inr ha
  exact event_insert_Int_channel_in_left (A := A) (B := Set.insert b B) ha'

theorem event_insert_Int_insert_channel_notin {A B : Set α} {a b : α} :
    (a ≠ b ∨ b ≠ a) → a ∉ B →
      Set.insert a A ∩ Set.insert b B = A ∩ Set.insert b B := by
  intro hne ha
  have hab : a ≠ b := by
    cases hne with
    | inl hab => exact hab
    | inr hba => exact fun hab => hba hab.symm
  have ha' : a ∉ Set.insert b B := by
    intro hx
    rcases hx with rfl | hx
    · exact hab rfl
    · exact ha hx
  exact event_insert_Int_channel_notin_left (A := A) (B := Set.insert b B) ha'

/- -------------------------------------------- *
                  Insert Un
 * -------------------------------------------- -/

theorem event_insert_in {A : Set α} {a : α} : a ∈ A → Set.insert a A = A := by
  intro ha
  exact Set.insert_eq_of_mem ha

/- -------------------------------------------- *
                     diff
 * -------------------------------------------- -/

theorem event_diff_in {A : Set α} {a : α} : a ∈ A → ({a} : Set α) \ A = {} := by
  intro ha
  ext x
  constructor
  · intro hx
    exact False.elim (hx.2 (hx.1 ▸ ha))
  · intro hx
    exact False.elim hx

theorem event_diff_notin {A : Set α} {a : α} : a ∉ A → ({a} : Set α) \ A = {a} := by
  intro ha
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hx
    exact ⟨hx, hx ▸ ha⟩

theorem event_diff_notin_map {c : α → β} {v : α} {X : Set α} :
    Injective c → v ∉ X → ({c v} : Set β) \ (c '' X) = {c v} := by
  intro hc hv
  have hcv : c v ∉ c '' X := by
    intro hmem
    exact hv ((event_in_channel_map_inj hc).mp hmem)
  exact event_diff_notin hcv

theorem channel_diff_eq_map {c : α → β} {X Y : Set α} :
    Injective c → (c '' X) \ (c '' Y) = c '' (X \ Y) := by
  intro hc
  exact (inj_image_diff_dist hc).symm

theorem channel_diff_neq_map {a : α → γ} {b : β → γ} {X : Set α} {Y : Set β} :
    (∀ x ∈ X, ∀ y ∈ Y, a x ≠ b y) → (a '' X) \ (b '' Y) = a '' X := by
  intro h
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    rintro ⟨y, hy, hyz⟩
    rcases hz with ⟨x, hx, hzx⟩
    exact h x hx y hy (hzx.trans hyz.symm)

theorem channel_diff_neq_range {a : α → γ} {b : β → γ} :
    (∀ x y, a x ≠ b y) → Set.range a \ Set.range b = Set.range a := by
  intro h
  ext z
  constructor
  · exact fun hz => hz.1
  · intro hz
    refine ⟨hz, ?_⟩
    rintro ⟨y, hy⟩
    rcases hz with ⟨x, hx⟩
    exact h x y (hx.trans hy.symm)

/- -------------------------------------------- *
                distribustion
 * -------------------------------------------- -/

theorem Un_diff_dist_right {A B C : Set α} : (A ∪ B) \ C = (A \ C) ∪ (B \ C) := by
  ext x
  constructor <;> intro hx <;> aesop

theorem Un_diff_dist_left {A B C : Set α} : C \ (A ∪ B) = (C \ A) ∩ (C \ B) := by
  ext x
  constructor <;> intro hx <;> aesop

theorem insert_diff_dist_right_in {A C : Set α} {a : α} :
    a ∈ C → Set.insert a A \ C = A \ C := by
  intro ha
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨hxL, hxR⟩
    rcases hxL with rfl | hxA
    · exact False.elim (hxR ha)
    · exact ⟨hxA, hxR⟩
  · exact ⟨Or.inr hx.1, hx.2⟩

theorem insert_diff_dist_right_notin {A C : Set α} {a : α} :
    a ∉ C → Set.insert a A \ C = ({a} : Set α) ∪ (A \ C) := by
  intro ha
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨hxL, hxR⟩
    rcases hxL with rfl | hxA
    · exact Or.inl rfl
    · exact Or.inr ⟨hxA, hxR⟩
  · rcases hx with rfl | hx
    · exact ⟨Or.inl rfl, by simpa using ha⟩
    · exact ⟨Or.inr hx.1, hx.2⟩

theorem insert_diff_dist_left_eq_event {A : Set α} {a : α} :
    ({a} : Set α) \ Set.insert a A = {} := by
  ext x
  constructor <;> intro hx
  · exact False.elim (hx.2 (Or.inl hx.1))
  · exact False.elim hx

theorem insert_diff_dist_left_eq_map {c : α → β} {X : Set α} {v : α} {A : Set β} :
    Injective c →
      (c '' X) \ Set.insert (c v) A = (c '' (X \ {v})) ∩ ((c '' X) \ A) := by
  intro hc
  rw [inj_image_diff_dist hc]
  have hsingle : c '' ({v} : Set α) = ({c v} : Set β) := by
    ext x
    simp
  rw [hsingle]
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxX, hxIns⟩
    have hxNe : x ≠ c v := by
      intro hxEq
      exact hxIns (hxEq ▸ Or.inl rfl)
    have hxA : x ∉ A := by
      intro hxA
      exact hxIns (Or.inr hxA)
    exact ⟨⟨hxX, by simpa [hxNe]⟩, hxX, hxA⟩
  · intro hx
    rcases hx with ⟨hxDiff, hxX, hxA⟩
    refine ⟨hxX, ?_⟩
    intro hxIns
    cases hxIns with
    | inl hxEq =>
        exact hxDiff.2 (by simpa [hxEq])
    | inr hxInA =>
        exact hxA hxInA

theorem insert_diff_dist_left_eq_range {c : α → β} {v : α} {A : Set β} :
    Injective c →
      Set.range c \ Set.insert (c v) A =
        (c '' ((Set.univ : Set α) \ {v})) ∩ (Set.range c \ A) := by
  intro hc
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, hxIns⟩
    have hyNe : y ≠ v := by
      intro hyEq
      exact hxIns (Or.inl (hyEq ▸ rfl))
    have hxA : c y ∉ A := by
      intro hxA
      exact hxIns (Or.inr hxA)
    exact ⟨⟨y, ⟨by trivial, by simpa [hyNe]⟩, rfl⟩, ⟨⟨y, rfl⟩, hxA⟩⟩
  · rintro ⟨⟨y, ⟨_, hyNe⟩, rfl⟩, ⟨hyRange, hxA⟩⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    intro hxIns
    rcases hxIns with hxEq | hxA'
    · exact hyNe (hc hxEq)
    · exact hxA hxA'

theorem insert_diff_dist_left_neq_event {A : Set α} {a b : α} :
    (a ≠ b ∨ b ≠ a) → ({a} : Set α) \ Set.insert b A = ({a} : Set α) \ A := by
  intro hne
  have hab : a ≠ b := by
    cases hne with
    | inl hab => exact hab
    | inr hba => exact fun hab => hba hab.symm
  ext x
  constructor <;> intro hx
  · rcases hx with ⟨hxL, hxR⟩
    refine ⟨hxL, ?_⟩
    intro hxA
    exact hxR (Or.inr hxA)
  · rcases hx with ⟨hxL, hxR⟩
    refine ⟨hxL, ?_⟩
    intro hxBA
    rcases hxBA with rfl | hxA
    · exact hab (by simpa using hxL.symm)
    · exact hxR hxA

theorem insert_diff_dist_left_neq {X A : Set α} {a : α} :
    a ∉ X → X \ Set.insert a A = X \ A := by
  intro ha
  ext x
  constructor <;> intro hx
  · exact ⟨hx.1, fun hxA => hx.2 (Or.inr hxA)⟩
  · exact ⟨hx.1, fun hxIns =>
      match hxIns with
      | Or.inl hEq => ha (hEq ▸ hx.1)
      | Or.inr hxA => hx.2 hxA⟩

/- Isabelle lemma bundles such as `event_notin_channel`, `channel_Int_event`,
   `channel_Int_channel`, `event_insert_Int`, `event_diff`, `channel_diff`,
   `event_insert_diff_dist`, `dist_event_set`, and `simp_event_set` do not have a
   direct Lean analogue. Later proofs should reference the constituent lemmas
   above explicitly. -/
