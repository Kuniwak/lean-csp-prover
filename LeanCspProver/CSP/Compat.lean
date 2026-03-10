import Mathlib

/-
Compatibility definitions for Isabelle/HOL list operations that do not exist
under the same names in Lean.
-/

def set (s : List α) : Set α := { x | x ∈ s }

@[simp]
theorem mem_set {a : α} {s : List α} : a ∈ set s ↔ a ∈ s :=
  Iff.rfl

@[simp]
theorem set_nil : set ([] : List α) = (∅ : Set α) := by
  ext x
  simp [_root_.set]

@[simp]
theorem set_cons (a : α) (s : List α) : set (a :: s) = Set.insert a (set s) := by
  ext x
  constructor <;> intro hx <;> simpa [_root_.set] using hx

abbrev tl : List α → List α := List.tail

abbrev butlast : List α → List α := List.dropLast

def nth [Inhabited α] (s : List α) (i : Nat) : α :=
  s.getD i default

@[simp]
theorem nth_nil [Inhabited α] (i : Nat) : nth ([] : List α) i = default := by
  simp [nth]

@[simp]
theorem nth_cons_zero [Inhabited α] (a : α) (s : List α) : nth (a :: s) 0 = a := by
  simp [nth]

@[simp]
theorem nth_cons_succ [Inhabited α] (a : α) (s : List α) (i : Nat) :
    nth (a :: s) (i + 1) = nth s i := by
  simp [nth]

/-
Compatibility definition for Isabelle/HOL's use of `THE ... else the None`.
Lean needs an explicit default inhabitant for the undefined branch.
-/
noncomputable def chooseOrDefault {α : Type _} [Inhabited α] (p : α → Prop) : α :=
  by
    classical
    exact if h : ∃ x, p x then Classical.choose h else default

theorem chooseOrDefault_spec {α : Type _} [Inhabited α] {p : α → Prop} (h : ∃ x, p x) :
    p (chooseOrDefault p) := by
  classical
  unfold chooseOrDefault
  simpa [h] using Classical.choose_spec h

theorem chooseOrDefault_eq {α : Type _} [Inhabited α] {p : α → Prop} {x : α}
    (hx : p x) (_huniq : ∀ y, p y → y = x) :
    chooseOrDefault p = x := by
  classical
  let h : ∃ y, p y := ⟨x, hx⟩
  simpa [chooseOrDefault, h] using _huniq (Classical.choose h) (Classical.choose_spec h)

abbrev mono {α : Type _} {β : Type _} [Preorder α] [Preorder β] (f : α → β) : Prop :=
  Monotone f

theorem mono_def {α : Type _} {β : Type _} [Preorder α] [Preorder β] {f : α → β} :
    mono f ↔ ∀ ⦃x y : α⦄, x <= y → f x <= f y :=
  Iff.rfl

noncomputable abbrev card (X : Set α) : Nat :=
  Set.ncard X

noncomputable abbrev SOME {α : Type _} [Inhabited α] (p : α → Prop) : α :=
  chooseOrDefault p

noncomputable abbrev THE {α : Type _} [Inhabited α] (p : α → Prop) : α :=
  chooseOrDefault p
