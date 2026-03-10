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
