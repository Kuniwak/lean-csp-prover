           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_fun

/-
(*****************************************************
              Infinite Sequence type
 *****************************************************)
-/

/- types 'a infinite_seq = "nat => 'a"   isabelle 2011   -/     /- synonym -/

abbrev infinite_seq (α : Type _) := Nat → α

/- synonym -/

/-
(**********************************************************
                      two types
 **********************************************************)
-/

inductive SumType (α : Type u) (β : Type v) where
  | type1 : α → SumType α β
  | type2 : β → SumType α β
deriving DecidableEq

abbrev sum (α : Type u) (β : Type v) := SumType α β

open SumType

/- lemmas -/

@[simp]
theorem inj_type1 : Function.Injective (@type1 α β) := by
  intro x y hxy
  cases hxy
  rfl

@[simp]
theorem inj_type2 : Function.Injective (@type2 α β) := by
  intro x y hxy
  cases hxy
  rfl

theorem type1_or_type2 : ∀ x : sum α β, (∃ b, x = type1 b) ∨ ∃ c, x = type2 c := by
  intro x
  cases x with
  | type1 b => exact Or.inl ⟨b, rfl⟩
  | type2 c => exact Or.inr ⟨c, rfl⟩

theorem P_inv_type1I [Inhabited α] {P : α → Prop} {y : α}
    (hP : ∀ x : sum α β, P (Function.invFun (@type1 α β) x)) : P y := by
  have hall : ∀ z : α, P z := (Pr1_inv_inj (f := @type1 α β) (Pr := P) inj_type1).mp hP
  exact hall y

theorem P_inv_type2I [Inhabited β] {P : β → Prop} {y : β}
    (hP : ∀ x : sum α β, P (Function.invFun (@type2 α β) x)) : P y := by
  have hall : ∀ z : β, P z := (Pr1_inv_inj (f := @type2 α β) (Pr := P) inj_type2).mp hP
  exact hall y

/- *** functions *** -/

def sumset : sum (Set α) (Set β) → Set (sum α β)
  | type1 X => type1 '' X
  | type2 X => type2 '' X

/- Isabelle leaves the other branch unspecified; Lean needs an explicit default. -/
def open1 [Inhabited α] : sum α β → α
  | type1 x => x
  | type2 _ => default

def open2 [Inhabited β] : sum α β → β
  | type1 _ => default
  | type2 x => x

def type1check : sum α β → Prop
  | type1 _ => True
  | type2 _ => False

def type2check : sum α β → Prop
  | type1 _ => False
  | type2 _ => True

def sum_type_eq_chk (x y : sum α β) : Prop := type1check x ↔ type1check y

infix:55 " =type= " => sum_type_eq_chk

def sum_cup : sum (Set α) (Set β) → sum (Set α) (Set β) → sum (Set α) (Set β)
  | type1 X, type1 Y => type1 (X ∪ Y)
  | type1 _, type2 _ => type1 ∅
  | type2 _, type1 _ => type1 ∅
  | type2 X, type2 Y => type2 (X ∪ Y)

def sum_cap : sum (Set α) (Set β) → sum (Set α) (Set β) → sum (Set α) (Set β)
  | type1 X, type1 Y => type1 (X ∩ Y)
  | type1 _, type2 _ => type1 ∅
  | type2 _, type1 _ => type1 ∅
  | type2 X, type2 Y => type2 (X ∩ Y)

infixl:65 " Uns " => sum_cup
infixl:65 " Ints " => sum_cap

/- lemmas -/

theorem type1_sumset_type1 {α : Type _} {β : Type _} {x : α} {X : Set α} :
    ((@type1 α β x) ∈ sumset (@type1 (Set α) (Set β) X) : Prop) ↔ x ∈ X := by
  simp [sumset]

theorem type2_sumset_type2 {α : Type _} {β : Type _} {x : β} {X : Set β} :
    ((@type2 α β x) ∈ sumset (@type2 (Set α) (Set β) X) : Prop) ↔ x ∈ X := by
  simp [sumset]

theorem P_inv_type1 [Inhabited α] {X : Set α} {P : α → Prop} {y : sum α β}
    (hP : ∀ x ∈ X, P x) (hy : y ∈ sumset (type1 X)) :
    P (Function.invFun (@type1 α β) y) := by
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Function.leftInverse_invFun inj_type1 x] using hP x hx

theorem P_inv_type2 [Inhabited β] {X : Set β} {P : β → Prop} {y : sum α β}
    (hP : ∀ x ∈ X, P x) (hy : y ∈ sumset (type2 X)) :
    P (Function.invFun (@type2 α β) y) := by
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Function.leftInverse_invFun inj_type2 x] using hP x hx

theorem mem_sumset_cup_lm {X Y : sum (Set α) (Set β)} {x : sum α β} :
    X =type= Y →
      ((x ∈ sumset (X Uns Y) : Prop) ↔ x ∈ sumset X ∨ x ∈ sumset Y) := by
  cases X with
  | type1 X =>
      cases Y with
      | type1 Y =>
          intro _
          constructor
          · rintro ⟨z, hz, rfl⟩
            rcases hz with hz | hz
            · exact Or.inl ⟨z, hz, rfl⟩
            · exact Or.inr ⟨z, hz, rfl⟩
          · intro hx
            rcases hx with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
            · exact ⟨z, Or.inl hz, rfl⟩
            · exact ⟨z, Or.inr hz, rfl⟩
      | type2 Y =>
          intro hXY
          simp [sum_type_eq_chk, type1check] at hXY
  | type2 X =>
      cases Y with
      | type1 Y =>
          intro hXY
          simp [sum_type_eq_chk, type1check] at hXY
      | type2 Y =>
          intro _
          constructor
          · rintro ⟨z, hz, rfl⟩
            rcases hz with hz | hz
            · exact Or.inl ⟨z, hz, rfl⟩
            · exact Or.inr ⟨z, hz, rfl⟩
          · intro hx
            rcases hx with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
            · exact ⟨z, Or.inl hz, rfl⟩
            · exact ⟨z, Or.inr hz, rfl⟩

@[simp]
theorem mem_sumset_cup {X Y : sum (Set α) (Set β)} {x : sum α β} :
    X =type= Y →
      ((x ∈ sumset (X Uns Y) : Prop) ↔ x ∈ sumset X ∨ x ∈ sumset Y) :=
  mem_sumset_cup_lm

theorem mem_sumset_cap_lm {X Y : sum (Set α) (Set β)} {x : sum α β} :
    X =type= Y →
      ((x ∈ sumset (X Ints Y) : Prop) ↔ x ∈ sumset X ∧ x ∈ sumset Y) := by
  cases X with
  | type1 X =>
      cases Y with
      | type1 Y =>
          intro _
          constructor
          · rintro ⟨z, ⟨hzX, hzY⟩, rfl⟩
            exact ⟨⟨z, hzX, rfl⟩, ⟨z, hzY, rfl⟩⟩
          · rintro ⟨⟨z, hzX, hzx⟩, ⟨w, hwY, hwx⟩⟩
            have hzw : z = w := inj_type1 (hzx.trans hwx.symm)
            subst hzw
            exact ⟨z, ⟨hzX, hwY⟩, hzx⟩
      | type2 Y =>
          intro hXY
          simp [sum_type_eq_chk, type1check] at hXY
  | type2 X =>
      cases Y with
      | type1 Y =>
          intro hXY
          simp [sum_type_eq_chk, type1check] at hXY
      | type2 Y =>
          intro _
          constructor
          · rintro ⟨z, ⟨hzX, hzY⟩, rfl⟩
            exact ⟨⟨z, hzX, rfl⟩, ⟨z, hzY, rfl⟩⟩
          · rintro ⟨⟨z, hzX, hzx⟩, ⟨w, hwY, hwx⟩⟩
            have hzw : z = w := inj_type2 (hzx.trans hwx.symm)
            subst hzw
            exact ⟨z, ⟨hzX, hwY⟩, hzx⟩

@[simp]
theorem mem_sumset_cap {X Y : sum (Set α) (Set β)} {x : sum α β} :
    X =type= Y →
      ((x ∈ sumset (X Ints Y) : Prop) ↔ x ∈ sumset X ∧ x ∈ sumset Y) :=
  mem_sumset_cap_lm

theorem sum_type1_or_type2 {x : sum α β} : type1check x ∨ type2check x := by
  cases x <;> simp [type1check, type2check]

/- *** sub set *** -/

def sub_sumset : sum (Set α) (Set β) → (sum α β → Prop) → sum (Set α) (Set β)
  | type1 X, f => type1 {x | x ∈ X ∧ f (type1 x)}
  | type2 X, f => type2 {x | x ∈ X ∧ f (type2 x)}

@[simp]
theorem sub_sumset_true {X : sum (Set α) (Set β)} :
    sub_sumset X (fun _ => True) = X := by
  cases X <;> simp [sub_sumset]

@[simp]
theorem sub_sumset_cup {X : sum (Set α) (Set β)} {f g : sum α β → Prop} :
    (sub_sumset X f Uns sub_sumset X g) = sub_sumset X (fun x => f x ∨ g x) := by
  cases X <;> simp [sub_sumset, sum_cup]

@[simp]
theorem sub_sumset_cap {X : sum (Set α) (Set β)} {f g : sum α β → Prop} :
    (sub_sumset X f Ints sub_sumset X g) = sub_sumset X (fun x => f x ∧ g x) := by
  cases X <;> simp [sub_sumset, sum_cap]

@[simp]
theorem sub_sumset_type_eq {X : sum (Set α) (Set β)} {f g : sum α β → Prop} :
    sub_sumset X f =type= sub_sumset X g := by
  cases X <;> simp [sum_type_eq_chk, sub_sumset, type1check]

@[simp]
theorem sumset_sub_sumset {X : sum (Set α) (Set β)} {f : sum α β → Prop} :
    sumset (sub_sumset X f) = {x | x ∈ sumset X ∧ f x} := by
  ext x
  cases X <;> cases x <;> simp [sumset, sub_sumset]

theorem sub_sumset_eq_lm {C : sum (Set α) (Set β)} {f g : sum α β → Prop} :
    (∀ c ∈ sumset C, f c = g c) → sub_sumset C f = sub_sumset C g := by
  intro hfg
  cases C with
  | type1 X =>
      apply congrArg type1
      ext x
      constructor <;> intro hx
      · refine ⟨hx.1, ?_⟩
        have hEq := hfg (type1 x) (by simpa [sumset] using hx.1)
        simpa [hEq] using hx.2
      · refine ⟨hx.1, ?_⟩
        have hEq := hfg (type1 x) (by simpa [sumset] using hx.1)
        simpa [hEq] using hx.2
  | type2 X =>
      apply congrArg type2
      ext x
      constructor <;> intro hx
      · refine ⟨hx.1, ?_⟩
        have hEq := hfg (type2 x) (by simpa [sumset] using hx.1)
        simpa [hEq] using hx.2
      · refine ⟨hx.1, ?_⟩
        have hEq := hfg (type2 x) (by simpa [sumset] using hx.1)
        simpa [hEq] using hx.2

theorem sub_sumset_eq {C : sum (Set α) (Set β)} {f g : sum α β → Prop} :
    (∀ c ∈ sumset C, f c = g c) → sub_sumset C f = sub_sumset C g :=
  sub_sumset_eq_lm
