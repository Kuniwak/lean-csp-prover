           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2007         |
            |                January 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_order

open Function

noncomputable section

/-
(*****************************************************
            Small lemmas for functions
 *****************************************************)
-/

def inv_on {α : Type _} {β : Type _} [Inhabited α] (A : Set α) (f : α → β) (y : β) : α :=
  chooseOrDefault (fun x => x ∈ A ∧ f x = y)

theorem inv_f_f_on {α : Type _} {β : Type _} [Inhabited α] {A : Set α} {f : α → β} {x : α}
    (hf : Set.InjOn f A) (hx : x ∈ A) : inv_on A f (f x) = x := by
  apply chooseOrDefault_eq
  · exact ⟨hx, rfl⟩
  · intro y hy
    exact hf hy.1 hx hy.2

/-
(*****************************************************
                      fun (Product)
 *****************************************************)
-/

/-
(*******************************
        <= in fun
 *******************************)
-/

theorem order_prod_def {ι : Type _} {α : Type _} [LE α] {xp yp : ι → α} :
    (∀ x, xp x <= yp x) ↔ xp <= yp :=
  Iff.rfl

theorem order_less_prod_def {ι : Type _} {α : Type _} [PartialOrder α] {xp yp : ι → α} :
    xp < yp ↔ (∀ x, xp x <= yp x) ∧ ∃ x, xp x ≠ yp x := by
  constructor
  · intro h
    refine ⟨le_of_lt h, ?_⟩
    by_contra hEq
    apply ne_of_lt h
    funext x
    by_contra hxy
    exact hEq ⟨x, hxy⟩
  · intro h
    refine lt_of_le_of_ne h.1 ?_
    intro hyp
    rcases h.2 with ⟨x, hxy⟩
    exact hxy (congrArg (fun z => z x) hyp)

theorem fold_order_prod_def {ι : Type _} {α : Type _} [LE α] {xp yp : ι → α} :
    (∀ x, xp x <= yp x) ↔ xp <= yp :=
  order_prod_def

/-
(*** order in prod ***)
-/

theorem order_prod_inv {ι : Type _} {α : Type _} [LE α] {f g : ι → α}
    (hfg : ∀ x, f x <= g x) : f <= g :=
  hfg

/-
(*****************************************************
                   fun (Projection)
 *****************************************************)
-/

def proj_fun {ι : Type _} {α : Type _} (i : ι) : (ι → α) → α :=
  fun x => x i

/-
 (*** lub for projection ***)

(*** only if ***)
-/

theorem prod_LUB_decompo_only_if {ι : Type _} {α : Type _} [PartialOrder α]
    {x : ι → α} {X : Set (ι → α)} :
    isLUB x X → ∀ i, isLUB (proj_fun i x) (proj_fun i '' X) := by
  intro hx i
  classical
  constructor
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hx.1 z hz i
  · intro y hy
    have hUpper : isUB (fun j => if i = j then y else x j) X := by
      intro z hz j
      by_cases hij : i = j
      · subst hij
        simpa using hy (z i) ⟨z, hz, rfl⟩
      · simp [hij, hx.1 z hz j]
    have hLeast := hx.2 (fun j => if i = j then y else x j) hUpper
    simpa using hLeast i

/-
(*** if ***)
-/

theorem prod_LUB_decompo_if {ι : Type _} {α : Type _} [PartialOrder α]
    {x : ι → α} {X : Set (ι → α)} :
    (∀ i, isLUB (proj_fun i x) (proj_fun i '' X)) → isLUB x X := by
  intro hx
  constructor
  · intro y hy i
    exact (hx i).1 (y i) ⟨y, hy, rfl⟩
  · intro y hy i
    exact (hx i).2 (y i) <| by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact hy w hw i

/-
(*** iff ***)
-/

theorem prod_LUB_decompo {ι : Type _} {α : Type _} [PartialOrder α]
    {x : ι → α} {X : Set (ι → α)} :
    isLUB x X ↔ ∀ i, isLUB (proj_fun i x) (proj_fun i '' X) := by
  constructor
  · exact prod_LUB_decompo_only_if
  · exact prod_LUB_decompo_if

/-
(*****************************************************
                       mono
 *****************************************************)
-/

theorem prod_mono_only_if {δ : Type _} {ι : Type _} {α : Type _}
    [Preorder δ] [Preorder α] {f : δ → ι → α} (i : ι) :
    mono f → mono (proj_fun i ∘ f) := by
  intro hf x y hxy
  exact hf hxy i

theorem prod_mono_if {δ : Type _} {ι : Type _} {α : Type _}
    [Preorder δ] [Preorder α] {f : δ → ι → α} :
    (∀ i, mono (proj_fun i ∘ f)) → mono f := by
  intro hf x y hxy i
  exact hf i hxy

theorem prod_mono {δ : Type _} {ι : Type _} {α : Type _}
    [Preorder δ] [Preorder α] {f : δ → ι → α} :
    mono f ↔ ∀ i, mono (proj_fun i ∘ f) := by
  constructor
  · intro hf i
    exact prod_mono_only_if (f := f) i hf
  · exact prod_mono_if

/-
(**********************************************************
         some preparation for fixed point induction
 **********************************************************)
-/

def inductivefun {α : Type _} (R : α → Prop) (f : α → α) : Prop :=
  ∀ x, R x → R (f x)

def Ref_fun {α : Type _} [Preorder α] (X : α) : α → Prop :=
  fun Y => X <= Y

def Rev_fun {α : Type _} [Preorder α] (X : α) : α → Prop :=
  fun Y => Y <= X

theorem inductivefun_all_n {α : Type _} {R : α → Prop} {f : α → α} {x : α}
    (hInd : inductivefun R f) (hx : R x) : ∀ n, R (f^[n] x) := by
  intro n
  induction n with
  | zero =>
      simpa using hx
  | succ n ih =>
      simpa [Function.iterate_succ_apply'] using hInd (f^[n] x) ih

/-
(*----------------------------------------------------------*
              simplify inverse functions
 *----------------------------------------------------------*)
-/

@[simp]
theorem Pr1_inv_inj {α : Type _} {β : Type _} [Nonempty α] {f : α → β} {Pr : α → Prop}
    (hf : Injective f) : (∀ x, Pr (invFun f x)) ↔ ∀ y, Pr y := by
  constructor
  · intro h y
    simpa [Function.leftInverse_invFun hf y] using h (f y)
  · intro h x
    exact h (invFun f x)

@[simp]
theorem Pr2_inv_inj {α : Type _} {β : Type _} [Nonempty α] {f : α → β}
    {Pr1 : γ → Prop} {Pr2 : α → γ} (hf : Injective f) :
    (∀ x, Pr1 (Pr2 (invFun f x))) ↔ ∀ y, Pr1 (Pr2 y) := by
  simpa using (Pr1_inv_inj (f := f) (Pr := fun y => Pr1 (Pr2 y)) hf)

@[simp]
theorem Pr3_inv_inj {α : Type _} {β : Type _} [Nonempty α] {f : α → β}
    {Pr1 : δ → Prop} {Pr2 : γ → δ} {Pr3 : α → γ} (hf : Injective f) :
    (∀ x, Pr1 (Pr2 (Pr3 (invFun f x)))) ↔ ∀ y, Pr1 (Pr2 (Pr3 y)) := by
  simpa using (Pr1_inv_inj (f := f) (Pr := fun y => Pr1 (Pr2 (Pr3 y))) hf)

end
