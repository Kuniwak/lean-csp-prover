           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_common

/- --------------------------*
 |  exchange order in ALL   |
 *-------------------------- -/

theorem exchange_forall_orderE {α : Sort _} {β : Sort _} {P : α → β → Prop} {R : Prop}
    (hP : ∀ x y, P x y) (hR : (∀ y x, P x y) → R) : R :=
  hR fun y x ↦ hP x y

theorem exchange_forall_order3E {α : Sort _} {β : Sort _} {γ : Sort _}
    {P : α → β → γ → Prop} {R : Prop}
    (hP : ∀ x y z, P x y z) (hR : (∀ y z x, P x y z) → R) : R :=
  hR fun y z x ↦ hP x y z

theorem exchange_ALL_BALL {α : Sort _} {β : Sort _} {X : Set α} {P : α → β → Prop} :
    (∀ x ∈ X, ∀ y, P x y) ↔ ∀ y, ∀ x ∈ X, P x y := by
  constructor
  · intro h y x hx
    exact h x hx y
  · intro h x hx y
    exact h y x hx

theorem ALL_BALL_fun {α : Sort _} {β : Sort _} {X : Set α} {P : α → β → Prop} :
    (∀ y, ∀ x ∈ X, P x y) ↔ ∀ f : α → β, ∀ x ∈ X, P x (f x) := by
  constructor
  · intro h f x hx
    exact h (f x) x hx
  · intro h y x hx
    exact h (fun _ ↦ y) x hx

theorem ALL_BALL_funE {α : Sort _} {β : Sort _} {X : Set α} {P : α → β → Prop} {S : Prop}
    (hP : ∀ y, ∀ x ∈ X, P x y) (hS : (∀ f : α → β, ∀ x ∈ X, P x (f x)) → S) : S :=
  hS (ALL_BALL_fun.1 hP)

/- -------------------------------*
 |  distribution of ALL on conj  |
 *------------------------------- -/

theorem dist_ALL_conjI {α : Sort _} {P Q : α → Prop} :
    (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)
  | h => ⟨fun x ↦ (h x).1, fun x ↦ (h x).2⟩

theorem dist_ALL_conjE {α : Sort _} {P Q : α → Prop} {R : Prop}
    (hPQ : ∀ x, P x ∧ Q x) (hR : (∀ x, P x) → (∀ x, Q x) → R) : R :=
  hR (fun x ↦ (hPQ x).1) (fun x ↦ (hPQ x).2)

theorem dist_ALL_conj {α : Sort _} {P Q : α → Prop} :
    (∀ x, P x ∧ Q x) ↔ ((∀ x, P x) ∧ (∀ x, Q x)) := by
  constructor
  · exact dist_ALL_conjI
  · rintro ⟨hP, hQ⟩ x
    exact ⟨hP x, hQ x⟩

theorem dist_ALL_conj2I {α : Sort _} {β : Sort _} {P Q : α → β → Prop} :
    (∀ x y, P x y ∧ Q x y) → (∀ x y, P x y) ∧ (∀ x y, Q x y)
  | h => ⟨fun x y ↦ (h x y).1, fun x y ↦ (h x y).2⟩

theorem dist_ALL_conj2E {α : Sort _} {β : Sort _} {P Q : α → β → Prop} {R : Prop}
    (hPQ : ∀ x y, P x y ∧ Q x y) (hR : (∀ x y, P x y) → (∀ x y, Q x y) → R) : R :=
  hR (fun x y ↦ (hPQ x y).1) (fun x y ↦ (hPQ x y).2)

theorem dist_ALL_conj2 {α : Sort _} {β : Sort _} {P Q : α → β → Prop} :
    (∀ x y, P x y ∧ Q x y) ↔ ((∀ x y, P x y) ∧ (∀ x y, Q x y)) := by
  constructor
  · exact dist_ALL_conj2I
  · rintro ⟨hP, hQ⟩ x y
    exact ⟨hP x y, hQ x y⟩

/- BALL -/

theorem dist_BALL_conjI {α : Sort _} {X : Set α} {P Q : α → Prop} :
    (∀ x ∈ X, P x ∧ Q x) → (∀ x ∈ X, P x) ∧ (∀ x ∈ X, Q x)
  | h => ⟨fun x hx ↦ (h x hx).1, fun x hx ↦ (h x hx).2⟩

theorem dist_BALL_conjE {α : Sort _} {X : Set α} {P Q : α → Prop} {S : Prop}
    (hPQ : ∀ x ∈ X, P x ∧ Q x) (hS : (∀ x ∈ X, P x) → (∀ x ∈ X, Q x) → S) : S :=
  hS (fun x hx ↦ (hPQ x hx).1) (fun x hx ↦ (hPQ x hx).2)

theorem dist_BALL_conj2I {α : Sort _} {β : Sort _} {X : Set α} {Y : α → Set β}
    {P Q : α → β → Prop} :
    (∀ x ∈ X, ∀ y ∈ Y x, P x y ∧ Q x y) →
      (∀ x ∈ X, ∀ y ∈ Y x, P x y) ∧
      (∀ x ∈ X, ∀ y ∈ Y x, Q x y)
  | h => ⟨fun x hx y hy ↦ (h x hx y hy).1, fun x hx y hy ↦ (h x hx y hy).2⟩

theorem dist_BALL_conj2E {α : Sort _} {β : Sort _} {X : Set α} {Y : α → Set β}
    {P Q : α → β → Prop} {S : Prop}
    (hPQ : ∀ x ∈ X, ∀ y ∈ Y x, P x y ∧ Q x y)
    (hS : (∀ x ∈ X, ∀ y ∈ Y x, P x y) → (∀ x ∈ X, ∀ y ∈ Y x, Q x y) → S) : S :=
  hS (fun x hx y hy ↦ (hPQ x hx y hy).1) (fun x hx y hy ↦ (hPQ x hx y hy).2)

theorem dist_ALL_imply_conjE {α : Sort _} {b P Q : α → Prop} :
    (∀ x, b x → P x ∧ Q x) ↔ ((∀ x, b x → P x) ∧ (∀ x, b x → Q x)) := by
  constructor
  · intro h
    exact ⟨fun x hx ↦ (h x hx).1, fun x hx ↦ (h x hx).2⟩
  · rintro ⟨hP, hQ⟩ x hx
    exact ⟨hP x hx, hQ x hx⟩

/- *****************************************************
                   ALL EX --> EX ALL
 ***************************************************** -/

/- *** ALL *** -/

theorem choice_ALL_EX_only_if {α : Sort _} {β : Sort _} {P : α → β → Prop} :
    (∀ x, ∃ y, P x y) → ∃ f : α → β, ∀ x, P x (f x) := by
  classical
  intro h
  choose f hf using h
  exact ⟨f, hf⟩

theorem choice_ALL_EX {α : Sort _} {β : Sort _} {P : α → β → Prop} :
    (∀ x, ∃ y, P x y) ↔ ∃ f : α → β, ∀ x, P x (f x) := by
  constructor
  · exact choice_ALL_EX_only_if
  · rintro ⟨f, hf⟩ x
    exact ⟨f x, hf x⟩

/- *** imply *** -/

/- Lean note: unlike Isabelle/HOL, Lean types are not inhabited by default,
   so the implication-based choice lemmas require `Nonempty β`. -/
theorem choice_ALL_imply_EX_only_if {α : Sort _} {β : Sort _} [Nonempty β]
    {b : α → Prop} {P : α → β → Prop} :
    (∀ x, b x → ∃ y, P x y) → ∃ f : α → β, ∀ x, b x → P x (f x) := by
  classical
  intro h
  let f : α → β := fun x =>
    if hb : b x then Classical.choose (h x hb) else Classical.choice ‹Nonempty β›
  refine ⟨f, ?_⟩
  intro x hx
  simpa [f, hx] using Classical.choose_spec (h x hx)

theorem choice_ALL_imply_EX {α : Sort _} {β : Sort _} [Nonempty β]
    {b : α → Prop} {P : α → β → Prop} :
    (∀ x, b x → ∃ y, P x y) ↔ ∃ f : α → β, ∀ x, b x → P x (f x) := by
  constructor
  · exact choice_ALL_imply_EX_only_if
  · rintro ⟨f, hf⟩ x hx
    exact ⟨f x, hf x hx⟩

/- *** BALL *** -/

theorem choice_BALL_EX {α : Sort _} {β : Sort _} [Nonempty β] {X : Set α}
    {P : α → β → Prop} :
    (∀ x ∈ X, ∃ y, P x y) ↔ ∃ f : α → β, ∀ x ∈ X, P x (f x) := by
  simpa using (choice_ALL_imply_EX (b := fun x ↦ x ∈ X) (P := P))

/- *****************************************************
                        EX!
 ***************************************************** -/

theorem ex1_implies_exE {α : Sort _} {P : α → Prop} {S : Prop}
    (hEX1 : ∃! x, P x) (hS : (∃ x, P x) → S) : S :=
  hS hEX1.exists

/- *** 1 *** -/

theorem EX1_1I {α : Sort _} {P : α → Prop} :
    (∃ X1, P X1 ∧ (∀ Y1, P Y1 → Y1 = X1)) → (∃! X1, P X1) := by
  rintro ⟨X1, hP, huniq⟩
  exact ⟨X1, hP, huniq⟩

/- *** 2 *** -/

theorem EX1_2I {α : Sort _} {β : Sort _} {P : α → β → Prop} :
    (∃ X1 X2, P X1 X2 ∧ (∀ Y1 Y2, P Y1 Y2 → (Y1 = X1) ∧ (Y2 = X2))) →
      (∃! X1, ∃! X2, P X1 X2) := by
  rintro ⟨X1, X2, hP, huniq⟩
  refine ⟨X1, ?_, ?_⟩
  · refine ⟨X2, hP, ?_⟩
    intro Y2 hY2
    exact (huniq X1 Y2 hY2).2
  · intro Y1 hY1
    rcases hY1.exists with ⟨Y2, hY2⟩
    exact (huniq Y1 Y2 hY2).1

/- *** 3 *** -/

theorem EX1_3I {α : Sort _} {β : Sort _} {γ : Sort _} {P : α → β → γ → Prop} :
    (∃ X1 X2 X3, P X1 X2 X3 ∧
      (∀ Y1 Y2 Y3, P Y1 Y2 Y3 → (Y1 = X1) ∧ (Y2 = X2) ∧ (Y3 = X3))) →
      (∃! X1, ∃! X2, ∃! X3, P X1 X2 X3) := by
  rintro ⟨X1, X2, X3, hP, huniq⟩
  refine ⟨X1, ?_, ?_⟩
  · refine ⟨X2, ?_, ?_⟩
    · refine ⟨X3, hP, ?_⟩
      intro Y3 hY3
      exact (huniq X1 X2 Y3 hY3).2.2
    · intro Y2 hY2
      rcases hY2.exists with ⟨Y3, hY3⟩
      exact (huniq X1 Y2 Y3 hY3).2.1
  · intro Y1 hY1
    rcases hY1.exists with ⟨Y2, hY2⟩
    rcases hY2.exists with ⟨Y3, hY3⟩
    exact (huniq Y1 Y2 Y3 hY3).1

/- *** 4 *** -/

theorem EX1_4I {α : Sort _} {β : Sort _} {γ : Sort _} {δ : Sort _}
    {P : α → β → γ → δ → Prop} :
    (∃ X1 X2 X3 X4, P X1 X2 X3 X4 ∧
      (∀ Y1 Y2 Y3 Y4, P Y1 Y2 Y3 Y4 →
        (Y1 = X1) ∧ (Y2 = X2) ∧ (Y3 = X3) ∧ (Y4 = X4))) →
      (∃! X1, ∃! X2, ∃! X3, ∃! X4, P X1 X2 X3 X4) := by
  rintro ⟨X1, X2, X3, X4, hP, huniq⟩
  refine ⟨X1, ?_, ?_⟩
  · refine ⟨X2, ?_, ?_⟩
    · refine ⟨X3, ?_, ?_⟩
      · refine ⟨X4, hP, ?_⟩
        intro Y4 hY4
        exact (huniq X1 X2 X3 Y4 hY4).2.2.2
      · intro Y3 hY3
        rcases hY3.exists with ⟨Y4, hY4⟩
        exact (huniq X1 X2 Y3 Y4 hY4).2.2.1
    · intro Y2 hY2
      rcases hY2.exists with ⟨Y3, hY3⟩
      rcases hY3.exists with ⟨Y4, hY4⟩
      exact (huniq X1 Y2 Y3 Y4 hY4).2.1
  · intro Y1 hY1
    rcases hY1.exists with ⟨Y2, hY2⟩
    rcases hY2.exists with ⟨Y3, hY3⟩
    rcases hY3.exists with ⟨Y4, hY4⟩
    exact (huniq Y1 Y2 Y3 Y4 hY4).1

/- *** 5 *** -/

theorem EX1_5I {α : Sort _} {β : Sort _} {γ : Sort _} {δ : Sort _} {ε : Sort _}
    {P : α → β → γ → δ → ε → Prop} :
    (∃ X1 X2 X3 X4 X5, P X1 X2 X3 X4 X5 ∧
      (∀ Y1 Y2 Y3 Y4 Y5, P Y1 Y2 Y3 Y4 Y5 →
        (Y1 = X1) ∧ (Y2 = X2) ∧ (Y3 = X3) ∧ (Y4 = X4) ∧ (Y5 = X5))) →
      (∃! X1, ∃! X2, ∃! X3, ∃! X4, ∃! X5, P X1 X2 X3 X4 X5) := by
  rintro ⟨X1, X2, X3, X4, X5, hP, huniq⟩
  refine ⟨X1, ?_, ?_⟩
  · refine ⟨X2, ?_, ?_⟩
    · refine ⟨X3, ?_, ?_⟩
      · refine ⟨X4, ?_, ?_⟩
        · refine ⟨X5, hP, ?_⟩
          intro Y5 hY5
          exact (huniq X1 X2 X3 X4 Y5 hY5).2.2.2.2
        · intro Y4 hY4
          rcases hY4.exists with ⟨Y5, hY5⟩
          exact (huniq X1 X2 X3 Y4 Y5 hY5).2.2.2.1
      · intro Y3 hY3
        rcases hY3.exists with ⟨Y4, hY4⟩
        rcases hY4.exists with ⟨Y5, hY5⟩
        exact (huniq X1 X2 Y3 Y4 Y5 hY5).2.2.1
    · intro Y2 hY2
      rcases hY2.exists with ⟨Y3, hY3⟩
      rcases hY3.exists with ⟨Y4, hY4⟩
      rcases hY4.exists with ⟨Y5, hY5⟩
      exact (huniq X1 Y2 Y3 Y4 Y5 hY5).2.1
  · intro Y1 hY1
    rcases hY1.exists with ⟨Y2, hY2⟩
    rcases hY2.exists with ⟨Y3, hY3⟩
    rcases hY3.exists with ⟨Y4, hY4⟩
    rcases hY4.exists with ⟨Y5, hY5⟩
    exact (huniq Y1 Y2 Y3 Y4 Y5 hY5).1

/- *** 6 *** -/

theorem EX1_6I {α : Sort _} {β : Sort _} {γ : Sort _} {δ : Sort _} {ε : Sort _}
    {ζ : Sort _} {P : α → β → γ → δ → ε → ζ → Prop} :
    (∃ X1 X2 X3 X4 X5 X6, P X1 X2 X3 X4 X5 X6 ∧
      (∀ Y1 Y2 Y3 Y4 Y5 Y6, P Y1 Y2 Y3 Y4 Y5 Y6 →
        (Y1 = X1) ∧ (Y2 = X2) ∧ (Y3 = X3) ∧
        (Y4 = X4) ∧ (Y5 = X5) ∧ (Y6 = X6))) →
      (∃! X1, ∃! X2, ∃! X3, ∃! X4, ∃! X5, ∃! X6, P X1 X2 X3 X4 X5 X6) := by
  rintro ⟨X1, X2, X3, X4, X5, X6, hP, huniq⟩
  refine ⟨X1, ?_, ?_⟩
  · refine ⟨X2, ?_, ?_⟩
    · refine ⟨X3, ?_, ?_⟩
      · refine ⟨X4, ?_, ?_⟩
        · refine ⟨X5, ?_, ?_⟩
          · refine ⟨X6, hP, ?_⟩
            intro Y6 hY6
            exact (huniq X1 X2 X3 X4 X5 Y6 hY6).2.2.2.2.2
          · intro Y5 hY5
            rcases hY5.exists with ⟨Y6, hY6⟩
            exact (huniq X1 X2 X3 X4 Y5 Y6 hY6).2.2.2.2.1
        · intro Y4 hY4
          rcases hY4.exists with ⟨Y5, hY5⟩
          rcases hY5.exists with ⟨Y6, hY6⟩
          exact (huniq X1 X2 X3 Y4 Y5 Y6 hY6).2.2.2.1
      · intro Y3 hY3
        rcases hY3.exists with ⟨Y4, hY4⟩
        rcases hY4.exists with ⟨Y5, hY5⟩
        rcases hY5.exists with ⟨Y6, hY6⟩
        exact (huniq X1 X2 Y3 Y4 Y5 Y6 hY6).2.2.1
    · intro Y2 hY2
      rcases hY2.exists with ⟨Y3, hY3⟩
      rcases hY3.exists with ⟨Y4, hY4⟩
      rcases hY4.exists with ⟨Y5, hY5⟩
      rcases hY5.exists with ⟨Y6, hY6⟩
      exact (huniq X1 Y2 Y3 Y4 Y5 Y6 hY6).2.1
  · intro Y1 hY1
    rcases hY1.exists with ⟨Y2, hY2⟩
    rcases hY2.exists with ⟨Y3, hY3⟩
    rcases hY3.exists with ⟨Y4, hY4⟩
    rcases hY4.exists with ⟨Y5, hY5⟩
    rcases hY5.exists with ⟨Y6, hY6⟩
    exact (huniq Y1 Y2 Y3 Y4 Y5 Y6 hY6).1

/- =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== -/

/- -----------
      no eq
 * ----------- -/

theorem add_not_eq_sym_funE {α : Sort _} {β : Sort _} {γ : Sort _}
    {f : α → γ} {g : β → γ} {R : Prop}
    (hfg : ∀ x y, f x ≠ g y)
    (hR : ((∀ x y, f x ≠ g y) ∧ (∀ x y, g x ≠ f y)) → R) : R := by
  apply hR
  constructor
  · exact hfg
  · intro x y hEq
    exact hfg y x hEq.symm

theorem add_not_eq_sym_cons_funE {α : Sort _} {β : Sort _} {f : α → β} {a : β} {R : Prop}
    (haf : ∀ x, a ≠ f x) (hR : ((∀ x, a ≠ f x) ∧ (∀ x, f x ≠ a)) → R) : R := by
  apply hR
  constructor
  · exact haf
  · intro x hEq
    exact haf x hEq.symm

theorem add_not_eq_sym_consE {α : Sort _} {a b : α} {R : Prop}
    (hab : a ≠ b) (hR : (a ≠ b ∧ b ≠ a) → R) : R := by
  exact hR ⟨hab, fun hEq ↦ hab hEq.symm⟩

-- Isabelle: lemmas add_not_eq_symE =
--            add_not_eq_sym_funE
--            add_not_eq_sym_cons_funE
--            add_not_eq_sym_consE

theorem not_eq_fun_range_Int {α : Sort _} {β : Sort _} {γ : Sort _} {f : α → γ} {g : β → γ} :
    (∀ x y, f x ≠ g y) ↔ Set.range f ∩ Set.range g = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.2
    intro z hz
    rcases hz with ⟨⟨x, rfl⟩, ⟨y, hy⟩⟩
    exact h x y hy.symm
  · intro h x y hEq
    have hz : f x ∈ Set.range f ∩ Set.range g := ⟨Set.mem_range_self x, ⟨y, hEq.symm⟩⟩
    simp [h] at hz

theorem not_eq_fun_range_Int_only_if {α : Sort _} {β : Sort _} {γ : Sort _}
    {f : α → γ} {g : β → γ} :
    (∀ x y, f x ≠ g y) → Set.range f ∩ Set.range g = ∅ :=
  not_eq_fun_range_Int.1

theorem not_eq_fun_range_Int_if {α : Sort _} {β : Sort _} {γ : Sort _}
    {f : α → γ} {g : β → γ} :
    Set.range f ∩ Set.range g = ∅ → (∀ x y, f x ≠ g y) :=
  not_eq_fun_range_Int.2
