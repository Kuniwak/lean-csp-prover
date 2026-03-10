           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                October 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                  April 2011  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_HOL

open Function

set_option autoImplicit true

noncomputable section

/- -------------------------- *
      renaming (Intra_ren)
 * -------------------------- -/

def fun_to_rel {α : Type _} (f : α → α) : Set (α × α) :=
  {p | p.2 = f p.1}

axiom diff_fun {x a : Type _} : Set (x → a) → Prop

noncomputable def Renaming1_event_fun {α : Type _} (a : α) (b : α) : α → α := by
  classical
  exact fun c => if c = a then b else if c = b then a else c

noncomputable def Renaming1_channel_fun {x α : Type _} (f : x → α) (g : x → α) : α → α := by
  classical
  exact fun c =>
    if hfg : ∀ x y, f x ≠ g y then
      if hfc : ∃ x, f x = c then
        g (Classical.choose hfc)
      else if hgc : ∃ y, g y = c then
        f (Classical.choose hgc)
      else
        c
    else
      c

noncomputable def Renaming1_event {α : Type _} (a : α) (b : α) : Set (α × α) :=
  fun_to_rel (Renaming1_event_fun a b)

noncomputable def Renaming1_channel {x α : Type _} (f : x → α) (g : x → α) : Set (α × α) :=
  fun_to_rel (Renaming1_channel_fun f g)

noncomputable def Renaming2_event_fun {α : Type _} (A : Set α) (b : α) : α → α := by
  classical
  exact fun c => if c ∈ A then b else c

noncomputable def Renaming2_channel_fun {x α : Type _} (f : x → α) (g : x → α) : α → α := by
  classical
  exact fun c =>
    if hfg : ∀ x y, f x ≠ g y then
      if hfc : ∃ x, f x = c then
        g (Classical.choose hfc)
      else
        c
    else
      c

noncomputable def Renaming2_event {α : Type _} (A : Set α) (b : α) : Set (α × α) :=
  fun_to_rel (Renaming2_event_fun A b)

noncomputable def Renaming2_channel {x α : Type _} (f : x → α) (g : x → α) : Set (α × α) :=
  fun_to_rel (Renaming2_channel_fun f g)

abbrev Renaming2_signle_event {α : Type _} (a : α) (b : α) : Set (α × α) :=
  Renaming2_event {a} b

notation:100 a " <--> " b => Renaming1_event a b
notation:100 f " <==> " g => Renaming1_channel f g
notation:100 A " <<- " b => Renaming2_event A b
notation:100 f " <== " g => Renaming2_channel f g
notation:100 a " <-- " b => Renaming2_signle_event a b

@[simp]
theorem mem_fun_to_rel {α : Type _} {f : α → α} {a b : α} : (a, b) ∈ fun_to_rel f ↔ b = f a :=
  Iff.rfl

@[simp]
theorem mem_Renaming1_event {α : Type _} {x y a b : α} :
    (a, b) ∈ Renaming1_event x y ↔ b = Renaming1_event_fun x y a :=
  Iff.rfl

@[simp]
theorem mem_Renaming1_channel {x α : Type _} {f g : x → α} {a b : α} :
    (a, b) ∈ Renaming1_channel f g ↔ b = Renaming1_channel_fun f g a :=
  Iff.rfl

@[simp]
theorem mem_Renaming2_event {α : Type _} {A : Set α} {y a b : α} :
    (a, b) ∈ Renaming2_event A y ↔ b = Renaming2_event_fun A y a :=
  Iff.rfl

@[simp]
theorem mem_Renaming2_channel {x α : Type _} {f g : x → α} {a b : α} :
    (a, b) ∈ Renaming2_channel f g ↔ b = Renaming2_channel_fun f g a :=
  Iff.rfl

private theorem choose_eq_of_injective {f : α → β} (hf : Injective f) {y : β}
    (hy : ∃ x, f x = y) {x : α} (hx : f x = y) : Classical.choose hy = x := by
  apply hf
  simpa [hx] using Classical.choose_spec hy

private theorem disjoint_symm {f : α → γ} {g : β → γ} :
    (∀ x y, f x ≠ g y) ↔ ∀ y x, g y ≠ f x := by
  constructor
  · intro h y x
    exact (h x y).symm
  · intro h x y
    exact (h y x).symm

private theorem not_exists_eq_of_forall_ne {f : α → β} {c : β} (hc : ∀ x, c ≠ f x) :
    ¬ ∃ x, f x = c := by
  intro h
  rcases h with ⟨x, hx⟩
  exact hc x hx.symm

private theorem Renaming1_channel_fun_fix {f : x → α} {g : x → α} {c : α}
    (hfg : ∀ x y, f x ≠ g y) (hcf : ∀ x, c ≠ f x) (hcg : ∀ y, c ≠ g y) :
    Renaming1_channel_fun f g c = c := by
  classical
  have hfc : ¬ ∃ x, f x = c := not_exists_eq_of_forall_ne hcf
  have hgc : ¬ ∃ y, g y = c := not_exists_eq_of_forall_ne hcg
  simp [Renaming1_channel_fun, hfg, hfc, hgc]

private theorem Renaming2_channel_fun_fix {f : x → α} {g : x → α} {c : α}
    (hfg : ∀ x y, f x ≠ g y) (hcf : ∀ x, c ≠ f x) :
    Renaming2_channel_fun f g c = c := by
  classical
  have hfc : ¬ ∃ x, f x = c := not_exists_eq_of_forall_ne hcf
  simp [Renaming2_channel_fun, hfg, hfc]

theorem Renaming_event_fun_commut :
    Renaming1_event_fun a b = Renaming1_event_fun b a := by
  classical
  funext c
  by_cases hca : c = a <;> by_cases hcb : c = b <;> simp [Renaming1_event_fun, hca, hcb, eq_comm]

theorem Renaming_event_commut : (a <--> b) = (b <--> a) := by
  ext p
  rcases p with ⟨x, y⟩
  simp [Renaming1_event, Renaming_event_fun_commut]

theorem Renaming_channel_fun_commut :
    Renaming1_channel_fun f g = Renaming1_channel_fun g f := by
  classical
  funext c
  by_cases hfg : ∀ x y, f x ≠ g y
  · have hgf : ∀ y x, g y ≠ f x := (disjoint_symm).1 hfg
    by_cases hfc : ∃ x, f x = c
    · have hgc : ¬ ∃ y, g y = c := by
        intro h
        rcases hfc with ⟨x, hx⟩
        rcases h with ⟨y, hy⟩
        exact hfg x y (hx.trans hy.symm)
      simp [Renaming1_channel_fun, hfg, hgf, hfc, hgc]
    · by_cases hgc : ∃ y, g y = c
      · simp [Renaming1_channel_fun, hfg, hgf, hfc, hgc]
      · simp [Renaming1_channel_fun, hfg, hgf, hfc, hgc]
  · have hgf : ¬ ∀ y x, g y ≠ f x := by
      intro hgf
      exact hfg ((disjoint_symm).2 hgf)
    simp [Renaming1_channel_fun, hfg, hgf]

theorem Renaming_channel_commut : (f <==> g) = (g <==> f) := by
  ext p
  rcases p with ⟨a, b⟩
  simp [Renaming_channel_fun_commut]

theorem Renaming1_channel_fun_f (hf : Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g (f x) = g x := by
  classical
  have hff : ∃ x', f x' = f x := ⟨x, rfl⟩
  have hgf : ¬ ∃ y, g y = f x := by
    intro h
    rcases h with ⟨y, hy⟩
    exact hfg x y hy.symm
  have hchoose : Classical.choose hff = x := choose_eq_of_injective hf hff rfl
  simp [Renaming1_channel_fun, hfg, hff, hchoose]

theorem Renaming2_channel_fun_f (hf : Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming2_channel_fun f g (f x) = g x := by
  classical
  have hff : ∃ x', f x' = f x := ⟨x, rfl⟩
  have hchoose : Classical.choose hff = x := choose_eq_of_injective hf hff rfl
  simp [Renaming2_channel_fun, hfg, hff, hchoose]

theorem Renaming_channel_fun_f (hf : Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g (f x) = g x ∧
      Renaming2_channel_fun f g (f x) = g x :=
  ⟨Renaming1_channel_fun_f (f := f) (g := g) (x := x) hf hfg,
    Renaming2_channel_fun_f (f := f) (g := g) (x := x) hf hfg⟩

theorem Renaming_channel_fun_g (hg : Injective g) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g (g x) = f x := by
  classical
  have hgf : ∃ y, g y = g x := ⟨x, rfl⟩
  have hff : ¬ ∃ y, f y = g x := by
    intro h
    rcases h with ⟨y, hy⟩
    exact hfg y x hy
  have hchoose : Classical.choose hgf = x := choose_eq_of_injective hg hgf rfl
  simp [Renaming1_channel_fun, hfg, hgf, hchoose]

theorem Renaming1_channel_fun_h {x y α : Type _} {f g : x → α} {h : y → α} {x0 : y}
    (hfg : ∀ x y, f x ≠ g y) (hfh : ∀ x y, f x ≠ h y) (hgh : ∀ x y, g x ≠ h y) :
    Renaming1_channel_fun f g (h x0) = h x0 := by
  exact Renaming1_channel_fun_fix hfg (fun y => (hfh y x0).symm) (fun y => (hgh y x0).symm)

theorem Renaming2_channel_fun_h {x y α : Type _} {f g : x → α} {h : y → α} {x0 : y}
    (hfg : ∀ x y, f x ≠ g y) (hfh : ∀ x y, f x ≠ h y) :
    Renaming2_channel_fun f g (h x0) = h x0 := by
  exact Renaming2_channel_fun_fix hfg (fun y => (hfh y x0).symm)

theorem Renaming_channel_fun_h {x y α : Type _} {f g : x → α} {h : y → α} {x0 : y}
    (hfg : ∀ x y, f x ≠ g y) (hfh : ∀ x y, f x ≠ h y) (hgh : ∀ x y, g x ≠ h y) :
    Renaming1_channel_fun f g (h x0) = h x0 ∧
      Renaming2_channel_fun f g (h x0) = h x0 :=
  ⟨Renaming1_channel_fun_h (f := f) (g := g) (h := h) (x0 := x0) hfg hfh hgh,
    Renaming2_channel_fun_h (f := f) (g := g) (h := h) (x0 := x0) hfg hfh⟩

theorem Renaming1_channel_fun_map_f (hf : Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g '' (f '' X) = g '' X := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Renaming1_channel_fun_f (f := f) (g := g) (x := x) hf hfg).symm⟩
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, Renaming1_channel_fun_f (f := f) (g := g) (x := x) hf hfg⟩

theorem Renaming2_channel_fun_map_f (hf : Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming2_channel_fun f g '' (f '' X) = g '' X := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Renaming2_channel_fun_f (f := f) (g := g) (x := x) hf hfg).symm⟩
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, Renaming2_channel_fun_f (f := f) (g := g) (x := x) hf hfg⟩

theorem Renaming_channel_fun_map_f (hf : Injective f) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g '' (f '' X) = g '' X ∧
      Renaming2_channel_fun f g '' (f '' X) = g '' X :=
  ⟨Renaming1_channel_fun_map_f (f := f) (g := g) (X := X) hf hfg,
    Renaming2_channel_fun_map_f (f := f) (g := g) (X := X) hf hfg⟩

theorem Renaming_channel_fun_map_g (hg : Injective g) (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g '' (g '' X) = f '' X := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Renaming_channel_fun_g (f := f) (g := g) (x := x) hg hfg).symm⟩
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨g x, ⟨x, hx, rfl⟩, Renaming_channel_fun_g (f := f) (g := g) (x := x) hg hfg⟩

theorem Renaming1_channel_fun_map_h (hfh : ∀ x y, f x ≠ h y) (hgh : ∀ x y, g x ≠ h y)
    (hfg : ∀ x y, f x ≠ g y) : Renaming1_channel_fun f g '' (h '' X) = h '' X := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Renaming1_channel_fun_h (f := f) (g := g) (h := h) (x0 := x) hfg hfh hgh).symm⟩
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨h x, ⟨x, hx, rfl⟩,
      Renaming1_channel_fun_h (f := f) (g := g) (h := h) (x0 := x) hfg hfh hgh⟩

theorem Renaming2_channel_fun_map_h (hfh : ∀ x y, f x ≠ h y) (hfg : ∀ x y, f x ≠ g y) :
    Renaming2_channel_fun f g '' (h '' X) = h '' X := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hz, rfl⟩
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨x, hx, (Renaming2_channel_fun_h (f := f) (g := g) (h := h) (x0 := x) hfg hfh).symm⟩
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨h x, ⟨x, hx, rfl⟩, Renaming2_channel_fun_h (f := f) (g := g) (h := h) (x0 := x) hfg hfh⟩

theorem Renaming_channel_fun_map_h (hfh : ∀ x y, f x ≠ h y) (hgh : ∀ x y, g x ≠ h y)
    (hfg : ∀ x y, f x ≠ g y) :
    Renaming1_channel_fun f g '' (h '' X) = h '' X ∧
      Renaming2_channel_fun f g '' (h '' X) = h '' X :=
  ⟨Renaming1_channel_fun_map_h (f := f) (g := g) (h := h) (X := X) hfh hgh hfg,
    Renaming2_channel_fun_map_h (f := f) (g := g) (h := h) (X := X) hfh hfg⟩

private theorem Renaming1_channel_fun_involutive {f : x → α} {g : x → α}
    (hf : Injective f) (hg : Injective g) : Function.Involutive (Renaming1_channel_fun f g) := by
  classical
  intro c
  by_cases hfg : ∀ x y, f x ≠ g y
  · by_cases hfc : ∃ x, f x = c
    · rcases hfc with ⟨x, rfl⟩
      simp [Renaming1_channel_fun_f (f := f) (g := g) (x := x) hf hfg,
        Renaming_channel_fun_g (f := f) (g := g) (x := x) hg hfg]
    · by_cases hgc : ∃ y, g y = c
      · rcases hgc with ⟨y, rfl⟩
        simp [Renaming1_channel_fun_f (f := f) (g := g) (x := y) hf hfg,
          Renaming_channel_fun_g (f := f) (g := g) (x := y) hg hfg]
      · simp [Renaming1_channel_fun, hfg, hfc, hgc]
  · simp [Renaming1_channel_fun, hfg]

/- --- Ren --- -/

theorem pair_in_Renaming_channel_1 (hf : Injective f) (hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) : ((a, g x) ∈ (f <==> g)) ↔ a = f x := by
  constructor
  · intro h
    have hag : g x = Renaming1_channel_fun f g a := by
      simpa using h
    have hInv := Renaming1_channel_fun_involutive (f := f) (g := g) hf hg
    have := congrArg (Renaming1_channel_fun f g) hag.symm
    simpa [hInv a, Renaming_channel_fun_g (f := f) (g := g) (x := x) hg hfg] using this
  · intro h
    subst h
    simp [Renaming1_channel_fun_f (f := f) (g := g) (x := x) hf hfg]

theorem pair_in_Renaming_channel_2 (hf : Injective f) (hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) : ((a, g x) ∈ (g <==> f)) ↔ a = f x := by
  simpa [Renaming_channel_commut (f := f) (g := g)] using
    (pair_in_Renaming_channel_1 (f := f) (g := g) (a := a) (x := x) hf hg hfg)

theorem pair_in_Renaming1_channel_3 (hf : Injective f) (_hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) : ((f x, a) ∈ (f <==> g)) ↔ a = g x := by
  simp [Renaming1_channel_fun_f (f := f) (g := g) (x := x) hf hfg]

theorem pair_in_Renaming2_channel_3 (hf : Injective f) (_hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) : ((f x, a) ∈ (f <== g)) ↔ a = g x := by
  simp [Renaming2_channel_fun_f (f := f) (g := g) (x := x) hf hfg]

theorem pair_in_Renaming_channel_3 (hf : Injective f) (hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) :
    (((f x, a) ∈ (f <==> g)) ↔ a = g x) ∧ (((f x, a) ∈ (f <== g)) ↔ a = g x) :=
  ⟨pair_in_Renaming1_channel_3 (f := f) (g := g) (a := a) (x := x) hf hg hfg,
    pair_in_Renaming2_channel_3 (f := f) (g := g) (a := a) (x := x) hf hg hfg⟩

theorem pair_in_Renaming_channel_4 (hf : Injective f) (hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) : ((f x, a) ∈ (g <==> f)) ↔ a = g x := by
  simpa [Renaming_channel_commut (f := f) (g := g)] using
    (pair_in_Renaming1_channel_3 (f := f) (g := g) (a := a) (x := x) hf hg hfg)

theorem pair_in_Renaming_channel_5 (hf : Injective f) (hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) (hbf : ∀ x, b ≠ f x) (hbg : ∀ x, b ≠ g x) :
    ((a, b) ∈ (f <==> g)) ↔ a = b := by
  constructor
  · intro h
    have hab : b = Renaming1_channel_fun f g a := by
      simpa using h
    have hInv := Renaming1_channel_fun_involutive (f := f) (g := g) hf hg
    have hbfix : Renaming1_channel_fun f g b = b := Renaming1_channel_fun_fix hfg hbf hbg
    have := congrArg (Renaming1_channel_fun f g) hab.symm
    simpa [hInv a, hbfix] using this
  · intro h
    subst a
    simp [Renaming1_channel_fun_fix (f := f) (g := g) (c := b) hfg hbf hbg]

theorem pair_in_Renaming1_channel_6 (_hf : Injective f) (_hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) (haf : ∀ x, a ≠ f x) (hag : ∀ x, a ≠ g x) :
    ((a, b) ∈ (f <==> g)) ↔ a = b := by
  simp [Renaming1_channel_fun_fix (f := f) (g := g) (c := a) hfg haf hag, eq_comm]

theorem pair_in_Renaming2_channel_6 (_hf : Injective f) (_hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) (haf : ∀ x, a ≠ f x) :
    ((a, b) ∈ (f <== g)) ↔ a = b := by
  simp [Renaming2_channel_fun_fix (f := f) (g := g) (c := a) hfg haf, eq_comm]

theorem pair_in_Renaming_channel_6 (hf : Injective f) (hg : Injective g)
    (hfg : ∀ x y, f x ≠ g y) (haf : ∀ x, a ≠ f x) (hag : ∀ x, a ≠ g x) :
    (((a, b) ∈ (f <==> g)) ↔ a = b) ∧ (((a, b) ∈ (f <== g)) ↔ a = b) :=
  ⟨pair_in_Renaming1_channel_6 (f := f) (g := g) (a := a) (b := b) hf hg hfg haf hag,
    pair_in_Renaming2_channel_6 (f := f) (g := g) (a := a) (b := b) hf hg hfg haf⟩

/- --- sym --- -/

theorem Renaming_channel_sym_rule (hf : Injective f) (hg : Injective g)
    (h : (b, a) ∈ (f <==> g)) : (a, b) ∈ (f <==> g) := by
  have hba : a = Renaming1_channel_fun f g b := by
    simpa using h
  have hInv := Renaming1_channel_fun_involutive (f := f) (g := g) hf hg
  have hab : b = Renaming1_channel_fun f g a := by
    have := congrArg (Renaming1_channel_fun f g) hba.symm
    simpa [hInv b] using this
  simpa using hab

theorem Renaming_channel_sym (hf : Injective f) (hg : Injective g) :
    ((b, a) ∈ (f <==> g)) ↔ ((a, b) ∈ (f <==> g)) := by
  constructor
  · exact Renaming_channel_sym_rule (f := f) (g := g) hf hg
  · exact Renaming_channel_sym_rule (f := f) (g := g) hf hg

/- --- inj --- -/

theorem inj_Renaming_channel_fun (hf : Injective f) (hg : Injective g) :
    Injective (Renaming1_channel_fun f g) := by
  intro a b hab
  have hInv := Renaming1_channel_fun_involutive (f := f) (g := g) hf hg
  have := congrArg (Renaming1_channel_fun f g) hab
  simpa [hInv a, hInv b] using this

theorem Renaming1_channel_unique :
    ∀ a b c, (((a, b) ∈ (f <==> g)) ∧ ((a, c) ∈ (f <==> g))) → b = c := by
  intro a b c h
  have hab : b = Renaming1_channel_fun f g a := by
    simpa using h.1
  have hac : c = Renaming1_channel_fun f g a := by
    simpa using h.2
  exact hab.trans hac.symm

theorem Renaming2_channel_unique :
    ∀ a b c, (((a, b) ∈ (f <== g)) ∧ ((a, c) ∈ (f <== g))) → b = c := by
  intro a b c h
  have hab : b = Renaming2_channel_fun f g a := by
    simpa using h.1
  have hac : c = Renaming2_channel_fun f g a := by
    simpa using h.2
  exact hab.trans hac.symm

theorem Renaming_channel_unique :
    (∀ a b c, (((a, b) ∈ (f <==> g)) ∧ ((a, c) ∈ (f <==> g))) → b = c) ∧
      (∀ a b c, (((a, b) ∈ (f <== g)) ∧ ((a, c) ∈ (f <== g))) → b = c) :=
  ⟨Renaming1_channel_unique (f := f) (g := g), Renaming2_channel_unique (f := f) (g := g)⟩

private theorem not_exists_of_not_exists_eq {f : α → β} {a : β} (h : ¬ ∃ x, f x = a) :
    ∀ x, a ≠ f x := by
  intro x hx
  exact h ⟨x, hx.symm⟩

private theorem Renaming_channel_fun_independ {f1 f2 : x → α} {g1 g2 : y → α}
    (hf1 : Injective f1) (hf2 : Injective f2) (hg1 : Injective g1)
    (hg2 : Injective g2) (h12 : ∀ x y, f1 x ≠ f2 y) (h1g1 : ∀ x y, f1 x ≠ g1 y)
    (h1g2 : ∀ x y, f1 x ≠ g2 y) (h2g1 : ∀ x y, f2 x ≠ g1 y) (h2g2 : ∀ x y, f2 x ≠ g2 y)
    (hg12 : ∀ x y, g1 x ≠ g2 y) :
    ∀ a,
      Renaming1_channel_fun g1 g2 (Renaming1_channel_fun f1 f2 a) =
        Renaming1_channel_fun f1 f2 (Renaming1_channel_fun g1 g2 a) := by
  intro a
  by_cases ha1 : ∃ x, f1 x = a
  · rcases ha1 with ⟨x, rfl⟩
    simp [Renaming1_channel_fun_f (f := f1) (g := f2) (x := x) hf1 h12,
      Renaming1_channel_fun_fix (f := g1) (g := g2) (c := f2 x) hg12
        (fun y => h2g1 x y) (fun y => h2g2 x y),
      Renaming1_channel_fun_fix (f := g1) (g := g2) (c := f1 x) hg12
        (fun y => h1g1 x y) (fun y => h1g2 x y)]
  · by_cases ha2 : ∃ x, f2 x = a
    · rcases ha2 with ⟨x, rfl⟩
      simp [Renaming_channel_fun_g (f := f1) (g := f2) (x := x) hf2 h12,
        Renaming1_channel_fun_fix (f := g1) (g := g2) (c := f1 x) hg12
          (fun y => h1g1 x y) (fun y => h1g2 x y),
        Renaming1_channel_fun_fix (f := g1) (g := g2) (c := f2 x) hg12
          (fun y => h2g1 x y) (fun y => h2g2 x y)]
    · by_cases hb1 : ∃ y, g1 y = a
      · rcases hb1 with ⟨y, rfl⟩
        simp [Renaming1_channel_fun_f (f := g1) (g := g2) (x := y) hg1 hg12,
          Renaming1_channel_fun_fix (f := f1) (g := f2) (c := g2 y) h12
            (fun x => (h1g2 x y).symm) (fun x => (h2g2 x y).symm),
          Renaming1_channel_fun_fix (f := f1) (g := f2) (c := g1 y) h12
            (fun x => (h1g1 x y).symm) (fun x => (h2g1 x y).symm)]
      · by_cases hb2 : ∃ y, g2 y = a
        · rcases hb2 with ⟨y, rfl⟩
          simp [Renaming_channel_fun_g (f := g1) (g := g2) (x := y) hg2 hg12,
            Renaming1_channel_fun_fix (f := f1) (g := f2) (c := g1 y) h12
              (fun x => (h1g1 x y).symm) (fun x => (h2g1 x y).symm),
            Renaming1_channel_fun_fix (f := f1) (g := f2) (c := g2 y) h12
              (fun x => (h1g2 x y).symm) (fun x => (h2g2 x y).symm)]
        · simp [Renaming1_channel_fun_fix (f := f1) (g := f2) (c := a) h12
            (not_exists_of_not_exists_eq ha1) (not_exists_of_not_exists_eq ha2),
            Renaming1_channel_fun_fix (f := g1) (g := g2) (c := a) hg12
            (not_exists_of_not_exists_eq hb1) (not_exists_of_not_exists_eq hb2)]

theorem Renaming_channel_independ :
    ∀ {x y α : Type _} (f1 f2 : x → α) (g1 g2 : y → α) (a b c d d' : α),
      (Injective f1 ∧ Injective f2 ∧ Injective g1 ∧ Injective g2 ∧
        (∀ x y, f1 x ≠ f2 y) ∧
        (∀ x y, f1 x ≠ g1 y) ∧
        (∀ x y, f1 x ≠ g2 y) ∧
        (∀ x y, f2 x ≠ g1 y) ∧
        (∀ x y, f2 x ≠ g2 y) ∧
        (∀ x y, g1 x ≠ g2 y) ∧
        ((a, b) ∈ (f1 <==> f2)) ∧
        ((b, d) ∈ (g1 <==> g2)) ∧
        ((a, c) ∈ (g1 <==> g2)) ∧
        ((c, d') ∈ (f1 <==> f2))) →
      d = d' := by
  intro x y α f1 f2 g1 g2 a b c d d' h
  rcases h with ⟨hf1, hf2, hg1, hg2, h12, h1g1, h1g2, h2g1, h2g2, hg12, hab, hbd, hac, hcd'⟩
  have hb : b = Renaming1_channel_fun f1 f2 a := by
    simpa using hab
  have hc : c = Renaming1_channel_fun g1 g2 a := by
    simpa using hac
  subst b
  subst c
  have hd : d = Renaming1_channel_fun g1 g2 (Renaming1_channel_fun f1 f2 a) := by
    simpa using hbd
  have hd' : d' = Renaming1_channel_fun f1 f2 (Renaming1_channel_fun g1 g2 a) := by
    simpa using hcd'
  subst d
  subst d'
  exact Renaming_channel_fun_independ hf1 hf2 hg1 hg2 h12 h1g1 h1g2 h2g1 h2g2 hg12 a

end
