           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra

open Function

noncomputable section

/-
(*****************************************************************

         1. Complete partial order (cpo)
         2. Continuity
         3. Tarski Theorem

 *****************************************************************)
-/

def directed {α : Type _} [Preorder α] (X : Set α) : Prop :=
  Set.Nonempty X ∧
    ∀ x y, x ∈ X → y ∈ X → ∃ z, z ∈ X ∧ x <= z ∧ y <= z

theorem directed_def {α : Type _} [Preorder α] {X : Set α} :
    directed X ↔
      (Set.Nonempty X ∧
        ∀ x y, x ∈ X → y ∈ X → ∃ z, z ∈ X ∧ x <= z ∧ y <= z) :=
  Iff.rfl

class bot0 (α : Type _) extends PartialOrder α, Bot α

notation "Bot" => (⊥)

instance {α : Type _} [bot0 α] : Inhabited α :=
  ⟨Bot⟩

class bot (α : Type _) extends bot0 α where
  bottom_bot : ∀ x : α, Bot <= x

@[simp]
theorem bottom_bot {α : Type _} [bot α] (x : α) : Bot <= x :=
  bot.bottom_bot x

class cpo (α : Type _) extends PartialOrder α, Inhabited α where
  complete_cpo : ∀ X : Set α, directed X → hasLUB X

theorem complete_cpo {α : Type _} [cpo α] (X : Set α) :
    directed X → hasLUB X :=
  cpo.complete_cpo X

/- *** pointed cpo *** -/

class cpo_bot (α : Type _) extends cpo α, bot α

def continuous {α : Type _} {β : Type _} [cpo α] [cpo β] (f : α → β) : Prop :=
  ∀ X, directed X → hasLUB (f '' X) ∧ LUB (f '' X) = f (LUB X)

def admissible {α : Type _} [cpo α] (P : α → Prop) : Prop :=
  ∀ X, directed X → (∀ x ∈ X, P x) → P (LUB X)

/-
(**********************************************************
                    small lemmas
 **********************************************************)
-/

theorem complete_cpo_lm {α : Type _} [cpo α] :
    ∀ X : Set α, directed X → hasLUB X := by
  intro X
  exact complete_cpo X

/- *** another definition of continuous *** -/

theorem continuous_only_if {α : Type _} {β : Type _} [cpo α] [cpo β]
    {f : α → β} {X : Set α} :
    continuous f →
      directed X → ∃ x, isLUB (f x) (f '' X) ∧ isLUB x X := by
  intro hcont hX
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  have hfx := hcont X hX
  simpa [hfx.2] using (LUB_is hfx.1)

/-
Isabelle theorem name: continuous_if
-/
theorem continuous_if_cpo {α : Type _} {β : Type _} [cpo α] [cpo β] {f : α → β} :
    (∀ X, directed X → ∃ x, isLUB (f x) (f '' X) ∧ isLUB x X) →
      continuous f := by
  intro h X hX
  rcases h X hX with ⟨x, hfx, hx⟩
  have hX' : hasLUB X := complete_cpo X hX
  constructor
  · exact ⟨f x, hfx⟩
  · have hxEq : x = LUB X := (isLUB_to_LUB (X := X) (x := x) hX').mp hx
    have hfxEq : f x = LUB (f '' X) := by
      exact (isLUB_to_LUB (X := f '' X) (x := f x) ⟨f x, hfx⟩).mp hfx
    calc
      LUB (f '' X) = f x := hfxEq.symm
      _ = f (LUB X) := by simp [hxEq]

/- *** iff *** -/

theorem continuous_iff {α : Type _} {β : Type _} [cpo α] [cpo β] {f : α → β} :
    continuous f ↔
      (∀ X, directed X → ∃ x, isLUB (f x) (f '' X) ∧ isLUB x X) := by
  constructor
  · intro h X hX
    exact continuous_only_if (f := f) (X := X) h hX
  · exact continuous_if_cpo

/-
(**********************************************************
             lemmas and theorems for Tarski
 **********************************************************)
-/

/- LUB is not affected by Bot -/

theorem LUB_with_Bot {α : Type _} [cpo_bot α] {f : α → Prop} {x : α} :
    isLUB x {y | f y ∨ y = Bot} ↔ isLUB x {y | f y} := by
  constructor
  · intro hx
    constructor
    · intro y hy
      exact hx.1 y (Or.inl hy)
    · intro y hy
      exact hx.2 y <| by
        intro z hz
        rcases hz with hz | rfl
        · exact hy z hz
        · exact bottom_bot y
  · intro hx
    constructor
    · intro y hy
      rcases hy with hy | rfl
      · exact hx.1 y hy
      · exact bottom_bot x
    · intro y hy
      exact hx.2 y (fun z hz => hy z (Or.inl hz))

/-
(************************************************************)

(* if x<=y then {x,y} is a directed set. *)
(* this is used in a proof for continuous_mono *)
-/

theorem directed_x_y {α : Type _} [PartialOrder α] {x y : α} :
    x <= y → directed ({x, y} : Set α) := by
  intro hxy
  constructor
  · exact ⟨x, by simp⟩
  · intro a b ha hb
    refine ⟨y, by
      constructor
      · simp
      constructor
      · rcases (by simpa [eq_comm] using ha : a = x ∨ a = y) with rfl | rfl
        · exact hxy
        · exact le_rfl
      · rcases (by simpa [eq_comm] using hb : b = x ∨ b = y) with rfl | rfl
        · exact hxy
        · exact le_rfl⟩

/- the least upper bound of a set {x,y} -/
/- this is used in a proof for continuous_mono -/

theorem LUB_x_y {α : Type _} [PartialOrder α] {x y z : α} :
    x <= y → isLUB z ({x, y} : Set α) → z = y := by
  intro hxy hz
  apply le_antisymm
  · exact hz.2 y (by
      intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | rfl
      · exact hxy
      · exact le_rfl)
  · exact hz.1 y (by simp)

/- ************************ continuity ***************************** -/

/- f is continuous --> f is monotonic -/

theorem continuous_mono {α : Type _} {β : Type _} [cpo α] [cpo β] {f : α → β} :
    continuous f → mono f := by
  intro hcont A B hAB
  rcases (continuous_iff.mp hcont) ({A, B} : Set α) (directed_x_y hAB) with ⟨x, hfx, hx⟩
  have hxB : x = B := LUB_x_y hAB hx
  have hAx : f A <= f x := hfx.1 (f A) ⟨A, by simp, rfl⟩
  simpa [hxB] using hAx

/- directed and functions -/

theorem directed_continuous {α : Type _} {β : Type _} [cpo α] [cpo β]
    {f : α → β} {X : Set α} :
    continuous f → directed X → directed (f '' X) := by
  intro hcont hX
  have hmono : mono f := continuous_mono hcont
  rcases hX.1 with ⟨x, hx⟩
  constructor
  · exact ⟨f x, ⟨x, hx, rfl⟩⟩
  · intro ya yb hya hyb
    rcases hya with ⟨xa, hxa, rfl⟩
    rcases hyb with ⟨xb, hxb, rfl⟩
    rcases hX.2 xa xb hxa hxb with ⟨z, hz, hxz, hyz⟩
    exact ⟨f z, ⟨z, hz, rfl⟩, hmono hxz, hmono hyz⟩

/- composition of continuous functions -/

theorem compo_continuous {α : Type _} {β : Type _} {γ : Type _}
    [cpo α] [cpo β] [cpo γ] {f : α → β} {g : β → γ} :
    continuous f → continuous g → continuous (g ∘ f) := by
  intro hf hg
  apply continuous_if_cpo
  intro X hX
  rcases (continuous_iff.mp hf) X hX with ⟨x, hfx, hx⟩
  rcases (continuous_iff.mp hg) (f '' X) (directed_continuous hf hX) with ⟨y, hgy, hy⟩
  have hyEq : y = f x := LUB_unique hy hfx
  refine ⟨x, ?_, hx⟩
  simpa [Function.comp, Set.image_image, hyEq] using hgy

/- *********************** Tarski continuous **************************** -/

theorem Tarski_directed_lm1 {α : Type _} [cpo_bot α] {f : α → α} :
    mono f → ∀ n, (f^[n]) Bot <= (f^[n + 1]) Bot := by
  intro hmono n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Function.iterate_succ_apply'] using hmono ih

theorem Tarski_directed_lm2 {α : Type _} [cpo_bot α] {f : α → α} :
    mono f → ∀ n m, (f^[n]) Bot <= (f^[n + m]) Bot := by
  intro hmono n m
  induction m with
  | zero =>
      simp
  | succ m ih =>
      exact le_trans ih <| by
        simpa [Nat.add_assoc, Function.iterate_succ_apply'] using
          (Tarski_directed_lm1 (f := f) hmono (n + m))

theorem Tarski_directed {α : Type _} [cpo_bot α] {f : α → α} :
    mono f → directed {x | ∃ n, x = (f^[n]) Bot} := by
  intro hmono
  constructor
  · exact ⟨Bot, ⟨0, by simp⟩⟩
  · intro x y hx hy
    rcases hx with ⟨n, rfl⟩
    rcases hy with ⟨m, rfl⟩
    by_cases hmn : m <= n
    · refine ⟨(f^[n]) Bot, ⟨n, rfl⟩, le_rfl, ?_⟩
      simpa [Nat.add_sub_of_le hmn] using
        (Tarski_directed_lm2 (f := f) hmono m (n - m))
    · have hnm : n <= m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      refine ⟨(f^[m]) Bot, ⟨m, rfl⟩, ?_, le_rfl⟩
      simpa [Nat.add_sub_of_le hnm] using
        (Tarski_directed_lm2 (f := f) hmono n (m - n))

theorem Tarski_image_expand_lm {α : Type _} [cpo_bot α] {f : α → α} :
    f '' {x | ∃ n, x = (f^[n]) Bot} = {x | ∃ n, x = f ((f^[n]) Bot)} := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨(f^[n]) Bot, ⟨n, rfl⟩, rfl⟩

theorem Tarski_by_continuity {α : Type _} [cpo_bot α] {f : α → α} :
    continuous f →
      ∃ x, isLUB (f x) {x | ∃ n, x = f ((f^[n]) Bot)} ∧
        isLUB x {x | ∃ n, x = (f^[n]) Bot} := by
  intro hcont
  rcases (continuous_iff.mp hcont) {x | ∃ n, x = (f^[n]) Bot}
      (Tarski_directed (f := f) (continuous_mono hcont)) with ⟨x, hx1, hx2⟩
  refine ⟨x, ?_, hx2⟩
  simpa [Tarski_image_expand_lm] using hx1

/- ****** -/

theorem Tarski_LUB_lm {α : Type _} [cpo_bot α] {f : α → α} {x : α} :
    (∃ n, x = (f^[n]) Bot) ↔ (∃ n, x = (f^[(Nat.succ n)]) Bot) ∨ x = Bot := by
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero =>
        exact Or.inr rfl
    | succ n =>
        exact Or.inl ⟨n, rfl⟩
  · intro h
    rcases h with h | h
    · rcases h with ⟨n, rfl⟩
      exact ⟨n + 1, rfl⟩
    · exact ⟨0, by simpa using h⟩

/- ****** -/

theorem Tarski_LUB {α : Type _} [cpo_bot α] :
    ∀ (f : α → α) x,
      isLUB x {x | ∃ n, x = f ((f^[n]) Bot)} ↔
        isLUB x {x | ∃ n, x = (f^[n]) Bot} := by
  intro f x
  simpa [Tarski_LUB_lm, Function.iterate_succ_apply'] using
    (LUB_with_Bot (f := fun y => ∃ n, y = (f^[(Nat.succ n)]) Bot) (x := x)).symm

/- ****** -/

theorem Tarski_least_lm {α : Type _} [cpo_bot α] {f : α → α} {y : α} :
    mono f → y = f y → ∀ n, (f^[n]) Bot <= y := by
  intro hmono hy n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hfy : f y = y := hy.symm
      exact le_trans (by simpa [Function.iterate_succ_apply'] using hmono ih) (by simp [hfy])

theorem Tarski_least {α : Type _} [cpo_bot α] {f : α → α} {x y : α} :
    mono f →
      isLUB x {x | ∃ n, x = (f^[n]) Bot} →
      y = f y → x <= y := by
  intro hmono hx hy
  exact hx.2 y <| by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    exact Tarski_least_lm (f := f) hmono hy n

/- -------------------*
 |       Tarski      |
 *------------------- -/

theorem Tarski_thm {α : Type _} [cpo_bot α] {f : α → α} :
    continuous f →
      hasLFP f ∧ isLUB (LFP f) {x | ∃ n, x = (f^[n]) Bot} := by
  intro hcont
  rcases Tarski_by_continuity (f := f) hcont with ⟨x, hfx, hx⟩
  have hfx' : isLUB (f x) {x | ∃ n, x = (f^[n]) Bot} :=
    (Tarski_LUB (f := f) (x := f x)).mp hfx
  have hfp : x = f x := LUB_unique hx hfx'
  have hxlfp : isLFP x f := by
    constructor
    · exact hfp
    · intro y hy
      exact Tarski_least (f := f) (continuous_mono hcont) hx hy
  constructor
  · exact ⟨x, hxlfp⟩
  · simpa [isLFP_LFP hxlfp] using hx

/- -------------------*
 |    Tarski LUB     |
 *------------------- -/

theorem Tarski_thm_LFP_LUB {α : Type _} [cpo_bot α] {f : α → α} :
    continuous f → LFP f = LUB {x | ∃ n, x = (f^[n]) Bot} := by
  intro hcont
  exact (isLUB_LUB ((Tarski_thm (f := f) hcont).2)).symm

/- --------------------*
 | Tarski (existency) |
 *-------------------- -/

theorem Tarski_thm_EX {α : Type _} [cpo_bot α] {f : α → α} :
    continuous f → hasLFP f := by
  intro hcont
  exact (Tarski_thm (f := f) hcont).1

/- ========================================================*
 |           Fixed Point Induction (pointed CPO)          |
 *======================================================== -/

theorem cpo_fixpoint_induction {α : Type _} [cpo_bot α] {R : α → Prop} {f : α → α} :
    R Bot → continuous f → admissible R → inductivefun R f →
      hasLFP f ∧ R (LFP f) := by
  intro hBot hcont hAdm hInd
  have hTarski := Tarski_thm (f := f) hcont
  have hDir : directed {x | ∃ n, x = (f^[n]) Bot} :=
    Tarski_directed (f := f) (continuous_mono hcont)
  have hAll : ∀ x ∈ {x | ∃ n, x = (f^[n]) Bot}, R x := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact inductivefun_all_n hInd hBot n
  have hRLUB : R (LUB {x | ∃ n, x = (f^[n]) Bot}) := hAdm _ hDir hAll
  constructor
  · exact hTarski.1
  · simpa [Tarski_thm_LFP_LUB (f := f) hcont] using hRLUB

theorem cpo_fixpoint_induction_R {α : Type _} [cpo_bot α] {R : α → Prop} {f : α → α} :
    R Bot → continuous f → admissible R → inductivefun R f →
      R (LFP f) := by
  intro hBot hcont hAdm hInd
  exact (cpo_fixpoint_induction (f := f) hBot hcont hAdm hInd).2

/- ----------------------------------------------------------*
 |                                                          |
 |       Fixed point induction for refinement (CPO)         |
 |                                                          |
 *---------------------------------------------------------- -/

/- ************************************************************
         admissibility lemma for refinement for cpo
 ************************************************************ -/

theorem admissible_Rev_fun {α : Type _} [cpo α] {X : α} :
    admissible (Rev_fun X) := by
  intro Y hY hAll
  exact LUB_least hAll (complete_cpo Y hY)

/- *** Bot *** -/

theorem Rev_fun_Bot {α : Type _} [bot α] {X : α} : Rev_fun X Bot := by
  simp [Rev_fun]

/- ************************************************************
         Fixed Point Induction (CPO) for refinement
 ************************************************************ -/

theorem cpo_fixpoint_induction_rev {α : Type _} [cpo_bot α] {f : α → α} {X : α} :
    continuous f → f X <= X → LFP f <= X := by
  intro hcont hX
  have hInd : inductivefun (Rev_fun X) f := by
    intro x hx
    have hmono : mono f := continuous_mono hcont
    exact le_trans (hmono hx) hX
  simpa [Rev_fun] using
    (cpo_fixpoint_induction_R (R := Rev_fun X) (f := f) (Rev_fun_Bot) hcont
      admissible_Rev_fun hInd)

/- *** EX version *** -/

theorem cpo_fixpoint_induction_rev_EX {α : Type _} [cpo_bot α] {f : α → α} {X Y : α} :
    continuous f → f X <= X → isLFP Y f → Y <= X := by
  intro hcont hX hY
  simpa [isLFP_LFP hY] using (cpo_fixpoint_induction_rev (f := f) (X := X) hcont hX)

/-(*****************************************************************)-/

end
