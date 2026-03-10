           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.CPO

open Function

noncomputable section

/-
(*****************************************************************

         1. Productions of CPO are also CPO.
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(**********************************************************
              def: prod of bot
 **********************************************************)
-/

instance instBot0Fun {ι : Type _} {α : Type _} [bot0 α] : bot0 (ι → α) where
  toPartialOrder := inferInstance
  bot := fun _ => Bot

@[simp]
theorem prod_Bot_def {ι : Type _} {α : Type _} [bot0 α] :
    (Bot : ι → α) = fun _ => Bot :=
  rfl

/-
(************************************************************
                   Product bot ==> bot
 ************************************************************)
-/

/- (*** prod Bot ***) -/

theorem prod_Bot {ι : Type _} {α : Type _} [bot α] :
    ∀ x : ι → α, Bot <= x := by
  intro x i
  exact bottom_bot (x i)

/-
(*****************************
       Prod bot => bot
 *****************************)
-/

instance instBotFun {ι : Type _} {α : Type _} [bot α] : bot (ι → α) where
  bottom_bot := prod_Bot

/-
(************************************************************
                   Product CPO ==> CPO
 ************************************************************)
-/

/- (*** prod directed decompo ***) -/

theorem prod_directed_decompo {ι : Type _} {α : Type _} [cpo α]
    {Xp : Set (ι → α)} :
    directed Xp → ∀ i, directed (proj_fun i '' Xp) := by
  intro hXp i
  rcases hXp.1 with ⟨xp, hxp⟩
  constructor
  · exact ⟨xp i, ⟨xp, hxp, rfl⟩⟩
  · intro x y hx hy
    rcases hx with ⟨xp, hxp, rfl⟩
    rcases hy with ⟨yp, hyp, rfl⟩
    rcases hXp.2 xp yp hxp hyp with ⟨z, hz, hxpz, hypz⟩
    exact ⟨z i, ⟨z, hz, rfl⟩, hxpz i, hypz i⟩

/- (*** prod cpo lemma ***) -/

theorem prod_cpo_lm {ι : Type _} {α : Type _} [cpo α] {Xp : Set (ι → α)} :
    directed Xp → hasLUB Xp := by
  intro hXp
  refine ⟨fun i => LUB (proj_fun i '' Xp), ?_⟩
  apply prod_LUB_decompo.mpr
  intro i
  exact LUB_is (complete_cpo _ (prod_directed_decompo hXp i))

/-
(*****************************
       Prod CPO => CPO
 *****************************)
-/

instance instCpoFun {ι : Type _} {α : Type _} [cpo α] : cpo (ι → α) where
  toPartialOrder := inferInstance
  toInhabited := inferInstance
  complete_cpo := fun X => prod_cpo_lm (Xp := X)

/-
(************************************************************
                Product CPO_BOT ==> CPO_BOT
 ************************************************************)
-/

instance instCpoBotFun {ι : Type _} {α : Type _} [cpo_bot α] : cpo_bot (ι → α) where
  complete_cpo := fun X => prod_cpo_lm (Xp := X)
  bottom_bot := prod_Bot

/-
(************************************************************
                   Project continuity
 ************************************************************)
-/

theorem proj_continuous {ι : Type _} {α : Type _} [cpo α] (i : ι) :
    continuous (proj_fun i : (ι → α) → α) := by
  apply continuous_if_cpo
  intro X hX
  let x : ι → α := LUB X
  have hLUBX : isLUB x X := by
    simpa [x] using (LUB_is (complete_cpo X hX))
  exact ⟨x, (prod_LUB_decompo.mp hLUBX) i, hLUBX⟩

/-
(************************************************************
                   Product continuity
 ************************************************************)
-/

theorem prod_continuous_only_if {δ : Type _} {ι : Type _} {α : Type _}
    [cpo δ] [cpo α] {h : δ → ι → α} :
    continuous h → ∀ i, continuous (proj_fun i ∘ h) := by
  intro hh i
  exact compo_continuous hh (proj_continuous (i := i))

theorem prod_continuous_if {δ : Type _} {ι : Type _} {α : Type _}
    [cpo δ] [cpo α] {h : δ → ι → α} :
    (∀ i, continuous (proj_fun i ∘ h)) → continuous h := by
  intro hh
  apply continuous_if_cpo
  intro X hX
  have hLUBX : hasLUB X := complete_cpo X hX
  refine ⟨LUB X, ?_, LUB_is hLUBX⟩
  change isLUB (h (LUB X)) (h '' X)
  apply prod_LUB_decompo.mpr
  intro i
  have hiX := hh i X hX
  have hiLUB : isLUB (LUB ((proj_fun i ∘ h) '' X)) ((proj_fun i ∘ h) '' X) := LUB_is hiX.1
  have hiEq : LUB ((proj_fun i ∘ h) '' X) = proj_fun i (h (LUB X)) := by
    simpa [Function.comp] using hiX.2
  exact hiEq ▸ (by
    simpa [Function.comp, Set.image_image] using hiLUB)

theorem prod_continuous {δ : Type _} {ι : Type _} {α : Type _}
    [cpo δ] [cpo α] {h : δ → ι → α} :
    continuous h ↔ ∀ i, continuous (proj_fun i ∘ h) := by
  constructor
  · exact prod_continuous_only_if
  · exact prod_continuous_if

/-
(************************************************************
                    prod_variable continuity
 ************************************************************)
-/

theorem continuous_prod_variable {ι : Type _} {α : Type _} [cpo α] (pn : ι) :
    continuous (fun f : ι → α => f pn) := by
  simpa [proj_fun] using (proj_continuous (i := pn) : continuous (proj_fun pn))

end
