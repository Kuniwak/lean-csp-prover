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
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.CPO

open Function

noncomputable section

/-
(*****************************************************************

         1. Pairs of CPO are also CPO.
         2.
         3.
         4.

 *****************************************************************)

Lean handles pair witnesses directly, so no special split rules are needed here.
-/

/-
(**********************************************************
              def: pair of bot
 **********************************************************)
-/

instance instBot0Prod {α β : Type _} [bot0 α] [bot0 β] : bot0 (α × β) where
  toPartialOrder := inferInstance
  bot := (Bot, Bot)

@[simp]
theorem pair_Bot_def {α β : Type _} [bot0 α] [bot0 β] :
    (Bot : α × β) = ((Bot : α), (Bot : β)) :=
  rfl

/-
(************************************************************
                   Pairuct bot ==> bot
 ************************************************************)
-/

/- (*** pair Bot ***) -/

theorem pair_Bot {α β : Type _} [bot α] [bot β] :
    ∀ x : α × β, Bot <= x := by
  intro x
  exact order_pair_def.mpr ⟨bottom_bot (Prod.fst x), bottom_bot (Prod.snd x)⟩

/-
(*****************************
       Pair bot => bot
 *****************************)
-/

instance instBotProd {α β : Type _} [bot α] [bot β] : bot (α × β) where
  bottom_bot := pair_Bot

/-
(************************************************************
                   Pair CPO ==> CPO
 ************************************************************)
-/

/- (*** pair directed decompo ***) -/

theorem pair_directed_decompo_fst {α β : Type _} [cpo α] [cpo β]
    {Xc : Set (α × β)} :
    directed Xc → directed (Prod.fst '' Xc) := by
  intro hXc
  rcases hXc.1 with ⟨x, hx⟩
  constructor
  · exact ⟨Prod.fst x, ⟨x, hx, rfl⟩⟩
  · intro ya yb hya hyb
    rcases hya with ⟨xa, hxa, rfl⟩
    rcases hyb with ⟨xb, hxb, rfl⟩
    rcases hXc.2 xa xb hxa hxb with ⟨z, hz, hxz, hyz⟩
    refine ⟨Prod.fst z, ⟨z, hz, rfl⟩, ?_, ?_⟩
    · exact (order_pair_def.mp hxz).1
    · exact (order_pair_def.mp hyz).1

theorem pair_directed_decompo_snd {α β : Type _} [cpo α] [cpo β]
    {Xc : Set (α × β)} :
    directed Xc → directed (Prod.snd '' Xc) := by
  intro hXc
  rcases hXc.1 with ⟨x, hx⟩
  constructor
  · exact ⟨Prod.snd x, ⟨x, hx, rfl⟩⟩
  · intro ya yb hya hyb
    rcases hya with ⟨xa, hxa, rfl⟩
    rcases hyb with ⟨xb, hxb, rfl⟩
    rcases hXc.2 xa xb hxa hxb with ⟨z, hz, hxz, hyz⟩
    refine ⟨Prod.snd z, ⟨z, hz, rfl⟩, ?_, ?_⟩
    · exact (order_pair_def.mp hxz).2
    · exact (order_pair_def.mp hyz).2

/- (*** pair cpo lemma ***) -/

theorem pair_cpo_lm {α β : Type _} [cpo α] [cpo β] {Xc : Set (α × β)} :
    directed Xc → hasLUB Xc := by
  intro hXc
  have hfst : hasLUB (Prod.fst '' Xc) := complete_cpo _ (pair_directed_decompo_fst hXc)
  have hsnd : hasLUB (Prod.snd '' Xc) := complete_cpo _ (pair_directed_decompo_snd hXc)
  refine ⟨(LUB (Prod.fst '' Xc), LUB (Prod.snd '' Xc)), ?_⟩
  exact pair_LUB_decompo.mpr ⟨LUB_is hfst, LUB_is hsnd⟩

/-
(*****************************
       Pair CPO => CPO
 *****************************)
-/

instance instCpoProd {α β : Type _} [cpo α] [cpo β] : cpo (α × β) where
  toPartialOrder := inferInstance
  toInhabited := inferInstance
  complete_cpo := fun X => pair_cpo_lm (Xc := X)

/-
(************************************************************
                Pairuct CPO_BOT ==> CPO_BOT
 ************************************************************)
-/

instance instCpoBotProd {α β : Type _} [cpo_bot α] [cpo_bot β] : cpo_bot (α × β) where
  complete_cpo := fun X => pair_cpo_lm (Xc := X)
  bottom_bot := pair_Bot

/-
(************************************************************
                     fst continuity
 ************************************************************)
-/

theorem fst_continuous {α β : Type _} [cpo α] [cpo β] :
    continuous (Prod.fst : α × β → α) := by
  apply (continuous_if_cpo (f := (Prod.fst : α × β → α)))
  intro X hX
  let x : α × β := LUB X
  have hLUBX : isLUB x X := by
    simpa [x] using (LUB_is (complete_cpo X hX))
  exact ⟨x, (pair_LUB_decompo.mp hLUBX).1, hLUBX⟩

theorem snd_continuous {α β : Type _} [cpo α] [cpo β] :
    continuous (Prod.snd : α × β → β) := by
  apply (continuous_if_cpo (f := (Prod.snd : α × β → β)))
  intro X hX
  let x : α × β := LUB X
  have hLUBX : isLUB x X := by
    simpa [x] using (LUB_is (complete_cpo X hX))
  exact ⟨x, (pair_LUB_decompo.mp hLUBX).2, hLUBX⟩

/-
(************************************************************
                   Pair continuity
 ************************************************************)
-/

theorem pair_continuous_only_if {α β γ : Type _} [cpo α] [cpo β] [cpo γ]
    {h : α → β × γ} :
    continuous h → (continuous (Prod.fst ∘ h) ∧ continuous (Prod.snd ∘ h)) := by
  intro hh
  exact ⟨compo_continuous hh fst_continuous, compo_continuous hh snd_continuous⟩

theorem pair_continuous_if {α β γ : Type _} [cpo α] [cpo β] [cpo γ]
    {h : α → β × γ} :
    continuous (Prod.fst ∘ h) → continuous (Prod.snd ∘ h) → continuous h := by
  intro hfst hsnd
  apply continuous_if_cpo
  intro X hX
  have hLUBX : hasLUB X := complete_cpo X hX
  have hfstX := hfst X hX
  have hsndX := hsnd X hX
  refine ⟨LUB X, ?_, LUB_is hLUBX⟩
  change isLUB (Prod.fst (h (LUB X)), Prod.snd (h (LUB X))) (h '' X)
  apply pair_LUB_decompo.mpr
  constructor
  · have hfstLUB : isLUB (LUB ((Prod.fst ∘ h) '' X)) ((Prod.fst ∘ h) '' X) := LUB_is hfstX.1
    have hfstEq : LUB ((Prod.fst ∘ h) '' X) = Prod.fst (h (LUB X)) := hfstX.2
    exact hfstEq ▸ (by simpa [Function.comp, Set.image_image] using hfstLUB)
  · have hsndLUB : isLUB (LUB ((Prod.snd ∘ h) '' X)) ((Prod.snd ∘ h) '' X) := LUB_is hsndX.1
    have hsndEq : LUB ((Prod.snd ∘ h) '' X) = Prod.snd (h (LUB X)) := hsndX.2
    exact hsndEq ▸ (by simpa [Function.comp, Set.image_image] using hsndLUB)

theorem pair_continuous {α β γ : Type _} [cpo α] [cpo β] [cpo γ]
    {h : α → β × γ} :
    continuous h ↔ (continuous (Prod.fst ∘ h) ∧ continuous (Prod.snd ∘ h)) := by
  constructor
  · exact pair_continuous_only_if
  · rintro ⟨hfst, hsnd⟩
    exact pair_continuous_if hfst hsnd

end
