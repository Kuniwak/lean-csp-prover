           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                 August 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.CPO_prod

noncomputable section

/-
(*****************************************************************

         1. Bool is CPO.
         2. Sets are CPO.
         3.
         4.

The original file contains several Isabelle-version-specific Bool fragments.
Lean already provides the needed order structure on `Bool`, so only the active
`set` development is translated here.

 *****************************************************************)
-/

/-
(**********************************************************
              def: bot in bool
 **********************************************************)
-/

/-
Lean does not need the Isabelle-specific `le_bool_def` adjustments here.
-/

/-
(************************************************************
                   Bool bot ==> bot
 ************************************************************)
-/

/-
The original Bool-specific instance code is omitted because it was only needed
for legacy Isabelle versions.
-/

/-
(************************************************************
                   Set bot ==> bot

                    Isabelle 2011
 ************************************************************)
-/

/- (*** set Bot ***) -/

instance instBot0Set {α : Type _} : bot0 (Set α) where
  toPartialOrder := inferInstance
  bot := {}

@[simp]
theorem set_Bot_def {α : Type _} : (Bot : Set α) = {} :=
  rfl

theorem set_Bot {α : Type _} :
    ∀ X : Set α, Bot <= X := by
  intro X
  simp

instance instBotSet {α : Type _} : bot (Set α) where
  bottom_bot := set_Bot

/-
(************************************************************
                      Bool : CPO
 ************************************************************)
-/

/-
The original Bool-specific CPO proof is omitted because it was only needed for
legacy Isabelle versions.
-/

/-
(************************************************************
                      Bool : CPO_BOT
 ************************************************************)
-/

/-
The original Bool-specific `cpo_bot` instance is omitted for the same reason.
-/

/-
(************************************************************
                      Set : CPO
 ************************************************************)
-/

theorem set_cpo_lm {α : Type _} {Xs : Set (Set α)} :
    directed Xs → hasLUB Xs := by
  intro _
  exact ⟨Set.sUnion Xs, Union_isLUB⟩

/-
(*****************************
          Set : CPO
 *****************************)
-/

instance instCpoSet {α : Type _} : cpo (Set α) where
  toPartialOrder := inferInstance
  toInhabited := inferInstance
  complete_cpo := fun X => set_cpo_lm (Xs := X)

/-
(************************************************************
                      Set : CPO_BOT
 ************************************************************)
-/

instance instCpoBotSet {α : Type _} : cpo_bot (Set α) where
  complete_cpo := fun X => set_cpo_lm (Xs := X)
  bottom_bot := set_Bot

end
