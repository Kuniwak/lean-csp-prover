           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.Set_F
import LeanCspProver.CSP.CPO

noncomputable section

/-
(*****************************************************************

         1. Set_F is a pointed cpo.
         2.
         3.
         4.

 *****************************************************************)
-/

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.        -/
/-                  `Union (B \` A) = (UN x:A. B x)`                -/
/-                  `Inter (B \` A) = (INT x:A. B x)`               -/

/-
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
-/
/- no simp rules in Isabelle 2017
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
-/

/-
(*********************************************************
                      Bottom in Set_T
 *********************************************************)
-/

instance instBot0SetF {α : Type _} : bot0 (setFType α) where
  toPartialOrder := inferInstance
  bot := {}f

@[simp]
theorem bottom_setF_def {α : Type _} :
    (Bot : setFType α) = {}f :=
  rfl

theorem bottom_setF {α : Type _} :
    ∀ F : setFType α, Bot <= F := by
  intro F
  change {}f <= F
  exact BOT_is_bottom_setF (F := F)

instance instBotSetF {α : Type _} : bot (setFType α) where
  bottom_bot := bottom_setF

/-
(**********************************************************
      lemmas used in a proof that set_F is a cpo.
 **********************************************************)
-/

/- UnionF Fs is an upper bound of Fs -/

theorem UnionF_isUB {α : Type _} {Fs : Set (setFType α)} :
    isUB (UnionF Fs) Fs := by
  intro F hF
  exact subsetFI (fun s X hsX => memF_UnionF_if hF hsX)

/- UnionF Fs is the least upper bound of Fs -/

theorem UnionF_isLUB {α : Type _} {Fs : Set (setFType α)} :
    isLUB (UnionF Fs) Fs := by
  constructor
  · exact UnionF_isUB
  · intro F hF
    exact subsetFI <| by
      intro s X hsX
      rcases memF_UnionF_only_if hsX with ⟨E, hE, hsXE⟩
      exact hF E hE hsXE

/- the least upper bound of Fs is UnionF Fs -/

theorem isLUB_UnionF_only_if {α : Type _} {F : setFType α} {Fs : Set (setFType α)} :
    isLUB F Fs → F = UnionF Fs := by
  intro hF
  exact LUB_unique hF UnionF_isLUB

/- iff -/

theorem isLUB_UnionF {α : Type _} {F : setFType α} {Fs : Set (setFType α)} :
    isLUB F Fs ↔ F = UnionF Fs := by
  constructor
  · exact isLUB_UnionF_only_if
  · intro hF
    simpa [hF] using (UnionF_isLUB (Fs := Fs))

/- LUB is UnionF Fs -/

theorem LUB_UnionF {α : Type _} {Fs : Set (setFType α)} :
    LUB Fs = UnionF Fs :=
  isLUB_LUB (UnionF_isLUB (Fs := Fs))

/-
(**********************************************************
                 ( setF, <= ) is a CPO
 **********************************************************)
-/

instance instCpoSetF {α : Type _} : cpo (setFType α) where
  toPartialOrder := inferInstance
  toInhabited := inferInstance
  complete_cpo := by
    intro X _
    exact ⟨UnionF X, UnionF_isLUB⟩

/-
(**********************************************************
              ( setF, <= ) is a pointed CPO
 **********************************************************)
-/

instance instCpoBotSetF {α : Type _} : cpo_bot (setFType α) where
  complete_cpo := by
    intro X _
    exact ⟨UnionF X, UnionF_isLUB⟩
  bottom_bot := bottom_setF

/-(****************** to add them again ******************)
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
-/
/-
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
-/

end
