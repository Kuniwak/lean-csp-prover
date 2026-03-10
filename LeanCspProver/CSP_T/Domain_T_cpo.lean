           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
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

import LeanCspProver.CSP_T.Domain_T
import LeanCspProver.CSP.CPO

noncomputable section

/-
(*****************************************************************

         1. Domain_T is a pointed cpo.
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
                      Bottom in Dom_T
 *********************************************************)
-/

instance instBot0DomT {α : Type _} : bot0 (domTType α) where
  toPartialOrder := inferInstance
  bot := Abs_domT ({<>} : Set (traceType α))

@[simp]
theorem bottom_domT_def {α : Type _} :
    (Bot : domTType α) = Abs_domT ({<>} : Set (traceType α)) :=
  rfl

theorem bottom_domT {α : Type _} :
    ∀ T : domTType α, Bot <= T := by
  intro T
  change Abs_domT ({<>} : Set (traceType α)) <= T
  exact BOT_is_bottom_domT (T := T)

instance instBotDomT {α : Type _} : bot (domTType α) where
  bottom_bot := bottom_domT

/-
(**********************************************************
      lemmas used in a proof that domain_T is a cpo.
 **********************************************************)
-/

/- UnionT Ts is an upper bound of Ts -/

theorem UnionT_isUB {α : Type _} {Ts : Set (domTType α)} :
    isUB (UnionT Ts) Ts := by
  intro T hT
  exact subdomTI (fun t ht => memT_UnionT_if hT ht)

/- UnionT Ts is the least upper bound of Ts -/

theorem UnionT_isLUB {α : Type _} {Ts : Set (domTType α)} :
    Ts ≠ ∅ → isLUB (UnionT Ts) Ts := by
  intro hTs
  constructor
  · exact UnionT_isUB
  · intro T hT
    exact subdomTI <| by
      intro t ht
      rcases memT_UnionT_only_if hTs ht with ⟨S, hS, htS⟩
      exact hT S hS htS

/- the least upper bound of Ts is UnionT Ts -/

theorem isLUB_UnionT_only_if {α : Type _} {T : domTType α} {Ts : Set (domTType α)} :
    Ts ≠ ∅ → isLUB T Ts → T = UnionT Ts := by
  intro hTs hT
  exact LUB_unique hT (UnionT_isLUB (Ts := Ts) hTs)

/- iff -/

theorem isLUB_UnionT {α : Type _} {T : domTType α} {Ts : Set (domTType α)} :
    Ts ≠ ∅ → (isLUB T Ts ↔ T = UnionT Ts) := by
  intro hTs
  constructor
  · exact isLUB_UnionT_only_if hTs
  · intro hT
    simpa [hT] using (UnionT_isLUB (Ts := Ts) hTs)

/- LUB is UnionT Ts -/

theorem LUB_UnionT {α : Type _} {Ts : Set (domTType α)} :
    Ts ≠ ∅ → LUB Ts = UnionT Ts := by
  intro hTs
  exact isLUB_LUB (UnionT_isLUB (Ts := Ts) hTs)

/-
(**********************************************************
                 ( domT, <= ) is a CPO
 **********************************************************)
-/

instance instCpoDomT {α : Type _} : cpo (domTType α) where
  toPartialOrder := inferInstance
  toInhabited := inferInstance
  complete_cpo := by
    intro X hX
    exact ⟨UnionT X, UnionT_isLUB (Ts := X) (Set.nonempty_iff_ne_empty.mp hX.1)⟩

/-
(**********************************************************
              ( domT, <= ) is a pointed CPO
 **********************************************************)
-/

instance instCpoBotDomT {α : Type _} : cpo_bot (domTType α) where
  complete_cpo := by
    intro X hX
    exact ⟨UnionT X, UnionT_isLUB (Ts := X) (Set.nonempty_iff_ne_empty.mp hX.1)⟩
  bottom_bot := bottom_domT

/-(****************** to add them again ******************)
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
-/
/-
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
-/

end
