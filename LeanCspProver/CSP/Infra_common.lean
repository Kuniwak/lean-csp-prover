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

import Mathlib

/-
(*****************************************************
           Convenient technique for proofs
 *****************************************************)
-/

/- --------------------------*
 |    remove assumeption    |
 *--------------------------* -/

theorem rem_asmE {A R : Prop} (_ : A) (hR : R) : R := hR

/- --------------------------*
 |      !!x. ==> ALL x.     |
 *--------------------------* -/

theorem rev_all1E {α : Sort _} {P : α → Prop} {S : Prop}
    (hP : ∀ x, P x) (hS : (∀ x, P x) → S) : S :=
  hS hP

theorem rev_all2E {α : Sort _} {β : Sort _} {P : α → β → Prop} {S : Prop}
    (hP : ∀ x y, P x y) (hS : (∀ x y, P x y) → S) : S :=
  hS hP

theorem rev_all3E {α : Sort _} {β : Sort _} {γ : Sort _}
    {P : α → β → γ → Prop} {S : Prop}
    (hP : ∀ x y z, P x y z) (hS : (∀ x y z, P x y z) → S) : S :=
  hS hP

-- Isabelle: lemmas rev_allE = rev_all1E rev_all2E rev_all3E

theorem rev_allI {α : Sort _} {P : α → Prop} (hP : ∀ x, P x) : ∀ x, P x :=
  hP
