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

import LeanCspProver.CSP.Infra_common

/-
(*****************************************************
                      nat
 *****************************************************)
-/

theorem nat_zero_or_Suc : ∀ n : Nat, n = 0 ∨ ∃ m : Nat, n = Nat.succ m
  | 0 => Or.inl rfl
  | Nat.succ m => Or.inr ⟨m, rfl⟩

/- *** min *** -/

theorem min_is1 {α : Type _} [LinearOrder α] {m n : α} : m <= n -> min m n = m
  | h => min_eq_left h

theorem min_is2 {α : Type _} [LinearOrder α] {m n : α} : n <= m -> min m n = n
  | h => min_eq_right h

-- Isabelle: lemmas min_is = min_is1 min_is2

/- *** max *** -/

theorem max_is1 {α : Type _} [LinearOrder α] {m n : α} : m <= n -> max m n = n
  | h => max_eq_right h

theorem max_is2 {α : Type _} [LinearOrder α] {m n : α} : n <= m -> max m n = m
  | h => max_eq_left h

-- Isabelle: lemmas max_is = max_is1 max_is2
