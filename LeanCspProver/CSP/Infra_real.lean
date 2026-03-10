           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_common

/-
(*****************************************************
                    Real number
 *****************************************************)
-/

-- this lemma real_mult_less_mono
-- was given in Isabelle 2005, but is removed in Isabelle 2007

theorem real_mult_less_mono {u v x y : ℝ} :
    u < v -> x < y -> (0 : ℝ) < v -> 0 < x -> u * x < v * y
  | huv, hxy, hv, hx =>
      lt_trans (mul_lt_mul_of_pos_right huv hx) (mul_lt_mul_of_pos_left hxy hv)

-- mult_commute for Isabelle 2016
theorem mult_commute {x y : ℝ} : x * y = y * x := by
  exact mul_comm x y

theorem real_mult_add_distrib {x y z : ℝ} : x * (y + z) = x * y + x * z := by
  simpa using mul_add x y z

theorem real_mult_order_eq {x y : ℝ} : 0 <= x -> 0 <= y -> (0 : ℝ) <= x * y
  | hx, hy => mul_nonneg hx hy

theorem real_div_le_eq {x y z : ℝ} :
    0 < z -> (x <= y / z) = (x * z <= y)
  | hz => propext (le_div_iff₀ hz)

theorem real_div_less_eq {x y z : ℝ} :
    0 < z -> (x < y / z) = (x * z < y)
  | hz => propext (lt_div_iff₀ hz)

theorem real_less_div_eq {x y z : ℝ} :
    0 < z -> (x / z < y) = (x < y * z)
  | hz => propext (div_lt_iff₀ hz)

theorem real_mult_div_commute {x y z r : ℝ} :
    (0 : ℝ) <= x -> 0 < y -> 0 < z -> 0 < r ->
      (x < y * z / r) = (r * x / z < y)
  | _hx, _hy, hz, hr => by
      apply propext
      rw [lt_div_iff₀ hr, div_lt_iff₀ hz, mul_comm r x]

theorem real_mult_div_commuteI {x y z r : ℝ} :
    (0 : ℝ) <= x -> 0 < y -> 0 < z -> 0 < r -> x < y * z / r -> r * x / z < y
  | hx, hy, hz, hr, h => by
      simpa [real_mult_div_commute hx hy hz hr] using h

theorem real_mult_less_iff2 {x y z : ℝ} :
    (0 : ℝ) < z -> (z * x < z * y) = (x < y)
  | hz => by
      apply propext
      constructor
      · intro h
        nlinarith
      · intro h
        nlinarith

theorem real_mult_less_if2 {x y z : ℝ} :
    (0 : ℝ) < z -> x < y -> z * x < z * y
  | hz, hxy => by
      nlinarith

theorem real_mult_less_if1 {x y z : ℝ} :
    (0 : ℝ) < z -> x < y -> x * z < y * z
  | hz, hxy => by
      simpa [mul_comm] using real_mult_less_if2 hz hxy

/-
(*** rev_power_decreasing ***)
-/

theorem rev_power_decreasing {r : ℝ} {n m : ℕ} :
    (0 : ℝ) < r -> r < 1 -> r ^ n <= r ^ m -> m <= n
  | hr0, hr1, hpow => (pow_le_pow_iff_right_of_lt_one₀ hr0 hr1).mp hpow

/-
(*** rev_power_decreasing_strict ***)
-/

theorem rev_power_decreasing_strict {r : ℝ} {n m : ℕ} :
    (0 : ℝ) < r -> r < 1 -> r ^ n < r ^ m -> m < n
  | hr0, hr1, hpow => (pow_lt_pow_iff_right_of_lt_one₀ hr0 hr1).mp hpow
