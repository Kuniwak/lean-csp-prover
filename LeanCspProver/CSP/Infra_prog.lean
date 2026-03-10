           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_real

/-
(*****************************************************
                    Progression
 *****************************************************)
-/

def prog_sum0 : Nat → (Nat → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f => prog_sum0 n f + f (n + 1)

def prog_sum (m n : Nat) (f : Nat → ℝ) : ℝ :=
  prog_sum0 n f - prog_sum0 m f

def geo_prop (K alpha : ℝ) : Nat → ℝ :=
  fun n => (alpha ^ (n - (Nat.succ 0))) * K

theorem geo_prog_sum0 {K alpha : ℝ} :
    ∀ n, prog_sum0 n (geo_prop K alpha) * ((1 : ℝ) - alpha) = K * ((1 : ℝ) - alpha ^ n)
  | 0 => by
      simp [prog_sum0]
  | n + 1 => by
      rw [prog_sum0, add_mul, geo_prog_sum0 n, geo_prop]
      simp only [Nat.succ_eq_add_one, zero_add, add_tsub_cancel_right]
      rw [pow_succ]
      ring

theorem geo_prog_sum {K alpha : ℝ} {m n : Nat} :
    prog_sum m n (geo_prop K alpha) * ((1 : ℝ) - alpha) = K * (alpha ^ m - alpha ^ n) := by
  rw [prog_sum, sub_mul, geo_prog_sum0, geo_prog_sum0]
  ring

theorem geo_prog_sum_sym {K alpha : ℝ} {m n : Nat} :
    K * (alpha ^ m - alpha ^ n) = prog_sum m n (geo_prop K alpha) * ((1 : ℝ) - alpha) :=
  (geo_prog_sum (K := K) (alpha := alpha) (m := m) (n := n)).symm

theorem geo_prog_sum_div {K alpha : ℝ} {m n : Nat} :
    alpha < (1 : ℝ) ->
      prog_sum m n (geo_prop K alpha) = K * (alpha ^ m - alpha ^ n) / ((1 : ℝ) - alpha)
  | hlt => by
      have hneq : ((1 : ℝ) - alpha) ≠ 0 := by
        linarith
      apply (eq_div_iff hneq).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        geo_prog_sum (K := K) (alpha := alpha) (m := m) (n := n)

theorem geo_prog_sum_infinite {K alpha : ℝ} {m n : Nat} :
    (0 : ℝ) <= K ->
      (0 : ℝ) <= alpha ->
      prog_sum m n (geo_prop K alpha) * ((1 : ℝ) - alpha) <= K * (alpha ^ m)
  | hK, hAlpha => by
      rw [geo_prog_sum]
      have hpow : (0 : ℝ) <= alpha ^ n := pow_nonneg hAlpha n
      have hsub : alpha ^ m - alpha ^ n <= alpha ^ m := sub_le_self _ hpow
      exact mul_le_mul_of_nonneg_left hsub hK

theorem geo_prog_sum_infinite_div {K alpha : ℝ} {m n : Nat} :
    (0 : ℝ) <= K ->
      (0 : ℝ) <= alpha ->
      alpha < (1 : ℝ) ->
      prog_sum m n (geo_prop K alpha) <= K * (alpha ^ m) / ((1 : ℝ) - alpha)
  | hK, hAlpha, hlt => by
      have hpos : (0 : ℝ) < (1 - alpha) := sub_pos.mpr hlt
      rw [real_div_le_eq (x := prog_sum m n (geo_prop K alpha)) (y := K * (alpha ^ m))
        (z := (1 : ℝ) - alpha) hpos]
      exact geo_prog_sum_infinite (m := m) (n := n) hK hAlpha
