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
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_order

/-
(*****************************
         powr --> pow
 *****************************)
-/

theorem nat_powr_pow {r : ℝ} {n : ℕ} (_h : 0 < r) :
    r ^ (n : ℝ) = r ^ n := by
  simp [Real.rpow_natCast]

/-
(*****************************************************
              Exponentail convergence
 *****************************************************)
-/

theorem powr_less_mono_inv {a x y : ℝ}
    (ha : 1 < a) (hxy : x < y) :
    (a⁻¹ : ℝ) ^ y < (a⁻¹ : ℝ) ^ x := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hinv0 : 0 < (a⁻¹ : ℝ) := by
    exact inv_pos.mpr ha0
  have hinv1 : (a⁻¹ : ℝ) < 1 := inv_lt_one_of_one_lt₀ ha
  simpa using Real.rpow_lt_rpow_of_exponent_gt hinv0 hinv1 hxy

theorem powr_less_mono_conv {a x y : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (hxy : x < y) :
    a ^ y < a ^ x := by
  simpa using Real.rpow_lt_rpow_of_exponent_gt ha0 ha1 hxy

theorem powr_convergence {alpha x : ℝ}
    (ha0 : 0 < alpha) (ha1 : alpha < 1) (hx : 0 < x) :
    ∃ n : ℕ, alpha ^ (n : ℝ) < x := by
  let y := Real.logb alpha x
  obtain ⟨n, hn⟩ := exists_nat_gt y
  refine ⟨n, ?_⟩
  have hne : alpha ≠ 1 := ne_of_lt ha1
  have hlog : alpha ^ y = x := by
    simp [y, Real.rpow_logb ha0 hne hx]
  have hlt : alpha ^ (n : ℝ) < alpha ^ y := by
    exact Real.rpow_lt_rpow_of_exponent_gt ha0 ha1 hn
  simpa [hlog] using hlt

theorem pow_convergence {alpha x : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (hx : 0 < x) :
    ∃ n : ℕ, alpha ^ n < x := by
  by_cases hAlpha : alpha = 0
  · refine ⟨1, ?_⟩
    simp [hAlpha, hx]
  · have hAlpha0 : 0 < alpha := lt_of_le_of_ne ha0 (Ne.symm hAlpha)
    obtain ⟨n, hn⟩ := powr_convergence hAlpha0 ha1 hx
    refine ⟨n, ?_⟩
    simpa using hn

/-
(*** if 0 <=alpha < 1 then alpha^n ----> 0 ***)
-/

theorem zero_isGLB_pow {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) :
    isGLB 0 {r : ℝ | ∃ n : ℕ, r = alpha ^ n} := by
  constructor
  · intro y hy
    rcases hy with ⟨n, rfl⟩
    exact pow_nonneg ha0 n
  · intro y hy
    by_contra hy0
    have hy0' : 0 < y := lt_of_not_ge hy0
    obtain ⟨n, hn⟩ := pow_convergence ha0 ha1 hy0'
    exact (not_lt_of_ge (hy (alpha ^ n) ⟨n, rfl⟩)) hn

/-
(*** GLB ***)
-/

theorem zero_GLB_pow {alpha : ℝ}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) :
    GLB {r : ℝ | ∃ n : ℕ, r = alpha ^ n} = 0 :=
  isGLB_GLB (zero_isGLB_pow ha0 ha1)
