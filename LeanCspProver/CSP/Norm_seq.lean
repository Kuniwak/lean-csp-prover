           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2020         |
            |                  April 2020  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.CMS

noncomputable section

/-
(*****************************************************************

         1. Definition of Normarized sequences
         2. Properties of Normarized sequences
         3. How to transform each Cauchy sequence to NF
         4. The same limit between xs and NF(xs)

 *****************************************************************)
-/

def normal {α : Type u} [ms α] (xs : infinite_seq α) : Prop :=
  ∀ n m : Nat, distance (xs n) (xs m) ≤ (1 / 2 : ℝ) ^ min n m

def Nset {α : Type u} [ms α] (xs : infinite_seq α) (delta : ℝ) : Set Nat :=
  {N | ∀ n m, (N ≤ m ∧ N ≤ n) → distance (xs n) (xs m) ≤ delta}

def Nmin {α : Type u} [ms α] (xs : infinite_seq α) (delta : ℝ) : Nat :=
  Min (Nset xs delta)

def NF {α : Type u} [ms α] (xs : infinite_seq α) : infinite_seq α :=
  fun n => xs (Nmin xs ((1 / 2 : ℝ) ^ n))

private theorem half_pow_antitone {m n : Nat} (h : m ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt)
  · simp

/-
(********************************************************************
                          Normalization
 ********************************************************************)
-/

/-(*** normalized sequence --> Cauchy sequence ***)-/

theorem normal_cauchy {α : Type u} [ms α] {xs : infinite_seq α} :
    normal xs → cauchy xs := by
  intro hnormal delta hdelta
  obtain ⟨n, hn⟩ := pow_convergence (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hdelta
  refine ⟨n, ?_⟩
  intro i j hij
  have hdist := hnormal i j
  have hmin : n ≤ min i j := le_min hij.1 hij.2
  have hpow : (1 / 2 : ℝ) ^ min i j ≤ (1 / 2 : ℝ) ^ n := half_pow_antitone hmin
  exact lt_of_le_of_lt (le_trans hdist hpow) hn

theorem normal_Limit {α : Type u} [ms α] {xs : infinite_seq α} {y : α} {n : Nat} :
    normal xs → xs convergeTo y → distance (xs (Nat.succ n)) y < (1 / 2 : ℝ) ^ n := by
  intro hnormal hconv
  obtain ⟨N, hN⟩ := hconv ((1 / 2 : ℝ) ^ Nat.succ n) (by positivity)
  by_cases hcase : N ≤ Nat.succ n
  · have hy : distance y (xs (Nat.succ n)) < (1 / 2 : ℝ) ^ Nat.succ n := hN _ hcase
    have hy' : distance (xs (Nat.succ n)) y < (1 / 2 : ℝ) ^ Nat.succ n := by
      simpa [ms.symmetry_ms] using hy
    have hpow : (1 / 2 : ℝ) ^ Nat.succ n < (1 / 2 : ℝ) ^ n := by
      simpa [Nat.succ_eq_add_one] using
        (pow_lt_pow_right_of_lt_one₀
          (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (Nat.lt_succ_self n))
    exact lt_trans hy' hpow
  · have hlt : Nat.succ n < N := lt_of_not_ge hcase
    have hyN : distance y (xs N) < (1 / 2 : ℝ) ^ Nat.succ n := hN _ le_rfl
    have hyN' : distance (xs N) y < (1 / 2 : ℝ) ^ Nat.succ n := by
      simpa [ms.symmetry_ms] using hyN
    have hnorm :
        distance (xs (Nat.succ n)) (xs N) ≤ (1 / 2 : ℝ) ^ Nat.succ n := by
      have := hnormal (Nat.succ n) N
      simpa [min_eq_left (le_of_lt hlt)] using this
    have htri := ms.triangle_inequality_ms (xs (Nat.succ n)) (xs N) y
    have hsum :
        distance (xs (Nat.succ n)) y <
          (1 / 2 : ℝ) ^ Nat.succ n + (1 / 2 : ℝ) ^ Nat.succ n := by
      exact lt_of_le_of_lt htri (add_lt_add_of_le_of_lt hnorm hyN')
    calc
      distance (xs (Nat.succ n)) y
          < (1 / 2 : ℝ) ^ Nat.succ n + (1 / 2 : ℝ) ^ Nat.succ n := hsum
      _ = (1 / 2 : ℝ) ^ n := by
        rw [pow_succ]
        ring

/-
(********************************************************************
                                Nmin
 ********************************************************************)
-/

/-(*** Nmin exists ***)-/

theorem Nmin_exists {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} :
    0 < delta → cauchy xs → ∃ N, isMIN N (Nset xs delta) := by
  intro hdelta hcauchy
  obtain ⟨n, hn⟩ := hcauchy delta hdelta
  apply EX_MIN_nat
  intro hEmpty
  have hmem : n ∈ Nset xs delta := by
    intro i j hij
    exact le_of_lt (hn i j ⟨hij.2, hij.1⟩)
  have hne : Nset xs delta ≠ ∅ := Set.nonempty_iff_ne_empty.mp ⟨n, hmem⟩
  exact False.elim (hne hEmpty)

theorem Nset_hasMIN {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} :
    0 < delta → cauchy xs → hasMIN (Nset xs delta) := by
  intro hdelta hcauchy
  exact Nmin_exists (xs := xs) hdelta hcauchy

/-(*** Nmin unique ***)-/

theorem Nmin_unique {N M : Nat} {X : Set Nat}
    (hN : isMIN N X) (hM : isMIN M X) : N = M := by
  exact MIN_unique hN hM

/- -----------------------*
 |       the Nmin        |
 *----------------------- -/

theorem Nset_to_Nmin {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} {N : Nat} :
    0 < delta → cauchy xs → (isMIN N (Nset xs delta) ↔ Nmin xs delta = N) := by
  intro hdelta hcauchy
  simpa [Nmin] using
    (MIN_to_isMIN_sym (X := Nset xs delta) (x := N) (Nset_hasMIN (xs := xs) hdelta hcauchy)).symm

theorem Nmin_to_Nset {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} {N : Nat} :
    0 < delta → cauchy xs → (Nmin xs delta = N ↔ isMIN N (Nset xs delta)) := by
  intro hdelta hcauchy
  exact (Nset_to_Nmin (xs := xs) (delta := delta) (N := N) hdelta hcauchy).symm

theorem Nmin_to_Nset_sym {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} {N : Nat} :
    0 < delta → cauchy xs → (N = Nmin xs delta ↔ isMIN N (Nset xs delta)) := by
  intro hdelta hcauchy
  simpa [eq_comm] using Nmin_to_Nset (xs := xs) (delta := delta) (N := N) hdelta hcauchy

/- -----------------------*
 |      property         |
 *----------------------- -/

theorem Nmin_cauchy_lm {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} {N : Nat} :
    0 < delta → cauchy xs → Nmin xs delta = N →
      ∀ n m, (N ≤ m ∧ N ≤ n) → distance (xs n) (xs m) ≤ delta := by
  intro hdelta hcauchy hN
  have hmin : isMIN N (Nset xs delta) :=
    (Nmin_to_Nset (xs := xs) (delta := delta) (N := N) hdelta hcauchy).1 hN
  exact hmin.2

theorem Nmin_cauchy {α : Type u} [ms α] {xs : infinite_seq α} {delta : ℝ} {m n : Nat} :
    0 < delta → cauchy xs → Nmin xs delta ≤ m → Nmin xs delta ≤ n →
      distance (xs n) (xs m) ≤ delta := by
  intro hdelta hcauchy hm hn
  exact Nmin_cauchy_lm (xs := xs) (delta := delta) (N := Nmin xs delta)
    hdelta hcauchy rfl n m ⟨hm, hn⟩

/- -----------------------*
 |   min_number_cauchy   |
 *----------------------- -/

/-(*** Nmin order (check) ***)-/

theorem min_number_cauchy_lm {α : Type u} [ms α] {xs : infinite_seq α} {delta1 delta2 : ℝ} :
    0 < delta1 → delta1 ≤ delta2 → cauchy xs → Nset xs delta1 ⊆ Nset xs delta2 := by
  intro _hdelta1 hdelta hcauchy N hN n m hnm
  exact le_trans (hN n m hnm) hdelta

/-(*** Nmin order ***)-/

theorem min_number_cauchy {α : Type u} [ms α] {xs : infinite_seq α}
    {delta1 delta2 : ℝ} {N1 N2 : Nat} :
    0 < delta1 → delta1 ≤ delta2 → cauchy xs →
      Nmin xs delta1 = N1 → Nmin xs delta2 = N2 → N2 ≤ N1 := by
  intro hdelta1 hdelta hcauchy hN1 hN2
  have hdelta2 : 0 < delta2 := lt_of_lt_of_le hdelta1 hdelta
  have hmin1 : isMIN N1 (Nset xs delta1) :=
    (Nmin_to_Nset (xs := xs) (delta := delta1) (N := N1) hdelta1 hcauchy).1 hN1
  have hmin2 : isMIN N2 (Nset xs delta2) :=
    (Nmin_to_Nset (xs := xs) (delta := delta2) (N := N2) hdelta2 hcauchy).1 hN2
  exact isMIN_subset hmin1 hmin2 (min_number_cauchy_lm (xs := xs) hdelta1 hdelta hcauchy)

/-(*** Nmin order half ***)-/

theorem min_number_cauchy_half {α : Type u} [ms α] {xs : infinite_seq α}
    {n m N1 N2 : Nat} :
    n ≤ m → cauchy xs →
      Nmin xs ((1 / 2 : ℝ) ^ n) = N1 → Nmin xs ((1 / 2 : ℝ) ^ m) = N2 → N1 ≤ N2 := by
  intro hnm hcauchy hN1 hN2
  have hpos : 0 < (1 / 2 : ℝ) ^ m := by positivity
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ n := half_pow_antitone hnm
  exact min_number_cauchy (xs := xs) (delta1 := (1 / 2 : ℝ) ^ m) (delta2 := (1 / 2 : ℝ) ^ n)
    hpos hpow hcauchy hN2 hN1

/- ------------------------*
 | normal_form_seq_normal |
 *------------------------ -/

theorem normal_form_seq_normal {α : Type u} [ms α] {xs : infinite_seq α} :
    cauchy xs → normal (NF xs) := by
  intro hcauchy n m
  by_cases hnm : n ≤ m
  · have horder :
        Nmin xs ((1 / 2 : ℝ) ^ n) ≤ Nmin xs ((1 / 2 : ℝ) ^ m) := by
      exact min_number_cauchy_half (xs := xs) hnm hcauchy rfl rfl
    simpa [NF, min_eq_left hnm] using
      (Nmin_cauchy (xs := xs) (delta := (1 / 2 : ℝ) ^ n) (m := Nmin xs ((1 / 2 : ℝ) ^ m))
        (n := Nmin xs ((1 / 2 : ℝ) ^ n)) (by positivity) hcauchy horder le_rfl)
  · have hmn : m ≤ n := le_of_not_ge hnm
    have horder :
        Nmin xs ((1 / 2 : ℝ) ^ m) ≤ Nmin xs ((1 / 2 : ℝ) ^ n) := by
      exact min_number_cauchy_half (xs := xs) hmn hcauchy rfl rfl
    simpa [NF, min_eq_right hmn] using
      (Nmin_cauchy (xs := xs) (delta := (1 / 2 : ℝ) ^ m) (m := Nmin xs ((1 / 2 : ℝ) ^ m))
        (n := Nmin xs ((1 / 2 : ℝ) ^ n)) (by positivity) hcauchy le_rfl horder)

/- ----------------------------*
 | normal_form_seq_same_Limit |
 *---------------------------- -/

/-(*** only if part ***)-/

theorem normal_form_seq_same_Limit_only_if {α : Type u} [ms α] {xs : infinite_seq α} {y : α} :
    cauchy xs → xs convergeTo y → NF xs convergeTo y := by
  intro hcauchy hconv eps heps
  obtain ⟨N, hN⟩ := hconv (eps / 2) (by linarith)
  obtain ⟨M, hM⟩ := pow_convergence (alpha := (1 / 2 : ℝ)) (x := eps / 2)
    (by norm_num) (by norm_num) (by linarith)
  refine ⟨M, ?_⟩
  intro m hm
  by_cases hcase : N ≤ Nmin xs ((1 / 2 : ℝ) ^ m)
  · have hy : distance y (xs (Nmin xs ((1 / 2 : ℝ) ^ m))) < eps / 2 := hN _ hcase
    simpa [NF] using lt_of_lt_of_le hy (by linarith)
  · have hNm : Nmin xs ((1 / 2 : ℝ) ^ m) ≤ N := le_of_not_ge hcase
    have hyN : distance y (xs N) < eps / 2 := hN _ le_rfl
    have hNF :
        distance (xs N) (xs (Nmin xs ((1 / 2 : ℝ) ^ m))) ≤ (1 / 2 : ℝ) ^ m := by
      exact Nmin_cauchy (xs := xs) (delta := (1 / 2 : ℝ) ^ m)
        (m := Nmin xs ((1 / 2 : ℝ) ^ m)) (n := N)
        (by positivity) hcauchy le_rfl hNm
    have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ M := half_pow_antitone hm
    have htri := ms.triangle_inequality_ms y (xs N) (xs (Nmin xs ((1 / 2 : ℝ) ^ m)))
    have htarget : (1 / 2 : ℝ) ^ M < eps / 2 := hM
    simpa [NF] using (show distance y (xs (Nmin xs ((1 / 2 : ℝ) ^ m))) < eps from by
      nlinarith)

/-(*** if part ***)-/

theorem normal_form_seq_same_Limit_if {α : Type u} [ms α] {xs : infinite_seq α} {y : α} :
    cauchy xs → NF xs convergeTo y → xs convergeTo y := by
  intro hcauchy hNF eps heps
  obtain ⟨N, hN⟩ := hNF (eps / 2) (by linarith)
  obtain ⟨M, hM⟩ := pow_convergence (alpha := (1 / 2 : ℝ)) (x := eps / 2)
    (by norm_num) (by norm_num) (by linarith)
  refine ⟨Nmin xs ((1 / 2 : ℝ) ^ max N M), ?_⟩
  intro m hm
  have hy :
      distance y (xs (Nmin xs ((1 / 2 : ℝ) ^ max N M))) < eps / 2 := by
    simpa [NF] using hN (max N M) (le_max_left N M)
  have hdist :
      distance (xs (Nmin xs ((1 / 2 : ℝ) ^ max N M))) (xs m) ≤ (1 / 2 : ℝ) ^ max N M := by
    exact Nmin_cauchy (xs := xs) (delta := (1 / 2 : ℝ) ^ max N M)
      (m := m) (n := Nmin xs ((1 / 2 : ℝ) ^ max N M))
      (by positivity) hcauchy hm le_rfl
  have hpow : (1 / 2 : ℝ) ^ max N M ≤ (1 / 2 : ℝ) ^ M := half_pow_antitone (le_max_right N M)
  have htri := ms.triangle_inequality_ms y (xs (Nmin xs ((1 / 2 : ℝ) ^ max N M))) (xs m)
  have htarget : (1 / 2 : ℝ) ^ M < eps / 2 := hM
  nlinarith

/-(*** iff ***)-/

theorem normal_form_seq_same_Limit {α : Type u} [ms α] {xs : infinite_seq α} {y : α} :
    cauchy xs → (xs convergeTo y ↔ NF xs convergeTo y) := by
  intro hcauchy
  constructor
  · exact normal_form_seq_same_Limit_only_if hcauchy
  · exact normal_form_seq_same_Limit_if hcauchy

end
