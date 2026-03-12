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

import LeanCspProver.CSP.Infra_pair
import LeanCspProver.CSP.RS

open Function

noncomputable section

private theorem half_pow_antitone {m n : Nat} (h : m ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt)
  · simp

/-
(*****************************************************************

         1. Pairs of RS are also RS.
         2.
         3.
         4.

 *****************************************************************)
-/

/- (**********************************************************
              def: pair of restriction space
 **********************************************************) -/

instance instRs0Prod {α β : Type _} [rs α] [rs β] : rs0 (α × β) where
  restriction xc n := ((Prod.fst xc) .|. n, (Prod.snd xc) .|. n)

@[simp]
theorem pair_restriction_def {α β : Type _} [rs α] [rs β] {xc : α × β} {n : Nat} :
    xc .|. n = (((Prod.fst xc) .|. n), ((Prod.snd xc) .|. n)) :=
  rfl

def pair_Limit {α β : Type _} [ms_rs α] [ms_rs β] [Inhabited α] [Inhabited β]
    (xcs : infinite_seq (α × β)) : α × β :=
  (Limit (Prod.fst ∘ xcs), Limit (Prod.snd ∘ xcs))

@[simp]
theorem pair_Limit_def {α β : Type _} [ms_rs α] [ms_rs β] [Inhabited α] [Inhabited β]
    {xcs : infinite_seq (α × β)} :
    pair_Limit xcs = (Limit (Prod.fst ∘ xcs), Limit (Prod.snd ∘ xcs)) :=
  rfl

/- (************************************************************
                         Basics
 ************************************************************) -/

theorem rest_to_pair_rest {α β : Type _} [rs α] [rs β] {xc yc : α × β} {n : Nat} :
    (Prod.fst xc) .|. n = (Prod.fst yc) .|. n →
      (Prod.snd xc) .|. n = (Prod.snd yc) .|. n →
      xc .|. n = yc .|. n := by
  intro hfst hsnd
  cases xc
  cases yc
  simp [pair_restriction_def, hfst, hsnd]

/- (************************************************************
                   Pair RS ==> RS
 ************************************************************) -/

/- (*** pair_zero_eq_rs ***) -/

theorem pair_zero_eq_rs {α β : Type _} [rs α] [rs β] (xc yc : α × β) :
    xc .|. 0 = yc .|. 0 := by
  cases xc
  cases yc
  ext
  · exact rs.zero_eq_rs _ _
  · exact rs.zero_eq_rs _ _

/- (*** pair_min_rs ***) -/

theorem pair_min_rs {α β : Type _} [rs α] [rs β] (xc : α × β) (m n : Nat) :
    (xc .|. m) .|. n = xc .|. (min m n) := by
  cases xc
  simp [pair_restriction_def, rs.min_rs]

/- (*** contra_pair_diff_rs ***) -/

theorem contra_pair_diff_rs {α β : Type _} [rs α] [rs β] {xc yc : α × β} :
    (∀ n, xc .|. n = yc .|. n) → xc = yc := by
  intro hxy
  apply pair_eq_decompo.mpr
  constructor
  · apply contra_diff_rs
    intro n
    simpa [pair_restriction_def] using congrArg Prod.fst (hxy n)
  · apply contra_diff_rs
    intro n
    simpa [pair_restriction_def] using congrArg Prod.snd (hxy n)

/- (*** pair_diff_rs ***) -/

theorem pair_diff_rs {α β : Type _} [rs α] [rs β] {xc yc : α × β} :
    xc ≠ yc → ∃ n, xc .|. n ≠ yc .|. n := by
  intro hneq
  by_contra h
  apply hneq
  apply contra_pair_diff_rs
  intro n
  by_contra hneq'
  exact h ⟨n, hneq'⟩

/- (*****************************************
              Pair RS => RS
 *****************************************) -/

instance instRsProd {α β : Type _} [rs α] [rs β] : rs (α × β) where
  zero_eq_rs := pair_zero_eq_rs
  min_rs := pair_min_rs
  diff_rs := by
    intro x y
    exact pair_diff_rs (xc := x) (yc := y)

/- (************************************************************
                     Pair RS ==> MS
 ************************************************************) -/

instance instMs0Prod {α β : Type _} [rs α] [rs β] : ms0 (α × β) where
  distance := distance_rs

@[simp]
theorem pair_distance_def {α β : Type _} [rs α] [rs β] {xc yc : α × β} :
    distance xc yc = distance_rs xc yc :=
  rfl

instance instMsProd {α β : Type _} [rs α] [rs β] : ms (α × β) where
  positive_ms := by
    intro x y
    simpa [pair_distance_def] using positive_rs x y
  diagonal_ms := by
    intro x y
    simpa [pair_distance_def] using (diagonal_rs (x := x) (y := y))
  symmetry_ms := by
    intro x y
    simpa [pair_distance_def] using symmetry_rs x y
  triangle_inequality_ms := by
    intro x y z
    simpa [pair_distance_def] using triangle_inequality_rs x y z

/- (************************************************************
             i.e.  Pair RS ==> MS & RS
 ************************************************************) -/

instance instMs0RsProd {α β : Type _} [rs α] [rs β] : ms0_rs (α × β) where
  to_distance_rs := by
    intro x y
    rfl

instance instMsRsProd {α β : Type _} [rs α] [rs β] : ms_rs (α × β) where

/- (************************************************************
                     Lemmas (distance)
 ************************************************************) -/

/- distance_nat -/

theorem pair_distance_nat_le_fst {α β : Type _} [rs α] [rs β] {xc yc : α × β} :
    Prod.fst xc ≠ Prod.fst yc →
      distance_nat xc yc <= distance_nat (Prod.fst xc) (Prod.fst yc) := by
  intro hfst
  have hpair : xc ≠ yc := fun hEq => hfst (congrArg Prod.fst hEq)
  have hEqPair : xc .|. distance_nat xc yc = yc .|. distance_nat xc yc :=
    distance_nat_rest (x := xc) (y := yc) hpair rfl
  have hEqFst :
      (Prod.fst xc) .|. distance_nat xc yc = (Prod.fst yc) .|. distance_nat xc yc := by
    simpa [pair_restriction_def] using congrArg Prod.fst hEqPair
  exact distance_nat_le_1_only_if (x := Prod.fst xc) (y := Prod.fst yc) hfst hEqFst

theorem pair_distance_nat_le_snd {α β : Type _} [rs α] [rs β] {xc yc : α × β} :
    Prod.snd xc ≠ Prod.snd yc →
      distance_nat xc yc <= distance_nat (Prod.snd xc) (Prod.snd yc) := by
  intro hsnd
  have hpair : xc ≠ yc := fun hEq => hsnd (congrArg Prod.snd hEq)
  have hEqPair : xc .|. distance_nat xc yc = yc .|. distance_nat xc yc :=
    distance_nat_rest (x := xc) (y := yc) hpair rfl
  have hEqSnd :
      (Prod.snd xc) .|. distance_nat xc yc = (Prod.snd yc) .|. distance_nat xc yc := by
    simpa [pair_restriction_def] using congrArg Prod.snd hEqPair
  exact distance_nat_le_1_only_if (x := Prod.snd xc) (y := Prod.snd yc) hsnd hEqSnd

/- distance -/

theorem pair_distance_def_le_fst {α β : Type _} [ms0_rs α] [ms0_rs β] {xc yc : α × β} :
    distance (Prod.fst xc) (Prod.fst yc) <= distance xc yc := by
  calc
    distance (Prod.fst xc) (Prod.fst yc) = distance_rs (Prod.fst xc) (Prod.fst yc) := by
      exact ms0_rs.to_distance_rs _ _
    _ <= distance_rs xc yc := by
      exact rest_distance_subset (x := xc) (y := yc) (X := Prod.fst xc) (Y := Prod.fst yc)
        (fun n hEq => by simpa [pair_restriction_def] using congrArg Prod.fst hEq)
    _ = distance xc yc := by
      symm
      exact ms0_rs.to_distance_rs _ _

theorem pair_distance_def_le_fst_compo {α β : Type _} [ms0_rs α] [ms0_rs β]
    {a1 a2 : α} {b1 b2 : β} :
    distance a1 a2 <= distance (a1, b1) (a2, b2) := by
  simpa using (pair_distance_def_le_fst (xc := (a1, b1)) (yc := (a2, b2)))

theorem pair_distance_def_le_snd {α β : Type _} [ms0_rs α] [ms0_rs β] {xc yc : α × β} :
    distance (Prod.snd xc) (Prod.snd yc) <= distance xc yc := by
  calc
    distance (Prod.snd xc) (Prod.snd yc) = distance_rs (Prod.snd xc) (Prod.snd yc) := by
      exact ms0_rs.to_distance_rs _ _
    _ <= distance_rs xc yc := by
      exact rest_distance_subset (x := xc) (y := yc) (X := Prod.snd xc) (Y := Prod.snd yc)
        (fun n hEq => by simpa [pair_restriction_def] using congrArg Prod.snd hEq)
    _ = distance xc yc := by
      symm
      exact ms0_rs.to_distance_rs _ _

theorem pair_distance_def_le_snd_compo {α β : Type _} [ms0_rs α] [ms0_rs β]
    {a1 a2 : α} {b1 b2 : β} :
    distance b1 b2 <= distance (a1, b1) (a2, b2) := by
  simpa using (pair_distance_def_le_snd (xc := (a1, b1)) (yc := (a2, b2)))

/- (*** pair_distance (max) ***) -/

theorem pair_distance_max {α β : Type _} [ms_rs α] [ms_rs β] {xc yc : α × β} :
    distance xc yc =
      max (distance (Prod.fst xc) (Prod.fst yc)) (distance (Prod.snd xc) (Prod.snd yc)) := by
  have hfstLe := pair_distance_def_le_fst (xc := xc) (yc := yc)
  have hsndLe := pair_distance_def_le_snd (xc := xc) (yc := yc)
  apply le_antisymm
  · by_cases hfst : Prod.fst xc = Prod.fst yc
    · have hEq :
          max (distance (Prod.fst xc) (Prod.fst yc)) (distance (Prod.snd xc) (Prod.snd yc)) =
            distance (Prod.snd xc) (Prod.snd yc) := by
        apply max_eq_right
        simpa [hfst] using (ms.positive_ms (Prod.snd xc) (Prod.snd yc))
      rw [hEq]
      calc
        distance xc yc = distance_rs xc yc := ms0_rs.to_distance_rs _ _
        _ <= distance_rs (Prod.snd xc) (Prod.snd yc) := by
          exact rest_distance_subset (x := Prod.snd xc) (y := Prod.snd yc) (X := xc) (Y := yc)
            (fun n hs => rest_to_pair_rest (by simp [hfst]) hs)
        _ = distance (Prod.snd xc) (Prod.snd yc) := by
          symm
          exact ms0_rs.to_distance_rs _ _
    · by_cases hsnd : Prod.snd xc = Prod.snd yc
      · have hEq :
            max (distance (Prod.fst xc) (Prod.fst yc)) (distance (Prod.snd xc) (Prod.snd yc)) =
              distance (Prod.fst xc) (Prod.fst yc) := by
          apply max_eq_left
          simpa [hsnd] using (ms.positive_ms (Prod.fst xc) (Prod.fst yc))
        rw [hEq]
        calc
          distance xc yc = distance_rs xc yc := ms0_rs.to_distance_rs _ _
          _ <= distance_rs (Prod.fst xc) (Prod.fst yc) := by
            exact rest_distance_subset (x := Prod.fst xc) (y := Prod.fst yc) (X := xc) (Y := yc)
              (fun n hf => rest_to_pair_rest hf (by simp [hsnd]))
          _ = distance (Prod.fst xc) (Prod.fst yc) := by
            symm
            exact ms0_rs.to_distance_rs _ _
      · have hRestFst :
            (Prod.fst xc) .|. min (distance_nat (Prod.fst xc) (Prod.fst yc))
              (distance_nat (Prod.snd xc) (Prod.snd yc)) =
              (Prod.fst yc) .|. min (distance_nat (Prod.fst xc) (Prod.fst yc))
                (distance_nat (Prod.snd xc) (Prod.snd yc)) :=
          distance_nat_le_1_if (x := Prod.fst xc) (y := Prod.fst yc) hfst (Nat.min_le_left _ _)
        have hRestSnd :
            (Prod.snd xc) .|. min (distance_nat (Prod.fst xc) (Prod.fst yc))
              (distance_nat (Prod.snd xc) (Prod.snd yc)) =
              (Prod.snd yc) .|. min (distance_nat (Prod.fst xc) (Prod.fst yc))
                (distance_nat (Prod.snd xc) (Prod.snd yc)) :=
          distance_nat_le_1_if (x := Prod.snd xc) (y := Prod.snd yc) hsnd (Nat.min_le_right _ _)
        have hRestPair :
            xc .|. min (distance_nat (Prod.fst xc) (Prod.fst yc))
              (distance_nat (Prod.snd xc) (Prod.snd yc)) =
              yc .|. min (distance_nat (Prod.fst xc) (Prod.fst yc))
                (distance_nat (Prod.snd xc) (Prod.snd yc)) :=
          rest_to_pair_rest hRestFst hRestSnd
        have hDist :
            distance xc yc <=
              (1 / 2 : ℝ) ^
                min (distance_nat (Prod.fst xc) (Prod.fst yc))
                  (distance_nat (Prod.snd xc) (Prod.snd yc)) := by
          rw [ms0_rs.to_distance_rs (x := xc) (y := yc)]
          exact distance_rs_le_1_only_if hRestPair
        have hfstDist :
            distance (Prod.fst xc) (Prod.fst yc) =
              (1 / 2 : ℝ) ^ distance_nat (Prod.fst xc) (Prod.fst yc) :=
          by
            calc
              distance (Prod.fst xc) (Prod.fst yc) = distance_rs (Prod.fst xc) (Prod.fst yc) := by
                exact ms0_rs.to_distance_rs _ _
              _ = (1 / 2 : ℝ) ^ distance_nat (Prod.fst xc) (Prod.fst yc) :=
                distance_iff1 (x := Prod.fst xc) (y := Prod.fst yc) hfst
        have hsndDist :
            distance (Prod.snd xc) (Prod.snd yc) =
              (1 / 2 : ℝ) ^ distance_nat (Prod.snd xc) (Prod.snd yc) :=
          by
            calc
              distance (Prod.snd xc) (Prod.snd yc) = distance_rs (Prod.snd xc) (Prod.snd yc) := by
                exact ms0_rs.to_distance_rs _ _
              _ = (1 / 2 : ℝ) ^ distance_nat (Prod.snd xc) (Prod.snd yc) :=
                distance_iff1 (x := Prod.snd xc) (y := Prod.snd yc) hsnd
        by_cases hle :
            distance_nat (Prod.fst xc) (Prod.fst yc) <=
              distance_nat (Prod.snd xc) (Prod.snd yc)
        · have hmax :
              max (distance (Prod.fst xc) (Prod.fst yc)) (distance (Prod.snd xc) (Prod.snd yc)) =
                distance (Prod.fst xc) (Prod.fst yc) := by
            rw [hfstDist, hsndDist]
            apply max_eq_left
            exact half_pow_antitone hle
          rw [hmax]
          simpa [hfstDist, min_eq_left hle] using hDist
        · have hle' :
              distance_nat (Prod.snd xc) (Prod.snd yc) <=
                distance_nat (Prod.fst xc) (Prod.fst yc) := le_of_not_ge hle
          have hmax :
              max (distance (Prod.fst xc) (Prod.fst yc)) (distance (Prod.snd xc) (Prod.snd yc)) =
                distance (Prod.snd xc) (Prod.snd yc) := by
            rw [hfstDist, hsndDist]
            apply max_eq_right
            exact half_pow_antitone hle'
          rw [hmax]
          simpa [hsndDist, min_eq_right hle'] using hDist
  · exact max_le hfstLe hsndLe

theorem pair_distance_max_compo {α β : Type _} [ms_rs α] [ms_rs β]
    {a1 a2 : α} {b1 b2 : β} :
    distance (a1, b1) (a2, b2) = max (distance a1 a2) (distance b1 b2) := by
  simpa using (pair_distance_max (xc := (a1, b1)) (yc := (a2, b2)))

theorem ALL_pair_distance_max {α β : Type _} [ms_rs α] [ms_rs β] :
    ∀ xc yc : α × β,
      distance xc yc =
        max (distance (Prod.fst xc) (Prod.fst yc)) (distance (Prod.snd xc) (Prod.snd yc)) :=
  fun _ _ => pair_distance_max

/- (*****************************************
               pair maps
 *****************************************) -/

/- (*** fst ***) -/

theorem fst_non_expand {α β : Type _} [ms_rs α] [ms_rs β] :
    non_expanding (Prod.fst : α × β → α) := by
  constructor
  · norm_num
  · intro x y
    simpa using (pair_distance_def_le_fst (xc := x) (yc := y))

/- (*** snd ***) -/

theorem snd_non_expand {α β : Type _} [ms_rs α] [ms_rs β] :
    non_expanding (Prod.snd : α × β → β) := by
  constructor
  · norm_num
  · intro x y
    simpa using (pair_distance_def_le_snd (xc := x) (yc := y))

/- ---------------------*
 |      map_alpha      |
 *--------------------- -/

/- only_if -/

theorem pair_map_alpha_only_if {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {fc : α → β × γ} {alpha : ℝ} :
    map_alpha fc alpha →
      (map_alpha (Prod.fst ∘ fc) alpha ∧ map_alpha (Prod.snd ∘ fc) alpha) := by
  intro hfc
  exact
    ⟨compo_non_expand_map_alpha fst_non_expand hfc,
      compo_non_expand_map_alpha snd_non_expand hfc⟩

/- if -/

theorem pair_map_alpha_if {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {fc : α → β × γ} {alpha : ℝ} :
    map_alpha (Prod.fst ∘ fc) alpha →
      map_alpha (Prod.snd ∘ fc) alpha →
      map_alpha fc alpha := by
  intro hfst hsnd
  constructor
  · exact hfst.1
  · intro x y
    rw [pair_distance_max]
    exact max_le
      (by simpa [Function.comp] using hfst.2 x y)
      (by simpa [Function.comp] using hsnd.2 x y)

/- iff -/

theorem pair_map_alpha {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {fc : α → β × γ} {alpha : ℝ} :
    map_alpha fc alpha =
      (map_alpha (Prod.fst ∘ fc) alpha ∧ map_alpha (Prod.snd ∘ fc) alpha) := by
  apply propext
  constructor
  · exact pair_map_alpha_only_if
  · rintro ⟨hfst, hsnd⟩
    exact pair_map_alpha_if hfst hsnd

theorem pair_map_alpha_compo {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {f : α → β} {g : α → γ} {alpha : ℝ} :
    map_alpha (f ** g) alpha =
      (map_alpha f alpha ∧ map_alpha g alpha) := by
  simpa [pair_fun, Function.comp] using
    (pair_map_alpha (fc := (f ** g)) (alpha := alpha))

/- ---------------------*
 |    non_expanding    |
 *--------------------- -/

theorem pair_non_expand {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {fc : α → β × γ} :
    non_expanding fc =
      (non_expanding (Prod.fst ∘ fc) ∧ non_expanding (Prod.snd ∘ fc)) := by
  simpa [non_expanding] using (pair_map_alpha (fc := fc) (alpha := (1 : ℝ)))

theorem pair_non_expand_compo {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {f : α → β} {g : α → γ} :
    non_expanding (f ** g) =
      (non_expanding f ∧ non_expanding g) := by
  simpa [non_expanding] using (pair_map_alpha_compo (f := f) (g := g) (alpha := (1 : ℝ)))

/- ---------------------*
 |  alpha_contraction  |
 *--------------------- -/

theorem pair_contra_alpha {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {fc : α → β × γ} {alpha : ℝ} :
    contraction_alpha fc alpha =
      (contraction_alpha (Prod.fst ∘ fc) alpha ∧ contraction_alpha (Prod.snd ∘ fc) alpha) := by
  apply propext
  constructor
  · intro h
    exact ⟨⟨h.1, (pair_map_alpha_only_if h.2).1⟩, ⟨h.1, (pair_map_alpha_only_if h.2).2⟩⟩
  · rintro ⟨hfst, hsnd⟩
    exact ⟨hfst.1, pair_map_alpha_if hfst.2 hsnd.2⟩

theorem pair_contra_alpha_compo {α β γ : Type _} [ms_rs α] [ms_rs β] [ms_rs γ]
    {f : α → β} {g : α → γ} {alpha : ℝ} :
    contraction_alpha (f ** g) alpha =
      (contraction_alpha f alpha ∧ contraction_alpha g alpha) := by
  simpa [pair_fun, Function.comp] using
    (pair_contra_alpha (fc := (f ** g)) (alpha := alpha))

/- (************************************************************
                       Lemmas (Limit)
 ************************************************************) -/

/- (*****************************************
                  cauchy
 *****************************************) -/

theorem pair_cauchy_seq_fst {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} :
    cauchy xcs → cauchy (Prod.fst ∘ xcs) := by
  intro hcauchy delta hdelta
  rcases hcauchy delta hdelta with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro i j hij
  have hpair : distance (xcs i) (xcs j) < delta := hn i j hij
  have hmax :
      max (distance ((Prod.fst ∘ xcs) i) ((Prod.fst ∘ xcs) j))
        (distance ((Prod.snd ∘ xcs) i) ((Prod.snd ∘ xcs) j)) < delta := by
    rw [pair_distance_max] at hpair
    simpa [Function.comp] using hpair
  exact lt_of_le_of_lt (le_max_left _ _) hmax

theorem pair_cauchy_seq_snd {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} :
    cauchy xcs → cauchy (Prod.snd ∘ xcs) := by
  intro hcauchy delta hdelta
  rcases hcauchy delta hdelta with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro i j hij
  have hpair : distance (xcs i) (xcs j) < delta := hn i j hij
  have hmax :
      max (distance ((Prod.fst ∘ xcs) i) ((Prod.fst ∘ xcs) j))
        (distance ((Prod.snd ∘ xcs) i) ((Prod.snd ∘ xcs) j)) < delta := by
    rw [pair_distance_max] at hpair
    simpa [Function.comp] using hpair
  exact lt_of_le_of_lt (le_max_right _ _) hmax

theorem pair_cauchy_seq_fst_compo {α β : Type _} [ms_rs α] [ms_rs β]
    {xc : infinite_seq α} {yc : infinite_seq β} :
    cauchy (xc ** yc) → cauchy xc := by
  simpa [pair_fun, Function.comp] using
    (pair_cauchy_seq_fst (xcs := (xc ** yc)))

theorem pair_cauchy_seq_snd_compo {α β : Type _} [ms_rs α] [ms_rs β]
    {xc : infinite_seq α} {yc : infinite_seq β} :
    cauchy (xc ** yc) → cauchy yc := by
  simpa [pair_fun, Function.comp] using
    (pair_cauchy_seq_snd (xcs := (xc ** yc)))

/- (*** normal ***) -/

theorem pair_normal_seq_fst {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} :
    normal xcs → normal (Prod.fst ∘ xcs) := by
  intro hnormal n m
  have hpair : distance (xcs n) (xcs m) <= (1 / 2 : ℝ) ^ min n m := hnormal n m
  have hmax :
      max (distance ((Prod.fst ∘ xcs) n) ((Prod.fst ∘ xcs) m))
        (distance ((Prod.snd ∘ xcs) n) ((Prod.snd ∘ xcs) m)) <=
      (1 / 2 : ℝ) ^ min n m := by
    rw [pair_distance_max] at hpair
    simpa [Function.comp] using hpair
  exact le_trans (le_max_left _ _) hmax

theorem pair_normal_seq_snd {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} :
    normal xcs → normal (Prod.snd ∘ xcs) := by
  intro hnormal n m
  have hpair : distance (xcs n) (xcs m) <= (1 / 2 : ℝ) ^ min n m := hnormal n m
  have hmax :
      max (distance ((Prod.fst ∘ xcs) n) ((Prod.fst ∘ xcs) m))
        (distance ((Prod.snd ∘ xcs) n) ((Prod.snd ∘ xcs) m)) <=
      (1 / 2 : ℝ) ^ min n m := by
    rw [pair_distance_max] at hpair
    simpa [Function.comp] using hpair
  exact le_trans (le_max_right _ _) hmax

theorem pair_normal_seq_fst_compo {α β : Type _} [ms_rs α] [ms_rs β]
    {xc : infinite_seq α} {yc : infinite_seq β} :
    normal (xc ** yc) → normal xc := by
  simpa [pair_fun, Function.comp] using
    (pair_normal_seq_fst (xcs := (xc ** yc)))

theorem pair_normal_seq_snd_compo {α β : Type _} [ms_rs α] [ms_rs β]
    {xc : infinite_seq α} {yc : infinite_seq β} :
    normal (xc ** yc) → normal yc := by
  simpa [pair_fun, Function.comp] using
    (pair_normal_seq_snd (xcs := (xc ** yc)))

theorem pair_normal_seq_compo_only_if {α β : Type _} [ms_rs α] [ms_rs β]
    {xc : infinite_seq α} {yc : infinite_seq β} :
    normal xc → normal yc → normal (xc ** yc) := by
  intro hxc hyc n m
  rw [pair_distance_max]
  refine max_le ?_ ?_
  · simpa [pair_fun] using hxc n m
  · simpa [pair_fun] using hyc n m

/- iff -/

theorem pair_normal_seq_compo_iff {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} :
    normal xcs = (normal (Prod.fst ∘ xcs) ∧ normal (Prod.snd ∘ xcs)) := by
  apply propext
  constructor
  · intro hnormal
    exact ⟨pair_normal_seq_fst hnormal, pair_normal_seq_snd hnormal⟩
  · rintro ⟨hfst, hsnd⟩
    simpa [pair_fun, Function.comp] using
      (pair_normal_seq_compo_only_if (xc := Prod.fst ∘ xcs) (yc := Prod.snd ∘ xcs) hfst hsnd)

/- -----------------------*
 |     pairof Limits     |
 *----------------------- -/

/- (*** Limit (single <-- pair) ***) -/

theorem pair_convergeTo_fst_only_if {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} {yc : α × β} :
    xcs convergeTo yc → (Prod.fst ∘ xcs) convergeTo (Prod.fst yc) := by
  intro hconv eps heps
  rcases hconv eps heps with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro m hm
  have hpair : distance yc (xcs m) < eps := hn m hm
  have hmax :
      max (distance (Prod.fst yc) ((Prod.fst ∘ xcs) m))
        (distance (Prod.snd yc) ((Prod.snd ∘ xcs) m)) < eps := by
    rw [pair_distance_max] at hpair
    simpa [Function.comp] using hpair
  exact lt_of_le_of_lt (le_max_left _ _) hmax

theorem pair_convergeTo_snd_only_if {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} {yc : α × β} :
    xcs convergeTo yc → (Prod.snd ∘ xcs) convergeTo (Prod.snd yc) := by
  intro hconv eps heps
  rcases hconv eps heps with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro m hm
  have hpair : distance yc (xcs m) < eps := hn m hm
  have hmax :
      max (distance (Prod.fst yc) ((Prod.fst ∘ xcs) m))
        (distance (Prod.snd yc) ((Prod.snd ∘ xcs) m)) < eps := by
    rw [pair_distance_max] at hpair
    simpa [Function.comp] using hpair
  exact lt_of_le_of_lt (le_max_right _ _) hmax

/- (*** Limit (single --> pair) (note: ms_rs) ***) -/

theorem pair_convergeTo_if {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} {yc : α × β} :
    (Prod.fst ∘ xcs) convergeTo (Prod.fst yc) →
      (Prod.snd ∘ xcs) convergeTo (Prod.snd yc) →
      xcs convergeTo yc := by
  intro hfst hsnd eps heps
  rcases hfst eps heps with ⟨N1, hN1⟩
  rcases hsnd eps heps with ⟨N2, hN2⟩
  refine ⟨max N1 N2, ?_⟩
  intro n hn
  rw [pair_distance_max]
  exact max_lt_iff.mpr ⟨
    by simpa [Function.comp] using hN1 n (le_trans (le_max_left _ _) hn),
    by simpa [Function.comp] using hN2 n (le_trans (le_max_right _ _) hn)⟩

/- (*** iff ***) -/

theorem pair_convergeTo {α β : Type _} [ms_rs α] [ms_rs β]
    {xcs : infinite_seq (α × β)} {yc : α × β} :
    xcs convergeTo yc =
      ((Prod.fst ∘ xcs) convergeTo (Prod.fst yc) ∧ (Prod.snd ∘ xcs) convergeTo (Prod.snd yc)) := by
  apply propext
  constructor
  · intro hconv
    exact ⟨pair_convergeTo_fst_only_if hconv, pair_convergeTo_snd_only_if hconv⟩
  · rintro ⟨hfst, hsnd⟩
    exact pair_convergeTo_if hfst hsnd

theorem pair_convergeTo_compo {α β : Type _} [ms_rs α] [ms_rs β]
    {xs : infinite_seq α} {ys : infinite_seq β} {x : α} {y : β} :
    (xs ** ys) convergeTo (x, y) = (xs convergeTo x ∧ ys convergeTo y) := by
  simpa [pair_fun, Function.comp] using
    (pair_convergeTo (xcs := (xs ** ys)) (yc := (x, y)))

/- (*****************************************
     Limit (cms and cauchy --> Limit)
 *****************************************) -/

theorem pair_cms_cauchy_Limit {α β : Type _} [cms_rs α] [cms_rs β] [Inhabited α] [Inhabited β]
    {xcs : infinite_seq (α × β)} :
    cauchy xcs → xcs convergeTo (pair_Limit xcs) := by
  intro hcauchy
  rw [pair_convergeTo, pair_Limit_def]
  exact ⟨Limit_is (pair_cauchy_seq_fst hcauchy), Limit_is (pair_cauchy_seq_snd hcauchy)⟩

/- (*****************************************
     Pair Complete Metric Space (RS)
 *****************************************) -/

theorem pair_cms_rs {α β : Type _} [cms_rs α] [cms_rs β] {xcs : infinite_seq (α × β)} :
    cauchy xcs → ∃ yc, xcs convergeTo yc := by
  intro hcauchy
  rcases cms.complete_ms (Prod.fst ∘ xcs) (pair_cauchy_seq_fst hcauchy) with ⟨a, ha⟩
  rcases cms.complete_ms (Prod.snd ∘ xcs) (pair_cauchy_seq_snd hcauchy) with ⟨b, hb⟩
  exact ⟨(a, b), pair_convergeTo_if ha hb⟩

/- (************************************************************
                   Pair RS ==> CMS and RS
 ************************************************************) -/

instance instCmsRsProd {α β : Type _} [cms_rs α] [cms_rs β] : cms_rs (α × β) where
  complete_ms := by
    intro xs
    exact pair_cms_rs (xcs := xs)

/- ----------------------------------------------------------*
 |                                                          |
 |                Continuity on Metric space                |
 |                                                          |
 *---------------------------------------------------------- -/

theorem pair_continuous_rs {α β : Type _} [ms_rs α] [ms_rs β]
    {R1 : α → Prop} {R2 : β → Prop} :
    continuous_rs R1 →
      continuous_rs R2 →
      continuous_rs (fun xc => R1 (Prod.fst xc) ∧ R2 (Prod.snd xc)) := by
  intro hR1 hR2 xc hnot
  classical
  have hsplit : ¬ R1 (Prod.fst xc) ∨ ¬ R2 (Prod.snd xc) := by
    exact not_and_or.mp hnot
  rcases hsplit with hfst | hsnd
  · rcases hR1 (Prod.fst xc) hfst with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro yc hyEq hy
    have hEqFst : (Prod.fst yc) .|. n = (Prod.fst xc) .|. n := by
      simpa [pair_restriction_def] using congrArg Prod.fst hyEq
    exact (hn (Prod.fst yc) hEqFst) hy.1
  · rcases hR2 (Prod.snd xc) hsnd with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro yc hyEq hy
    have hEqSnd : (Prod.snd yc) .|. n = (Prod.snd xc) .|. n := by
      simpa [pair_restriction_def] using congrArg Prod.snd hyEq
    exact (hn (Prod.snd yc) hEqSnd) hy.2

/- ----------------------------------------------------------*
 |                                                          |
 |      !!!     order and restriction space     !!!         |
 |                                                          |
 *---------------------------------------------------------- -/

instance instMsRsOrder0Prod {α β : Type _} [ms_rs_order α] [ms_rs_order β] :
    ms_rs_order0 (α × β) where

instance instMsRsOrderProd {α β : Type _} [ms_rs_order α] [ms_rs_order β] :
    ms_rs_order (α × β) where
  rs_order_iff := by
    intro x y
    constructor
    · intro hrest
      apply order_pair_def.mpr
      constructor
      · exact (ms_rs_order.rs_order_iff (Prod.fst x) (Prod.fst y)).1 (fun n =>
          (order_pair_def.mp (hrest n)).1)
      · exact (ms_rs_order.rs_order_iff (Prod.snd x) (Prod.snd y)).1 (fun n =>
          (order_pair_def.mp (hrest n)).2)
    · intro hle
      rcases order_pair_def.mp hle with ⟨hfst, hsnd⟩
      intro n
      exact order_pair_def.mpr ⟨
        rs_order_if (x := Prod.fst x) (y := Prod.fst y) (n := n) hfst,
        rs_order_if (x := Prod.snd x) (y := Prod.snd y) (n := n) hsnd⟩

/- (*** cms rs order ***) -/

instance instCmsRsOrderProd {α β : Type _} [cms_rs_order α] [cms_rs_order β] :
    cms_rs_order (α × β) where

end
