           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
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

import LeanCspProver.CSP.Norm_seq

noncomputable section

open Set

/-
(*****************************************************************

         1. Definition of Restriction Spaces (RS)
         2. RS ==> MS
         3. Metric Fixed point induction
         4.

 *****************************************************************)
-/


/-
  It was defined by ("_ .|. _" [55,56] 55) until Isabelle 2007,
  but it was changed because it caused many syntactic ambiguity
  in Isabelle 2008.
-/


/- (******** X-symbols ********) -/
/-
notation (xsymbols) restriction ("_ \<down> _" [84,900] 84)

Isabelle 2005
syntax (output)
  "_restriction" :: "'a::ms0 => nat => 'a::ms0"  ("_ .|. _" [55,56] 55)

syntax (xsymbols)
  "_restriction" :: "'a::ms0 => nat => 'a::ms0"  ("_ \<down> _" [55,56] 55)

translations
  "x \<down> n"  == "x .|. n"
-/

/- (**********************************************************
                  restriction space (rs)
 **********************************************************) -/

/- isabelle2009-1
consts
  restriction :: "'a::ms0 => nat => 'a::ms0"  ("_ .|. _" [84,900] 84)

axclass rs < ms0
  zero_eq_rs: "ALL (x::'a::ms0) (y::'a::ms0). x .|. 0 = y .|. 0"
  min_rs    : "ALL (x::'a::ms0) (m::nat) (n::nat).
                     (x .|. m) .|. n = x .|. (min m n)"
  diff_rs   : "ALL (x::'a::ms0) (y::'a::ms0).
                     (x ~= y) --> (EX n. x .|. n ~= y .|. n)"
-/

class rs0 (α : Type u) where
  restriction : α → Nat → α

export rs0 (restriction)

infixl:84 " .|. " => restriction

class rs (α : Type u) extends rs0 α where
  zero_eq_rs : ∀ x y : α, x .|. 0 = y .|. 0
  min_rs : ∀ x : α, ∀ m n : Nat, (x .|. m) .|. n = x .|. (min m n)
  diff_rs : ∀ x y : α, x ≠ y → ∃ n : Nat, x .|. n ≠ y .|. n

attribute [simp] rs.zero_eq_rs

private theorem half_pow_antitone {m n : Nat} (h : m ≤ n) :
    (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ m := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · exact le_of_lt (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) hlt)
  · simp

theorem diff_rs_Suc {α : Type u} [rs α] :
    ∀ n (x y : α), x .|. n ≠ y .|. n → ∃ m, n = Nat.succ m := by
  intro n
  cases n with
  | zero =>
      intro x y h
      exact False.elim (h (rs.zero_eq_rs x y))
  | succ m =>
      intro x y _h
      exact ⟨m, rfl⟩

/- (**********************************************************
            restriction space --> metric space
 **********************************************************)
-/

def distance_nat_set {α : Type u} [rs α] (x y : α) : Set Nat :=
  {n | x .|. n = y .|. n}

def distance_nat {α : Type u} [rs α] (x y : α) : Nat :=
  Max (distance_nat_set x y)

def distance_rs_set {α : Type u} [rs α] (x y : α) : Set ℝ :=
  {r | ∃ n, n ∈ distance_nat_set x y ∧ r = (1 / 2 : ℝ) ^ n}

def distance_rs {α : Type u} [rs α] (x y : α) : ℝ :=
  GLB (distance_rs_set x y)

/- (**********************************************************
             complete restriction space (crs)
 **********************************************************)
-/

class ms0_rs (α : Type u) extends ms0 α, rs α where
  to_distance_rs : ∀ x y, distance x y = distance_rs x y

class ms_rs (α : Type u) extends ms α, ms0_rs α
class cms_rs (α : Type u) extends cms α, ms_rs α

/- (**********************************************************
                        RS lemmas
 **********************************************************)
-/

/- (*** contraposition of diff_rs ***) -/

theorem contra_diff_rs {α : Type u} [rs α] {x y : α} :
    (∀ n, x .|. n = y .|. n) → x = y := by
  intro hxy
  by_contra hneq
  rcases rs.diff_rs x y hneq with ⟨n, hn⟩
  exact hn (hxy n)

/- (*** diff_rs inv ***) -/

theorem contra_diff_rs_inv {α : Type u} [rs α] {x y : α} {n : Nat} :
    x .|. n ≠ y .|. n → x ≠ y := by
  intro hneq hxy
  subst hxy
  exact hneq rfl

/- (*** zero distance ***) -/

theorem distance_rs_zero {α : Type u} [rs α] (x : α) :
    distance_rs x x = 0 := by
  have hset :
      distance_rs_set x x = {r : ℝ | ∃ n : Nat, r = (1 / 2 : ℝ) ^ n} := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨n, -, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [distance_nat_set], rfl⟩
  rw [distance_rs, hset]
  simpa using (zero_GLB_pow (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num))

/- ---------------------------*
 |       equal-preserv       |
 *--------------------------- -/

theorem rest_equal_preserve {α : Type u} [rs α] {x y : α} {m n : Nat} :
    x .|. n = y .|. n → m ≤ n → x .|. m = y .|. m := by
  intro hxy hmn
  calc
    x .|. m = (x .|. n) .|. m := by
      symm
      simpa [min_eq_right hmn] using (rs.min_rs x n m)
    _ = (y .|. n) .|. m := by rw [hxy]
    _ = y .|. m := by
      simpa [min_eq_right hmn] using (rs.min_rs y n m)

theorem rest_equal_preserve_Suc {α : Type u} [rs α] {x y : α} {n : Nat} :
    x .|. Nat.succ n = y .|. Nat.succ n → x .|. n = y .|. n := by
  intro hxy
  exact rest_equal_preserve hxy (Nat.le_succ _)

theorem rest_nonequal_preserve {α : Type u} [rs α] {x y : α} {m n : Nat} :
    x .|. m ≠ y .|. m → m ≤ n → x .|. n ≠ y .|. n := by
  intro hneq hmn heq
  exact hneq (rest_equal_preserve heq hmn)

/- ---------------------------*
 |  distance_nat_set hasMAX  |
 *--------------------------- -/

theorem distance_nat_set_hasMAX {α : Type u} [rs α] {x y : α} :
    x ≠ y → hasMAX (distance_nat_set x y) := by
  intro hxy
  have hne : {m : Nat | x .|. m ≠ y .|. m} ≠ ∅ := by
    rcases rs.diff_rs x y hxy with ⟨n, hn⟩
    exact Set.nonempty_iff_ne_empty.mp ⟨n, hn⟩
  rcases EX_MIN_nat hne with ⟨n, hmin⟩
  have hn0 : n ≠ 0 := by
    intro hz
    exact hmin.2 (by simpa [hz] using (rs.zero_eq_rs x y))
  rcases nat_zero_or_Suc n with rfl | ⟨m, hm⟩
  · exact False.elim (hn0 rfl)
  · subst hm
    refine ⟨m, ?_⟩
    constructor
    · intro ya hya
      by_contra hlt
      have hsle : Nat.succ m ≤ ya := Nat.succ_le_of_lt (lt_of_not_ge hlt)
      have hEq : x .|. Nat.succ m = y .|. Nat.succ m := rest_equal_preserve hya hsle
      exact hmin.2 hEq
    · by_contra hmneq
      have hle : Nat.succ m ≤ m := hmin.1 m hmneq
      exact Nat.not_succ_le_self m hle

/- ---------------------------*
 |     isMAX <--> isGLB      |
 *--------------------------- -/

theorem to_distance_rsMAX_isGLB {α : Type u} [rs α] {x y : α} {n : Nat} :
    isMAX n (distance_nat_set x y) →
      isGLB ((1 / 2 : ℝ) ^ n) (distance_rs_set x y) := by
  intro hmax
  constructor
  · intro r hr
    rcases hr with ⟨m, hm, rfl⟩
    exact half_pow_antitone (hmax.1 m hm)
  · intro b hb
    exact hb ((1 / 2 : ℝ) ^ n) ⟨n, hmax.2, rfl⟩

/- ---------------------------*
 |    distance_set hasGLB    |
 *--------------------------- -/

theorem distance_rs_set_hasGLB {α : Type u} [rs α] (x y : α) :
    hasGLB (distance_rs_set x y) := by
  by_cases hxy : x = y
  · subst hxy
    refine ⟨0, ?_⟩
    have hset :
        distance_rs_set x x = {r : ℝ | ∃ n : Nat, r = (1 / 2 : ℝ) ^ n} := by
      ext r
      constructor
      · intro hr
        rcases hr with ⟨n, -, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨n, by simp [distance_nat_set], rfl⟩
    rw [hset]
    simpa using (zero_isGLB_pow (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  · rcases distance_nat_set_hasMAX (x := x) (y := y) hxy with ⟨n, hn⟩
    exact ⟨(1 / 2 : ℝ) ^ n, to_distance_rsMAX_isGLB hn⟩

/- ---------------------------*
 |       MAX <--> GLB        |
 *--------------------------- -/

theorem distance_rs_nat_lm {α : Type u} [rs α] {x y : α} {n : Nat} {r : ℝ} :
    x ≠ y → distance_nat x y = n → distance_rs x y = r → r = (1 / 2 : ℝ) ^ n := by
  intro hxy hnat hrs
  have hmax : isMAX n (distance_nat_set x y) := by
    exact (MAX_to_isMAX (X := distance_nat_set x y) (x := n)
      (distance_nat_set_hasMAX (x := x) (y := y) hxy)).1 (by simpa [distance_nat] using hnat.symm)
  have hglbR : isGLB r (distance_rs_set x y) := by
    exact (GLB_to_isGLB (X := distance_rs_set x y) (x := r)
      (distance_rs_set_hasGLB x y)).1 (by simpa [distance_rs] using hrs.symm)
  have hglbPow : isGLB ((1 / 2 : ℝ) ^ n) (distance_rs_set x y) :=
    to_distance_rsMAX_isGLB hmax
  simpa [eq_comm] using (GLB_unique hglbPow hglbR)

theorem distance_iff1 {α : Type u} [rs α] {x y : α} :
    x ≠ y → distance_rs x y = (1 / 2 : ℝ) ^ distance_nat x y := by
  intro hxy
  exact distance_rs_nat_lm (x := x) (y := y) (n := distance_nat x y) (r := distance_rs x y) hxy rfl rfl

theorem distance_iff2 {α : Type u} [rs α] {x y : α} :
    y ≠ x → distance_rs x y = (1 / 2 : ℝ) ^ distance_nat x y := by
  intro hyx
  exact distance_iff1 (x := x) (y := y) (by exact hyx.symm)

/- ---------------------------*
 |       less than 1B        |
 *--------------------------- -/

theorem distance_rs_less_one {α : Type u} [rs α] (x y : α) :
    distance_rs x y ≤ 1 := by
  by_cases hxy : x = y
  · subst hxy
    simp [distance_rs_zero]
  · rw [distance_iff1 hxy]
    have hpow := half_pow_antitone (m := 0) (n := distance_nat x y) (Nat.zero_le _)
    simpa using hpow

/- ---------------------------*
 |      distance_nat iff     |
 *--------------------------- -/

theorem isMAX_distance_nat1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (isMAX n (distance_nat_set x y) ↔ distance_nat x y = n) := by
  intro hxy
  constructor
  · intro hmax
    have hdist : isMAX (distance_nat x y) (distance_nat_set x y) := by
      exact (MAX_to_isMAX_sym (X := distance_nat_set x y) (x := distance_nat x y)
        (distance_nat_set_hasMAX (x := x) (y := y) hxy)).1 (by simp [distance_nat])
    exact MAX_unique hdist hmax
  · intro hnat
    exact (MAX_to_isMAX (X := distance_nat_set x y) (x := n)
      (distance_nat_set_hasMAX (x := x) (y := y) hxy)).1 (by simpa [distance_nat] using hnat.symm)

theorem distance_nat_isMAX1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (distance_nat x y = n ↔ isMAX n (distance_nat_set x y)) := by
  intro hxy
  exact (isMAX_distance_nat1 (x := x) (y := y) (n := n) hxy).symm

theorem distance_nat_isMAX_sym1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (n = distance_nat x y ↔ isMAX n (distance_nat_set x y)) := by
  intro hxy
  simpa [eq_comm] using distance_nat_isMAX1 (x := x) (y := y) (n := n) hxy

theorem isMAX_distance_nat2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    y ≠ x → (isMAX n (distance_nat_set x y) ↔ distance_nat x y = n) := by
  intro hyx
  exact isMAX_distance_nat1 (x := x) (y := y) (n := n) hyx.symm

theorem distance_nat_isMAX2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    y ≠ x → (distance_nat x y = n ↔ isMAX n (distance_nat_set x y)) := by
  intro hyx
  exact (isMAX_distance_nat2 (x := x) (y := y) (n := n) hyx).symm

theorem distance_nat_isMAX_sym2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    y ≠ x → (n = distance_nat x y ↔ isMAX n (distance_nat_set x y)) := by
  intro hyx
  simpa [eq_comm] using distance_nat_isMAX2 (x := x) (y := y) (n := n) hyx

/- (*** for insert ***) -/

theorem distance_nat_is {α : Type u} [rs α] {x y : α} :
    x ≠ y → isMAX (distance_nat x y) (distance_nat_set x y) := by
  intro hxy
  exact (distance_nat_isMAX1 (x := x) (y := y) (n := distance_nat x y) hxy).1 rfl

/- ============================================================*
 |                                                            |
 |         (restriction space ==> metric space)               |
 |                                                            |
 |    instance x :: (type) rs ==> instance x :: (type) ms     |
 |                                                            |
 |               by  positive_rs                              |
 |                   diagonal_rs                              |
 |                   symmetry_rs                              |
 |                   triangle_inequality_rs                   |
 |                                                            |
 *============================================================ -/

/- (*** positive_rs ***) -/

theorem positive_rs {α : Type u} [rs α] (x y : α) :
    0 ≤ distance_rs x y := by
  by_cases hxy : x = y
  · subst hxy
    simp [distance_rs_zero]
  · rw [distance_iff1 hxy]
    positivity

/- (*** diagonal_rs ***) -/

theorem diagonal_rs_only_if {α : Type u} [rs α] {x y : α} :
    distance_rs x y = 0 → x = y := by
  intro hdist
  by_cases hxy : x = y
  · exact hxy
  · rw [distance_iff1 hxy] at hdist
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ distance_nat x y := by positivity
    linarith

theorem diagonal_rs {α : Type u} [rs α] {x y : α} :
    distance_rs x y = 0 ↔ x = y := by
  constructor
  · exact diagonal_rs_only_if
  · intro hxy
    subst hxy
    simp [distance_rs_zero]

theorem diagonal_rs_neq {α : Type u} [rs α] {x y : α} :
    x ≠ y → 0 < distance_rs x y := by
  intro hxy
  rw [distance_iff1 hxy]
  positivity

/- (*** symmetry_rs ***) -/

theorem symmetry_nat_lm {α : Type u} [rs α] {x y : α} {n m : Nat} :
    x ≠ y → distance_nat x y = n → distance_nat y x = m → n = m := by
  intro hxy hxyNat hyxNat
  have hset : distance_nat_set x y = distance_nat_set y x := by
    ext k
    simp [distance_nat_set, eq_comm]
  have hmax1 : isMAX n (distance_nat_set x y) := by
    exact (distance_nat_isMAX1 (x := x) (y := y) (n := n) hxy).1 hxyNat
  have hmax2 : isMAX m (distance_nat_set x y) := by
    rw [hset]
    exact (distance_nat_isMAX1 (x := y) (y := x) (n := m) (Ne.symm hxy)).1 hyxNat
  exact MAX_unique hmax1 hmax2

theorem symmetry_nat {α : Type u} [rs α] {x y : α} :
    x ≠ y → distance_nat x y = distance_nat y x := by
  intro hxy
  exact symmetry_nat_lm (x := x) (y := y) (n := distance_nat x y) (m := distance_nat y x)
    hxy rfl rfl

theorem symmetry_rs {α : Type u} [rs α] (x y : α) :
    distance_rs x y = distance_rs y x := by
  by_cases hxy : x = y
  · subst hxy
    simp [distance_rs_zero]
  · rw [distance_iff1 hxy, distance_iff1 (Ne.symm hxy), symmetry_nat hxy]

/- (*** triangle_inequality_rs ***) -/

theorem triangle_inequality_nat_lm {α : Type u} [rs α] {x y z : α} {n1 n2 n3 : Nat} :
    x ≠ y → y ≠ z → x ≠ z →
      distance_nat x z = n1 →
      distance_nat x y = n2 →
      distance_nat y z = n3 →
      min n2 n3 ≤ n1 := by
  intro hxy hyz hxz hxzNat hxyNat hyzNat
  have hxyEq : x .|. n2 = y .|. n2 := by
    have hmax := distance_nat_is (x := x) (y := y) hxy
    rw [hxyNat] at hmax
    exact hmax.2
  have hyzEq : y .|. n3 = z .|. n3 := by
    have hmax := distance_nat_is (x := y) (y := z) hyz
    rw [hyzNat] at hmax
    exact hmax.2
  have hxyMin : x .|. min n2 n3 = y .|. min n2 n3 :=
    rest_equal_preserve hxyEq (min_le_left _ _)
  have hyzMin : y .|. min n2 n3 = z .|. min n2 n3 :=
    rest_equal_preserve hyzEq (min_le_right _ _)
  have hxzEq : x .|. min n2 n3 = z .|. min n2 n3 := by
    calc
      x .|. min n2 n3 = y .|. min n2 n3 := hxyMin
      _ = z .|. min n2 n3 := hyzMin
  rw [← hxzNat]
  exact (distance_nat_is (x := x) (y := z) hxz).1 _ hxzEq

theorem triangle_inequality_nat {α : Type u} [rs α] {x y z : α} :
    x ≠ y → y ≠ z → x ≠ z →
      min (distance_nat x y) (distance_nat y z) ≤ distance_nat x z := by
  intro hxy hyz hxz
  exact triangle_inequality_nat_lm (x := x) (y := y) (z := z)
    (n1 := distance_nat x z) (n2 := distance_nat x y) (n3 := distance_nat y z)
    hxy hyz hxz rfl rfl rfl

theorem triangle_inequality_neq {α : Type u} [rs α] {x y z : α} :
    x ≠ y → y ≠ z → x ≠ z →
      distance_rs x z ≤ max (distance_rs x y) (distance_rs y z) := by
  intro hxy hyz hxz
  rw [distance_iff1 hxz, distance_iff1 hxy, distance_iff1 hyz]
  have htri := triangle_inequality_nat (x := x) (y := y) (z := z) hxy hyz hxz
  by_cases hcase : distance_nat x y ≤ distance_nat y z
  · have hpow :
        (1 / 2 : ℝ) ^ distance_nat x z ≤ (1 / 2 : ℝ) ^ distance_nat x y :=
      half_pow_antitone (by simpa [min_eq_left hcase] using htri)
    have hmax : max ((1 / 2 : ℝ) ^ distance_nat x y) ((1 / 2 : ℝ) ^ distance_nat y z) =
        (1 / 2 : ℝ) ^ distance_nat x y := by
      apply max_eq_left
      exact half_pow_antitone hcase
    rw [hmax]
    exact hpow
  · have hyx : distance_nat y z ≤ distance_nat x y := le_of_not_ge hcase
    have hpow :
        (1 / 2 : ℝ) ^ distance_nat x z ≤ (1 / 2 : ℝ) ^ distance_nat y z :=
      half_pow_antitone (by simpa [min_eq_right hyx] using htri)
    have hmax : max ((1 / 2 : ℝ) ^ distance_nat x y) ((1 / 2 : ℝ) ^ distance_nat y z) =
        (1 / 2 : ℝ) ^ distance_nat y z := by
      apply max_eq_right
      exact half_pow_antitone hyx
    rw [hmax]
    exact hpow

theorem triangle_inequality_max {α : Type u} [rs α] (x y z : α) :
    distance_rs x z ≤ max (distance_rs x y) (distance_rs y z) := by
  by_cases hxy : x = y
  · subst hxy
    simpa [distance_rs_zero] using (le_max_right (distance_rs y y) (distance_rs y z))
  by_cases hyz : y = z
  · subst hyz
    simpa [distance_rs_zero] using (le_max_left (distance_rs x y) (distance_rs y y))
  by_cases hxz : x = z
  · subst hxz
    have hnonneg : (0 : ℝ) ≤ max (distance_rs x y) (distance_rs y x) :=
      le_trans (positive_rs x y) (le_max_left _ _)
    simpa [distance_rs_zero, symmetry_rs] using hnonneg
  · exact triangle_inequality_neq hxy hyz hxz

theorem triangle_inequality_rs {α : Type u} [rs α] (x y z : α) :
    distance_rs x z ≤ distance_rs x y + distance_rs y z := by
  have hmax := triangle_inequality_max x y z
  refine le_trans hmax ?_
  exact max_le (le_add_of_nonneg_right (positive_rs _ _))
    (le_add_of_nonneg_left (positive_rs _ _))

/- (**********************************************************
                 .|. <--> distance_nat
 **********************************************************)
-/

/- ---------------------------*
 |  distance_nat satisfies   |
 *--------------------------- -/

theorem distance_nat_rest {α : Type u} [rs α] {x y : α} :
    x ≠ y → distance_nat x y = n → x .|. n = y .|. n := by
  intro hxy hnat
  have hmax := distance_nat_is (x := x) (y := y) hxy
  rw [hnat] at hmax
  exact hmax.2

/- ---------------------------*
 |    distance_nat is max    |
 *--------------------------- -/

theorem distance_nat_rest_Suc {α : Type u} [rs α] {x y : α} :
    x ≠ y → distance_nat x y = n → x .|. Nat.succ n ≠ y .|. Nat.succ n := by
  intro hxy hnat
  have hmax := distance_nat_is (x := x) (y := y) hxy
  rw [hnat] at hmax
  intro heq
  have hle : Nat.succ n ≤ n := hmax.1 _ heq
  exact Nat.not_succ_le_self n hle

/- ---------------------------*
 |     distance_nat_le       |
 *--------------------------- -/

theorem distance_nat_le_1_only_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → x .|. n = y .|. n → n ≤ distance_nat x y := by
  intro hxy heq
  exact (distance_nat_is (x := x) (y := y) hxy).1 _ heq

theorem distance_nat_le_1_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → n ≤ distance_nat x y → x .|. n = y .|. n := by
  intro hxy hn
  exact rest_equal_preserve (distance_nat_rest (x := x) (y := y) hxy rfl) hn

theorem distance_nat_le_1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (x .|. n = y .|. n ↔ n ≤ distance_nat x y) := by
  intro hxy
  constructor
  · exact distance_nat_le_1_only_if hxy
  · exact distance_nat_le_1_if hxy

theorem distance_nat_le_2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (x .|. n ≠ y .|. n ↔ distance_nat x y < n) := by
  intro hxy
  constructor
  · intro hneq
    exact lt_of_not_ge (fun hle => hneq (distance_nat_le_1_if hxy hle))
  · intro hlt
    exact rest_nonequal_preserve (distance_nat_rest_Suc (x := x) (y := y) hxy rfl) (Nat.succ_le_of_lt hlt)

/- ---------------------------*
 |    distance_nat_less      |
 *--------------------------- -/

theorem distance_nat_less_1_only_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → x .|. Nat.succ n = y .|. Nat.succ n → n < distance_nat x y := by
  intro hxy heq
  exact lt_of_lt_of_le (Nat.lt_succ_self n) (distance_nat_le_1_only_if hxy heq)

theorem distance_nat_less_1_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → n < distance_nat x y → x .|. Nat.succ n = y .|. Nat.succ n := by
  intro hxy hlt
  exact rest_equal_preserve (distance_nat_rest (x := x) (y := y) hxy rfl) (Nat.succ_le_of_lt hlt)

theorem distance_nat_less_1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (x .|. Nat.succ n = y .|. Nat.succ n ↔ n < distance_nat x y) := by
  intro hxy
  constructor
  · exact distance_nat_less_1_only_if hxy
  · exact distance_nat_less_1_if hxy

theorem distance_nat_less_2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    x ≠ y → (x .|. Nat.succ n ≠ y .|. Nat.succ n ↔ distance_nat x y ≤ n) := by
  intro hxy
  constructor
  · intro hneq
    exact le_of_not_gt (fun hlt => hneq (distance_nat_less_1_if hxy hlt))
  · intro hle
    exact rest_nonequal_preserve (distance_nat_rest_Suc (x := x) (y := y) hxy rfl) (Nat.succ_le_succ hle)

/- (**********************************************************
                   .|. <--> distance
 **********************************************************)
-/

/- ---------------------------*
 |      distance_rs_le       |
 *--------------------------- -/

theorem distance_rs_le_1_only_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    x .|. n = y .|. n → distance_rs x y ≤ (1 / 2 : ℝ) ^ n := by
  intro heq
  by_cases hxy : x = y
  · subst hxy
    simp [distance_rs_zero]
  · rw [distance_iff1 hxy]
    exact half_pow_antitone (distance_nat_le_1_only_if hxy heq)

theorem distance_rs_le_1_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    distance_rs x y ≤ (1 / 2 : ℝ) ^ n → x .|. n = y .|. n := by
  intro hdist
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [distance_iff1 hxy] at hdist
    have hle : n ≤ distance_nat x y :=
      rev_power_decreasing (r := (1 / 2 : ℝ)) (n := distance_nat x y) (m := n)
        (by norm_num) (by norm_num) hdist
    exact distance_nat_le_1_if hxy hle

theorem distance_rs_le_1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    (x .|. n = y .|. n) ↔ distance_rs x y ≤ (1 / 2 : ℝ) ^ n := by
  constructor
  · exact distance_rs_le_1_only_if
  · exact distance_rs_le_1_if

theorem distance_rs_le_2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    (x .|. n ≠ y .|. n) ↔ (1 / 2 : ℝ) ^ n < distance_rs x y := by
  constructor
  · intro hneq
    exact lt_of_not_ge (fun hle => hneq (distance_rs_le_1_if hle))
  · intro hlt
    exact fun heq => not_lt_of_ge (distance_rs_le_1_only_if heq) hlt

/- ---------------------------*
 |       distance_rs_less    |
 *--------------------------- -/

theorem distance_rs_less_1_only_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    x .|. Nat.succ n = y .|. Nat.succ n → distance_rs x y < (1 / 2 : ℝ) ^ n := by
  intro heq
  by_cases hxy : x = y
  · subst hxy
    simp [distance_rs_zero]
  · have hle : distance_rs x y ≤ (1 / 2 : ℝ) ^ Nat.succ n := distance_rs_le_1_only_if heq
    have hlt : (1 / 2 : ℝ) ^ Nat.succ n < (1 / 2 : ℝ) ^ n := by
      simpa [pow_succ] using
        (mul_lt_mul_of_pos_left (by norm_num : (1 / 2 : ℝ) < 1) (show (0 : ℝ) < (1 / 2 : ℝ) ^ n by positivity))
    exact lt_of_le_of_lt hle hlt

theorem distance_rs_less_1_if {α : Type u} [rs α] {x y : α} {n : Nat} :
    distance_rs x y < (1 / 2 : ℝ) ^ n → x .|. Nat.succ n = y .|. Nat.succ n := by
  intro hdist
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [distance_iff1 hxy] at hdist
    have hlt : n < distance_nat x y :=
      rev_power_decreasing_strict (r := (1 / 2 : ℝ)) (n := distance_nat x y) (m := n)
        (by norm_num) (by norm_num) hdist
    exact distance_nat_less_1_if hxy hlt

theorem distance_rs_less_1 {α : Type u} [rs α] {x y : α} {n : Nat} :
    (x .|. Nat.succ n = y .|. Nat.succ n) ↔ distance_rs x y < (1 / 2 : ℝ) ^ n := by
  constructor
  · exact distance_rs_less_1_only_if
  · exact distance_rs_less_1_if

theorem distance_rs_less_2 {α : Type u} [rs α] {x y : α} {n : Nat} :
    (x .|. Nat.succ n ≠ y .|. Nat.succ n) ↔ (1 / 2 : ℝ) ^ n ≤ distance_rs x y := by
  constructor
  · intro hneq
    exact le_of_not_gt (fun hlt => hneq (distance_rs_less_1_if hlt))
  · intro hle
    exact fun heq => not_le_of_gt (distance_rs_less_1_only_if heq) hle

/- (*********************************************************************
                   for constructiveness of prefix
 *********************************************************************)
-/

theorem contra_diff_rs_Suc {α : Type u} [rs α] {x y : α} :
    (∀ n, x .|. Nat.succ n = y .|. Nat.succ n) → x = y := by
  intro hEq
  by_contra hneq
  rcases rs.diff_rs x y hneq with ⟨n, hn⟩
  rcases diff_rs_Suc n x y hn with ⟨m, hm⟩
  subst hm
  exact hn (hEq m)

/- ---------------------------*
 |    for contractiveness    |
 *--------------------------- -/

theorem rest_Suc_dist_half {α : Type u} [rs α] {x1 x2 y1 y2 : α} :
    (∀ n, (x1 .|. n = x2 .|. n) ↔ (y1 .|. Nat.succ n = y2 .|. Nat.succ n)) →
      (1 / 2 : ℝ) * distance_rs x1 x2 = distance_rs y1 y2 := by
  intro hrest
  by_cases hx : x1 = x2
  · subst hx
    have hy : y1 = y2 := by
      apply contra_diff_rs_Suc
      intro n
      exact (hrest n).1 (by simp)
    subst hy
    simp [distance_rs_zero]
  by_cases hy : y1 = y2
  · exfalso
    apply hx
    apply contra_diff_rs
    intro n
    exact (hrest n).2 (by simp [hy])
  · rw [distance_iff1 hx, distance_iff1 hy]
    have hle1 : Nat.succ (distance_nat x1 x2) ≤ distance_nat y1 y2 := by
      have hEq : y1 .|. Nat.succ (distance_nat x1 x2) = y2 .|. Nat.succ (distance_nat x1 x2) := by
        exact (hrest (distance_nat x1 x2)).1 (distance_nat_rest (x := x1) (y := x2) hx rfl)
      exact Nat.succ_le_of_lt (distance_nat_less_1_only_if (x := y1) (y := y2) hy hEq)
    have hle2 : distance_nat y1 y2 ≤ Nat.succ (distance_nat x1 x2) := by
      rcases nat_zero_or_Suc (distance_nat y1 y2) with hzero | ⟨m, hm⟩
      · exfalso
        have : Nat.succ (distance_nat x1 x2) ≤ 0 := by simpa [hzero] using hle1
        exact Nat.not_succ_le_zero _ this
      · have hyEq : y1 .|. Nat.succ m = y2 .|. Nat.succ m := by
          simpa [hm] using (distance_nat_rest (x := y1) (y := y2) hy hm)
        have hEq : x1 .|. m = x2 .|. m := by
          exact (hrest m).2 hyEq
        simpa [hm] using Nat.succ_le_succ (distance_nat_le_1_only_if (x := x1) (y := x2) hx hEq)
    have hNat : distance_nat y1 y2 = Nat.succ (distance_nat x1 x2) :=
      le_antisymm hle2 hle1
    simp [hNat, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/- (*********************************************************************
                  rest_to_dist_pair (fun and pair)
 *********************************************************************)
-/

theorem rest_to_dist_pair {α β : Type _} [rs α] [rs β]
    {xps : Set (α × α)} {y1 y2 : β} :
    xps ≠ ∅ →
      (∀ n, (∀ x ∈ xps, x.1 .|. n = x.2 .|. n) → y1 .|. n = y2 .|. n) →
      ∃ x ∈ xps, distance_rs y1 y2 ≤ distance_rs x.1 x.2 := by
  classical
  intro hxps hrest
  by_cases hy : y1 = y2
  · rcases Set.nonempty_iff_ne_empty.mpr hxps with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    subst hy
    simpa [distance_rs_zero] using (positive_rs x.1 x.2)
  · have hyNeq : y1 .|. Nat.succ (distance_nat y1 y2) ≠ y2 .|. Nat.succ (distance_nat y1 y2) :=
      distance_nat_rest_Suc (x := y1) (y := y2) hy rfl
    have hnotAll : ¬ ∀ x ∈ xps, x.1 .|. Nat.succ (distance_nat y1 y2) = x.2 .|. Nat.succ (distance_nat y1 y2) := by
      intro hall
      exact hyNeq (hrest (Nat.succ (distance_nat y1 y2)) hall)
    push_neg at hnotAll
    rcases hnotAll with ⟨x, hx, hneq⟩
    refine ⟨x, hx, ?_⟩
    rw [distance_iff1 hy]
    exact (distance_rs_less_2 (x := x.1) (y := x.2) (n := distance_nat y1 y2)).1 hneq

theorem rest_to_dist_pair_two {α β γ : Type _} [rs α] [rs β] [rs γ]
    {xps : Set (α × α)} {yps : Set (β × β)} {z1 z2 : γ} :
    xps ≠ ∅ → yps ≠ ∅ →
      (∀ n,
        (∀ x ∈ xps, x.1 .|. n = x.2 .|. n) ∧
        (∀ y ∈ yps, y.1 .|. n = y.2 .|. n) →
        z1 .|. n = z2 .|. n) →
      (∃ x ∈ xps, distance_rs z1 z2 ≤ distance_rs x.1 x.2) ∨
      (∃ y ∈ yps, distance_rs z1 z2 ≤ distance_rs y.1 y.2) := by
  classical
  intro hxps hyps hrest
  by_cases hz : z1 = z2
  · rcases Set.nonempty_iff_ne_empty.mpr hxps with ⟨x, hx⟩
    left
    refine ⟨x, hx, ?_⟩
    subst hz
    simpa [distance_rs_zero] using (positive_rs x.1 x.2)
  · have hzNeq : z1 .|. Nat.succ (distance_nat z1 z2) ≠ z2 .|. Nat.succ (distance_nat z1 z2) :=
      distance_nat_rest_Suc (x := z1) (y := z2) hz rfl
    have hnot : ¬ ((∀ x ∈ xps, x.1 .|. Nat.succ (distance_nat z1 z2) = x.2 .|. Nat.succ (distance_nat z1 z2)) ∧
        (∀ y ∈ yps, y.1 .|. Nat.succ (distance_nat z1 z2) = y.2 .|. Nat.succ (distance_nat z1 z2))) := by
      intro hall
      exact hzNeq (hrest (Nat.succ (distance_nat z1 z2)) hall)
    have hsplit :
        (¬ ∀ x ∈ xps, x.1 .|. Nat.succ (distance_nat z1 z2) = x.2 .|. Nat.succ (distance_nat z1 z2)) ∨
        (¬ ∀ y ∈ yps, y.1 .|. Nat.succ (distance_nat z1 z2) = y.2 .|. Nat.succ (distance_nat z1 z2)) := by
      exact not_and_or.mp hnot
    rcases hsplit with hx | hy'
    · left
      push_neg at hx
      rcases hx with ⟨x, hxmem, hneq⟩
      refine ⟨x, hxmem, ?_⟩
      rw [distance_iff1 hz]
      exact (distance_rs_less_2 (x := x.1) (y := x.2) (n := distance_nat z1 z2)).1 hneq
    · right
      push_neg at hy'
      rcases hy' with ⟨y, hymem, hneq⟩
      refine ⟨y, hymem, ?_⟩
      rw [distance_iff1 hz]
      exact (distance_rs_less_2 (x := y.1) (y := y.2) (n := distance_nat z1 z2)).1 hneq

/- (************************************************************
           .|. <--> distance lemma (different types)
 ************************************************************)
-/

theorem rest_distance_subset {α β : Type _} [rs α] [rs β] {x y : α} {X Y : β} :
    (∀ n, x .|. n = y .|. n → X .|. n = Y .|. n) →
      distance_rs X Y ≤ distance_rs x y := by
  intro hsub
  by_cases hXY : X = Y
  · subst hXY
    simpa [distance_rs_zero] using (positive_rs x y)
  by_cases hxy : x = y
  · have hall : ∀ n, X .|. n = Y .|. n := by
      intro n
      exact hsub n (by simpa [hxy])
    exact False.elim (hXY (contra_diff_rs hall))
  · have hEq : X .|. distance_nat x y = Y .|. distance_nat x y :=
      hsub _ (distance_nat_rest (x := x) (y := y) hxy rfl)
    calc
      distance_rs X Y ≤ (1 / 2 : ℝ) ^ distance_nat x y := distance_rs_le_1_only_if hEq
      _ = distance_rs x y := by symm; exact distance_iff1 hxy

theorem rest_distance_eq {α β : Type _} [rs α] [rs β] {x y : α} {X Y : β} :
    (∀ n, (x .|. n = y .|. n) ↔ (X .|. n = Y .|. n)) →
      distance_rs x y = distance_rs X Y := by
  intro heq
  exact le_antisymm
    (rest_distance_subset (x := X) (y := Y) (X := x) (Y := y) (fun n h => (heq n).2 h))
    (rest_distance_subset (x := x) (y := y) (X := X) (Y := Y) (fun n h => (heq n).1 h))

/- ----------------------------------------------------------*
 |                                                          |
 |                  distance = distance_rs                   |
 |                                                          |
 *---------------------------------------------------------- -/


/- (*********************************************************************
                             Limit (ms_rs)
 *********************************************************************)
-/

/- ---------------------------*
 |  mini_number_cauchy_rest  |
 *--------------------------- -/

theorem mini_number_cauchy_rest {α : Type u} [ms_rs α] {xs : infinite_seq α} {k : Nat} :
    (∀ x y : α, distance x y = distance_rs x y) →
      normal xs →
      ∀ n m, (k ≤ n ∧ k ≤ m) → (xs n) .|. k = (xs m) .|. k := by
  intro hdist hnormal n m hnm
  have hle : distance_rs (xs n) (xs m) ≤ (1 / 2 : ℝ) ^ k := by
    calc
      distance_rs (xs n) (xs m) = distance (xs n) (xs m) := by symm; exact hdist _ _
      _ ≤ (1 / 2 : ℝ) ^ min n m := hnormal n m
      _ ≤ (1 / 2 : ℝ) ^ k := half_pow_antitone (le_min hnm.1 hnm.2)
  exact distance_rs_le_1_if hle

/- ---------------------------*
 |        rest_Limit         |
 *--------------------------- -/

theorem rest_Limit {α : Type u} [ms_rs α] {xs : infinite_seq α} {y : α} :
    (∀ x y' : α, distance x y' = distance_rs x y') →
      (∀ n, y .|. n = (xs n) .|. n) →
      xs convergeTo y := by
  intro hdist hrest eps heps
  obtain ⟨N, hN⟩ := pow_convergence (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num) heps
  refine ⟨N, ?_⟩
  intro m hm
  have hle : distance_rs y (xs m) ≤ (1 / 2 : ℝ) ^ m := distance_rs_le_1_only_if (hrest m)
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N := half_pow_antitone hm
  calc
    distance y (xs m) = distance_rs y (xs m) := hdist _ _
    _ ≤ (1 / 2 : ℝ) ^ m := hle
    _ ≤ (1 / 2 : ℝ) ^ N := hpow
    _ < eps := hN


/- ----------------------------------------------------------*
 |                                                          |
 |              Metric Fixed point induction                |
 |                                                          |
 |               constructive & continuous                  |
 |                                                          |
 *---------------------------------------------------------- -/

def constructive_rs {α β : Type _} [ms_rs α] [ms_rs β] (f : α → β) : Prop :=
  ∀ x y n, x .|. n = y .|. n → (f x) .|. Nat.succ n = (f y) .|. Nat.succ n

def continuous_rs {α : Type _} [ms_rs α] (R : α → Prop) : Prop :=
  ∀ x, ¬ R x → ∃ n, ∀ y, y .|. n = x .|. n → ¬ R y

/- (**********************************************************
              Construction --> Contraction
 **********************************************************)
-/

theorem contst_to_contra_alpha {α β : Type _} [ms_rs α] [ms_rs β]
    {f : α → β} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      constructive_rs f →
      contraction_alpha f (1 / 2 : ℝ) := by
  intro hdistA hdistB hconst
  refine ⟨by norm_num, ?_⟩
  constructor
  · norm_num
  · intro x y
    by_cases hxy : x = y
    · subst hxy
      simp [hdistA, hdistB, distance_rs_zero]
    · by_cases hfx : f x = f y
      · calc
          distance (f x) (f y) = 0 := by simpa [hfx] using same_pnt_zero (f x)
          _ ≤ (1 / 2 : ℝ) * distance x y := by
            have hpos : 0 ≤ distance x y := ms.positive_ms x y
            nlinarith
      · have hEq : (f x) .|. Nat.succ (distance_nat x y) = (f y) .|. Nat.succ (distance_nat x y) :=
          hconst x y (distance_nat x y) (distance_nat_rest (x := x) (y := y) hxy rfl)
        have hle : distance_rs (f x) (f y) ≤ (1 / 2 : ℝ) ^ Nat.succ (distance_nat x y) :=
          distance_rs_le_1_only_if hEq
        calc
          distance (f x) (f y) = distance_rs (f x) (f y) := hdistB _ _
          _ ≤ (1 / 2 : ℝ) ^ Nat.succ (distance_nat x y) := hle
          _ = (1 / 2 : ℝ) * distance_rs x y := by
            rw [distance_iff1 hxy, pow_succ]
            ring
          _ = (1 / 2 : ℝ) * distance x y := by rw [hdistA]

theorem contst_to_contra {α β : Type _} [ms_rs α] [ms_rs β]
    {f : α → β} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      constructive_rs f →
      contraction f := by
  intro hdistA hdistB hconst
  exact ⟨(1 / 2 : ℝ), contst_to_contra_alpha hdistA hdistB hconst⟩

/- (**********************************************************
              Construction --> Contraction
 **********************************************************)
-/

theorem contra_alpha_to_contst {α β : Type _} [ms_rs α] [ms_rs β]
    {f : α → β} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      contraction_alpha f (1 / 2 : ℝ) →
      constructive_rs f := by
  intro hdistA hdistB hcontr x y n heq
  have hmap := hcontr.2.2 x y
  have hxy : distance x y ≤ (1 / 2 : ℝ) ^ n := by
    calc
      distance x y = distance_rs x y := hdistA _ _
      _ ≤ (1 / 2 : ℝ) ^ n := distance_rs_le_1_only_if heq
  have hdist : distance (f x) (f y) ≤ (1 / 2 : ℝ) ^ Nat.succ n := by
    calc
      distance (f x) (f y) ≤ (1 / 2 : ℝ) * distance x y := hmap
      _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_left hxy (by norm_num)
      _ = (1 / 2 : ℝ) ^ Nat.succ n := by
        rw [pow_succ]
        ring
  have hdistRs : distance_rs (f x) (f y) ≤ (1 / 2 : ℝ) ^ Nat.succ n := by
    calc
      distance_rs (f x) (f y) = distance (f x) (f y) := by symm; exact hdistB _ _
      _ ≤ (1 / 2 : ℝ) ^ Nat.succ n := hdist
  exact distance_rs_le_1_if hdistRs

theorem cms_fixpoint_induction {α β : Type _} [cms_rs α] [ms_rs β] [Inhabited α]
    {R : α → Prop} {x : α} {f : α → α} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      R x → continuous_rs R →
      constructive_rs f → inductivefun R f →
      hasUFP f ∧ R (UFP f) := by
  intro hdistA hdistB hx hcont hconst hind
  have hbanach := Banach_thm (f := f) (x0 := x) (contst_to_contra hdistA hdistA hconst)
  rcases hbanach with ⟨hufp, hconv⟩
  refine ⟨hufp, ?_⟩
  by_contra hnot
  rcases hcont (UFP f) hnot with ⟨n, hn⟩
  obtain ⟨N, hN⟩ := hconv ((1 / 2 : ℝ) ^ n) (by positivity)
  have hiter : R ((f^[N]) x) := inductivefun_all_n hind hx N
  have hEqSucc : (UFP f) .|. Nat.succ n = ((f^[N]) x) .|. Nat.succ n := by
    apply distance_rs_less_1_if
    calc
      distance_rs (UFP f) ((f^[N]) x) = distance (UFP f) ((f^[N]) x) := by
        symm
        exact hdistA _ _
      _ < (1 / 2 : ℝ) ^ n := hN _ le_rfl
  have hEq : ((f^[N]) x) .|. n = (UFP f) .|. n := by
    simpa [eq_comm] using rest_equal_preserve_Suc hEqSucc
  exact (hn ((f^[N]) x) hEq) hiter

theorem cms_fixpoint_induction_imp {α β : Type _} [cms_rs α] [ms_rs β] [Inhabited α]
    {R : α → Prop} {x : α} {f : α → α} :
    ((∀ x y : α, distance x y = distance_rs x y) ∧
      (∀ x y : β, distance x y = distance_rs x y) ∧
      R x ∧ continuous_rs R ∧ constructive_rs f ∧ inductivefun R f) →
      hasUFP f ∧ R (UFP f) := by
  rintro ⟨hdistA, hdistB, hx, hcont, hconst, hind⟩
  exact cms_fixpoint_induction hdistA hdistB hx hcont hconst hind

theorem cms_fixpoint_induction_R {α β : Type _} [cms_rs α] [ms_rs β] [Inhabited α]
    {R : α → Prop} {x : α} {f : α → α} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      R x → continuous_rs R →
      constructive_rs f → inductivefun R f →
      R (UFP f) := by
  intro hdistA hdistB hx hcont hconst hind
  exact (cms_fixpoint_induction hdistA hdistB hx hcont hconst hind).2


/- ----------------------------------------------------------*
 |                                                          |
 |      !!!     order and restriction space     !!!         |
 |                                                          |
 *---------------------------------------------------------- -/

class ms_rs_order0 (α : Type _) extends ms_rs α, PartialOrder α

class ms_rs_order (α : Type _) extends ms_rs_order0 α where
  rs_order_iff :
    ∀ x y : α, (∀ n, x .|. n ≤ y .|. n) ↔ x ≤ y

class cms_rs_order (α : Type _) extends cms_rs α, ms_rs_order α

theorem not_rs_orderI {α : Type _} [ms_rs_order α] {x y : α} {n : Nat} :
    ¬ x .|. n ≤ y .|. n → ¬ x ≤ y := by
  intro hnot hle
  exact hnot ((ms_rs_order.rs_order_iff x y).2 hle n)

theorem rs_order_if {α : Type _} [ms_rs_order α] {x y : α} {n : Nat} :
    x ≤ y → x .|. n ≤ y .|. n := by
  intro hle
  exact (ms_rs_order.rs_order_iff x y).2 hle n

/- ----------------------------------------------------------*
 |                                                          |
 |       Fixed point induction for refinement (CMS)         |
 |                                                          |
 *---------------------------------------------------------- -/

/- (************************************************************
             continuity lemma for refinement
 ************************************************************)
-/

theorem continuous_rs_Ref_fun {α : Type _} [ms_rs_order α] {z : α} :
    continuous_rs (Ref_fun z) := by
  classical
  intro x hnot
  have hnotAll : ¬ ∀ n, z .|. n ≤ x .|. n := by
    intro hall
    exact hnot ((ms_rs_order.rs_order_iff z x).1 hall)
  push_neg at hnotAll
  rcases hnotAll with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro y hyEq hy
  apply hn
  simpa [hyEq] using (rs_order_if (x := z) (y := y) (n := n) hy)

/- (************************************************************
         continuity lemma for (Reverse) refinement
 ************************************************************)
-/

theorem continuous_rs_Rev_fun {α : Type _} [ms_rs_order α] {z : α} :
    continuous_rs (Rev_fun z) := by
  classical
  intro x hnot
  have hnotAll : ¬ ∀ n, x .|. n ≤ z .|. n := by
    intro hall
    exact hnot ((ms_rs_order.rs_order_iff x z).1 hall)
  push_neg at hnotAll
  rcases hnotAll with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro y hyEq hy
  have hle : y .|. n ≤ z .|. n := rs_order_if (x := y) (y := z) (n := n) hy
  exact hn (by simpa [hyEq] using hle)

/- (************************************************************
          Metric Fixed Point Induction for refinement
 ************************************************************)
-/

theorem cms_fixpoint_induction_ref {α β : Type _}
    [cms_rs_order α] [ms_rs β] [Inhabited α]
    {f : α → α} {X Y : α} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      constructive_rs f → mono f → X ≤ f X → Y = f Y →
      X ≤ Y := by
  intro hdistA hdistB hconst hmono hpre hfix
  have hInd : inductivefun (Ref_fun X) f := by
    intro x hx
    exact le_trans hpre (hmono hx)
  have hmain := cms_fixpoint_induction (α := α) (β := β) (R := Ref_fun X) (x := X) (f := f)
    hdistA hdistB le_rfl continuous_rs_Ref_fun hconst hInd
  have hEq : UFP f = Y := hasUFP_unique_solution hmain.1 (UFP_fp hmain.1) hfix.symm
  simpa [Ref_fun, hEq] using hmain.2

theorem cms_fixpoint_induction_rev {α β : Type _}
    [cms_rs_order α] [ms_rs β] [Inhabited α]
    {f : α → α} {X Y : α} :
    (∀ x y : α, distance x y = distance_rs x y) →
      (∀ x y : β, distance x y = distance_rs x y) →
      constructive_rs f → mono f → f X ≤ X → Y = f Y →
      Y ≤ X := by
  intro hdistA hdistB hconst hmono hpre hfix
  have hInd : inductivefun (Rev_fun X) f := by
    intro x hx
    exact le_trans (hmono hx) hpre
  have hmain := cms_fixpoint_induction (α := α) (β := β) (R := Rev_fun X) (x := X) (f := f)
    hdistA hdistB le_rfl continuous_rs_Rev_fun hconst hInd
  have hEq : UFP f = Y := hasUFP_unique_solution hmain.1 (UFP_fp hmain.1) hfix.symm
  simpa [Rev_fun, hEq] using hmain.2
