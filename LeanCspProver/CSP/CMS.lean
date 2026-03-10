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
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra

open Function

noncomputable section

/-
(*****************************************************************

         1. Metric space (MS)
         2. Complete metric space (CMS)
         3. Contracting map
         4. Banach Theorem

 *****************************************************************)
-/


/-
axclass ms0 < type
consts
  distance    :: "'a::ms0 * 'a::ms0 => real"  (* Distance function *)
-/

class ms0 (α : Type u) where
  distance : α → α → ℝ -- Distance function

export ms0 (distance)

/-
(**********************************************************
                    metric space (MS)
 **********************************************************)
-/

class ms (α : Type u) extends ms0 α where
  positive_ms :
    ∀ x y : α, 0 ≤ distance x y
  diagonal_ms :
    ∀ x y : α, (distance x y = 0) ↔ x = y
  symmetry_ms :
    ∀ x y : α, distance x y = distance y x
  triangle_inequality_ms :
    ∀ x y z : α, distance x z ≤ distance x y + distance y z

/-
(*------------------*
 | cauchy and limit |
 *------------------*)
-/

def cauchy {α : Type u} [ms α] (xs : infinite_seq α) : Prop :=
  ∀ delta : ℝ, 0 < delta → ∃ n, ∀ i j, (n ≤ i ∧ n ≤ j) → distance (xs i) (xs j) < delta

def convergeTo {α : Type u} [ms α] (xs : infinite_seq α) (x : α) : Prop :=
  ∀ eps : ℝ, 0 < eps → ∃ n, ∀ m, n ≤ m → distance x (xs m) < eps

infix:55 " convergeTo " => convergeTo

/-
(*definition
  hasLimit   :: "'a::ms infinite_seq => bool"
  ...
*)
-/

noncomputable def Limit {α : Type u} [ms α] [Inhabited α] (xs : infinite_seq α) : α :=
  THE fun x => xs convergeTo x

/-
(*---------*
 | mapping |
 *---------*)
-/

def map_alpha {α : Type u} {β : Type v} [ms α] [ms β] (f : α → β) (alpha : ℝ) : Prop :=
  0 ≤ alpha ∧ ∀ x y, distance (f x) (f y) ≤ alpha * distance x y

def non_expanding {α : Type u} {β : Type v} [ms α] [ms β] (f : α → β) : Prop :=
  map_alpha f 1

def contraction_alpha {α : Type u} {β : Type v} [ms α] [ms β] (f : α → β) (alpha : ℝ) :
    Prop :=
  alpha < 1 ∧ map_alpha f alpha

def contraction {α : Type u} {β : Type v} [ms α] [ms β] (f : α → β) : Prop :=
  ∃ alpha : ℝ, contraction_alpha f alpha


/-
(**********************************************************
                     small lemmas
 **********************************************************)
-/

@[simp]
theorem same_pnt_zero {α : Type u} [ms α] (x : α) : distance x x = 0 := by
  exact (ms.diagonal_ms x x).2 rfl

theorem diff_pnt_pos_only_if {α : Type u} [ms α] {x y : α} :
    0 < distance x y → x ≠ y := by
  intro hxy hEq
  subst hEq
  simpa using hxy

theorem diff_pnt_pos_if {α : Type u} [ms α] {x y : α} :
    x ≠ y → 0 < distance x y := by
  intro hxy
  have hnonneg : 0 ≤ distance x y := ms.positive_ms x y
  have hne : distance x y ≠ 0 := by
    intro hzero
    exact hxy ((ms.diagonal_ms x y).1 hzero)
  rcases lt_or_eq_of_le hnonneg with hlt | heq
  · exact hlt
  · exact False.elim (hne heq.symm)

theorem diff_pnt_pos {α : Type u} [ms α] {x y : α} :
    (0 < distance x y) ↔ x ≠ y := by
  constructor
  · exact diff_pnt_pos_only_if
  · exact diff_pnt_pos_if

/-
(**********************************************************
                         map
 **********************************************************)
-/

/-(*** contraction_alpha ***)-/

theorem contraction_alpha_range {α : Type u} {β : Type v} [ms α] [ms β]
    {f : α → β} {alpha : ℝ} :
    contraction_alpha f alpha → 0 ≤ alpha ∧ alpha < 1 := by
  intro h
  exact ⟨h.2.1, h.1⟩

/-(*** contraction --> non expanding ***)-/

theorem contraction_non_expanding {α : Type u} {β : Type v} [ms α] [ms β]
    {f : α → β} :
    contraction f → non_expanding f := by
  intro h
  rcases h with ⟨alpha, halphaLt, halphaNonneg, hmap⟩
  refine ⟨by norm_num, ?_⟩
  intro x y
  have hxy := hmap x y
  have hdist : 0 ≤ distance x y := ms.positive_ms x y
  nlinarith

/-(*** composition ***)-/
-- map_alpha

theorem compo_map_alpha {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β}
    {alpha1 alpha2 : ℝ} :
    map_alpha f alpha1 → map_alpha g alpha2 → map_alpha (f ∘ g) (alpha1 * alpha2) := by
  intro hf hg
  rcases hf with ⟨hα1, hf⟩
  rcases hg with ⟨hα2, hg⟩
  refine ⟨mul_nonneg hα1 hα2, ?_⟩
  intro x y
  have hf' := hf (g x) (g y)
  have hg' := hg x y
  have hmul := mul_le_mul_of_nonneg_left hg' hα1
  exact le_trans hf' (by simpa [mul_assoc] using hmul)

theorem compo_contra_alpha {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β}
    {alpha1 alpha2 : ℝ} :
    contraction_alpha f alpha1 → contraction_alpha g alpha2 →
      contraction_alpha (f ∘ g) (alpha1 * alpha2) := by
  intro hf hg
  rcases hf with ⟨hα1lt, hmf⟩
  rcases hg with ⟨hα2lt, hmg⟩
  have hα1 : 0 ≤ alpha1 := hmf.1
  have hα2 : 0 ≤ alpha2 := hmg.1
  refine ⟨by nlinarith, compo_map_alpha hmf hmg⟩

theorem compo_non_expand_map_alpha {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β} {alpha : ℝ} :
    non_expanding f → map_alpha g alpha → map_alpha (f ∘ g) alpha := by
  intro hf hg
  simpa [non_expanding, one_mul] using
    (compo_map_alpha (f := f) (g := g) (alpha1 := 1) (alpha2 := alpha) hf hg)

theorem compo_map_alpha_non_expand {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β} {alpha : ℝ} :
    map_alpha f alpha → non_expanding g → map_alpha (f ∘ g) alpha := by
  intro hf hg
  simpa [non_expanding, mul_one] using
    (compo_map_alpha (f := f) (g := g) (alpha1 := alpha) (alpha2 := 1) hf hg)

theorem compo_non_expand_contra_alpha {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β} {alpha : ℝ} :
    non_expanding f → contraction_alpha g alpha → contraction_alpha (f ∘ g) alpha := by
  intro hf hg
  exact ⟨hg.1, compo_non_expand_map_alpha hf hg.2⟩

theorem compo_contra_alpha_non_expand {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β} {alpha : ℝ} :
    contraction_alpha f alpha → non_expanding g → contraction_alpha (f ∘ g) alpha := by
  intro hf hg
  exact ⟨hf.1, compo_map_alpha_non_expand hf.2 hg⟩

theorem compo_non_expand {α : Type u} {β : Type v} {γ : Type w}
    [ms α] [ms β] [ms γ] {f : β → γ} {g : α → β} :
    non_expanding f → non_expanding g → non_expanding (f ∘ g) := by
  intro hf hg
  simpa [non_expanding] using
    (compo_map_alpha (f := f) (g := g) (alpha1 := 1) (alpha2 := 1) hf hg)

/-
(**********************************************************
                     convergeTo
 **********************************************************)
-/

/-(*** The limit is unique ***)-/

theorem unique_convergence {α : Type u} [ms α] {xs : infinite_seq α} {x y : α} :
    xs convergeTo x → xs convergeTo y → x = y := by
  intro hx hy
  by_contra hxy
  have hdist : 0 < distance x y := diff_pnt_pos_if hxy
  obtain ⟨n, hn⟩ := hx (distance x y / 2) (by linarith)
  obtain ⟨m, hm⟩ := hy (distance x y / 2) (by linarith)
  let k := max n m
  have hxn : distance x (xs k) < distance x y / 2 := hn k (le_max_left _ _)
  have hyn : distance y (xs k) < distance x y / 2 := hm k (le_max_right _ _)
  have hyk : distance (xs k) y < distance x y / 2 := by
    simpa [ms.symmetry_ms] using hyn
  have htri := ms.triangle_inequality_ms x (xs k) y
  nlinarith

/-(*** Convergence implies cauchy seq***)-/

theorem convergece_cauchy {α : Type u} [ms α] {xs : infinite_seq α} {x : α} :
    xs convergeTo x → cauchy xs := by
  intro hx
  intro delta hdelta
  obtain ⟨n, hn⟩ := hx (delta / 2) (by linarith)
  refine ⟨n, ?_⟩
  intro i j hij
  have hni : n ≤ i := hij.1
  have hnj : n ≤ j := hij.2
  have hix : distance x (xs i) < delta / 2 := hn i hni
  have hxy : distance (xs i) x < delta / 2 := by
    simpa [ms.symmetry_ms] using hix
  have hxj : distance x (xs j) < delta / 2 := hn j hnj
  have htri := ms.triangle_inequality_ms (xs i) x (xs j)
  nlinarith

/-
(**********************************************************
                Complete metric space (CMS)
 **********************************************************)
-/

class cms (α : Type u) extends ms α where
  complete_ms : ∀ xs : infinite_seq α, cauchy xs → ∃ x, xs convergeTo x

/-
(**********************************************************
                     CMS lemmas
 **********************************************************)
-/

theorem convergeTo_to_Limit {α : Type u} [cms α] [Inhabited α]
    {xs : infinite_seq α} {x : α} :
    cauchy xs → ((xs convergeTo x) ↔ x = Limit xs) := by
  intro hxs
  constructor
  · intro hx
    have hLimit : Limit xs = x := by
      unfold Limit
      exact chooseOrDefault_eq hx (fun y hy => unique_convergence hy hx)
    exact hLimit.symm
  · intro hx
    rcases cms.complete_ms xs hxs with ⟨y, hy⟩
    have hLimit : Limit xs = y := by
      unfold Limit
      exact chooseOrDefault_eq hy (fun z hz => unique_convergence hz hy)
    have hxy : x = y := by simpa [hLimit] using hx
    simpa [hxy] using hy

theorem Limit_to_convergeTo {α : Type u} [cms α] [Inhabited α]
    {xs : infinite_seq α} {x : α} :
    cauchy xs → (x = Limit xs ↔ xs convergeTo x) := by
  intro hxs
  exact (convergeTo_to_Limit (xs := xs) (x := x) hxs).symm

theorem Limit_to_convergeTo_sym {α : Type u} [cms α] [Inhabited α]
    {xs : infinite_seq α} {x : α} :
    cauchy xs → (Limit xs = x ↔ xs convergeTo x) := by
  intro hxs
  simpa [eq_comm] using (Limit_to_convergeTo (xs := xs) (x := x) hxs)

theorem Limit_iff {α : Type u} [cms α] [Inhabited α] {xs : infinite_seq α} {x : α}
    (hxs : cauchy xs) : (x = Limit xs ↔ xs convergeTo x) ∧ (Limit xs = x ↔ xs convergeTo x) :=
  ⟨Limit_to_convergeTo (xs := xs) (x := x) hxs,
    Limit_to_convergeTo_sym (xs := xs) (x := x) hxs⟩

theorem Limit_is {α : Type u} [cms α] [Inhabited α] {xs : infinite_seq α} :
    cauchy xs → xs convergeTo Limit xs := by
  intro hxs
  exact (convergeTo_to_Limit (xs := xs) (x := Limit xs) hxs).2 rfl

/-
(**********************************************************
                     Banach Theory
 **********************************************************)
-/

/-(*** step 1 (cauchy) ***)-/

theorem Banach_lm_contraction {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    ∀ n, distance (xs n) (f (xs n)) ≤ alpha ^ n * distance (xs 0) (f (xs 0)) := by
  intro hcontr hxs
  rcases hcontr with ⟨hAlphaLt, hAlphaNonneg, hmap⟩
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hs : xs (Nat.succ n) = f (xs n) := hxs n
      have hmap' := hmap (xs n) (f (xs n))
      have hmul := mul_le_mul_of_nonneg_left ih hAlphaNonneg
      calc
        distance (xs (Nat.succ n)) (f (xs (Nat.succ n)))
            = distance (f (xs n)) (f (f (xs n))) := by simp [hs]
        _ ≤ alpha * distance (xs n) (f (xs n)) := hmap'
        _ ≤ alpha * (alpha ^ n * distance (xs 0) (f (xs 0))) := hmul
        _ = alpha ^ (Nat.succ n) * distance (xs 0) (f (xs 0)) := by
          rw [pow_succ]
          ring

theorem Banach_lm_triangle {α : Type u} [cms α] {xs : infinite_seq α} :
    ∀ n r, distance (xs r) (xs (r + n)) ≤
      prog_sum0 n (fun m => distance (xs (r + m - 1)) (xs (r + m))) := by
  intro n
  induction n with
  | zero =>
      intro r
      simp [prog_sum0]
  | succ n ih =>
      intro r
      have htri := ms.triangle_inequality_ms (xs r) (xs (r + n)) (xs (Nat.succ (r + n)))
      have ih' := ih r
      calc
        distance (xs r) (xs (r + Nat.succ n))
            = distance (xs r) (xs (Nat.succ (r + n))) := by simp [Nat.add_assoc]
        _ ≤ distance (xs r) (xs (r + n)) + distance (xs (r + n)) (xs (Nat.succ (r + n))) := by
          simpa [Nat.add_assoc] using htri
        _ ≤ prog_sum0 n (fun m => distance (xs (r + m - 1)) (xs (r + m))) +
              distance (xs (r + n)) (xs (Nat.succ (r + n))) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right ih' (distance (xs (r + n)) (xs (Nat.succ (r + n))))
        _ = prog_sum0 (Nat.succ n) (fun m => distance (xs (r + m - 1)) (xs (r + m))) := by
          simp [prog_sum0, Nat.add_assoc]

theorem Banach_lm_geo_prog_sum {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    ∀ n r,
      prog_sum0 n (fun m => distance (xs (r + m - 1)) (xs (r + m))) ≤
        prog_sum r (r + n) (geo_prop (distance (xs 0) (xs 1)) alpha) := by
  intro hcontr hxs
  intro n
  induction n with
  | zero =>
      intro r
      simp [prog_sum, prog_sum0]
  | succ n ih =>
      intro r
      have ih' := ih r
      have hcontr' := Banach_lm_contraction (f := f) (alpha := alpha) (xs := xs) hcontr hxs (r + n)
      have hrec : xs (r + Nat.succ n) = f (xs (r + n)) := by
        simpa [Nat.add_assoc] using hxs (r + n)
      have hstep :
          distance (xs (r + n)) (xs (r + Nat.succ n)) ≤
            geo_prop (distance (xs 0) (xs 1)) alpha (r + Nat.succ n) := by
        calc
          distance (xs (r + n)) (xs (r + Nat.succ n))
              = distance (xs (r + n)) (f (xs (r + n))) := by rw [hrec]
          _ ≤ alpha ^ (r + n) * distance (xs 0) (f (xs 0)) := hcontr'
          _ = geo_prop (distance (xs 0) (xs 1)) alpha (r + Nat.succ n) := by
            simp [geo_prop, hxs 0, Nat.add_assoc]
      calc
        prog_sum0 (Nat.succ n) (fun m => distance (xs (r + m - 1)) (xs (r + m)))
            = prog_sum0 n (fun m => distance (xs (r + m - 1)) (xs (r + m))) +
                distance (xs (r + n)) (xs (r + Nat.succ n)) := by
                  simp [prog_sum0, Nat.add_assoc]
        _ ≤ prog_sum r (r + n) (geo_prop (distance (xs 0) (xs 1)) alpha) +
              geo_prop (distance (xs 0) (xs 1)) alpha (r + Nat.succ n) := by
          exact add_le_add ih' hstep
        _ = prog_sum r (r + Nat.succ n) (geo_prop (distance (xs 0) (xs 1)) alpha) := by
          simp [prog_sum, prog_sum0, Nat.add_assoc, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm]

theorem Banach_lm_ineq {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    ∀ r n,
      distance (xs r) (xs (r + n)) ≤ distance (xs 0) (f (xs 0)) * alpha ^ r / (1 - alpha) := by
  intro hcontr hxs r n
  rcases contraction_alpha_range (f := f) (alpha := alpha) hcontr with ⟨hAlphaNonneg, hAlphaLt⟩
  have h0 : 0 ≤ distance (xs 0) (xs 1) := ms.positive_ms (xs 0) (xs 1)
  have htri := Banach_lm_triangle (xs := xs) n r
  have hgeo := Banach_lm_geo_prog_sum (f := f) (alpha := alpha) (xs := xs) hcontr hxs n r
  have hinf := geo_prog_sum_infinite_div (m := r) (n := r + n)
    (K := distance (xs 0) (xs 1)) (alpha := alpha) h0 hAlphaNonneg hAlphaLt
  calc
    distance (xs r) (xs (r + n))
        ≤ prog_sum0 n (fun m => distance (xs (r + m - 1)) (xs (r + m))) := htri
    _ ≤ prog_sum r (r + n) (geo_prop (distance (xs 0) (xs 1)) alpha) := hgeo
    _ ≤ distance (xs 0) (xs 1) * alpha ^ r / (1 - alpha) := hinf
    _ = distance (xs 0) (f (xs 0)) * alpha ^ r / (1 - alpha) := by
      simp [hxs 0]

theorem Banach_lm_cauchy_lm_pos_distance {α : Type u} [cms α]
    {f : α → α} {alpha delta : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    0 < delta →
    0 < distance (xs 0) (f (xs 0)) →
    ∃ n, ∀ m, distance (xs n) (xs (n + m)) < delta := by
  intro hcontr hxs hdelta hdist0
  rcases contraction_alpha_range (f := f) (alpha := alpha) hcontr with ⟨hAlphaNonneg, hAlphaLt⟩
  have hDen : 0 < 1 - alpha := by linarith
  have hTarget : 0 < delta * (1 - alpha) / distance (xs 0) (f (xs 0)) := by
    exact div_pos (mul_pos hdelta hDen) hdist0
  obtain ⟨n, hn⟩ := pow_convergence hAlphaNonneg hAlphaLt hTarget
  refine ⟨n, ?_⟩
  intro m
  have hineq := Banach_lm_ineq (f := f) (alpha := alpha) (xs := xs) hcontr hxs n m
  have hpowNonneg : 0 ≤ alpha ^ n := pow_nonneg hAlphaNonneg n
  have hbound :
      distance (xs 0) (f (xs 0)) * alpha ^ n / (1 - alpha) < delta := by
    exact real_mult_div_commuteI hpowNonneg hdelta hDen hdist0 hn
  exact lt_of_le_of_lt hineq hbound

theorem Banach_lm_cauchy_lm_zero_distance {α : Type u} [cms α]
    {f : α → α} {alpha delta : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    0 < delta →
    distance (xs 0) (f (xs 0)) = 0 →
    ∃ n, ∀ m, distance (xs n) (xs (n + m)) < delta := by
  intro hcontr hxs hdelta hzero
  refine ⟨0, ?_⟩
  intro m
  have hineq := Banach_lm_ineq (f := f) (alpha := alpha) (xs := xs) hcontr hxs 0 m
  have hnonneg : 0 ≤ distance (xs 0) (xs m) := ms.positive_ms (xs 0) (xs m)
  have hle : distance (xs 0) (xs m) ≤ 0 := by simpa [hzero] using hineq
  have hdist : distance (xs 0) (xs m) = 0 := le_antisymm hle hnonneg
  simpa [hdist] using hdelta

theorem Banach_lm_cauchy_lm {α : Type u} [cms α]
    {f : α → α} {alpha delta : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    0 < delta →
    ∃ n, ∀ m, distance (xs n) (xs (n + m)) < delta := by
  intro hcontr hxs hdelta
  by_cases hdist : 0 < distance (xs 0) (f (xs 0))
  · exact Banach_lm_cauchy_lm_pos_distance hcontr hxs hdelta hdist
  · have hnonneg : 0 ≤ distance (xs 0) (f (xs 0)) := ms.positive_ms (xs 0) (f (xs 0))
    have hzero : distance (xs 0) (f (xs 0)) = 0 := by linarith
    exact Banach_lm_cauchy_lm_zero_distance hcontr hxs hdelta hzero

theorem Banach_lm_cauchy {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    cauchy xs := by
  intro hcontr hxs
  intro delta hdelta
  obtain ⟨n, hn⟩ := Banach_lm_cauchy_lm (f := f) (alpha := alpha) (xs := xs) (delta := delta / 2)
    hcontr hxs (by linarith)
  refine ⟨n, ?_⟩
  intro i j hij
  have hni : n ≤ i := hij.1
  have hnj : n ≤ j := hij.2
  have hi : distance (xs n) (xs (n + (i - n))) < delta / 2 := hn (i - n)
  have hj : distance (xs n) (xs (n + (j - n))) < delta / 2 := hn (j - n)
  have hi' : distance (xs i) (xs n) < delta / 2 := by
    simpa [Nat.add_sub_of_le hni, ms.symmetry_ms] using hi
  have hj' : distance (xs n) (xs j) < delta / 2 := by
    simpa [Nat.add_sub_of_le hnj] using hj
  have htri := ms.triangle_inequality_ms (xs i) (xs n) (xs j)
  nlinarith

/-(*** step 2 (converge to a fixpoint) ***)-/

theorem Banach_lm_converge {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    ∃ x, xs convergeTo x := by
  intro hcontr hxs
  exact cms.complete_ms xs (Banach_lm_cauchy hcontr hxs)

theorem Banach_lm_fixpoint_lm {α : Type u} [cms α]
    {f : α → α} {alpha eps : ℝ} {xs : infinite_seq α} {y : α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    xs convergeTo y →
    0 < eps →
    distance y (f y) < eps := by
  intro hcontr hxs hy heps
  rcases hcontr with ⟨hAlphaLt, hAlphaNonneg, hmap⟩
  obtain ⟨n, hn⟩ := hy (eps / 2) (by linarith)
  have hyn : distance y (xs n) < eps / 2 := hn n le_rfl
  have hys : distance y (xs (Nat.succ n)) < eps / 2 := hn (Nat.succ n) (Nat.le_succ _)
  have hmap' := hmap (xs n) y
  have hxy : distance (xs n) y < eps / 2 := by
    simpa [ms.symmetry_ms] using hyn
  have hcontract :
      distance (xs (Nat.succ n)) (f y) ≤ distance (xs n) y := by
    calc
      distance (xs (Nat.succ n)) (f y)
          = distance (f (xs n)) (f y) := by simp [hxs n]
      _ ≤ alpha * distance (xs n) y := hmap'
      _ ≤ distance (xs n) y := by nlinarith [ms.positive_ms (xs n) y, hAlphaNonneg, hAlphaLt]
  have htri := ms.triangle_inequality_ms y (xs (Nat.succ n)) (f y)
  nlinarith

theorem Banach_lm_fixpoint {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} {y : α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    xs convergeTo y →
    y = f y := by
  intro hcontr hxs hy
  by_contra hneq
  have hdist : 0 < distance y (f y) := diff_pnt_pos_if hneq
  have hlt := Banach_lm_fixpoint_lm (f := f) (alpha := alpha) (xs := xs) (y := y)
    hcontr hxs hy hdist
  exact (lt_irrefl (distance y (f y))) hlt

/-(*** step 3 (unique fixpoint) ***)-/

theorem Banach_lm_unique_lm {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} {y z : α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    y = f y →
    z = f z →
    distance y z ≤ alpha * distance y z := by
  intro hcontr _ hy hz
  rcases hcontr with ⟨_, _, hmap⟩
  have hy' : f y = y := hy.symm
  have hz' : f z = z := hz.symm
  simpa [hy', hz'] using hmap y z

theorem Banach_lm_unique {α : Type u} [cms α]
    {f : α → α} {alpha : ℝ} {xs : infinite_seq α} {y z : α} :
    contraction_alpha f alpha →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    y = f y →
    z = f z →
    y = z := by
  intro hcontr hxs hy hz
  by_contra hne
  have hdist : 0 < distance y z := diff_pnt_pos_if hne
  have hle := Banach_lm_unique_lm (f := f) (alpha := alpha) (xs := xs) (y := y) (z := z)
    hcontr hxs hy hz
  have hAlphaLt : alpha < 1 := hcontr.1
  nlinarith

/-(*** final step (Banach Theory) ***)-/

/- ------------------*
 |     Banach lm    |
 *------------------ -/

theorem Banach_thm_xs {α : Type u} [cms α]
    {f : α → α} {xs : infinite_seq α} :
    contraction f →
    (∀ i, xs (Nat.succ i) = f (xs i)) →
    ∃ y, xs convergeTo y ∧ isUFP y f := by
  intro hcontr hxs
  rcases hcontr with ⟨alpha, hAlpha⟩
  rcases Banach_lm_converge (f := f) (alpha := alpha) (xs := xs) hAlpha hxs with ⟨y, hy⟩
  refine ⟨y, hy, ?_⟩
  constructor
  · exact Banach_lm_fixpoint (f := f) (alpha := alpha) (xs := xs) (y := y) hAlpha hxs hy
  · intro z hz
    exact Banach_lm_unique (f := f) (alpha := alpha) (xs := xs) (y := y) (z := z)
      hAlpha hxs (Banach_lm_fixpoint (f := f) (alpha := alpha) (xs := xs) (y := y) hAlpha hxs hy) hz

/- -------------------*
 |      Banach       |
 *------------------- -/

theorem Banach_thm {α : Type u} [cms α] [Inhabited α] {f : α → α} {x0 : α} :
    contraction f →
      hasUFP f ∧ (fun n => (f^[n]) x0) convergeTo UFP f := by
  intro hcontr
  let xs : infinite_seq α := fun n => (f^[n]) x0
  have hstep : ∀ i, xs (Nat.succ i) = f (xs i) := by
    intro i
    simp [xs, Function.iterate_succ_apply']
  rcases Banach_thm_xs (f := f) (xs := xs) hcontr hstep with ⟨y, hyconv, hyufp⟩
  have hHas : hasUFP f := ⟨y, hyufp⟩
  refine ⟨hHas, ?_⟩
  have hEq : y = UFP f := UFP_unique hyufp (UFP_is hHas)
  simpa [xs, hEq] using hyconv

/- ------------------*
 | Banach existency |
 *------------------ -/

theorem Banach_thm_EX {α : Type u} [cms α] [Inhabited α] {f : α → α} :
    contraction f → hasUFP f := by
  intro h
  exact (Banach_thm (f := f) (x0 := default) h).1
