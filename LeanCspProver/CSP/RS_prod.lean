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
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_fun
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

         1. Productions of RS are also RS.
         2.
         3.
         4.

 *****************************************************************)
-/

/- (**********************************************************
              def: prod of restriction space
 **********************************************************) -/

instance instRs0Fun {ι : Type _} {α : Type _} [rs α] : rs0 (ι → α) where
  restriction xp n := fun i => xp i .|. n

@[simp]
theorem prod_restriction_def {ι : Type _} {α : Type _} [rs α] {xp : ι → α} {n : Nat} :
    xp .|. n = fun i => xp i .|. n :=
  rfl

def prod_Limit {ι : Type _} {α : Type _} [ms_rs α] [Inhabited α]
    (xps : infinite_seq (ι → α)) : ι → α :=
  fun i => Limit (proj_fun i ∘ xps)

@[simp]
theorem prod_Limit_def {ι : Type _} {α : Type _} [ms_rs α] [Inhabited α]
    {xps : infinite_seq (ι → α)} :
    prod_Limit xps = fun i => Limit (proj_fun i ∘ xps) :=
  rfl

/- (************************************************************
                           Basics
 ************************************************************) -/

theorem rest_to_prod_rest {ι : Type _} {α : Type _} [rs α] {xp yp : ι → α} {n : Nat} :
    (∀ i, xp i .|. n = yp i .|. n) → xp .|. n = yp .|. n := by
  intro h
  funext i
  exact h i

/- (************************************************************
                     Product RS ==> RS
 ************************************************************) -/

/- (*** prod_zero_eq_rs ***) -/

theorem prod_zero_eq_rs {ι : Type _} {α : Type _} [rs α] (xp yp : ι → α) :
    xp .|. 0 = yp .|. 0 := by
  funext i
  exact rs.zero_eq_rs _ _

/- (*** prod_min_rs ***) -/

theorem prod_min_rs {ι : Type _} {α : Type _} [rs α] (xp : ι → α) (m n : Nat) :
    (xp .|. m) .|. n = xp .|. (min m n) := by
  funext i
  simp [prod_restriction_def, rs.min_rs]

/- (*** prod_diff_rs ***) -/

theorem prod_diff_rs {ι : Type _} {α : Type _} [rs α] {xp yp : ι → α} :
    xp ≠ yp → ∃ n, xp .|. n ≠ yp .|. n := by
  intro hneq
  by_contra h
  apply hneq
  funext i
  apply contra_diff_rs
  intro n
  have hEq : xp .|. n = yp .|. n := by
    by_contra hEq
    exact h ⟨n, hEq⟩
  simpa [prod_restriction_def] using congrArg (fun f => f i) hEq

/- (*****************************
       Prod RS => RS
 *****************************) -/

instance instRsFun {ι : Type _} {α : Type _} [rs α] : rs (ι → α) where
  zero_eq_rs := prod_zero_eq_rs
  min_rs := prod_min_rs
  diff_rs := by
    intro x y
    exact prod_diff_rs (xp := x) (yp := y)

/- (************************************************************
                   Product RS ==> MS
 ************************************************************) -/

instance instMs0Fun {ι : Type _} {α : Type _} [rs α] : ms0 (ι → α) where
  distance := distance_rs

@[simp]
theorem prod_distance_def {ι : Type _} {α : Type _} [rs α] {xp yp : ι → α} :
    distance xp yp = distance_rs xp yp :=
  rfl

instance instMsFun {ι : Type _} {α : Type _} [rs α] : ms (ι → α) where
  positive_ms := by
    intro x y
    simpa [prod_distance_def] using positive_rs x y
  diagonal_ms := by
    intro x y
    simpa [prod_distance_def] using (diagonal_rs (x := x) (y := y))
  symmetry_ms := by
    intro x y
    simpa [prod_distance_def] using symmetry_rs x y
  triangle_inequality_ms := by
    intro x y z
    simpa [prod_distance_def] using triangle_inequality_rs x y z

/- (************************************************************
             i.e.  Product RS ==> MS & RS
 ************************************************************) -/

instance instMs0RsFun {ι : Type _} {α : Type _} [rs α] : ms0_rs (ι → α) where
  to_distance_rs := by
    intro x y
    rfl

instance instMsRsFun {ι : Type _} {α : Type _} [rs α] : ms_rs (ι → α) where

/- (************************************************************
                    distance
 ************************************************************) -/

theorem prod_distance_nat_le {ι : Type _} {α : Type _} [rs α]
    {xp yp : ι → α} {i : ι} :
    xp i ≠ yp i →
      distance_nat xp yp <= distance_nat (xp i) (yp i) := by
  intro hxy
  have hfun : xp ≠ yp := fun hEq => hxy (congrArg (fun f => f i) hEq)
  have hEqFun : xp .|. distance_nat xp yp = yp .|. distance_nat xp yp :=
    distance_nat_rest (x := xp) (y := yp) hfun rfl
  have hEqI : xp i .|. distance_nat xp yp = yp i .|. distance_nat xp yp := by
    simpa [prod_restriction_def] using congrArg (fun f => f i) hEqFun
  exact distance_nat_le_1_only_if (x := xp i) (y := yp i) hxy hEqI

theorem prod_distance_def_le {ι : Type _} {α : Type _} [ms0_rs α]
    {xp yp : ι → α} {i : ι} :
    distance (xp i) (yp i) <= distance xp yp := by
  calc
    distance (xp i) (yp i) = distance_rs (xp i) (yp i) := by
      exact ms0_rs.to_distance_rs _ _
    _ <= distance_rs xp yp := by
      exact rest_distance_subset (x := xp) (y := yp) (X := xp i) (Y := yp i)
        (fun n hEq => by simpa [prod_restriction_def] using congrArg (fun f => f i) hEq)
    _ = distance xp yp := by
      symm
      exact ms0_rs.to_distance_rs _ _

/- (*** prod_distance (Upper Bound) ***) -/

theorem prod_distance_UB {ι : Type _} [Nonempty ι] {α : Type _} [ms0_rs α]
    {xp yp : ι → α} :
    isUB (distance xp yp) {u | ∃ i, u = distance (xp i) (yp i)} := by
  intro u hu
  rcases hu with ⟨i, rfl⟩
  exact prod_distance_def_le (xp := xp) (yp := yp) (i := i)

/- (*** prod_distance (Least) ***) -/

theorem prod_distance_least {ι : Type _} [Nonempty ι] {α : Type _} [ms0_rs α]
    {xp yp : ι → α} {u : ℝ} :
    (∀ i, distance (xp i) (yp i) <= u) →
      distance xp yp <= u := by
  intro hdist
  by_cases hxy : xp = yp
  · subst hxy
    let i0 : ι := Classical.choice ‹Nonempty ι›
    have hi0 : distance (xp i0) (xp i0) <= u := hdist i0
    have hzero : distance (xp i0) (xp i0) = 0 := by
      rw [ms0_rs.to_distance_rs]
      simpa using distance_rs_zero (xp i0)
    have hnonneg : 0 <= u := by
      nlinarith [hi0, hzero]
    rw [same_pnt_zero]
    exact hnonneg
  · by_contra hnot
    have hEqSucc : xp .|. Nat.succ (distance_nat xp yp) = yp .|. Nat.succ (distance_nat xp yp) := by
      apply rest_to_prod_rest
      intro i
      by_cases hi : xp i = yp i
      · simpa [hi]
      · have hiu : distance (xp i) (yp i) <= u := hdist i
        have hlt : distance (xp i) (yp i) < distance xp yp := by
          exact lt_of_le_of_lt hiu (lt_of_not_ge hnot)
        have hlt' : distance_rs (xp i) (yp i) < (1 / 2 : ℝ) ^ distance_nat xp yp := by
          calc
            distance_rs (xp i) (yp i) = distance (xp i) (yp i) := by
              symm
              exact ms0_rs.to_distance_rs _ _
            _ < distance xp yp := hlt
            _ = distance_rs xp yp := by
              exact (ms0_rs.to_distance_rs _ _).symm
            _ = (1 / 2 : ℝ) ^ distance_nat xp yp := distance_iff1 (x := xp) (y := yp) hxy
        exact distance_rs_less_1_if hlt'
    have hltSelf : distance xp yp < (1 / 2 : ℝ) ^ distance_nat xp yp := by
      calc
        distance xp yp = distance_rs xp yp := ms0_rs.to_distance_rs _ _
        _ < (1 / 2 : ℝ) ^ distance_nat xp yp := distance_rs_less_1_only_if hEqSucc
    have hEqDist : distance xp yp = (1 / 2 : ℝ) ^ distance_nat xp yp := by
      calc
        distance xp yp = distance_rs xp yp := ms0_rs.to_distance_rs _ _
        _ = (1 / 2 : ℝ) ^ distance_nat xp yp := distance_iff1 (x := xp) (y := yp) hxy
    exact lt_irrefl _ (hEqDist ▸ hltSelf)

/- (*** prod_distance (Least Upper Bound) ***) -/

theorem prod_distance {ι : Type _} [Nonempty ι] {α : Type _} [ms0_rs α]
    {xp yp : ι → α} :
    isLUB (distance xp yp) {u | ∃ i, u = distance (xp i) (yp i)} := by
  constructor
  · exact prod_distance_UB (xp := xp) (yp := yp)
  · intro u hu
    apply prod_distance_least (xp := xp) (yp := yp)
    intro i
    exact hu _ ⟨i, rfl⟩

theorem ALL_prod_distance {ι : Type _} [Nonempty ι] {α : Type _} [ms0_rs α] :
    ∀ xp yp : ι → α,
      isLUB (distance xp yp) {u | ∃ i, u = distance (xp i) (yp i)} :=
  fun _ _ => prod_distance

/- (*************************************************************
                        product maps
 *************************************************************) -/

/- (*** proj_fun ***) -/

theorem proj_non_expand {ι : Type _} {α : Type _} [ms_rs α] (i : ι) :
    non_expanding (proj_fun i : (ι → α) → α) := by
  constructor
  · norm_num
  · intro x y
    simpa [proj_fun] using (prod_distance_def_le (xp := x) (yp := y) (i := i))

/- ---------------------*
 |    non_expanding    |
 *--------------------- -/

/- only_if -/

theorem prod_non_expand_only_if {ι : Type _} {α β : Type _} [ms_rs α] [ms_rs β]
    {fp : α → ι → β} :
    non_expanding fp →
      ∀ i, non_expanding (proj_fun i ∘ fp) := by
  intro h
  exact fun i => compo_non_expand (proj_non_expand i) h

/- if -/

theorem prod_non_expand_if {ι : Type _} [Nonempty ι] {α β : Type _} [ms_rs α] [ms_rs β]
    {fp : α → ι → β} :
    (∀ i, non_expanding (proj_fun i ∘ fp)) →
      non_expanding fp := by
  intro h
  constructor
  · norm_num
  · intro x y
    apply prod_distance_least (xp := fp x) (yp := fp y)
    intro i
    simpa [non_expanding, proj_fun, Function.comp] using (h i).2 x y

/- iff -/

theorem prod_non_expand {ι : Type _} [Nonempty ι] {α β : Type _} [ms_rs α] [ms_rs β]
    {fp : α → ι → β} :
    non_expanding fp =
      (∀ i, non_expanding (proj_fun i ∘ fp)) := by
  apply propext
  constructor
  · exact prod_non_expand_only_if
  · exact prod_non_expand_if

/- ---------------------*
 |  alpha_contraction  |
 *--------------------- -/

/- only_if -/

theorem prod_contra_alpha_only_if {ι : Type _} {α β : Type _} [ms_rs α] [ms_rs β]
    {fp : α → ι → β} {alpha : ℝ} :
    contraction_alpha fp alpha →
      ∀ i, contraction_alpha (proj_fun i ∘ fp) alpha := by
  intro h
  exact fun i => compo_non_expand_contra_alpha (proj_non_expand i) h

/- if -/

theorem prod_contra_alpha_if {ι : Type _} [Nonempty ι] {α β : Type _} [ms_rs α] [ms_rs β]
    {fp : α → ι → β} {alpha : ℝ} :
    (∀ i, contraction_alpha (proj_fun i ∘ fp) alpha) →
      contraction_alpha fp alpha := by
  intro h
  let i0 : ι := Classical.choice ‹Nonempty ι›
  refine ⟨(h i0).1, ?_⟩
  refine ⟨(h i0).2.1, ?_⟩
  intro x y
  apply prod_distance_least (xp := fp x) (yp := fp y)
  intro i
  simpa [contraction_alpha, proj_fun, Function.comp] using (h i).2.2 x y

/- iff -/

theorem prod_contra_alpha {ι : Type _} [Nonempty ι] {α β : Type _} [ms_rs α] [ms_rs β]
    {fp : α → ι → β} {alpha : ℝ} :
    contraction_alpha fp alpha =
      (∀ i, contraction_alpha (proj_fun i ∘ fp) alpha) := by
  apply propext
  constructor
  · exact prod_contra_alpha_only_if
  · exact prod_contra_alpha_if

/- (************************************************************
                       Lemmas (limit)
 ************************************************************) -/

/- (*** cauchy ***) -/

theorem prod_cauchy_seq {ι : Type _} {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} {i : ι} :
    cauchy xps →
      cauchy (proj_fun i ∘ xps) := by
  intro hcauchy
  intro delta hdelta
  rcases hcauchy delta hdelta with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro m k hmk
  have hprod : distance (xps m) (xps k) < delta := hn m k hmk
  exact lt_of_le_of_lt
    (prod_distance_def_le (xp := xps m) (yp := xps k) (i := i))
    (by simpa [proj_fun, Function.comp] using hprod)

/- (*** normal ***) -/

theorem prod_normal_seq {ι : Type _} {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} {i : ι} :
    normal xps →
      normal (proj_fun i ∘ xps) := by
  intro hnormal
  intro n m
  have hprod : distance (xps n) (xps m) <= (1 / 2 : ℝ) ^ min n m := hnormal n m
  exact le_trans
    (prod_distance_def_le (xp := xps n) (yp := xps m) (i := i))
    (by simpa [proj_fun, Function.comp] using hprod)

theorem prod_normal_seq_only_if {ι : Type _} [Nonempty ι] {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} :
    (∀ i, normal (proj_fun i ∘ xps)) →
      normal xps := by
  intro h
  intro n m
  apply prod_distance_least (xp := xps n) (yp := xps m)
  intro i
  simpa [proj_fun, Function.comp] using h i n m

/- iff -/

theorem prod_normal_seq_iff {ι : Type _} [Nonempty ι] {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} :
    normal xps =
      (∀ i, normal (proj_fun i ∘ xps)) := by
  apply propext
  constructor
  · intro hnormal i
    exact prod_normal_seq (i := i) hnormal
  · exact prod_normal_seq_only_if

/- -----------------------*
 |   product of limits   |
 *----------------------- -/

/- (*** limit (single <-- prod) ***) -/

theorem prod_convergeTo_only_if {ι : Type _} {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} {yp : ι → α} :
    xps convergeTo yp →
      ∀ i, (proj_fun i ∘ xps) convergeTo (yp i) := by
  intro hconv i
  intro eps heps
  rcases hconv eps heps with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro m hm
  have hprod : distance yp (xps m) < eps := hn m hm
  exact lt_of_le_of_lt
    (prod_distance_def_le (xp := yp) (yp := xps m) (i := i))
    (by simpa [proj_fun, Function.comp] using hprod)

/- (*** limit (single --> prod) (note: ms_rs) ***) -/

theorem prod_convergeTo_if {ι : Type _} [Nonempty ι] {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} {yp : ι → α} :
    normal xps →
      (∀ i, (proj_fun i ∘ xps) convergeTo (yp i)) →
      xps convergeTo yp := by
  intro hnormal hconv eps heps
  obtain ⟨M, hM⟩ := pow_convergence (alpha := (1 / 2 : ℝ)) (by norm_num) (by norm_num) heps
  refine ⟨Nat.succ M, ?_⟩
  intro m hm
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos M) hm)
  rcases Nat.exists_eq_succ_of_ne_zero hm0 with ⟨n, rfl⟩
  have hMn : M <= n := Nat.succ_le_succ_iff.mp hm
  have hdistI :
      ∀ i, distance (yp i) ((xps (Nat.succ n)) i) <= (1 / 2 : ℝ) ^ M := by
    intro i
    have hi :
        distance ((proj_fun i ∘ xps) (Nat.succ n)) (yp i) < (1 / 2 : ℝ) ^ n :=
      normal_Limit (xs := proj_fun i ∘ xps) (y := yp i) (n := n)
        (prod_normal_seq (i := i) hnormal) (hconv i)
    have hi' : distance (yp i) ((xps (Nat.succ n)) i) < (1 / 2 : ℝ) ^ n := by
      simpa [proj_fun, Function.comp, ms.symmetry_ms] using hi
    exact le_trans (le_of_lt hi') (half_pow_antitone hMn)
  have hprod :
      distance yp (xps (Nat.succ n)) <= (1 / 2 : ℝ) ^ M :=
    prod_distance_least (xp := yp) (yp := xps (Nat.succ n)) hdistI
  exact lt_of_le_of_lt hprod hM

/- iff -/

theorem prod_convergeTo {ι : Type _} [Nonempty ι] {α : Type _} [ms_rs α]
    {xps : infinite_seq (ι → α)} {yp : ι → α} :
    normal xps →
      (xps convergeTo yp ↔ ∀ i, (proj_fun i ∘ xps) convergeTo (yp i)) := by
  intro hnormal
  constructor
  · exact prod_convergeTo_only_if
  · exact prod_convergeTo_if hnormal

/- (*****************************************
      limit (cms and normal --> limit)
 *****************************************) -/

theorem prod_cms_normal_Limit {ι : Type _} [Nonempty ι] {α : Type _}
    [cms_rs α] [Inhabited α] {xps : infinite_seq (ι → α)} :
    normal xps →
      xps convergeTo prod_Limit xps := by
  intro hnormal
  exact (prod_convergeTo (xps := xps) (yp := prod_Limit xps) hnormal).2 (fun i => by
    simpa [prod_Limit, proj_fun, Function.comp] using
      (Limit_is (xs := proj_fun i ∘ xps)
        (normal_cauchy (prod_normal_seq (i := i) hnormal))))

/- (*****************************************
      limit (cms and cauchy --> limit)
 *****************************************) -/

theorem prod_cms_cauchy_Limit {ι : Type _} [Nonempty ι] {α : Type _}
    [cms_rs α] [Inhabited α] {xps : infinite_seq (ι → α)} :
    cauchy xps →
      xps convergeTo prod_Limit (NF xps) := by
  intro hcauchy
  exact normal_form_seq_same_Limit_if (xs := xps) (y := prod_Limit (NF xps)) hcauchy
    (prod_cms_normal_Limit (xps := NF xps) (normal_form_seq_normal hcauchy))

/- (*****************************************
     Product Complete Metric Space (RS)
 *****************************************) -/

theorem prod_cms_rs {ι : Type _} [Nonempty ι] {α : Type _} [cms_rs α]
    {xps : infinite_seq (ι → α)} :
    cauchy xps →
      ∃ yp, xps convergeTo yp := by
  intro hcauchy
  classical
  let zps : infinite_seq (ι → α) := NF xps
  have hnormal : normal zps := normal_form_seq_normal hcauchy
  have hzCauchy : cauchy zps := normal_cauchy hnormal
  have hcoord : ∀ i, ∃ y : α, (proj_fun i ∘ zps) convergeTo y := by
    intro i
    exact cms.complete_ms (proj_fun i ∘ zps) (prod_cauchy_seq (xps := zps) (i := i) hzCauchy)
  choose yp hlim using hcoord
  refine ⟨yp, ?_⟩
  exact normal_form_seq_same_Limit_if (xs := xps) (y := yp) hcauchy
    (prod_convergeTo_if (xps := zps) (yp := yp) hnormal hlim)

/- (************************************************************
                   Product RS ==> CMS and RS
 ************************************************************) -/

instance instCmsFun {ι : Type _} [Nonempty ι] {α : Type _} [cms_rs α] : cms (ι → α) where
  complete_ms := by
    intro xps
    exact prod_cms_rs (xps := xps)

instance instCmsRsFun {ι : Type _} [Nonempty ι] {α : Type _} [cms_rs α] :
    cms_rs (ι → α) where
  complete_ms := by
    intro xps
    exact prod_cms_rs (xps := xps)

/- (************************************************************
                       prod_variable
 ************************************************************) -/

theorem non_expanding_prod_variable {ι : Type _} {α : Type _} [ms_rs α] (pn : ι) :
    non_expanding (fun (f : ι → α) => f pn) := by
  simpa [proj_fun] using (proj_non_expand (α := α) pn)

/- (************************************************************
               Banach theorem for production
 ************************************************************) -/

theorem Banach_thm_prod {ι : Type _} [Nonempty ι] {α : Type _}
    [cms_rs α] [Inhabited α]
    {f : (ι → α) → ι → α} {x0 : ι → α} :
    normal (fun n => (f^[n]) x0) →
      contraction f →
      hasUFP f ∧ ∀ i, (fun n => (f^[n]) x0 i) convergeTo (UFP f) i := by
  intro hnormal hcontr
  rcases Banach_thm (f := f) (x0 := x0) hcontr with ⟨hufp, hconv⟩
  refine ⟨hufp, ?_⟩
  have hprod :
      ∀ i, (proj_fun i ∘ fun n => (f^[n]) x0) convergeTo (UFP f) i :=
    (prod_convergeTo (xps := fun n => (f^[n]) x0) (yp := UFP f) hnormal).1 hconv
  intro i
  simpa [proj_fun, Function.comp] using hprod i

/- ----------------------------------------------------------*
 |                                                          |
 |                Continuity on Metric space                |
 |                                                          |
 *---------------------------------------------------------- -/

theorem prod_continuous_rs {ι : Type _} {α : Type _} [ms_rs α]
    {R : ι → α → Prop} :
    (∀ i, continuous_rs (R i)) →
      continuous_rs (fun xp : ι → α => ∀ i, R i (xp i)) := by
  intro hR xp hnot
  classical
  have hnotAll : ¬ ∀ i, R i (xp i) := hnot
  push_neg at hnotAll
  rcases hnotAll with ⟨i, hi⟩
  rcases hR i (xp i) hi with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro yp hEq hy
  have hEqI : yp i .|. n = xp i .|. n := by
    simpa [prod_restriction_def] using congrArg (fun f => f i) hEq
  exact (hn (yp i) hEqI) (hy i)

/- ----------------------------------------------------------*
 |                                                          |
 |      !!!     order and restriction space     !!!         |
 |                                                          |
 *---------------------------------------------------------- -/

instance instMsRsOrder0Fun {ι : Type _} {α : Type _} [ms_rs_order α] :
    ms_rs_order0 (ι → α) where

instance instMsRsOrderFun {ι : Type _} {α : Type _} [ms_rs_order α] :
    ms_rs_order (ι → α) where
  rs_order_iff := by
    intro x y
    constructor
    · intro hrest i
      exact (ms_rs_order.rs_order_iff (x i) (y i)).1 (fun n => hrest n i)
    · intro hle n i
      exact rs_order_if (x := x i) (y := y i) (n := n) (hle i)

/- (*** cms rs order ***) -/

instance instCmsRsOrderFun {ι : Type _} [Nonempty ι] {α : Type _} [cms_rs_order α] :
    cms_rs_order (ι → α) where
  complete_ms := by
    intro xps
    exact prod_cms_rs (xps := xps)

end
