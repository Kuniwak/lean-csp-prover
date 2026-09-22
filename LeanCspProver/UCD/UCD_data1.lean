           /- -------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_HOL
import LeanCspProver.CSP.Infra_list

open Classical

abbrev hd [Inhabited α] : List α → α := List.head!
abbrev last [Inhabited α] : List α → α := List.getLast!

/-
(*****************************************************************

         1. Data part

 *****************************************************************)
-/

/- line and circ -/

def fill : Nat → Nat
  | n => if Even n then n else n + 1

def allEven : List Nat → Prop
  | s => ∀ n ∈ set s, Even n

def lineNext : List Nat → Nat → List Nat
  | [], _ => []
  | n :: s, x =>
      if s = [] then [fill (n / 2 + x)]
      else fill (n / 2 + hd s / 2) :: lineNext s x

def circNext : List Nat → List Nat
  | s => if s = [] then [] else lineNext s (hd s / 2)

def circNexts : Nat → List Nat → List Nat
  | 0, s => s
  | N + 1, s => circNexts N (circNext s)

/- max and min -/

def maxList : List Nat → Nat
  | [] => 0
  | n :: s => max n (maxList s)

def minList : List Nat → Nat
  | [] => 0
  | n :: s =>
      if s = [] then n
      else min n (minList s)

def howMany (m : Nat) : List Nat → Nat
  | [] => 0
  | n :: s => (if m = n then Nat.succ (howMany m s) else howMany m s)

def stableList (s : List Nat) : Prop :=
  ∀ n ∈ set s, n = minList s

def makeStableList : Nat → Nat → List Nat
  | 0, _ => []
  | l + 1, n => n :: makeStableList l n

/- ------ test ------ -/

theorem lineNext_test :
    lineNext [4, 2, 10] 2 = [4, 6, 8] := by
  native_decide

theorem circNext_test :
    circNext [4, 2, 10] = [4, 6, 8] := by
  native_decide

theorem maxList_test :
    maxList [4, 2, 10, 1, 5] = 10 := by
  simp [maxList]

theorem minList_test :
    minList [4, 2, 10, 1, 5] = 1 := by
  simp [minList]

theorem howMany_test :
    howMany 2 [4, 2, 10, 2, 5, 2] = 3 := by
  simp [howMany]

theorem makeStableList_test :
    makeStableList (Nat.succ (Nat.succ (Nat.succ 0))) 5 = [5, 5, 5] := by
  simp [makeStableList]

/- ------------------------------------------------- *
                convenient lemmas
 * ------------------------------------------------- -/

theorem not_nil_EX {s : List α} : (s ≠ []) ↔ ∃ a t, s = a :: t := by
  simpa using (not_nil (s := s))

@[simp]
theorem hd_in_list {s : List α} [Inhabited α] : s ≠ [] → hd s ∈ set s := by
  cases s with
  | nil => simp
  | cons a t => simp [_root_.set, hd]

theorem nth_hd {s : List α} [Inhabited α] : s ≠ [] → nth s 0 = hd s := by
  cases s with
  | nil => simp
  | cons a t => simp [nth, hd]

theorem nth_last {s : List α} [Inhabited α] {i : Nat} :
    Nat.succ i = s.length → nth s i = last s := by
  intro h
  rcases list_last_nil_or_unnil s with rfl | ⟨t, a, rfl⟩
  · simp at h
  · have hi : i = t.length := by simpa using h
    subst hi
    simp [nth, last]

theorem list_not_nil {s : List α} : (s ≠ []) ↔ ∃ a t, s = a :: t := by
  simpa using (not_nil_EX (s := s))

theorem even_EX {n : Nat} : Even n ↔ ∃ m, n = (2 : Nat) * m := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by omega⟩
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    omega

theorem less_Suc {n N : Nat} :
    (n < Nat.succ N) ↔ (n = 0 ∨ ∃ m, n = Nat.succ m ∧ m < N) := by
  cases n with
  | zero =>
      simp
  | succ m =>
      simp

theorem zero_less_EX {n : Nat} : (0 < n) ↔ ∃ m, n = Nat.succ m := by
  cases n with
  | zero => simp
  | succ m => simp

theorem in_set_nth [Inhabited α] {n : α} {s : List α} :
    Iff (n ∈ set s) (∃ i, i < s.length ∧ n = nth s i) := by
  constructor
  · intro hn
    rcases List.mem_iff_getElem.mp (by simpa [_root_.set] using hn) with ⟨i, hi, hEq⟩
    have hNth : nth s i = s[i] := by simp [nth, hi]
    exact ⟨i, hi, by simpa [hNth] using hEq.symm⟩
  · rintro ⟨i, hi, hEq⟩
    have hget : s[i] = n := by simpa [nth, hi] using hEq.symm
    have hs : n ∈ s := List.mem_of_getElem hget
    simpa [_root_.set] using hs

theorem list_length_more_one {s : List α} :
    Iff (Nat.succ 0 < s.length) (s ≠ [] ∧ tl s ≠ []) := by
  cases s with
  | nil => simp [tl]
  | cons a t =>
      cases t with
      | nil => simp [tl]
      | cons b u => simp [tl]

/- ------------------------------------------------- *
               lemmas on line and circ
 * ------------------------------------------------- -/

/- [] -/

@[simp]
theorem allEven_nil : allEven [] := by
  simp [allEven]

@[simp]
theorem lineNext_nil_iff {s : List Nat} {x : Nat} :
    (lineNext s x = []) ↔ (s = []) := by
  cases s with
  | nil => simp [lineNext]
  | cons a t =>
      cases t <;> simp [lineNext]

@[simp]
theorem circNext_nil_iff {s : List Nat} :
    (circNext s = []) ↔ (s = []) := by
  simp [circNext]

@[simp]
theorem tl_lineNext_nil_iff {s : List Nat} {x : Nat} :
    (tl (lineNext s x) = []) ↔ (tl s = []) := by
  cases s with
  | nil => simp [lineNext, tl]
  | cons a t =>
      cases t with
      | nil => simp [lineNext, tl]
      | cons b u =>
          cases u with
          | nil => simp [lineNext, tl]
          | cons c v => simp [lineNext, tl]

@[simp]
theorem tl_circNext_nil_iff {s : List Nat} :
    (tl (circNext s) = []) ↔ (tl s = []) := by
  cases s with
  | nil => simp [circNext, tl]
  | cons a t =>
      cases t with
      | nil => simp [circNext, lineNext, tl, hd]
      | cons b u =>
          cases u with
          | nil => simp [circNext, lineNext, tl, hd]
          | cons c v => simp [circNext, lineNext, tl, hd]

@[simp]
theorem circNext_nil : circNext ([] : List Nat) = [] := by
  simp [circNext]

@[simp]
theorem circNexts_nil_iff {N : Nat} : ∀ s : List Nat, (circNexts N s = []) ↔ (s = []) := by
  intro s
  induction N generalizing s with
  | zero =>
      simp [circNexts]
  | succ N ih =>
      simp [circNexts, ih]

@[simp]
theorem circNexts_nil {N : Nat} : ∀ s : List Nat, circNexts N [] = [] := by
  intro s
  induction N with
  | zero =>
      simp [circNexts]
  | succ N ih =>
      simp [circNexts, ih]

/- length -/

@[simp]
theorem length_lineNext {s : List Nat} {x : Nat} :
    (lineNext s x).length = s.length := by
  induction s with
  | nil =>
      simp [lineNext]
  | cons a t ih =>
      cases t with
      | nil => simp [lineNext]
      | cons b u =>
          simpa [lineNext] using congrArg Nat.succ ih

@[simp]
theorem length_circNext {s : List Nat} :
    (circNext s).length = s.length := by
  cases s <;> simp [circNext]

@[simp]
theorem length_circNexts {N : Nat} : ∀ s : List Nat, (circNexts N s).length = s.length := by
  intro s
  induction N generalizing s with
  | zero => simp [circNexts]
  | succ N ih => simp [circNexts, ih]

/- even -/

theorem even_fill {n : Nat} : Even (fill n) := by
  by_cases h : Even n
  · simp [fill, h]
  · simpa [fill, h] using (Nat.even_add_one).2 h

@[simp]
theorem fill_div_times {n : Nat} : fill n / 2 * 2 = fill n := by
  have hEven : Even (fill n) := even_fill
  rcases even_EX.mp hEven with ⟨m, hm⟩
  rw [hm]
  omega

@[simp]
theorem lineNext_even {s : List Nat} {nn : Nat} : allEven (lineNext s nn) := by
  induction s generalizing nn with
  | nil =>
      simp [lineNext, allEven]
  | cons a t ih =>
      cases t with
      | nil =>
          intro n hn
          simp [_root_.set, lineNext] at hn
          rcases hn with rfl
          exact even_fill
      | cons b u =>
          intro n hn
          simp [_root_.set, lineNext] at hn
          rcases hn with rfl | hn
          · exact even_fill
          · exact ih _ hn

@[simp]
theorem circNext_even {s : List Nat} : allEven (circNext s) := by
  cases s <;> simp [circNext]

theorem circNexts_even_lm {N : Nat} : ∀ s : List Nat, allEven s → allEven (circNexts N s) := by
  intro s hs
  induction N generalizing s with
  | zero =>
      simpa [circNexts]
  | succ N ih =>
      simpa [circNexts] using ih (circNext s) (circNext_even (s := s))

@[simp]
theorem circNexts_even {N : Nat} {s : List Nat} :
    allEven s → allEven (circNexts N s) := by
  exact circNexts_even_lm (N := N) s

theorem circNexts_sum {N1 N2 : Nat} :
    ∀ s : List Nat, circNexts (N1 + N2) s = circNexts N1 (circNexts N2 s) := by
  intro s
  induction N2 generalizing s with
  | zero =>
      simp [circNexts]
  | succ N2 ih =>
      simpa [circNexts, Nat.add_assoc] using ih (circNext s)

/- ------------------------------------------------- *
               lemmas on min and max
 * ------------------------------------------------- -/

/- max and min -/

@[simp]
theorem maxList_max {s : List Nat} : ∀ n ∈ set s, n ≤ maxList s := by
  intro n hn
  induction s generalizing n with
  | nil =>
      simp at hn
  | cons a t ih =>
      simp [_root_.set] at hn
      rcases hn with rfl | hn
      · exact Nat.le_max_left _ _
      · exact le_trans (ih _ hn) (Nat.le_max_right _ _)

@[simp]
theorem maxList_max_nth {s : List Nat} [Inhabited Nat] :
    (∀ i, i < s.length → nth s i ≤ maxList s) := by
  intro i hi
  have hmem : nth s i ∈ set s := (in_set_nth).2 ⟨i, hi, rfl⟩
  exact maxList_max _ hmem

@[simp]
theorem minList_min {s : List Nat} : ∀ n ∈ set s, minList s ≤ n := by
  intro n hn
  induction s generalizing n with
  | nil =>
      simp at hn
  | cons a t ih =>
      cases t with
      | nil =>
          simp [_root_.set] at hn
          simpa [minList, hn]
      | cons b u =>
          simp [_root_.set] at hn
          rcases hn with rfl | hn
          · simpa [minList] using (Nat.min_le_left a (minList (b :: u)))
          · have hn' : n ∈ set (b :: u) := by simpa [_root_.set] using hn
            exact le_trans (by simpa [minList] using (Nat.min_le_right a (minList (b :: u)))) (ih _ hn')

@[simp]
theorem maxList_min_nth {s : List Nat} [Inhabited Nat] :
    (∀ i, i < s.length → minList s ≤ nth s i) := by
  intro i hi
  have hmem : nth s i ∈ set s := (in_set_nth).2 ⟨i, hi, rfl⟩
  exact minList_min _ hmem

/- exist -/

theorem maxList_exist {s : List Nat} : s ≠ [] → maxList s ∈ set s := by
  intro hs
  induction s with
  | nil => simp at hs
  | cons a t ih =>
      cases t with
      | nil =>
          simpa [_root_.set, maxList]
      | cons b u =>
          by_cases h : a ≤ maxList (b :: u)
          · have hmem : maxList (b :: u) = b ∨ maxList (b :: u) ∈ u := by
              simpa [_root_.set] using ih (by simp)
            have hEq : max a (maxList (b :: u)) = maxList (b :: u) := Nat.max_eq_right h
            rcases hmem with hmem | hmem
            · have hEq' : max a (max b (maxList u)) = b := by
                have hEqb : max b (maxList u) = b := by
                  simpa [maxList] using hmem
                simpa [maxList, hEqb] using hEq
              simp [_root_.set, maxList, hEq']
            · have hu : max b (maxList u) ∈ u := by
                simpa [maxList] using hmem
              have hEq' : max a (max b (maxList u)) = max b (maxList u) := by
                simpa [maxList] using hEq
              simp [_root_.set, maxList, hEq', hu]
          · have hEq : max a (maxList (b :: u)) = a := Nat.max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge h))
            have hEq' : max a (max b (maxList u)) = a := by
              simpa [maxList] using hEq
            simp [_root_.set, maxList, hEq']

theorem maxList_exist_nth {s : List Nat} [Inhabited Nat] :
    (s ≠ [] → ∃ i, i < s.length ∧ nth s i = maxList s) := by
  intro hs
  rcases (in_set_nth).1 (maxList_exist hs) with ⟨i, hi, hEq⟩
  exact ⟨i, hi, hEq.symm⟩

theorem minList_exist {s : List Nat} : s ≠ [] → minList s ∈ set s := by
  intro hs
  induction s with
  | nil => simp at hs
  | cons a t ih =>
      cases t with
      | nil =>
          simpa [_root_.set, minList]
      | cons b u =>
          by_cases h : a ≤ minList (b :: u)
          · have hEq : min a (minList (b :: u)) = a := Nat.min_eq_left h
            have hEq' : min a (if u = [] then b else min b (minList u)) = a := by
              simpa [minList] using hEq
            simp [_root_.set, minList, hEq']
          · have hEq : min a (minList (b :: u)) = minList (b :: u) :=
              Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge h))
            have hmem : minList (b :: u) = b ∨ minList (b :: u) ∈ u := by
              simpa [_root_.set] using ih (by simp)
            rcases hmem with hmem | hmem
            · have hEq' : min a (if u = [] then b else min b (minList u)) = b := by
                have hEqb : (if u = [] then b else min b (minList u)) = b := by
                  simpa [minList] using hmem
                simpa [minList, hEqb] using hEq
              simp [_root_.set, minList, hEq']
            · have hu : (if u = [] then b else min b (minList u)) ∈ u := by
                simpa [minList] using hmem
              have hEq' : min a (if u = [] then b else min b (minList u)) =
                  (if u = [] then b else min b (minList u)) := by
                simpa [minList] using hEq
              simp [_root_.set, minList, hEq', hu]

theorem minList_exist_nth {s : List Nat} [Inhabited Nat] :
    (s ≠ [] → ∃ i, i < s.length ∧ nth s i = minList s) := by
  intro hs
  rcases (in_set_nth).1 (minList_exist hs) with ⟨i, hi, hEq⟩
  exact ⟨i, hi, hEq.symm⟩

/- basic -/

theorem minList_le_maxList {s : List Nat} : minList s ≤ maxList s := by
  by_cases hs : s = []
  · simp [hs, minList, maxList]
  · exact maxList_max (n := minList s) (minList_exist hs)

@[simp]
theorem maxList_single {n : Nat} : maxList [n] = n := by
  simp [maxList]

@[simp]
theorem minList_single {n : Nat} : minList [n] = n := by
  simp [minList]

theorem minList_le_forall {t : List Nat} {m : Nat} :
    t ≠ [] → ((m ≤ minList t) ↔ ∀ n ∈ set t, m ≤ n) := by
  intro ht
  constructor
  · intro hm n hn
    exact le_trans hm (minList_min _ hn)
  · intro h
    exact h _ (minList_exist ht)

theorem minList_less_forall {t : List Nat} {m : Nat} :
    t ≠ [] → ((m < minList t) ↔ ∀ n ∈ set t, m < n) := by
  intro ht
  constructor
  · intro hm n hn
    exact lt_of_lt_of_le hm (minList_min _ hn)
  · intro h
    exact h _ (minList_exist ht)

theorem maxList_le_forall {t : List Nat} {m : Nat} :
    (maxList t ≤ m) ↔ ∀ n ∈ set t, n ≤ m := by
  constructor
  · intro hm n hn
    exact le_trans (maxList_max _ hn) hm
  · intro h
    by_cases ht : t = []
    · simp [ht, maxList]
    · exact h _ (maxList_exist ht)

theorem maxList_less_forall {t : List Nat} {m : Nat} :
    (t ≠ [] → Iff (maxList t < m) (∀ n ∈ set t, n < m)) := by
  intro ht
  constructor
  · intro hm n hn
    exact lt_of_le_of_lt (maxList_max _ hn) hm
  · intro h
    exact h _ (maxList_exist ht)

/- fill -/

@[simp]
theorem even_le_fill {n m : Nat} :
    Even n → ((fill m ≤ n) ↔ (m ≤ n)) := by
  intro hn
  rcases even_EX.mp hn with ⟨k, hk⟩
  by_cases hm : Even m
  · simp [fill, hm]
  · have hm' : Even (m + 1) := (Nat.even_add_one).2 hm
    rcases even_EX.mp hm' with ⟨j, hj⟩
    rw [hk, show fill m = m + 1 by simp [fill, hm], hj]
    omega

theorem even_fill_le {n m : Nat} : n ≤ m → n ≤ fill m := by
  intro h
  by_cases hm : Even m
  · simp [fill, hm, h]
  · simp [fill, hm]
    omega

@[simp]
theorem even_fill_less {n m : Nat} :
    Even n → ((n < fill m) ↔ (n < m)) := by
  intro hn
  rcases even_EX.mp hn with ⟨k, hk⟩
  by_cases hm : Even m
  · simp [fill, hm]
  · have hm' : Even (m + 1) := (Nat.even_add_one).2 hm
    rcases even_EX.mp hm' with ⟨j, hj⟩
    rw [hk, show fill m = m + 1 by simp [fill, hm], hj]
    omega

/- even -/

@[simp]
theorem allEven_maxList {s : List Nat} :
    (∀ n ∈ set s, Even n) → Even (maxList s) := by
  intro hs
  by_cases hnil : s = []
  · simp [hnil, maxList]
  · exact hs _ (maxList_exist hnil)

@[simp]
theorem allEven_minList {s : List Nat} :
    (∀ n ∈ set s, Even n) → Even (minList s) := by
  intro hs
  by_cases hnil : s = []
  · simp [hnil, minList]
  · exact hs _ (minList_exist hnil)

theorem alleven_hd {n : Nat} {s : List Nat} :
    allEven (n :: s) ↔ (Even n ∧ allEven s) := by
  constructor
  · intro h
    refine ⟨h n (by simp [_root_.set]), ?_⟩
    intro m hm
    have hm' : m = n ∨ m ∈ s := Or.inr hm
    exact h m (by simpa [_root_.set] using hm')
  · rintro ⟨hn, hs⟩ m hm
    simp [_root_.set] at hm
    rcases hm with rfl | hm
    · exact hn
    · exact hs _ hm

@[simp]
theorem allEven_div {s : List Nat} :
    s ≠ [] → allEven s → 2 * (hd s / 2) = hd s := by
  intro hs hEven
  have hhd : Even (hd s) := by
    exact hEven _ (hd_in_list hs)
  rcases even_EX.mp hhd with ⟨m, hm⟩
  cases s with
  | nil => simp at hs
  | cons a t =>
      simp [hd] at hm ⊢
      omega

theorem allEven_hd {s : List Nat} :
    s ≠ [] → allEven s → Even (hd s) := by
  intro hs hEven
  exact hEven _ (hd_in_list hs)

/- stable -/

theorem stable_min_max {s : List Nat} :
    stableList s ↔ (minList s = maxList s) := by
  constructor
  · intro hs
    apply le_antisymm
    · exact minList_le_maxList
    · rw [maxList_le_forall]
      intro n hn
      exact (hs n hn).le
  · intro hEq
    intro n hn
    apply le_antisymm
    · simpa [hEq] using (maxList_max (n := n) hn)
    · exact minList_min n hn

theorem stable_lineNext_lm {s : List Nat} {N : Nat} :
    (∀ n ∈ set s, n = 2 * N) → lineNext s N = s := by
  intro hs
  induction s with
  | nil =>
      simp [lineNext]
  | cons a t ih =>
      cases t with
      | nil =>
          have ha : a = 2 * N := hs a (by simp [_root_.set])
          have hEven : Even (N + N) := ⟨N, by omega⟩
          have hfill : fill (a / 2 + N) = a := by
            rw [ha]
            have htwo : N + N = 2 * N := by omega
            rw [show (2 * N) / 2 + N = N + N by omega, htwo]
            simp [fill, hEven]
          simpa [lineNext, hfill]
      | cons b u =>
          have ha : a = 2 * N := hs a (by simp [_root_.set])
          have hb : hd (b :: u) = 2 * N := by
            simpa [hd, _root_.set] using hs b (by simp [_root_.set])
          have htail : ∀ n ∈ (_root_.set (b :: u) : Set Nat), n = 2 * N := by
            intro n hn
            have hn' : n = b ∨ n ∈ u := by simpa [_root_.set] using hn
            exact hs n (by simpa [_root_.set] using Or.inr hn')
          have hfirst : fill (a / 2 + b / 2) = a := by
            rw [ha]
            have hb' : b = 2 * N := hs b (by simp [_root_.set])
            rw [hb']
            have hEven : Even (N + N) := ⟨N, by omega⟩
            have htwo : N + N = 2 * N := by omega
            rw [show (2 * N) / 2 + (2 * N) / 2 = N + N by omega, htwo]
            simp [fill, hEven]
          have hrest : lineNext (b :: u) N = b :: u := ih htail
          have hfirst' : fill (a / 2 + hd (b :: u) / 2) = a := by
            have hb' : b = 2 * N := hs b (by simp [_root_.set])
            rw [hb]
            simpa [hb'] using hfirst
          rw [lineNext, if_neg (by simp), hfirst']
          simpa using congrArg (List.cons a) hrest

theorem stable_lineNext {s : List Nat} :
    allEven s → stableList s → lineNext s (hd s / 2) = s := by
  intro hEven hStable
  by_cases hs : s = []
  · simp [hs, lineNext]
  · apply stable_lineNext_lm
    intro n hn
    have hmin : n = minList s := hStable n hn
    have hhd : hd s = minList s := hStable _ (hd_in_list hs)
    rw [hmin, ← hhd]
    exact (allEven_div hs hEven).symm

theorem stable_circNext {s : List Nat} :
    allEven s → stableList s → circNext s = s := by
  intro hEven hStable
  simp [circNext, stable_lineNext hEven hStable]

theorem stable_circNexts {N : Nat} {s : List Nat} :
    allEven s → stableList s → circNexts N s = s := by
  intro hEven hStable
  induction N generalizing s with
  | zero =>
      simp [circNexts]
  | succ N ih =>
      simp [circNexts, stable_circNext hEven hStable, ih hEven hStable]

/- howMany -/

theorem howMany_zero {m : Nat} {s : List Nat} :
    (howMany m s = 0) ↔ ∀ n ∈ set s, m ≠ n := by
  induction s with
  | nil =>
      simp [howMany]
  | cons a t ih =>
      by_cases h : m = a
      · subst h
        simp [howMany, ih, _root_.set]
      · simp [howMany, h, ih, _root_.set]

theorem less_minList_howMany_zero {s : List Nat} {M : Nat} :
    s ≠ [] → M < minList s → howMany M s = 0 := by
  intro hs hM
  rw [howMany_zero]
  intro n hn
  exact ne_of_lt ((minList_less_forall (t := s) (m := M) hs).1 hM n hn)

/- makeStableList -/

@[simp]
theorem makeStableList_nil {l n : Nat} :
    (makeStableList l n = []) ↔ (l = 0) := by
  induction l with
  | zero =>
      simp [makeStableList]
  | succ l ih =>
      simp [makeStableList]

@[simp]
theorem tl_makeStableList_nil {l n : Nat} :
    (tl (makeStableList l n) = []) ↔ (l ≤ Nat.succ 0) := by
  induction l with
  | zero =>
      simp [makeStableList, tl]
  | succ l ih =>
      cases l with
      | zero =>
          simp [makeStableList, tl]
      | succ k =>
          simp [makeStableList, tl]

@[simp]
theorem makeStableList_hd {l n : Nat} :
    0 < l → hd (makeStableList l n) = n := by
  intro hl
  cases l with
  | zero =>
      simp at hl
  | succ k =>
      simp [makeStableList, hd]

@[simp]
theorem set_makeStableList {l n : Nat} :
    0 < l → set (makeStableList l n) = {n} := by
  intro hl
  induction l with
  | zero =>
      simp at hl
  | succ l ih =>
      cases l with
      | zero =>
          ext x
          simp [makeStableList, _root_.set]
      | succ k =>
          have hset : set (makeStableList (k + 1) n) = {n} := ih (by omega)
          ext x
          constructor
          · intro hx
            have hx' : x = n ∨ x ∈ set (makeStableList (k + 1) n) := by
              simpa [makeStableList, _root_.set] using hx
            rcases hx' with rfl | hx
            · simp
            · simpa [hset] using hx
          · intro hx
            have hx' : x = n := by simpa using hx
            simp [_root_.set, makeStableList, hx']

@[simp]
theorem length_makeStableList {l n : Nat} :
    (makeStableList l n).length = l := by
  induction l with
  | zero =>
      simp [makeStableList]
  | succ l ih =>
      simp [makeStableList, ih]

theorem stableList_makeStableList_lm {l n : Nat} :
    stableList (makeStableList l n) := by
  intro m hm
  by_cases hl : l = 0
  · simp [hl, makeStableList] at hm
  · have hpos : 0 < l := Nat.pos_of_ne_zero hl
    have hset : set (makeStableList l n) = {n} := set_makeStableList hpos
    have hmEq : m = n := by simpa [hset] using hm
    have hne : makeStableList l n ≠ [] := by
      simpa [makeStableList_nil] using hl
    have hminmem : minList (makeStableList l n) ∈ set (makeStableList l n) := minList_exist hne
    have hmin : minList (makeStableList l n) = n := by
      simpa [hset] using hminmem
    simpa [hmEq, hmin]

@[simp]
theorem stableList_makeStableList {s : List Nat} {l n : Nat} :
    s = makeStableList l n → stableList s := by
  intro hs
  simpa [hs] using stableList_makeStableList_lm (l := l) (n := n)

@[simp]
theorem allEven_makeStableList {l n : Nat} :
    Even n → allEven (makeStableList l n) := by
  intro hn
  induction l with
  | zero =>
      simp [makeStableList, allEven]
  | succ l ih =>
      intro m hm
      simp [_root_.set, makeStableList] at hm
      rcases hm with rfl | hm
      · exact hn
      · exact ih _ hm

theorem makeStableList_hd_stableList_if {l : Nat} :
    ∀ s : List Nat, (s.length = l ∧ stableList s) → s = makeStableList l (hd s) := by
  induction l with
  | zero =>
      intro s hs
      rcases hs with ⟨hlen, _⟩
      cases s <;> simp at hlen <;> simp [makeStableList]
  | succ l ih =>
      intro s hs
      rcases hs with ⟨hlen, hstable⟩
      cases s with
      | nil =>
          simp at hlen
      | cons a t =>
          cases t with
          | nil =>
              have hl0 : l = 0 := by simpa using hlen
              subst hl0
              simp [makeStableList, hd]
          | cons b u =>
              have hlen' : (b :: u).length = l := by simpa using hlen
              have hab : b = a := by
                have hbmin : b = minList (a :: b :: u) := hstable b (by simp [_root_.set])
                have hamin : a = minList (a :: b :: u) := hstable a (by simp [_root_.set])
                exact hbmin.trans hamin.symm
              have hconst : ∀ n ∈ set (b :: u), n = b := by
                intro n hn
                have hn' : n = b ∨ n ∈ u := by simpa [_root_.set] using hn
                have hnmin : n = minList (a :: b :: u) := hstable n (by simpa [_root_.set] using Or.inr hn')
                have hbmin : b = minList (a :: b :: u) := hstable b (by simp [_root_.set])
                exact hnmin.trans hbmin.symm
              have hsetbu : set (b :: u) = {b} := by
                ext n
                constructor
                · intro hn
                  simpa [hconst n hn]
                · intro hn
                  have hn' : n = b := by simpa using hn
                  simpa [hn', _root_.set]
              have hminbu : minList (b :: u) = b := by
                have hmem : minList (b :: u) ∈ (_root_.set (b :: u) : Set Nat) := minList_exist (by simp)
                simpa [hsetbu] using hmem
              have hstable' : stableList (b :: u) := by
                intro n hn
                have hnEq : n = b := by simpa [hsetbu] using hn
                simpa [hnEq, hminbu]
              have ht : b :: u = makeStableList l b := by
                simpa [hd] using ih (b :: u) ⟨hlen', hstable'⟩
              simpa [makeStableList, hd, hab] using congrArg (List.cons a) (by simpa [hab] using ht)

theorem makeStableList_hd_stableList_only_if {l : Nat} :
    ∀ s : List Nat, s = makeStableList l (hd s) → s.length = l := by
  intro s hs
  cases s with
  | nil =>
      cases l with
      | zero => simp [makeStableList] at hs ⊢
      | succ l => simp [makeStableList] at hs
  | cons a t =>
      cases l with
      | zero =>
          simp [makeStableList] at hs
      | succ l =>
          have ht : t = makeStableList l a := by
            simpa [makeStableList, hd] using hs
          simp [ht, makeStableList, length_makeStableList]

theorem makeStableList_hd_stableList {s : List Nat} {l : Nat} :
    (s = makeStableList l (hd s)) ↔ (s.length = l ∧ stableList s) := by
  constructor
  · intro hs
    refine ⟨makeStableList_hd_stableList_only_if (l := l) s hs, ?_⟩
    have hstable : stableList (makeStableList l (hd s)) := stableList_makeStableList_lm
    rw [hs]
    exact hstable
  · intro hs
    exact makeStableList_hd_stableList_if (l := l) s hs

/- ------------------------------------------------- *
             lemmas on line, min and max
 * ------------------------------------------------- -/

private theorem self_le_fill {n : Nat} : n ≤ fill n := by
  by_cases h : Even n
  · simp [fill, h]
  · simp [fill, h]

private theorem allEven_nth {s : List Nat} (hs : allEven s) {i : Nat} (hi : i < s.length) :
    Even (nth s i) := by
  exact hs _ ((in_set_nth).2 ⟨i, hi, rfl⟩)

private theorem nth_le_of_forall {s : List Nat} {M i : Nat}
    (hs : ∀ n ∈ set s, n ≤ M) (hi : i < s.length) : nth s i ≤ M := by
  exact hs _ ((in_set_nth).2 ⟨i, hi, rfl⟩)

private theorem le_nth_of_forall {s : List Nat} {M i : Nat}
    (hs : ∀ n ∈ set s, M ≤ n) (hi : i < s.length) : M ≤ nth s i := by
  exact hs _ ((in_set_nth).2 ⟨i, hi, rfl⟩)

private theorem nth_lineNext_lt_succ {s : List Nat} {x i : Nat}
    (hs : s ≠ []) (hi : Nat.succ i < s.length) :
    nth (lineNext s x) i = fill (nth s i / 2 + nth s (Nat.succ i) / 2) := by
  induction s generalizing i with
  | nil =>
      cases hs rfl
  | cons a t ih =>
      cases i with
      | zero =>
          cases t with
          | nil =>
              simp at hi
          | cons b u =>
              simp [lineNext, hd]
      | succ i =>
          cases t with
          | nil =>
              simp at hi
          | cons b u =>
              have ht : b :: u ≠ [] := by simp
              have hi' : Nat.succ i < (b :: u).length := by simpa using hi
              simpa [lineNext, nth_cons_succ] using ih ht hi'

private theorem nth_lineNext_last {s : List Nat} {x i : Nat}
    (hs : s ≠ []) (hi : Nat.succ i = s.length) :
    nth (lineNext s x) i = fill (nth s i / 2 + x) := by
  induction s generalizing i with
  | nil =>
      cases hs rfl
  | cons a t ih =>
      cases i with
      | zero =>
          cases t with
          | nil =>
              simp [lineNext] at hi ⊢
          | cons b u =>
              simp at hi
      | succ i =>
          cases t with
          | nil =>
              simp at hi
          | cons b u =>
              have ht : b :: u ≠ [] := by simp
              have hi' : Nat.succ i = (b :: u).length := by simpa using hi
              simpa [lineNext, nth_cons_succ] using ih ht hi'

private theorem last_lineNext {s : List Nat} {x : Nat} (hs : s ≠ []) :
    last (lineNext s x) = fill (last s / 2 + x) := by
  let i := s.length - 1
  have hiEq : Nat.succ i = s.length := by
    have hlen : 0 < s.length := by
      cases s with
      | nil => cases hs rfl
      | cons a t => simp
    dsimp [i]
    omega
  have hLast1 : last (lineNext s x) = nth (lineNext s x) i := by
    symm
    exact nth_last (s := lineNext s x) (i := i) (by simpa using hiEq)
  have hNth : nth (lineNext s x) i = fill (nth s i / 2 + x) := nth_lineNext_last hs hiEq
  have hLast2 : nth s i = last s := nth_last (s := s) (i := i) hiEq
  rw [hLast1, hNth, hLast2]

/- line max <= -/

theorem lineNext_max_le_lm {s : List Nat} {M nn : Nat} :
    ∀ n,
      (s ≠ [] ∧ allEven s ∧ Even M ∧ (∀ m ∈ set s, m ≤ M) ∧ 2 * nn ≤ M ∧
        n ∈ set (lineNext s nn)) →
      n ≤ M := by
  intro n h
  rcases h with ⟨hs, hEvenS, hEvenM, hBound, hnn, hn⟩
  rcases (in_set_nth).1 hn with ⟨i, hi, rfl⟩
  have hiS : i < s.length := by simpa using hi
  by_cases hlast : Nat.succ i = s.length
  · rw [nth_lineNext_last hs hlast]
    have hsi : nth s i ≤ M := nth_le_of_forall hBound hiS
    have hsiEven : Even (nth s i) := allEven_nth hEvenS hiS
    have hInner : nth s i / 2 + nn ≤ M := by
      rcases even_EX.mp hEvenM with ⟨mM, hM⟩
      rcases even_EX.mp hsiEven with ⟨mi, hi'⟩
      rw [hM, hi']
      omega
    exact (even_le_fill (n := M) (m := nth s i / 2 + nn) hEvenM).2 hInner
  · have hi1 : Nat.succ i < s.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hiS) hlast
    rw [nth_lineNext_lt_succ hs hi1]
    have hsi : nth s i ≤ M := nth_le_of_forall hBound hiS
    have hsj : nth s (Nat.succ i) ≤ M := nth_le_of_forall hBound hi1
    have hsiEven : Even (nth s i) := allEven_nth hEvenS hiS
    have hsjEven : Even (nth s (Nat.succ i)) := allEven_nth hEvenS hi1
    have hInner : nth s i / 2 + nth s (Nat.succ i) / 2 ≤ M := by
      rcases even_EX.mp hEvenM with ⟨mM, hM⟩
      rcases even_EX.mp hsiEven with ⟨mi, hi'⟩
      rcases even_EX.mp hsjEven with ⟨mj, hj'⟩
      rw [hM, hi', hj']
      omega
    exact (even_le_fill (n := M) (m := nth s i / 2 + nth s (Nat.succ i) / 2) hEvenM).2
      hInner

theorem lineNext_max_le {s : List Nat} {M nn n : Nat} :
    s ≠ [] → allEven s → Even M → (∀ m ∈ set s, m ≤ M) → 2 * nn ≤ M →
      n ∈ set (lineNext s nn) → n ≤ M := by
  intro hs hEvenS hEvenM hBound hnn hn
  exact lineNext_max_le_lm n ⟨hs, hEvenS, hEvenM, hBound, hnn, hn⟩

theorem lineNext_maxList_le {s : List Nat} {nn n : Nat} :
    s ≠ [] → allEven s → 2 * nn ≤ maxList s → n ∈ set (lineNext s nn) →
      n ≤ maxList s := by
  intro hs hEvenS hnn hn
  apply lineNext_max_le (s := s) (M := maxList s) (nn := nn)
  · exact hs
  · exact hEvenS
  · exact allEven_maxList hEvenS
  · intro m hm
    exact maxList_max _ hm
  · exact hnn
  · exact hn

/- line min <= -/

theorem lineNext_min_le_lm {s : List Nat} {M nn : Nat} :
    ∀ n,
      (s ≠ [] ∧ allEven s ∧ Even M ∧ (∀ m ∈ set s, M ≤ m) ∧ M ≤ 2 * nn ∧
        n ∈ set (lineNext s nn)) →
      M ≤ n := by
  intro n h
  rcases h with ⟨hs, hEvenS, hEvenM, hBound, hnn, hn⟩
  rcases (in_set_nth).1 hn with ⟨i, hi, rfl⟩
  have hiS : i < s.length := by simpa using hi
  by_cases hlast : Nat.succ i = s.length
  · rw [nth_lineNext_last hs hlast]
    have hsi : M ≤ nth s i := le_nth_of_forall hBound hiS
    have hsiEven : Even (nth s i) := allEven_nth hEvenS hiS
    have hInner : M ≤ nth s i / 2 + nn := by
      rcases even_EX.mp hEvenM with ⟨mM, hM⟩
      rcases even_EX.mp hsiEven with ⟨mi, hi'⟩
      rw [hM, hi']
      omega
    exact even_fill_le hInner
  · have hi1 : Nat.succ i < s.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hiS) hlast
    rw [nth_lineNext_lt_succ hs hi1]
    have hsi : M ≤ nth s i := le_nth_of_forall hBound hiS
    have hsj : M ≤ nth s (Nat.succ i) := le_nth_of_forall hBound hi1
    have hsiEven : Even (nth s i) := allEven_nth hEvenS hiS
    have hsjEven : Even (nth s (Nat.succ i)) := allEven_nth hEvenS hi1
    have hInner : M ≤ nth s i / 2 + nth s (Nat.succ i) / 2 := by
      rcases even_EX.mp hEvenM with ⟨mM, hM⟩
      rcases even_EX.mp hsiEven with ⟨mi, hi'⟩
      rcases even_EX.mp hsjEven with ⟨mj, hj'⟩
      rw [hM, hi', hj']
      omega
    exact even_fill_le hInner

theorem lineNext_min_le {s : List Nat} {M nn n : Nat} :
    s ≠ [] → allEven s → Even M → (∀ m ∈ set s, M ≤ m) → M ≤ 2 * nn →
      n ∈ set (lineNext s nn) → M ≤ n := by
  intro hs hEvenS hEvenM hBound hnn hn
  exact lineNext_min_le_lm n ⟨hs, hEvenS, hEvenM, hBound, hnn, hn⟩

theorem lineNext_minList_le {s : List Nat} {nn n : Nat} :
    s ≠ [] → allEven s → minList s ≤ 2 * nn → n ∈ set (lineNext s nn) →
      minList s ≤ n := by
  intro hs hEvenS hnn hn
  apply lineNext_min_le (s := s) (M := minList s) (nn := nn)
  · exact hs
  · exact hEvenS
  · exact allEven_minList hEvenS
  · intro m hm
    exact minList_min _ hm
  · exact hnn
  · exact hn

/- line min < -/

theorem lineNext_min_less_lm {s : List Nat} {M nn : Nat} :
    ∀ i,
      (s ≠ [] ∧ allEven s ∧ Even M ∧ (∀ n ∈ set s, M ≤ n) ∧ M ≤ 2 * nn ∧
        Nat.succ i < s.length ∧ nth s i = M ∧ M < nth s (Nat.succ i)) →
      M < nth (lineNext s nn) i := by
  intro i h
  rcases h with ⟨hs, hEvenS, hEvenM, hBound, hnn, hi1, hiEq, hlt⟩
  rw [nth_lineNext_lt_succ hs hi1, hiEq]
  have hsjEven : Even (nth s (Nat.succ i)) := allEven_nth hEvenS hi1
  have hInner : M < M / 2 + nth s (Nat.succ i) / 2 := by
    rcases even_EX.mp hEvenM with ⟨mM, hM⟩
    rcases even_EX.mp hsjEven with ⟨mj, hj'⟩
    rw [hM, hj'] at hlt ⊢
    omega
  exact (even_fill_less (n := M) (m := M / 2 + nth s (Nat.succ i) / 2) hEvenM).2 hInner

theorem lineNext_min_less {s : List Nat} {M nn i : Nat} :
    s ≠ [] → allEven s → Even M → (∀ n ∈ set s, M ≤ n) → M ≤ 2 * nn →
      Nat.succ i < s.length → nth s i = M → M < nth s (Nat.succ i) →
      M < nth (lineNext s nn) i := by
  intro hs hEvenS hEvenM hBound hnn hi1 hiEq hlt
  exact lineNext_min_less_lm i ⟨hs, hEvenS, hEvenM, hBound, hnn, hi1, hiEq, hlt⟩

theorem lineNext_minList_less {s : List Nat} {nn i : Nat} :
    s ≠ [] → allEven s → minList s ≤ 2 * nn → Nat.succ i < s.length →
      nth s i = minList s → minList s < nth s (Nat.succ i) →
      minList s < nth (lineNext s nn) i := by
  intro hs hEvenS hnn hi1 hiEq hlt
  apply lineNext_min_less (s := s) (M := minList s) (nn := nn) (i := i)
  · exact hs
  · exact hEvenS
  · exact allEven_minList hEvenS
  · intro n hn
    exact minList_min _ hn
  · exact hnn
  · exact hi1
  · exact hiEq
  · exact hlt

/- last -/

theorem lineNext_min_less_last_sublm {s : List Nat} {a : Nat} :
    s ≠ [] ∧ last s < a → last s < last (lineNext s a) := by
  rintro ⟨hs, hlt⟩
  rw [last_lineNext hs]
  have hInner : last s < last s / 2 + a := by
    omega
  exact lt_of_lt_of_le hInner self_le_fill

theorem lineNext_min_less_last_lm {s : List Nat} {M nn : Nat} :
    (s ≠ [] ∧ allEven s ∧ (∀ n ∈ set s, M ≤ n) ∧ M = last s ∧ M < 2 * nn) →
      last s < last (lineNext s nn) := by
  rintro ⟨hs, hEvenS, _, hLast, hlt⟩
  have hmem : last s ∈ set s := by
    rcases minList_exist_nth (s := s) hs with ⟨i, hi, _⟩
    have hiLast : nth s (s.length - 1) = last s := by
      have hEq : Nat.succ (s.length - 1) = s.length := by
        have hlen : 0 < s.length := by
          cases s with
          | nil => cases hs rfl
          | cons a t => simp
        omega
      exact nth_last (s := s) (i := s.length - 1) hEq
    have hnth : nth s (s.length - 1) ∈ set s := by
      have hlen : s.length - 1 < s.length := by
        have : 0 < s.length := by
          cases s with
          | nil => cases hs rfl
          | cons a t => simp
        omega
      exact (in_set_nth).2 ⟨s.length - 1, hlen, rfl⟩
    simpa [hiLast] using hnth
  have hEvenLast : Even (last s) := hEvenS _ hmem
  have hlt' : last s < 2 * nn := by
    simpa [hLast] using hlt
  have hInner : last s < last s / 2 + nn := by
    rcases even_EX.mp hEvenLast with ⟨m, hm⟩
    rw [hm] at hlt' ⊢
    omega
  have hFill : last s < fill (last s / 2 + nn) :=
    (even_fill_less (n := last s) (m := last s / 2 + nn) hEvenLast).2 hInner
  rw [last_lineNext hs]
  exact hFill

theorem lineNext_min_less_last {s : List Nat} {M nn : Nat} :
    s ≠ [] → allEven s → (∀ n ∈ set s, M ≤ n) → last s = M → M < 2 * nn →
      M < last (lineNext s nn) := by
  intro hs hEvenS hBound hLast hlt
  have h := lineNext_min_less_last_lm (s := s) (M := M) (nn := nn)
    ⟨hs, hEvenS, hBound, hLast.symm, hlt⟩
  rw [← hLast]
  exact h

theorem lineNext_minList_less_last {s : List Nat} {nn : Nat} :
    s ≠ [] → allEven s → last s = minList s → minList s < 2 * nn →
      minList s < last (lineNext s nn) := by
  intro hs hEvenS hLast hlt
  apply lineNext_min_less_last (s := s) (M := minList s) (nn := nn)
  · exact hs
  · exact hEvenS
  · intro n hn
    exact minList_min _ hn
  · exact hLast
  · exact hlt

/- other less -/

theorem lineNext_min_other_less_lm {s : List Nat} {M nn : Nat} :
    ∀ i,
      (s ≠ [] ∧ allEven s ∧ Even M ∧ (∀ n ∈ set s, M ≤ n) ∧ M ≤ 2 * nn ∧
        i < s.length ∧ M < nth s i) →
      M < nth (lineNext s nn) i := by
  intro i h
  rcases h with ⟨hs, hEvenS, hEvenM, hBound, hnn, hi, hlt⟩
  by_cases hlast : Nat.succ i = s.length
  · rw [nth_lineNext_last hs hlast]
    have hsiEven : Even (nth s i) := allEven_nth hEvenS hi
    have hInner : M < nth s i / 2 + nn := by
      rcases even_EX.mp hEvenM with ⟨mM, hM⟩
      rcases even_EX.mp hsiEven with ⟨mi, hi'⟩
      rw [hM, hi'] at hlt ⊢
      omega
    exact (even_fill_less (n := M) (m := nth s i / 2 + nn) hEvenM).2 hInner
  · have hi1 : Nat.succ i < s.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hi) hlast
    rw [nth_lineNext_lt_succ hs hi1]
    have hsj : M ≤ nth s (Nat.succ i) := le_nth_of_forall hBound hi1
    have hsiEven : Even (nth s i) := allEven_nth hEvenS hi
    have hsjEven : Even (nth s (Nat.succ i)) := allEven_nth hEvenS hi1
    have hInner : M < nth s i / 2 + nth s (Nat.succ i) / 2 := by
      rcases even_EX.mp hEvenM with ⟨mM, hM⟩
      rcases even_EX.mp hsiEven with ⟨mi, hi'⟩
      rcases even_EX.mp hsjEven with ⟨mj, hj'⟩
      have hlt' : 2 * mM < 2 * mi := by simpa [hM, hi'] using hlt
      have hsj' : 2 * mM ≤ 2 * mj := by simpa [hM, hj'] using hsj
      rw [hM, hi', hj']
      omega
    exact (even_fill_less (n := M) (m := nth s i / 2 + nth s (Nat.succ i) / 2) hEvenM).2
      hInner

theorem lineNext_min_other_less {s : List Nat} {M nn i : Nat} :
    s ≠ [] → allEven s → Even M → (∀ n ∈ set s, M ≤ n) → M ≤ 2 * nn →
      i < s.length → M < nth s i → M < nth (lineNext s nn) i := by
  intro hs hEvenS hEvenM hBound hnn hi hlt
  exact lineNext_min_other_less_lm i ⟨hs, hEvenS, hEvenM, hBound, hnn, hi, hlt⟩

theorem lineNext_minList_other_less {s : List Nat} {nn i : Nat} :
    s ≠ [] → allEven s → minList s ≤ 2 * nn → i < s.length →
      minList s < nth s i → minList s < nth (lineNext s nn) i := by
  intro hs hEvenS hnn hi hlt
  apply lineNext_min_other_less (s := s) (M := minList s) (nn := nn) (i := i)
  · exact hs
  · exact hEvenS
  · exact allEven_minList hEvenS
  · intro n hn
    exact minList_min _ hn
  · exact hnn
  · exact hi
  · exact hlt

/- ------------------------------------------------- *
              lemmas on circ, min and max
 * ------------------------------------------------- -/

/- max le -/

theorem circNext_maxList_le {s : List Nat} {n : Nat} :
    s ≠ [] → allEven s → n ∈ set (circNext s) → n ≤ maxList s := by
  intro hs hEvenS hn
  simp [circNext, hs] at hn
  apply lineNext_maxList_le (s := s) (nn := hd s / 2)
  · exact hs
  · exact hEvenS
  · rw [allEven_div hs hEvenS]
    exact maxList_max _ (hd_in_list hs)
  · exact hn

theorem maxList_circNext_le {s : List Nat} :
    s ≠ [] → allEven s → maxList (circNext s) ≤ maxList s := by
  intro hs hEvenS
  rw [maxList_le_forall]
  intro n hn
  exact circNext_maxList_le hs hEvenS hn

/- min le -/

theorem circNext_minList_le {s : List Nat} {n : Nat} :
    s ≠ [] → allEven s → n ∈ set (circNext s) → minList s ≤ n := by
  intro hs hEvenS hn
  simp [circNext, hs] at hn
  apply lineNext_minList_le (s := s) (nn := hd s / 2)
  · exact hs
  · exact hEvenS
  · rw [allEven_div hs hEvenS]
    exact minList_min _ (hd_in_list hs)
  · exact hn

theorem minList_circNext_le {s : List Nat} :
    s ≠ [] → allEven s → minList s ≤ minList (circNext s) := by
  intro hs hEvenS
  by_cases hnil : circNext s = []
  · simpa [circNext_nil_iff.mp hnil]
  · exact (minList_le_forall (t := circNext s) (m := minList s) hnil).2
      (fun n hn => circNext_minList_le hs hEvenS hn)

/- min less -/

theorem circNext_minList_less {s : List Nat} {i : Nat} :
    s ≠ [] → allEven s → i < s.length → nth s i = minList s →
      ((Nat.succ i = s.length ∧ minList s < hd s) ∨
        (Nat.succ i < s.length ∧ minList s < nth s (Nat.succ i))) →
      minList s < nth (circNext s) i := by
  intro hs hEvenS hi hiEq hCase
  simp [circNext, hs]
  rcases hCase with ⟨hiLast, hhd⟩ | ⟨hi1, hnext⟩
  · have hlastEq : last s = minList s := by
      symm
      rw [← nth_last (s := s) (i := i) hiLast]
      exact hiEq.symm
    have hLastLt : minList s < last (lineNext s (hd s / 2)) := by
      apply lineNext_minList_less_last (s := s) (nn := hd s / 2)
      · exact hs
      · exact hEvenS
      · exact hlastEq
      · rw [allEven_div hs hEvenS]
        exact hhd
    simpa [nth_last (s := lineNext s (hd s / 2)) (i := i) (by simpa using hiLast)] using hLastLt
  · apply lineNext_minList_less (s := s) (nn := hd s / 2) (i := i)
    · exact hs
    · exact hEvenS
    · rw [allEven_div hs hEvenS]
      exact minList_min _ (hd_in_list hs)
    · exact hi1
    · exact hiEq
    · exact hnext

theorem circNext_minList_other_less {s : List Nat} {i : Nat} :
    s ≠ [] → allEven s → i < s.length → minList s < nth s i →
      minList s < nth (circNext s) i := by
  intro hs hEvenS hi hlt
  simp [circNext, hs]
  apply lineNext_minList_other_less (s := s) (nn := hd s / 2) (i := i)
  · exact hs
  · exact hEvenS
  · rw [allEven_div hs hEvenS]
    exact minList_min _ (hd_in_list hs)
  · exact hi
  · exact hlt

/- ------------------------------------------------- *
            lemmas on circNexts, min, and max
 * ------------------------------------------------- -/

theorem maxList_circNexts_le_lm {N : Nat} :
    ∀ s : List Nat, (s ≠ [] ∧ allEven s) → maxList (circNexts N s) ≤ maxList s := by
  intro s hs
  induction N generalizing s with
  | zero =>
      simp [circNexts]
  | succ N ih =>
      rcases hs with ⟨hne, hEven⟩
      have h1 : maxList (circNexts N (circNext s)) ≤ maxList (circNext s) := by
        apply ih (circNext s)
        have hCircNe : circNext s ≠ [] := by
          intro hnil
          exact hne ((circNext_nil_iff (s := s)).mp hnil)
        exact ⟨hCircNe, circNext_even (s := s)⟩
      exact le_trans h1 (maxList_circNext_le hne hEven)

theorem maxList_circNexts_le {N : Nat} {s : List Nat} :
    s ≠ [] → allEven s → maxList (circNexts N s) ≤ maxList s := by
  intro hs hEvenS
  exact maxList_circNexts_le_lm (N := N) s ⟨hs, hEvenS⟩

theorem minList_circNexts_le_lm {N : Nat} :
    ∀ s : List Nat, (s ≠ [] ∧ allEven s) → minList s ≤ minList (circNexts N s) := by
  intro s hs
  induction N generalizing s with
  | zero =>
      simp [circNexts]
  | succ N ih =>
      rcases hs with ⟨hne, hEven⟩
      have h1 : minList (circNext s) ≤ minList (circNexts N (circNext s)) := by
        apply ih (circNext s)
        have hCircNe : circNext s ≠ [] := by
          intro hnil
          exact hne ((circNext_nil_iff (s := s)).mp hnil)
        exact ⟨hCircNe, circNext_even (s := s)⟩
      exact le_trans (minList_circNext_le hne hEven) h1

theorem minList_circNexts_le {N : Nat} {s : List Nat} :
    s ≠ [] → allEven s → minList s ≤ minList (circNexts N s) := by
  intro hs hEvenS
  exact minList_circNexts_le_lm (N := N) s ⟨hs, hEvenS⟩

/- ----------------------------------------------------------- *
           to get the assumption of circ_minList_less
 * ----------------------------------------------------------- -/

theorem unstable_exists_diff_one_lm {s : List Nat} :
    ∀ j,
      (j < s.length ∧ minList s < nth s j) →
        ∃ i,
          i < s.length ∧ nth s i = minList s ∧
            ((Nat.succ i = s.length ∧ minList s < hd s) ∨
              (Nat.succ i < s.length ∧ minList s < nth s (Nat.succ i))) := by
  intro j hj
  have hs : s ≠ [] := by
    intro hnil
    simp [hnil] at hj
  let P : Nat → Prop := fun k => k < s.length ∧ minList s < nth s k
  have hP : ∃ k, P k := ⟨j, hj⟩
  let k := Nat.find hP
  have hk : P k := Nat.find_spec hP
  have hkleast : ∀ n, n < k → ¬ P n := by
    intro n hn hPn
    have hle : k ≤ n := Nat.find_min' hP hPn
    exact (Nat.not_le_of_gt hn) hle
  cases Nat.eq_zero_or_pos k with
  | inl hk0 =>
      have hkZero : k = 0 := hk0
      rcases minList_exist_nth (s := s) hs with ⟨i0, hi0, hi0Eq⟩
      let Q : Nat → Prop := fun i => i < s.length ∧ nth s i = minList s
      let i := Nat.findGreatest Q (s.length - 1)
      have hi0Bound : i0 ≤ s.length - 1 := by
        omega
      have hQi : Q i := Nat.findGreatest_spec hi0Bound ⟨hi0, hi0Eq⟩
      refine ⟨i, hQi.1, hQi.2, ?_⟩
      have hhd : minList s < hd s := by
        have : minList s < nth s 0 := by simpa [hkZero] using hk.2
        simpa [nth_hd hs] using this
      by_cases hiLast : Nat.succ i = s.length
      · exact Or.inl ⟨hiLast, hhd⟩
      · have hi1 : Nat.succ i < s.length := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hQi.1) hiLast
        have hminLe : minList s ≤ nth s (Nat.succ i) := maxList_min_nth (s := s) (i := Nat.succ i) hi1
        have hlt : minList s < nth s (Nat.succ i) := by
          by_contra hnot
          have hEq : nth s (Nat.succ i) = minList s := by
            exact Nat.le_antisymm (Nat.not_lt.mp hnot) hminLe
          have hQsucc : Q (Nat.succ i) := ⟨hi1, hEq⟩
          have hiBound : Nat.succ i ≤ s.length - 1 := by
            omega
          have hcontra :
              ¬ Q (Nat.succ i) := Nat.findGreatest_is_greatest
                (P := Q) (n := s.length - 1) (k := Nat.succ i) (by
                  simpa [i] using Nat.lt_succ_self i) hiBound
          exact hcontra hQsucc
        exact Or.inr ⟨hi1, hlt⟩
  | inr hkpos =>
      have hprev : k - 1 < s.length := by
        omega
      have hnot : ¬ P (k - 1) := hkleast (k - 1) (by omega)
      have hEqPrev : nth s (k - 1) = minList s := by
        have hle : minList s ≤ nth s (k - 1) := maxList_min_nth (s := s) (i := k - 1) hprev
        have hge : nth s (k - 1) ≤ minList s := by
          by_contra hgt
          exact hnot ⟨hprev, lt_of_not_ge hgt⟩
        exact Nat.le_antisymm hge hle
      refine ⟨k - 1, hprev, hEqPrev, ?_⟩
      refine Or.inr ⟨by omega, ?_⟩
      have hkStep : Nat.succ (k - 1) = k := by omega
      have hk2 : minList s < nth s (Nat.succ (k - 1)) := by
        rw [hkStep]
        exact hk.2
      simpa [Nat.succ_eq_add_one] using hk2

theorem unstable_exists_diff_one {s : List Nat} {j : Nat} :
    j < s.length → minList s < nth s j →
      ∃ i,
        i < s.length ∧ nth s i = minList s ∧
          ((Nat.succ i = s.length ∧ minList s < hd s) ∨
            (Nat.succ i < s.length ∧ minList s < nth s (Nat.succ i))) := by
  intro hj hlt
  exact unstable_exists_diff_one_lm j ⟨hj, hlt⟩

/- --- to increase the minList --- -/

theorem unstable_circNext_minList_less {s : List Nat} {j : Nat} :
    s ≠ [] → allEven s → j < s.length → minList s < nth s j →
      ∃ i, i < s.length ∧ nth s i = minList s ∧ minList s < nth (circNext s) i := by
  intro hs hEvenS hj hlt
  rcases unstable_exists_diff_one hj hlt with ⟨i, hi, hiEq, hCase⟩
  exact ⟨i, hi, hiEq, circNext_minList_less hs hEvenS hi hiEq hCase⟩

/- ----------------------------------------------------------- *
                to decrease howMany (minList s)
 * ----------------------------------------------------------- -/

theorem Suc_length_list_EX {s t : List α} :
    Nat.succ s.length = t.length ↔ ∃ b u, t = b :: u ∧ s.length = u.length := by
  cases t with
  | nil =>
      simp
  | cons b u =>
      simp

/- howMany <= -/

theorem howMany_le_lm {M : Nat} :
    ∀ s t (j : Nat),
      (s.length = t.length ∧ (∀ i, (i < t.length ∧ M ≠ nth s i) → M ≠ nth t i)) →
        howMany M t ≤ howMany M s := by
  intro s
  induction s with
  | nil =>
      intro t j h
      cases t with
      | nil =>
          simp [howMany]
      | cons b u =>
          rcases h with ⟨hlen, _⟩
          simp at hlen
  | cons a s ih =>
      intro t j h
      cases t with
      | nil =>
          rcases h with ⟨hlen, _⟩
          simp at hlen
      | cons b u =>
          rcases h with ⟨hlen, hprop⟩
          have hlen' : s.length = u.length := by simpa using hlen
          have hprop' : ∀ i, (i < u.length ∧ M ≠ nth s i) → M ≠ nth u i := by
            intro i hi
            have h0 : Nat.succ i < (b :: u).length ∧ M ≠ nth (a :: s) (Nat.succ i) := by
              simpa [nth_cons_succ] using hi
            simpa [nth_cons_succ] using hprop (Nat.succ i) h0
          have ih' := ih u j ⟨hlen', hprop'⟩
          by_cases ha : M = a
          · by_cases hb : M = b
            · have hab : a = b := ha.symm.trans hb
              simpa [howMany, ha, hab] using Nat.succ_le_succ ih'
            · have hab : a ≠ b := by
                intro hab
                exact hb (ha.trans hab)
              simpa [howMany, ha, hab] using Nat.le_succ_of_le ih'
          · have hb : M ≠ b := by
              apply hprop 0
              simp [ha]
            simp [howMany, ha, hb, ih']

theorem howMany_le {M : Nat} {s t : List Nat} :
    s.length = t.length →
      (∀ i, i < t.length → M ≠ nth s i → M ≠ nth t i) →
      howMany M t ≤ howMany M s := by
  intro hlen hprop
  apply howMany_le_lm (M := M) s t 0
  refine ⟨hlen, ?_⟩
  intro i hi
  exact hprop i hi.1 hi.2

/- howMany < -/

theorem howMany_less_lm {M : Nat} :
    ∀ s t (j : Nat),
      (s.length = t.length ∧
        (∀ i, (i < t.length ∧ M ≠ nth s i) → M ≠ nth t i) ∧
        j < t.length ∧ nth s j = M ∧ M < nth t j) →
      howMany M t < howMany M s := by
  intro s
  induction s with
  | nil =>
      intro t j h
      rcases h with ⟨hlen, _, hj, _, _⟩
      cases t with
      | nil =>
          simp at hj
      | cons b u =>
          simp at hlen
  | cons a s ih =>
      intro t j h
      cases t with
      | nil =>
          rcases h with ⟨hlen, _, _, _, _⟩
          simp at hlen
      | cons b u =>
          rcases h with ⟨hlen, hprop, hj, hjEq, hjLt⟩
          cases j with
          | zero =>
              have ha : M = a := by simpa using hjEq.symm
              have hb : M ≠ b := by
                intro hb
                have : M < M := by simpa [hb] using hjLt
                exact lt_irrefl _ this
              have hab : a ≠ b := by
                intro hab
                exact hb (ha.trans hab)
              have hTail : howMany M u ≤ howMany M s := by
                apply howMany_le (M := M)
                · simpa using hlen
                · intro i hi hiNe
                  have h0 : Nat.succ i < (b :: u).length := by simpa using hi
                  have hs : M ≠ nth (M :: s) (Nat.succ i) := by simpa [nth_cons_succ] using hiNe
                  have ht : M ≠ nth (b :: u) (Nat.succ i) := hprop (Nat.succ i) ⟨h0, hs⟩
                  simpa [nth_cons_succ] using ht
              have hltTail : howMany M u < Nat.succ (howMany M s) :=
                lt_of_le_of_lt hTail (Nat.lt_succ_self _)
              simpa [howMany, ha, hab] using hltTail
          | succ j =>
              have hlen' : s.length = u.length := by simpa using hlen
              have hprop' : ∀ i, (i < u.length ∧ M ≠ nth s i) → M ≠ nth u i := by
                intro i hi
                have h0 : Nat.succ i < (b :: u).length ∧ M ≠ nth (a :: s) (Nat.succ i) := by
                  simpa [nth_cons_succ] using hi
                simpa [nth_cons_succ] using hprop (Nat.succ i) h0
              have hj' : j < u.length := by simpa using hj
              have hjEq' : nth s j = M := by simpa [nth_cons_succ] using hjEq
              have hjLt' : M < nth u j := by simpa [nth_cons_succ] using hjLt
              have ih' := ih u j ⟨hlen', hprop', hj', hjEq', hjLt'⟩
              by_cases ha : M = a
              · by_cases hb : M = b
                · have hab : a = b := ha.symm.trans hb
                  simpa [howMany, ha, hab] using Nat.succ_lt_succ ih'
                · have hltTail : howMany M u < Nat.succ (howMany M s) :=
                    lt_trans ih' (Nat.lt_succ_self _)
                  have hab : a ≠ b := by
                    intro hab
                    exact hb (ha.trans hab)
                  simpa [howMany, ha, hab] using hltTail
              · have hb : M ≠ b := by
                  apply hprop 0
                  simp [ha]
                simpa [howMany, ha, hb] using ih'

theorem howMany_less {M : Nat} {s t : List Nat} :
    s.length = t.length →
      (∀ i, (i < t.length ∧ M ≠ nth s i) → M ≠ nth t i) →
      (∃ j, j < t.length ∧ nth s j = M ∧ M < nth t j) →
      howMany M t < howMany M s := by
  intro hlen hprop
  rintro ⟨j, hj, hjEq, hjLt⟩
  exact howMany_less_lm (M := M) s t j ⟨hlen, hprop, hj, hjEq, hjLt⟩

/- howMany circNext -/

theorem howMany_circNext_less {s : List Nat} {j : Nat} :
    s ≠ [] → allEven s → j < s.length → minList s < nth s j →
      howMany (minList s) (circNext s) < howMany (minList s) s := by
  intro hs hEvenS hj hlt
  apply howMany_less (M := minList s) (s := s) (t := circNext s)
  · simp
  · intro i hi
    rcases hi with ⟨hi, hiNe⟩
    have hiS : i < s.length := by simpa using hi
    have hlt' : minList s < nth (circNext s) i := by
      apply circNext_minList_other_less hs hEvenS hiS
      exact lt_of_le_of_ne (maxList_min_nth (s := s) (i := i) hiS) hiNe
    exact ne_of_lt hlt'
  · rcases unstable_circNext_minList_less hs hEvenS hj hlt with ⟨i, hi, hiEq, hiLt⟩
    exact ⟨i, by simpa using hi, hiEq, hiLt⟩

/- ----------------------------------------------------------- *
                     to increase minList
 * ----------------------------------------------------------- -/

theorem minList_circNext_less_lm {i : Nat} :
    ∀ k s,
      (s ≠ [] ∧ allEven s ∧ i < s.length ∧ minList s < nth s i ∧
        howMany (minList s) s ≤ k) →
      ∃ N, minList s < minList (circNexts N s) := by
  intro k
  induction k with
  | zero =>
      intro s h
      rcases h with ⟨hs, _, _, _, hCount⟩
      have hzero : howMany (minList s) s = 0 := Nat.eq_zero_of_le_zero hCount
      have hNo := (howMany_zero (m := minList s) (s := s)).1 hzero
      exact False.elim (hNo _ (minList_exist hs) rfl)
  | succ k ih =>
      intro s h
      rcases h with ⟨hs, hEvenS, hi, hlt, hCount⟩
      by_cases hEq : minList (circNext s) = minList s
      · have hHow : howMany (minList s) (circNext s) ≤ k := by
          have hltHow : howMany (minList s) (circNext s) < howMany (minList s) s :=
            howMany_circNext_less hs hEvenS hi hlt
          omega
        have hNextLt : minList (circNext s) < nth (circNext s) i := by
          simpa [hEq] using circNext_minList_other_less hs hEvenS hi hlt
        have hCircNe : circNext s ≠ [] := by
          intro hnil
          exact hs ((circNext_nil_iff (s := s)).mp hnil)
        rcases ih (circNext s) ⟨hCircNe, circNext_even (s := s), by simpa, hNextLt,
            by simpa [hEq] using hHow⟩ with ⟨N, hN⟩
        refine ⟨Nat.succ N, ?_⟩
        simpa [circNexts, hEq] using hN
      · refine ⟨1, ?_⟩
        have hle : minList s ≤ minList (circNext s) := minList_circNext_le hs hEvenS
        exact lt_of_le_of_ne hle (Ne.symm hEq)

theorem minList_circNext_less {s : List Nat} {i : Nat} :
    s ≠ [] → allEven s → i < s.length → minList s < nth s i →
      ∃ N, minList s < minList (circNexts N s) := by
  intro hs hEvenS hi hlt
  exact minList_circNext_less_lm (i := i) (howMany (minList s) s) s
    ⟨hs, hEvenS, hi, hlt, le_rfl⟩

/- ----------------------------------------------------------- *
                    eventually stable
 * ----------------------------------------------------------- -/

theorem circNexts_eventually_stable_lm :
    ∀ k s i,
      (s ≠ [] ∧ allEven s ∧ i < s.length ∧ minList s < nth s i ∧
        maxList s ≤ minList s + k) →
      ∃ N, stableList (circNexts N s) := by
  intro k
  induction k with
  | zero =>
      intro s i h
      rcases h with ⟨_, _, _, _, hMax⟩
      refine ⟨0, ?_⟩
      apply (stable_min_max (s := s)).2
      apply le_antisymm
      · exact minList_le_maxList
      · omega
  | succ k ih =>
      intro s i h
      rcases h with ⟨hs, hEvenS, hi, hlt, hMax⟩
      rcases minList_circNext_less hs hEvenS hi hlt with ⟨N, hMin⟩
      by_cases hUnstable : ∃ j, j < s.length ∧ minList (circNexts N s) < nth (circNexts N s) j
      · rcases hUnstable with ⟨j, hj, hjLt⟩
        have hEvenN : allEven (circNexts N s) := circNexts_even (N := N) hEvenS
        have hMaxN : maxList (circNexts N s) ≤ minList (circNexts N s) + k := by
          have h1 : maxList (circNexts N s) ≤ maxList s := maxList_circNexts_le hs hEvenS
          omega
        have hNeN : circNexts N s ≠ [] := by
          intro hnil
          exact hs ((circNexts_nil_iff (N := N) s).mp hnil)
        rcases ih (circNexts N s) j
            ⟨hNeN, hEvenN, by simpa using hj, hjLt, hMaxN⟩ with ⟨N2, hStable⟩
        refine ⟨N2 + N, ?_⟩
        simpa [circNexts_sum] using hStable
      · refine ⟨N, ?_⟩
        apply (stable_min_max (s := circNexts N s)).2
        apply le_antisymm
        · exact minList_le_maxList
        · rw [maxList_le_forall]
          intro n hn
          rcases (in_set_nth).1 hn with ⟨j, hj, rfl⟩
          have hle : nth (circNexts N s) j ≤ minList (circNexts N s) := by
            by_contra hgt
            exact hUnstable ⟨j, by simpa using hj, lt_of_not_ge hgt⟩
          simpa using hle

theorem circNexts_eventually_stable {s : List Nat} :
    s ≠ [] → allEven s → ∃ N, stableList (circNexts N s) := by
  intro hs hEvenS
  by_cases hStableIdx : ∀ i, i < s.length → minList s = nth s i
  · refine ⟨0, ?_⟩
    apply (stable_min_max (s := s)).2
    apply le_antisymm
    · exact minList_le_maxList
    · rw [maxList_le_forall]
      intro n hn
      rcases (in_set_nth).1 hn with ⟨i, hi, rfl⟩
      simpa [hStableIdx i hi]
  · have hUnstable : ∃ i, i < s.length ∧ minList s < nth s i := by
      push_neg at hStableIdx
      rcases hStableIdx with ⟨i, hi, hne⟩
      have hle : minList s ≤ nth s i := maxList_min_nth (s := s) (i := i) hi
      exact ⟨i, hi, lt_of_le_of_ne hle hne⟩
    rcases hUnstable with ⟨i, hi, hlt⟩
    exact circNexts_eventually_stable_lm (maxList s - minList s) s i
      ⟨hs, hEvenS, hi, hlt, by omega⟩
