           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Compat
import LeanCspProver.CSP.Infra_nat

/-
(*****************************************************
               Small lemmas for List
 *****************************************************)
-/

/- *** list of the empty set *** -/

def Emptyset_list : Nat → List (Set α)
  | 0 => []
  | n + 1 => ∅ :: Emptyset_list n

theorem not_emptyset_EX {A : Set α} : A ≠ ∅ ↔ ∃ a, a ∈ A := by
  constructor
  · intro h
    by_contra hEx
    apply h
    ext a
    constructor
    · intro ha
      exact False.elim (hEx ⟨a, ha⟩)
    · intro ha
      exact False.elim ha
  · rintro ⟨a, ha⟩ h
    simp [h] at ha

theorem one_list_decompo {a : α} {s t : List α} :
    ([a] = s ++ t) ↔ ((s = [] ∧ t = [a]) ∨ (s = [a] ∧ t = [])) := by
  cases s <;> cases t <;> simp [eq_comm]

theorem list_nil_or_unnil : ∀ t : List α, t = [] ∨ ∃ a s, t = a :: s
  | [] => Or.inl rfl
  | a :: s => Or.inr ⟨a, s, rfl⟩

theorem list_last_nil_or_unnil : ∀ t : List α, t = [] ∨ ∃ s a, t = s ++ [a] := by
  intro t
  induction t using List.reverseRecOn with
  | nil =>
      exact Or.inl rfl
  | append_singleton s a _ =>
      exact Or.inr ⟨s, a, rfl⟩

/- *** unnil *** -/

theorem unnil_ex_ALL : ∀ s : List α, s ≠ [] → ∃ a, a ∈ set s
  | [], h => False.elim (h rfl)
  | a :: _, _ => ⟨a, by simp [_root_.set]⟩

theorem unnil_ex {s : List α} : s ≠ [] → ∃ a, a ∈ set s :=
  unnil_ex_ALL s

/- *** nil *** -/

theorem emptyset_to_nil {t : List α} : ((∅ : Set α) = set t) ↔ t = [] := by
  cases t with
  | nil =>
      simp [_root_.set]
  | cons a t =>
      constructor
      · intro h
        have : a ∈ (∅ : Set α) := by
          simpa [h] using (show a ∈ _root_.set (a :: t) from by simp [_root_.set])
        simp at this
      · intro h
        cases h

theorem nil_to_emptyset {X : Set α} : (X = set ([] : List α)) ↔ X = ∅ := by
  simp [_root_.set]

/- ***** butlast ***** -/

private theorem butlast_subseteq_aux {s : List α} : set (butlast s) ⊆ set s := by
  intro x hx
  simpa [_root_.set, butlast] using List.mem_of_mem_dropLast hx

theorem notin_butlast_decompo {e : α} {s t : List α} :
    (e ∉ set (butlast (s ++ t))) ↔
      ((e ∉ set s ∧ e ∉ set (butlast t)) ∨ (e ∉ set (butlast s) ∧ t = [])) := by
  rcases list_last_nil_or_unnil t with rfl | ⟨u, a, rfl⟩
  · constructor
    · intro h
      exact Or.inr ⟨by simpa using h, rfl⟩
    · intro h
      rcases h with h | h
      · intro hx
        have hx' : e ∈ set (butlast s) := by simpa using hx
        exact h.1 (butlast_subseteq_aux hx')
      · simpa using h.1
  · simp [butlast, _root_.set]

theorem in_butlast_decompo {e : α} {s t : List α} :
    (e ∈ set (butlast (s ++ t))) ↔
      ((e ∈ set s ∨ e ∈ set (butlast t)) ∧ (e ∈ set (butlast s) ∨ t ≠ [])) := by
  rcases list_last_nil_or_unnil t with rfl | ⟨u, a, rfl⟩
  · constructor
    · intro h
      exact ⟨Or.inl (butlast_subseteq_aux (by simpa using h)), Or.inl (by simpa using h)⟩
    · rintro ⟨h1, h2⟩
      exact h2.elim (by simpa using ·) (fun h => False.elim (h rfl))
  · simp [butlast, _root_.set]

theorem butlast_subseteq {s : List α} : set (butlast s) ⊆ set s :=
  butlast_subseteq_aux

/- *** length s = 1 *** -/

theorem list_length_one {s : List α} : (s.length = 1) ↔ ∃ a, s = [a] := by
  cases s with
  | nil => simp
  | cons a s =>
      cases s with
      | nil => simp
      | cons b t => simp

/- ***** list app app ***** -/

/- *** lm *** -/

theorem list_app_app_only_if :
    ∀ s1 s2 t1 t2 : List α,
      s1 ++ s2 = t1 ++ t2 →
        (∃ u, s1 = t1 ++ u ∧ t2 = u ++ s2) ∨
        (∃ u, t1 = s1 ++ u ∧ s2 = u ++ t2)
  | [], s2, t1, t2, h =>
      Or.inr ⟨t1, rfl, by simpa using h⟩
  | a :: s1, s2, [], t2, h =>
      Or.inl ⟨a :: s1, rfl, by simpa using h.symm⟩
  | a :: s1, s2, b :: t1, t2, h => by
      injection h with hEq hTail
      subst hEq
      rcases list_app_app_only_if s1 s2 t1 t2 hTail with h1 | h2
      · rcases h1 with ⟨u, hs1, ht2⟩
        exact Or.inl ⟨u, by simp [hs1], ht2⟩
      · rcases h2 with ⟨u, ht1, hs2⟩
        exact Or.inr ⟨u, by simp [ht1], hs2⟩

/- *** list app app *** -/

theorem list_app_app {s1 s2 t1 t2 : List α} :
    (s1 ++ s2 = t1 ++ t2) ↔
      ((∃ u, s1 = t1 ++ u ∧ t2 = u ++ s2) ∨
       (∃ u, t1 = s1 ++ u ∧ s2 = u ++ t2)) := by
  constructor
  · exact list_app_app_only_if s1 s2 t1 t2
  · rintro (⟨u, hs1, ht2⟩ | ⟨u, ht1, hs2⟩)
    · simp [hs1, ht2]
    · simp [ht1, hs2]

/- *** list app [a] *** -/

theorem list_app_decompo_one {s t : List α} {a : α} :
    (s ++ t = [a]) ↔ ((s = [a] ∧ t = []) ∨ (s = [] ∧ t = [a])) := by
  cases s <;> cases t <;> simp

/- *** map *** -/

theorem divide_map_fst_ALL {α β : Type _} :
    ∀ ss s2 s1,
      List.map Prod.fst (ss : List (α × β)) = s1 ++ s2 →
        ∃ ss1 ss2,
          ss = ss1 ++ ss2 ∧
          List.map Prod.fst ss1 = s1 ∧
          List.map Prod.fst ss2 = s2 := by
  intro ss s2 s1 h
  refine ⟨ss.take s1.length, ss.drop s1.length, (List.take_append_drop s1.length ss).symm, ?_, ?_⟩
  · have hTake := congrArg (List.take s1.length) h
    simpa [List.map_take, List.take_append_of_le_length] using hTake
  · have hDrop := congrArg (List.drop s1.length) h
    simpa [List.map_drop, List.drop_append_of_le_length] using hDrop

theorem divide_map_fst {α β : Type _} {ss : List (α × β)} {s1 : List α} {s2 : List α} :
    List.map Prod.fst ss = s1 ++ s2 →
      ∃ ss1 ss2,
        ss = ss1 ++ ss2 ∧
        List.map Prod.fst ss1 = s1 ∧
        List.map Prod.fst ss2 = s2 :=
  divide_map_fst_ALL ss s2 s1

/- *** zip *** -/

theorem map_fst_zip_eq_lm {α β : Type _} :
    ∀ s : List α, ∀ t : List β, s.length ≤ t.length → List.map Prod.fst (List.zip s t) = s
  | [], _, _ => by simp
  | _ :: _, [], h => False.elim (Nat.not_succ_le_zero _ h)
  | a :: s, b :: t, h => by
      simp at h
      simp [map_fst_zip_eq_lm s t h]

theorem map_fst_zip_eq {α β : Type _} {s : List α} {t : List β} :
    s.length ≤ t.length → List.map Prod.fst (List.zip s t) = s :=
  map_fst_zip_eq_lm s t

theorem fst_set_zip_eq_lm {α β : Type _} :
    ∀ s : List α, ∀ t : List β, s.length ≤ t.length → Prod.fst '' set (List.zip s t) = set s
  | s, t, h => by
      ext x
      constructor
      · intro hx
        have hx' : x ∈ List.map Prod.fst (List.zip s t) := by
          simpa [_root_.set] using hx
        simpa [_root_.set, map_fst_zip_eq_lm s t h] using hx'
      · intro hx
        have hx' : x ∈ List.map Prod.fst (List.zip s t) := by
          simpa [_root_.set, map_fst_zip_eq_lm s t h] using hx
        simpa [_root_.set] using hx'

theorem fst_set_zip_eq {α β : Type _} {s : List α} {t : List β} :
    s.length ≤ t.length → Prod.fst '' set (List.zip s t) = set s :=
  fst_set_zip_eq_lm s t

theorem zip_map_fst_snd {α β : Type _} :
    ∀ s : List (α × β), List.zip (List.map Prod.fst s) (List.map Prod.snd s) = s
  | [] => by simp
  | (a, b) :: s => by
      simp [zip_map_fst_snd s]

theorem set_nth {α : Type _} [Inhabited α] {a : α} {s : List α} :
    (a ∈ set s) ↔ ∃ i, i < s.length ∧ a = nth s i := by
  constructor
  · intro ha
    rcases (List.exists_mem_iff_getElem (l := s) (p := fun x => x = a)).1 ⟨a, ha, rfl⟩ with
      ⟨i, hi, hElem⟩
    refine ⟨i, hi, ?_⟩
    have hNth : nth s i = a := by
      rw [nth, List.getD_eq_getElem (l := s) (d := default) hi]
      exact hElem
    exact hNth.symm
  · rintro ⟨i, hi, ha⟩
    have hNth : nth s i = a := ha.symm
    have hElem : s[i] = a := by
      rw [← List.getD_eq_getElem (l := s) (d := default) hi]
      simpa [nth] using hNth
    rcases (List.exists_mem_iff_getElem (l := s) (p := fun x => x = a)).2 ⟨i, hi, hElem⟩ with
      ⟨x, hx, hxa⟩
    simpa [hxa] using hx

theorem nth_pair_zip_in_ALL {α β : Type _} [Inhabited α] [Inhabited β] :
    ∀ (s : List α) (t : List β) (i : Nat),
      (s.length = t.length ∧ i < t.length) →
        (nth s i, nth t i) ∈ set (List.zip s t)
  | [], [], _, h => False.elim (Nat.not_lt_zero _ h.2)
  | [], _ :: _, _, h => False.elim (by cases h.1)
  | _ :: _, [], _, h => False.elim (by cases h.1)
  | a :: s, b :: t, 0, h => by
      simp [_root_.set]
  | a :: s, b :: t, i + 1, h => by
      have h' : s.length = t.length ∧ i < t.length := by
        exact ⟨Nat.succ.inj h.1, Nat.lt_of_succ_lt_succ h.2⟩
      simpa [_root_.set] using
        (Or.inr (nth_pair_zip_in_ALL (α := α) (β := β) s t i h') :
          (nth s i = a ∧ nth t i = b) ∨ (nth s i, nth t i) ∈ set (List.zip s t))

theorem nth_pair_zip_in {α β : Type _} [Inhabited α] [Inhabited β]
    {s : List α} {t : List β} {i : Nat} :
    s.length = t.length → i < t.length → (nth s i, nth t i) ∈ set (List.zip s t) :=
  fun hlen hi => nth_pair_zip_in_ALL s t i ⟨hlen, hi⟩

/- *** emptyset list *** -/

@[simp]
theorem length_Emptyset_list : ∀ n : Nat, (Emptyset_list (α := α) n).length = n
  | 0 => by simp [Emptyset_list]
  | n + 1 => by simp [Emptyset_list, length_Emptyset_list n]

/-
* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *
-/

/-
* --------------------------------------------------- *
             convenient lemmas for proofs
 * --------------------------------------------------- *
-/

/-
-----------
      list
 * ----------- *
-/

theorem not_nil {s : List α} : (s ≠ []) ↔ ∃ a t, s = a :: t := by
  cases s <;> simp

theorem tl_nil {s : List α} : (tl s = []) ↔ (s = [] ∨ ∃ a, s = [a]) := by
  cases s with
  | nil => simp [tl]
  | cons a s =>
      cases s with
      | nil => simp [tl]
      | cons b t => simp [tl]

theorem tl_not_nil {s : List α} : (tl s ≠ []) ↔ ∃ a1 a2 t, s = a1 :: a2 :: t := by
  cases s with
  | nil => simp [tl]
  | cons a s =>
      cases s with
      | nil => simp [tl]
      | cons b t => simp [tl]
