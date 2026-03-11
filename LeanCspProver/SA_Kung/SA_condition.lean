           /- -------------------------------------------*
            |    Example 1 [Roscoe_Dathi_1987 P.10]     |
            |             WITH computation              |
            |  Self-timed version of a systolic array   |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.3.0            |
            |              September 2006  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.4.0            |
            |                  April 2007  (modified)   |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.SA_Kung.SA_definition

open event
open SA_definition

noncomputable section

namespace SA_condition

local instance instInhabitedOfZero (α : Type _) [Zero α] : Inhabited α where
  default := 0

/-
(*********************************************************
     Small conditions for Deadlock freedom verification
 *********************************************************)
-/

/- finite set -/
/-
lemma Example1_finite_lm1: "finite ({i. i < (n::nat)} <*> {m})"
apply (induct_tac n)
apply (simp)
apply (subgoal_tac
  "{i. i < Suc n} <*> {m} = ({i. i < n} <*> {m}) Un {(n,m)}")
by (auto)

lemma Example1_finite_lm2: "finite ({m} <*> {i. i < (n::nat)})"
apply (induct_tac n)
apply (simp)
apply (subgoal_tac
  "{m} <*> {i. i < Suc n} = ({m} <*> {i. i < n}) Un {(m,n)}")
by (auto)
-/

theorem Example1_finite (N : Nat) : (Array_Index N).Finite := by
  refine
    (finite_pair_set2
      (F1 := {j : Nat | j < N})
      (F2 := fun _ : Nat => {i : Nat | i < N})
      (hF1 := Set.finite_lt_nat N)
      (hF2 := by
        intro _ _
        exact Set.finite_lt_nat N)).subset ?_
  intro p hp
  rcases p with ⟨i, j⟩
  simpa [Array_Index_def] using hp

/- Example1_triple_disjoint -/

theorem Example1_triple_disjoint {r : Type _} (N : Nat) :
    triple_disjoint (Systolic_ArrayF (r := r) N) := by
  rw [triple_disjoint_def, Systolic_ArrayF_def]
  intro i _hi j _hj k _hk hij hjk hki
  ext a
  constructor
  · intro ha
    rcases i with ⟨i1, i2⟩
    rcases j with ⟨j1, j2⟩
    rcases k with ⟨k1, k2⟩
    rcases ha with ⟨⟨hai, haj⟩, hak⟩
    cases a with
    | vert ij x =>
        rcases ij with ⟨m, n⟩
        have hi : (m = i1 ∧ n = i2) ∨ (m = i1 + 1 ∧ n = i2) := by
          rcases
              (by
                simpa [Alpha_pe, Prod.mk.injEq] using hai :
                  ∃ x_1, ((m = i1 ∧ n = i2) ∧ x = x_1) ∨ ((m = i1 + 1 ∧ n = i2) ∧ x = x_1))
            with ⟨_, h⟩
          exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        have hj : (m = j1 ∧ n = j2) ∨ (m = j1 + 1 ∧ n = j2) := by
          rcases
              (by
                simpa [Alpha_pe, Prod.mk.injEq] using haj :
                  ∃ x_1, ((m = j1 ∧ n = j2) ∧ x = x_1) ∨ ((m = j1 + 1 ∧ n = j2) ∧ x = x_1))
            with ⟨_, h⟩
          exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        have hk : (m = k1 ∧ n = k2) ∨ (m = k1 + 1 ∧ n = k2) := by
          rcases
              (by
                simpa [Alpha_pe, Prod.mk.injEq] using hak :
                  ∃ x_1, ((m = k1 ∧ n = k2) ∧ x = x_1) ∨ ((m = k1 + 1 ∧ n = k2) ∧ x = x_1))
            with ⟨_, h⟩
          exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
        · exact hij (by ext <;> omega)
        · exact hij (by ext <;> omega)
        · exact hki (by ext <;> omega)
        · exact hjk (by ext <;> omega)
        · exact hjk (by ext <;> omega)
        · exact hki (by ext <;> omega)
        · exact hij (by ext <;> omega)
        · exact hij (by ext <;> omega)
    | hori ij x =>
        rcases ij with ⟨m, n⟩
        have hi : (m = i1 ∧ n = i2) ∨ (m = i1 ∧ n = i2 + 1) := by
          rcases
              (by
                simpa [Alpha_pe, Prod.mk.injEq] using hai :
                  ∃ x_1, ((m = i1 ∧ n = i2) ∧ x = x_1) ∨ ((m = i1 ∧ n = i2 + 1) ∧ x = x_1))
            with ⟨_, h⟩
          exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        have hj : (m = j1 ∧ n = j2) ∨ (m = j1 ∧ n = j2 + 1) := by
          rcases
              (by
                simpa [Alpha_pe, Prod.mk.injEq] using haj :
                  ∃ x_1, ((m = j1 ∧ n = j2) ∧ x = x_1) ∨ ((m = j1 ∧ n = j2 + 1) ∧ x = x_1))
            with ⟨_, h⟩
          exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        have hk : (m = k1 ∧ n = k2) ∨ (m = k1 ∧ n = k2 + 1) := by
          rcases
              (by
                simpa [Alpha_pe, Prod.mk.injEq] using hak :
                  ∃ x_1, ((m = k1 ∧ n = k2) ∧ x = x_1) ∨ ((m = k1 ∧ n = k2 + 1) ∧ x = x_1))
            with ⟨_, h⟩
          exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        rcases hi with hi | hi <;> rcases hj with hj | hj <;> rcases hk with hk | hk
        · exact hij (by ext <;> omega)
        · exact hij (by ext <;> omega)
        · exact hki (by ext <;> omega)
        · exact hjk (by ext <;> omega)
        · exact hjk (by ext <;> omega)
        · exact hki (by ext <;> omega)
        · exact hij (by ext <;> omega)
        · exact hij (by ext <;> omega)
  · intro ha
    simp at ha

/- Example1_BusyNetwork -/

private theorem Example1_out_base_ne {r : Type _} {i j : Nat} {x y : r} :
    {e |
      ∃ z,
        e = Ev (Event.hori (i, j) z) ∨
          e = Ev (Event.vert (i, j) z) ∨
            e = Ev (Event.hori (i, j + 1) z) ∧ ¬z = y ∨
              e = Ev (Event.vert (i + 1, j) z) ∧ ¬z = x} ≠
      Ev '' Alpha_pe (r := r) (i, j) := by
  intro hEq
  have hIn : Ev (Event.hori (i, j + 1) y) ∈ Ev '' Alpha_pe (r := r) (i, j) := by
    simp [Alpha_pe]
  have hNot :
      Ev (Event.hori (i, j + 1) y) ∉
        {e |
          ∃ z,
            e = Ev (Event.hori (i, j) z) ∨
              e = Ev (Event.vert (i, j) z) ∨
                e = Ev (Event.hori (i, j + 1) z) ∧ ¬z = y ∨
                  e = Ev (Event.vert (i + 1, j) z) ∧ ¬z = x} := by
    simp
  exact hNot (hEq.symm ▸ hIn)

private theorem Example1_out_hori_base_ne {r : Type _} {i j : Nat} {y : r} :
    {e |
      ∃ z,
        e = Ev (Event.vert (i, j) z) ∨
          e = Ev (Event.hori (i, j) z) ∨
            e = Ev (Event.vert (i + 1, j) z) ∨
              e = Ev (Event.hori (i, j + 1) z) ∧ ¬z = y} ≠
      Ev '' Alpha_pe (r := r) (i, j) := by
  intro hEq
  have hIn : Ev (Event.hori (i, j + 1) y) ∈ Ev '' Alpha_pe (r := r) (i, j) := by
    simp [Alpha_pe]
  have hNot :
      Ev (Event.hori (i, j + 1) y) ∉
        {e |
          ∃ z,
            e = Ev (Event.vert (i, j) z) ∨
              e = Ev (Event.hori (i, j) z) ∨
                e = Ev (Event.vert (i + 1, j) z) ∨
                  e = Ev (Event.hori (i, j + 1) z) ∧ ¬z = y} := by
    simp
  exact hNot (hEq.symm ▸ hIn)

private theorem Example1_out_vert_base_ne {r : Type _} {i j : Nat} {x : r} :
    {e |
      ∃ z,
        e = Ev (Event.hori (i, j) z) ∨
          e = Ev (Event.vert (i, j) z) ∨
            e = Ev (Event.hori (i, j + 1) z) ∨
              e = Ev (Event.vert (i + 1, j) z) ∧ ¬z = x} ≠
      Ev '' Alpha_pe (r := r) (i, j) := by
  intro hEq
  have hIn : Ev (Event.vert (i + 1, j) x) ∈ Ev '' Alpha_pe (r := r) (i, j) := by
    simp [Alpha_pe]
  have hNot :
      Ev (Event.vert (i + 1, j) x) ∉
        {e |
          ∃ z,
            e = Ev (Event.hori (i, j) z) ∨
              e = Ev (Event.vert (i, j) z) ∨
                e = Ev (Event.hori (i, j + 1) z) ∨
                  e = Ev (Event.vert (i + 1, j) z) ∧ ¬z = x} := by
    simp
  exact hNot (hEq.symm ▸ hIn)

private theorem Example1_in_base_ne {r : Type _} [Zero r] {i j : Nat} :
    {e |
      ∃ z,
        e = Ev (Event.vert (i + 1, j) z) ∨
          e = Ev (Event.hori (i, j + 1) z)} ≠
      Ev '' Alpha_pe (r := r) (i, j) := by
  intro hEq
  have hIn : Ev (Event.vert (i, j) (0 : r)) ∈ Ev '' Alpha_pe (r := r) (i, j) := by
    simp [Alpha_pe]
  have hNot :
      Ev (Event.vert (i, j) (0 : r)) ∉
        {e |
          ∃ z,
            e = Ev (Event.vert (i + 1, j) z) ∨
              e = Ev (Event.hori (i, j + 1) z)} := by
    simp
  exact hNot (hEq.symm ▸ hIn)

private theorem Example1_in_hori_base_ne {r : Type _} [Zero r] {i j : Nat} :
    {e |
      ∃ z,
        e = Ev (Event.vert (i, j) z) ∨
          e = Ev (Event.hori (i, j + 1) z) ∨
            e = Ev (Event.vert (i + 1, j) z)} ≠
      Ev '' Alpha_pe (r := r) (i, j) := by
  intro hEq
  have hIn : Ev (Event.hori (i, j) (0 : r)) ∈ Ev '' Alpha_pe (r := r) (i, j) := by
    simp [Alpha_pe]
  have hNot :
      Ev (Event.hori (i, j) (0 : r)) ∉
        {e |
          ∃ z,
            e = Ev (Event.vert (i, j) z) ∨
              e = Ev (Event.hori (i, j + 1) z) ∨
                e = Ev (Event.vert (i + 1, j) z)} := by
    simp
  exact hNot (hEq.symm ▸ hIn)

private theorem Example1_in_vert_base_ne {r : Type _} [Zero r] {i j : Nat} :
    {e |
      ∃ z,
        e = Ev (Event.hori (i, j) z) ∨
          e = Ev (Event.vert (i + 1, j) z) ∨
            e = Ev (Event.hori (i, j + 1) z)} ≠
      Ev '' Alpha_pe (r := r) (i, j) := by
  intro hEq
  have hIn : Ev (Event.vert (i, j) (0 : r)) ∈ Ev '' Alpha_pe (r := r) (i, j) := by
    simp [Alpha_pe]
  have hNot :
      Ev (Event.vert (i, j) (0 : r)) ∉
        {e |
          ∃ z,
            e = Ev (Event.hori (i, j) z) ∨
              e = Ev (Event.vert (i + 1, j) z) ∨
                e = Ev (Event.hori (i, j + 1) z)} := by
    simp
  exact hNot (hEq.symm ▸ hIn)

set_option maxHeartbeats 1000000 in
-- The translated case splits over failure-set encodings require a larger heartbeat budget.
theorem Example1_BusyNetwork_out_lm {r : Type _} [Ring r]
    {n i j : Nat} {x y : r} {s : traceType (Event r)} {Y : Set (event (Event r))}
    (hAll : ∀ s Y, (s, Y) ∈ peF_rec (r := r) n (i, j) → Y ≠ Ev '' Alpha_pe (r := r) (i, j))
    (hMem : (s, Y) ∈ Faiures_out x y (i, j) (peF_rec (r := r) n (i, j))) :
    Y ≠ Ev '' Alpha_pe (r := r) (i, j) := by
  simp [Faiures_out_def] at hMem
  rcases hMem with hMem | hMem
  · rcases hMem with hMem | hMem
    · rcases hMem with ⟨_, rfl⟩
      exact Example1_out_base_ne (i := i) (j := j) (x := x) (y := y)
    · rcases hMem with ⟨_, _, _, hInner⟩
      simp [Faiures_out_hori_def] at hInner
      rcases hInner with hBase | hRec
      · rcases hBase with ⟨_, rfl⟩
        exact Example1_out_hori_base_ne (i := i) (j := j) (y := y)
      · rcases hRec with ⟨_, _, _, hRec⟩
        exact hAll _ _ hRec
  · rcases hMem with ⟨_, _, _, hInner⟩
    simp [Faiures_out_vert_def] at hInner
    rcases hInner with hBase | hRec
    · rcases hBase with ⟨_, rfl⟩
      exact Example1_out_vert_base_ne (i := i) (j := j) (x := x)
    · rcases hRec with ⟨_, _, _, hRec⟩
      exact hAll _ _ hRec

set_option maxHeartbeats 1000000 in
-- The recursive proof expands nested translated failure sets and needs extra heartbeats.
theorem Example1_BusyNetwork_lm {r : Type _} [Ring r]
    (n i j : Nat) :
    ∀ s Y, (s, Y) ∈ peF_rec (r := r) n (i, j) → Y ≠ Ev '' Alpha_pe (r := r) (i, j) := by
  induction n with
  | zero =>
      intro s Y hMem
      simpa [peF_rec] using hMem
  | succ n ih =>
      intro s Y hMem
      simp [peF_rec, Faiures_in_def] at hMem
      rcases hMem with hMem | hMem
      · rcases hMem with hMem | hMem
        · rcases hMem with ⟨_, rfl⟩
          exact Example1_in_base_ne (i := i) (j := j)
        · rcases hMem with ⟨_, _, _, hInner⟩
          dsimp [Faiures_in_hori] at hInner
          rw [Set.mem_insert_iff] at hInner
          have hInner' := hInner.2
          exact
            match hInner' with
            | Or.inl hBase =>
                by
                  simp at hBase
                  rcases hBase with ⟨_, rfl⟩
                  exact Example1_in_hori_base_ne (i := i) (j := j)
            | Or.inr hRec =>
                by
                  simp at hRec
                  rcases hRec with ⟨_, _, _, _, hRec⟩
                  exact Example1_BusyNetwork_out_lm (hAll := ih) hRec
      · rcases hMem with ⟨_, _, _, _, hInner⟩
        dsimp [Faiures_in_vert] at hInner
        rw [Set.mem_insert_iff] at hInner
        have hInner' := hInner
        exact
          match hInner' with
          | Or.inl hBase =>
              by
                simp at hBase
                rcases hBase with ⟨_, rfl⟩
                exact Example1_in_vert_base_ne (i := i) (j := j)
          | Or.inr hRec =>
              by
                simp at hRec
                rcases hRec with ⟨_, _, _, _, hRec⟩
                exact Example1_BusyNetwork_out_lm (hAll := ih) hRec

theorem Example1_BusyNetwork {r : Type _} [Ring r] (N : Nat) :
    BusyNetwork (Systolic_ArrayF (r := r) N) := by
  apply check_BusyNetwork
  intro ij _hij s Y hMem
  rcases ij with ⟨i, j⟩
  rw [peF_def] at hMem
  rcases Set.mem_iUnion.mp hMem with ⟨n, hIn⟩
  simpa using Example1_BusyNetwork_lm (r := r) n i j s Y hIn

end SA_condition
