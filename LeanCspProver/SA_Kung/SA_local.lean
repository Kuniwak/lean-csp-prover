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

namespace SA_local

attribute [local instance] Classical.propDecidable

/- Lean note:
   Isabelle's `{ FX | i:I }Fnet` syntax is written directly as `(I, fun i => FX)`
   in Lean. -/

/- ----------------------*
 |     small lemma      |
 *---------------------- -/

axiom possible_pairs {r : Type _}
    (i1 j1 i2 j2 : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (Lambda : Set (Event r)) :
    isUngrantedRequestOfwrt
        ((({(i1, j1), (i2, j2)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i1, j1) (t, Yf) Lambda (i2, j2) →
      (i1 = i2 ∧ j1 = j2 + 1) ∨
        (i1 = i2 ∧ j2 = j1 + 1) ∨
        (i1 = i2 + 1 ∧ j1 = j2) ∨
        (i2 = i1 + 1 ∧ j1 = j2)

/- --------------------------------*
 |       local calculation        |
 *-------------------------------- -/

/- (*** i j hori ***) -/

axiom local_i_j_hori_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))) ≤
          lengtht s

theorem local_i_j_hori {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))) ≤
          lengtht s := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_i_j_hori_ALL n i j Yf s ⟨hs, hx⟩

/- (*** i (Suc j) hori ***) -/

axiom local_i_Suc_j_hori_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1) ∧
          (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1)))

theorem local_i_Suc_j_hori {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
      (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_i_Suc_j_hori_ALL n i j Yf s ⟨hs, hx⟩

/- (*** i j vert ***) -/

axiom local_i_j_vert_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))) ≤
          lengtht s

theorem local_i_j_vert {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))) ≤
          lengtht s := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_i_j_vert_ALL n i j Yf s ⟨hs, hx⟩

/- (*** (Suc i) j vert ***) -/

axiom local_Suc_i_j_vert_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j) ∧
          (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j)))

theorem local_Suc_i_j_vert {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
      (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_Suc_i_j_vert_ALL n i j Yf s ⟨hs, hx⟩

/- (****** reverse ******) -/

/- (*** i j hori ***) -/

axiom local_i_j_hori_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))

theorem local_i_j_hori_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1)))) := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_i_j_hori_rev_ALL n i j Yf s ⟨hs, hx⟩

/- (*** i (Suc j) hori ***) -/

axiom local_i_Suc_j_hori_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1) ∧
          (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
        4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s

theorem local_i_Suc_j_hori_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
      (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
        4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_i_Suc_j_hori_rev_ALL n i j Yf s ⟨hs, hx⟩

/- (*** i j vert ***) -/

axiom local_i_j_vert_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))

theorem local_i_j_vert_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j)))) := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_i_j_vert_rev_ALL n i j Yf s ⟨hs, hx⟩

/- (*** (Suc i) j vert ***) -/

axiom local_Suc_i_j_vert_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j) ∧
          (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
        4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s

theorem local_Suc_i_j_vert_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
      (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
        4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s := by
  intro hs hx
  rw [peF_def, Set.mem_iUnion] at hs
  obtain ⟨n, hs⟩ := hs
  exact local_Suc_i_j_vert_rev_ALL n i j Yf s ⟨hs, hx⟩

/- ---------------------------------------*
 |  ungranted request --> Yf properties  |
 *--------------------------------------- -/

/- the only event shared by `Alpha_pe (i, j)` and `Alpha_pe (i, j+1)` is
   `hori (i, j+1) _`, and the only one shared by `Alpha_pe (i, j)` and
   `Alpha_pe (i+1, j)` is `vert (i+1, j) _`. -/

private theorem hori_of_mem {r : Type _} {a : Event r} {i j : Nat}
    (h1 : a ∈ Alpha_pe (r := r) (i, j)) (h2 : a ∈ Alpha_pe (r := r) (i, j + 1)) :
    ∃ z, a = Event.hori (i, j + 1) z := by
  simp only [Alpha_pe, Set.mem_setOf_eq] at h1 h2
  obtain ⟨x, h1⟩ := h1
  obtain ⟨y, h2⟩ := h2
  rcases h1 with rfl | rfl | rfl | rfl
  · exact absurd h2 (by simp)
  · exact absurd h2 (by simp; omega)
  · exact absurd h2 (by simp)
  · exact ⟨x, rfl⟩

private theorem vert_of_mem {r : Type _} {a : Event r} {i j : Nat}
    (h1 : a ∈ Alpha_pe (r := r) (i, j)) (h2 : a ∈ Alpha_pe (r := r) (i + 1, j)) :
    ∃ z, a = Event.vert (i + 1, j) z := by
  simp only [Alpha_pe, Set.mem_setOf_eq] at h1 h2
  obtain ⟨x, h1⟩ := h1
  obtain ⟨y, h2⟩ := h2
  rcases h1 with rfl | rfl | rfl | rfl
  · exact absurd h2 (by simp; omega)
  · exact absurd h2 (by simp)
  · exact ⟨x, rfl⟩
  · exact absurd h2 (by simp)

/- hori -/

theorem EX1_request_hori {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ≠ ∅ →
      ∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j) := by
  intro h
  rcases Set.nonempty_iff_ne_empty.mpr h with ⟨e, ⟨⟨a, ha, rfl⟩, hY⟩, ⟨b, hb, hb'⟩⟩
  obtain rfl : b = a := by injection hb'
  obtain ⟨z, rfl⟩ := hori_of_mem ha hb
  exact ⟨z, hY⟩

theorem EX1_ungranted_hori_lm1 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ⊆
          Yf (i, j) ∪ Yf (i, j + 1) →
        ∃ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1) := by
  intro hne hsub
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨e, ⟨⟨a, ha, rfl⟩, hY⟩, ⟨b, hb, hb'⟩⟩
  obtain rfl : b = a := by injection hb'
  obtain ⟨z, rfl⟩ := hori_of_mem ha hb
  refine ⟨z, ?_⟩
  rcases hsub ⟨⟨_, ha, rfl⟩, ⟨_, hb, rfl⟩⟩ with h | h
  · exact absurd h hY
  · exact h

axiom EX1_ungranted_hori_lm2 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ n x,
      Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1) ∧
          (∃ t : traceType (Event r), (t, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1)) →
        ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)

theorem EX1_ungranted_hori {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ⊆
          Yf (i, j) ∪ Yf (i, j + 1) →
        (t, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
          ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1) := by
  intro hne hsub ht
  obtain ⟨x, hx⟩ := EX1_ungranted_hori_lm1 i j Yf hne hsub
  rw [peF_def, Set.mem_iUnion] at ht
  obtain ⟨n, ht⟩ := ht
  exact EX1_ungranted_hori_lm2 i j Yf n x ⟨hx, ⟨t, ht⟩⟩

/- vert -/

theorem EX1_request_vert {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ≠ ∅ →
      ∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j) := by
  intro h
  rcases Set.nonempty_iff_ne_empty.mpr h with ⟨e, ⟨⟨a, ha, rfl⟩, hY⟩, ⟨b, hb, hb'⟩⟩
  obtain rfl : b = a := by injection hb'
  obtain ⟨z, rfl⟩ := vert_of_mem ha hb
  exact ⟨z, hY⟩

theorem EX1_ungranted_vert_lm1 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ⊆
          Yf (i, j) ∪ Yf (i + 1, j) →
        ∃ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j) := by
  intro hne hsub
  rcases Set.nonempty_iff_ne_empty.mpr hne with ⟨e, ⟨⟨a, ha, rfl⟩, hY⟩, ⟨b, hb, hb'⟩⟩
  obtain rfl : b = a := by injection hb'
  obtain ⟨z, rfl⟩ := vert_of_mem ha hb
  refine ⟨z, ?_⟩
  rcases hsub ⟨⟨_, ha, rfl⟩, ⟨_, hb, rfl⟩⟩ with h | h
  · exact absurd h hY
  · exact h

axiom EX1_ungranted_vert_lm2 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ n x,
      Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j) ∧
          (∃ t : traceType (Event r), (t, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j)) →
        ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)

theorem EX1_ungranted_vert {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ⊆
          Yf (i, j) ∪ Yf (i + 1, j) →
        (t, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
          ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j) := by
  intro hne hsub ht
  obtain ⟨x, hx⟩ := EX1_ungranted_vert_lm1 i j Yf hne hsub
  rw [peF_def, Set.mem_iUnion] at ht
  obtain ⟨n, ht⟩ := ht
  exact EX1_ungranted_vert_lm2 i j Yf n x ⟨hx, ⟨t, ht⟩⟩

/- hori rev -/

theorem EX1_request_hori_rev {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j + 1) \ Yf (i, j + 1)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      ∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1) := by
  intro h
  rcases Set.nonempty_iff_ne_empty.mpr h with ⟨e, ⟨⟨a, ha, rfl⟩, hY⟩, ⟨b, hb, hb'⟩⟩
  obtain rfl : b = a := by injection hb'
  obtain ⟨z, rfl⟩ := hori_of_mem hb ha
  exact ⟨z, hY⟩

theorem EX1_request_hori_rev_ALL {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j + 1) \ Yf (i, j + 1)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      (t, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
        ∀ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1) := by
  intro hne ht
  by_contra hc
  push_neg at hc
  obtain ⟨x, hx⟩ := hc
  rw [peF_def, Set.mem_iUnion] at ht
  obtain ⟨n, ht⟩ := ht
  have hall := EX1_ungranted_hori_lm2 i j Yf n x ⟨hx, ⟨t, ht⟩⟩
  obtain ⟨y, hy⟩ := EX1_request_hori_rev i j Yf hne
  exact hy (hall y)

theorem EX1_ungranted_hori_rev {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j + 1) \ Yf (i, j + 1)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j + 1) ∩ Ev '' Alpha_pe (r := r) (i, j) ⊆
          Yf (i, j + 1) ∪ Yf (i, j) →
        (t, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
          ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j) := by
  intro hne hsub ht x
  have hnot := EX1_request_hori_rev_ALL i j t Yf hne ht x
  have hmem : Ev (Event.hori (i, j + 1) x) ∈
      Ev '' Alpha_pe (r := r) (i, j + 1) ∩ Ev '' Alpha_pe (r := r) (i, j) := by
    constructor
    · exact ⟨Event.hori (i, j + 1) x, ⟨x, Or.inr (Or.inl rfl)⟩, rfl⟩
    · exact ⟨Event.hori (i, j + 1) x, ⟨x, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩
  rcases hsub hmem with h | h
  · exact absurd h hnot
  · exact h

/- vert rev -/

theorem EX1_request_vert_rev {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i + 1, j) \ Yf (i + 1, j)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      ∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j) := by
  intro h
  rcases Set.nonempty_iff_ne_empty.mpr h with ⟨e, ⟨⟨a, ha, rfl⟩, hY⟩, ⟨b, hb, hb'⟩⟩
  obtain rfl : b = a := by injection hb'
  obtain ⟨z, rfl⟩ := vert_of_mem hb ha
  exact ⟨z, hY⟩

theorem EX1_request_vert_rev_ALL {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i + 1, j) \ Yf (i + 1, j)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      (t, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
        ∀ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j) := by
  intro hne ht
  by_contra hc
  push_neg at hc
  obtain ⟨x, hx⟩ := hc
  rw [peF_def, Set.mem_iUnion] at ht
  obtain ⟨n, ht⟩ := ht
  have hall := EX1_ungranted_vert_lm2 i j Yf n x ⟨hx, ⟨t, ht⟩⟩
  obtain ⟨y, hy⟩ := EX1_request_vert_rev i j Yf hne
  exact hy (hall y)

theorem EX1_ungranted_vert_rev {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i + 1, j) \ Yf (i + 1, j)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i + 1, j) ∩ Ev '' Alpha_pe (r := r) (i, j) ⊆
          Yf (i + 1, j) ∪ Yf (i, j) →
        (t, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
          ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j) := by
  intro hne hsub ht x
  have hnot := EX1_request_vert_rev_ALL i j t Yf hne ht x
  have hmem : Ev (Event.vert (i + 1, j) x) ∈
      Ev '' Alpha_pe (r := r) (i + 1, j) ∩ Ev '' Alpha_pe (r := r) (i, j) := by
    constructor
    · exact ⟨Event.vert (i + 1, j) x, ⟨x, Or.inl rfl⟩, rfl⟩
    · exact ⟨Event.vert (i + 1, j) x, ⟨x, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩
  rcases hsub hmem with h | h
  · exact absurd h hnot
  · exact h

/- --------------------------------*
 |        making function         |
 *-------------------------------- -/

/- small calculation -/

theorem EX1_cal1 (x y0 y1 : Nat) :
    Nat.succ (Nat.succ (4 * x)) ≤ y0 →
      Nat.succ y1 ≤ 4 * x →
        LT.lt (Nat.succ (Nat.succ y1)) y0 := by
  omega

theorem EX1_cal1_rev (x y0 y1 : Nat) :
    4 * x ≤ y1 →
      y0 ≤ Nat.succ (4 * x) →
        LT.lt y0 (Nat.succ (Nat.succ y1)) := by
  omega

/- (****** hori ******) -/

axiom local_hori_lm {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i, j), (i, j + 1)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i, j) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i, j + 1) →
      Nat.succ (Nat.succ (4 * lengtht (t rest-tr Set.range (Event.hori (i, j + 1))))) ≤
          lengtht (t rest-tr Alpha_pe (r := r) (i, j)) ∧
        Nat.succ (lengtht (t rest-tr Alpha_pe (r := r) (i, j + 1))) ≤
          4 * lengtht (t rest-tr Set.range (Event.hori (i, j + 1)))

/- local_hori -/

axiom local_hori {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i, j), (i, j + 1)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i, j) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i, j + 1) →
      LT.lt
        (Nat.succ (Nat.succ (lengtht (t rest-tr (Alpha_pe (r := r) (i, j + 1)))))
        )
        (lengtht (t rest-tr (Alpha_pe (r := r) (i, j))))

/- (****** vert ******) -/

axiom local_vert_lm {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i, j), (i + 1, j)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i, j) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i + 1, j) →
      Nat.succ (Nat.succ (4 * lengtht (t rest-tr Set.range (Event.vert (i + 1, j))))) ≤
          lengtht (t rest-tr Alpha_pe (r := r) (i, j)) ∧
        Nat.succ (lengtht (t rest-tr Alpha_pe (r := r) (i + 1, j))) ≤
          4 * lengtht (t rest-tr Set.range (Event.vert (i + 1, j)))

/- local_vert -/

axiom local_vert {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i, j), (i + 1, j)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i, j) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i + 1, j) →
      LT.lt
        (Nat.succ (Nat.succ (lengtht (t rest-tr (Alpha_pe (r := r) (i + 1, j)))))
        )
        (lengtht (t rest-tr (Alpha_pe (r := r) (i, j))))

/- (****** hori rev ******) -/

axiom local_hori_rev_lm {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i, j + 1), (i, j)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i, j + 1) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i, j) →
      lengtht (t rest-tr Alpha_pe (r := r) (i, j)) ≤
          Nat.succ (4 * lengtht (t rest-tr Set.range (Event.hori (i, j + 1)))) ∧
        4 * lengtht (t rest-tr Set.range (Event.hori (i, j + 1))) ≤
          lengtht (t rest-tr Alpha_pe (r := r) (i, j + 1))

/- local_hori_rev -/

axiom local_hori_rev {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i, j + 1), (i, j)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i, j + 1) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i, j) →
      LT.lt
        (lengtht (t rest-tr (Alpha_pe (r := r) (i, j))))
        (Nat.succ (Nat.succ (lengtht (t rest-tr (Alpha_pe (r := r) (i, j + 1)))))
        )

/- (****** vert rev ******) -/

axiom local_vert_rev_lm {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i + 1, j), (i, j)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i + 1, j) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i, j) →
      lengtht (t rest-tr Alpha_pe (r := r) (i, j)) ≤
          Nat.succ (4 * lengtht (t rest-tr Set.range (Event.vert (i + 1, j)))) ∧
        4 * lengtht (t rest-tr Set.range (Event.vert (i + 1, j))) ≤
          lengtht (t rest-tr Alpha_pe (r := r) (i + 1, j))

/- local_vert_rev -/

axiom local_vert_rev {r : Type _}
    (N i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    isUngrantedRequestOfwrt
        ((({(i + 1, j), (i, j)} : Set index_type)),
          fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
        (i + 1, j) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i, j) →
      LT.lt
        (lengtht (t rest-tr (Alpha_pe (r := r) (i, j))))
        (Nat.succ (Nat.succ (lengtht (t rest-tr (Alpha_pe (r := r) (i + 1, j)))))
        )

end SA_local
