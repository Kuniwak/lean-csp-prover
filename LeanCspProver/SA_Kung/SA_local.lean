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

axiom local_i_j_hori {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))) ≤
          lengtht s

/- (*** i (Suc j) hori ***) -/

axiom local_i_Suc_j_hori_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1) ∧
          (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1)))

axiom local_i_Suc_j_hori {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
      (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1)))

/- (*** i j vert ***) -/

axiom local_i_j_vert_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))) ≤
          lengtht s

axiom local_i_j_vert {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))) ≤
          lengtht s

/- (*** (Suc i) j vert ***) -/

axiom local_Suc_i_j_vert_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j) ∧
          (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j)))

axiom local_Suc_i_j_vert {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
      (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j)))

/- (****** reverse ******) -/

/- (*** i j hori ***) -/

axiom local_i_j_hori_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))

axiom local_i_j_hori_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))

/- (*** i (Suc j) hori ***) -/

axiom local_i_Suc_j_hori_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1) ∧
          (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
        4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s

axiom local_i_Suc_j_hori_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
      (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
        4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s

/- (*** i j vert ***) -/

axiom local_i_j_vert_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))

axiom local_i_j_vert_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i, j)) ∈ peF (r := r) (i, j) →
      (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))

/- (*** (Suc i) j vert ***) -/

axiom local_Suc_i_j_vert_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j) ∧
          (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
        4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s

axiom local_Suc_i_j_vert_rev {r : Type _}
    (s : traceType (Event r))
    (Yf : index_type → Set (event (Event r)))
    (i j : Nat) :
    (s, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
      (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
        4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s

/- ---------------------------------------*
 |  ungranted request --> Yf properties  |
 *--------------------------------------- -/

/- hori -/

axiom EX1_request_hori {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ≠ ∅ →
      ∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j)

axiom EX1_ungranted_hori_lm1 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ⊆
          Yf (i, j) ∪ Yf (i, j + 1) →
        ∃ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)

axiom EX1_ungranted_hori_lm2 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ n x,
      Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1) ∧
          (∃ t : traceType (Event r), (t, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1)) →
        ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)

axiom EX1_ungranted_hori {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i, j + 1) ⊆
          Yf (i, j) ∪ Yf (i, j + 1) →
        (t, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
          ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)

/- vert -/

axiom EX1_request_vert {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ≠ ∅ →
      ∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)

axiom EX1_ungranted_vert_lm1 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ⊆
          Yf (i, j) ∪ Yf (i + 1, j) →
        ∃ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)

axiom EX1_ungranted_vert_lm2 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ n x,
      Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j) ∧
          (∃ t : traceType (Event r), (t, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j)) →
        ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)

axiom EX1_ungranted_vert {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j) \ Yf (i, j)) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j) ∩ Ev '' Alpha_pe (r := r) (i + 1, j) ⊆
          Yf (i, j) ∪ Yf (i + 1, j) →
        (t, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
          ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)

/- hori rev -/

axiom EX1_request_hori_rev {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j + 1) \ Yf (i, j + 1)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      ∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)

axiom EX1_request_hori_rev_ALL {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j + 1) \ Yf (i, j + 1)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      (t, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
        ∀ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)

axiom EX1_ungranted_hori_rev {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i, j + 1) \ Yf (i, j + 1)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i, j + 1) ∩ Ev '' Alpha_pe (r := r) (i, j) ⊆
          Yf (i, j + 1) ∪ Yf (i, j) →
        (t, Yf (i, j + 1)) ∈ peF (r := r) (i, j + 1) →
          ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)

/- vert rev -/

axiom EX1_request_vert_rev {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i + 1, j) \ Yf (i + 1, j)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      ∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)

axiom EX1_request_vert_rev_ALL {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i + 1, j) \ Yf (i + 1, j)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      (t, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
        ∀ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)

axiom EX1_ungranted_vert_rev {r : Type _}
    (i j : Nat)
    (t : traceType (Event r))
    (Yf : index_type → Set (event (Event r))) :
    (Ev '' Alpha_pe (r := r) (i + 1, j) \ Yf (i + 1, j)) ∩ Ev '' Alpha_pe (r := r) (i, j) ≠ ∅ →
      Ev '' Alpha_pe (r := r) (i + 1, j) ∩ Ev '' Alpha_pe (r := r) (i, j) ⊆
          Yf (i + 1, j) ∪ Yf (i, j) →
        (t, Yf (i + 1, j)) ∈ peF (r := r) (i + 1, j) →
          ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)

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
