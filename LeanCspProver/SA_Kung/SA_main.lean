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
            |                                           |
            |   on DFP on CSP-Prover ver.5.0            |
            |                   July 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2012         |
            |               November 2012  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.SA_Kung.SA_condition
import LeanCspProver.SA_Kung.SA_expanding
import LeanCspProver.SA_Kung.SA_local

open SA_definition
open SA_condition
open SA_expanding
open SA_local

noncomputable section

namespace SA_main

/-=================================================================*
 |                 main theorem (deadlock freedom)                 |
 *=================================================================-/

theorem Example1_ring {r : Type _} [Ring r] :
    ∀ N, N ≠ 0 → DeadlockFreeNetwork (Systolic_Array (r := r) N) := by
  intro N hN
  refine Rule1_Roscoe_Dathi_1987_I (π := Nat)
    (I := Array_Index N)
    (FXf := fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
    (hF := ?_)
    (hI := ?_)
    (hFin := ?_)
    (hTD := ?_)
    (hBusy := ?_)
    (hRank := ?_)
  · simpa using EX1_isFailureOf (r := r) N
  · intro hEmpty
    have hPos : 0 < N := Nat.pos_of_ne_zero hN
    have hMem : ((0, 0) : index_type) ∈ Array_Index N := by
      simp [Array_Index_def, hPos]
    simpa [hEmpty] using hMem
  · exact Example1_finite N
  · simpa [Systolic_ArrayF_def] using Example1_triple_disjoint (r := r) N
  · simpa [Systolic_ArrayF_def] using Example1_BusyNetwork (r := r) N
  · refine ⟨fun ij sigma => lengtht sigma.1 + 2 * (ij.1 + ij.2), ?_⟩
    intro ij1 _hij1 ij2 _hij2 _hneq t Yf hReq
    rcases ij1 with ⟨i1, j1⟩
    rcases ij2 with ⟨i2, j2⟩
    have hReq' :
        isUngrantedRequestOfwrt
            ((({(i1, j1), (i2, j2)} : Set index_type)),
              fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij))
            (i1, j1) (t, Yf) (VocabularyOf (Systolic_ArrayF (r := r) N)) (i2, j2) := by
      simpa [Systolic_ArrayF_def] using hReq
    have hPairs :=
      possible_pairs (r := r) i1 j1 i2 j2 t Yf
        (VocabularyOf (Systolic_ArrayF (r := r) N)) hReq'
    rcases hPairs with hPair | hPair | hPair | hPair
    · rcases hPair with ⟨hii, hjj⟩
      subst i1
      subst j1
      have hlt := local_hori_rev (r := r) N i2 j2 t Yf (by simpa using hReq')
      dsimp
      omega
    · rcases hPair with ⟨hii, hjj⟩
      subst i1
      subst j2
      have hlt := local_hori (r := r) N i2 j1 t Yf (by simpa using hReq')
      dsimp
      omega
    · rcases hPair with ⟨hii, hjj⟩
      subst i1
      subst j1
      have hlt := local_vert_rev (r := r) N i2 j2 t Yf (by simpa using hReq')
      dsimp
      omega
    · rcases hPair with ⟨hii, hjj⟩
      subst i2
      subst j2
      have hlt := local_vert (r := r) N i1 j1 t Yf (by simpa using hReq')
      dsimp
      omega

/- (****************** to add it again ******************) -/

end SA_main
