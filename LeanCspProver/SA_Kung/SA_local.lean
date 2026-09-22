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

private theorem lengtht_cons {r : Type _} (e : Event r) (s : traceType (Event r)) :
    lengtht ((Abs_trace [Ev e] : traceType (Event r)) ^^^ s) = 1 + lengtht s := by
  rw [lengtht_app_decompo1 (Or.inl (by simp [noTick]))]
  simp [lengtht_one_event]

private theorem vert_notin_hori {r : Type _} (i j k l : Nat) (x : r) :
    Event.vert (i, j) x ∉ Set.range (Event.hori (k, l) (r := r)) := by
  rintro ⟨z, hz⟩
  cases hz

private theorem hori_notin_hori_succ {r : Type _} (i j : Nat) (y : r) :
    Event.hori (i, j) y ∉ Set.range (Event.hori (i, j + 1) (r := r)) := by
  rintro ⟨z, hz⟩
  cases hz

private theorem hori_mem_range {r : Type _} (i j : Nat) (y : r) :
    Event.hori (i, j + 1) y ∈ Set.range (Event.hori (i, j + 1) (r := r)) := ⟨y, rfl⟩

private theorem hori_notin_vert {r : Type _} (i j k l : Nat) (y : r) :
    Event.hori (i, j) y ∉ Set.range (Event.vert (k, l) (r := r)) := by
  rintro ⟨z, hz⟩
  cases hz

private theorem vert_notin_vert_succ {r : Type _} (i j : Nat) (x : r) :
    Event.vert (i, j) x ∉ Set.range (Event.vert (i + 1, j) (r := r)) := by
  rintro ⟨z, hz⟩
  cases hz

private theorem vert_mem_range {r : Type _} (i j : Nat) (x : r) :
    Event.vert (i + 1, j) x ∈ Set.range (Event.vert (i + 1, j) (r := r)) := ⟨x, rfl⟩

private theorem hori_notin_hori_ne {r : Type _} {i j k l : Nat} (y : r) (h : j ≠ l) :
    Event.hori (i, j) y ∉ Set.range (Event.hori (k, l) (r := r)) := by
  rintro ⟨z, hz⟩
  injection hz with h1 _
  exact h (congrArg Prod.snd h1).symm

private theorem vert_notin_vert_ne {r : Type _} {i j k l : Nat} (x : r) (h : i ≠ k) :
    Event.vert (i, j) x ∉ Set.range (Event.vert (k, l) (r := r)) := by
  rintro ⟨z, hz⟩
  injection hz with h1 _
  exact h (congrArg Prod.fst h1).symm

theorem local_i_j_hori_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))))) ≤
          lengtht s := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      -- the four inner levels of one unfolding step
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_hori (r := r) y (i, j) (peF_rec m (i, j)) →
            (∃ z, Ev (Event.hori (i, j + 1) z) ∉ Yf (i, j)) →
              4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) ≤ 1 + lengtht s3 := by
        rintro y s3 h3 hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h3
        rcases h3 with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (hori_mem_range i j y), lengtht_cons, lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_vert (r := r) x (i, j) (peF_rec m (i, j)) →
            (∃ z, Ev (Event.hori (i, j + 1) z) ∉ Yf (i, j)) →
              3 + 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s3 := by
        rintro x s3 h3 ⟨z, hz⟩
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h3
        rcases h3 with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          exact hz (hY ▸ ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) j i (j + 1) x), lengtht_cons]
          have := ih s4 ⟨h4, z, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i, j)) ∈ Faiures_out (r := r) x y (i, j) (peF_rec m (i, j)) →
            (∃ z, Ev (Event.hori (i, j + 1) z) ∉ Yf (i, j)) →
              4 * lengtht (s2 rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s2 := by
        rintro x y s2 h2 hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h2
        rcases h2 with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) j i (j + 1) x), lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (hori_mem_range i j y), lengtht_cons, lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_hori (r := r) x (i, j) (peF_rec m (i, j)) →
            (∃ z, Ev (Event.hori (i, j + 1) z) ∉ Yf (i, j)) →
              1 + 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s' := by
        rintro x s' h' hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h'
        rcases h' with h0 | ⟨y, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hz⟩ := hz
          exact hz (hY ▸ ⟨z, Or.inr (Or.inl rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_hori_succ i j y), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_vert (r := r) y (i, j) (peF_rec m (i, j)) →
            (∃ z, Ev (Event.hori (i, j + 1) z) ∉ Yf (i, j)) →
              1 + 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s' := by
        rintro y s' h' hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h'
        rcases h' with h0 | ⟨x, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hz⟩ := hz
          exact hz (hY ▸ ⟨z, Or.inr (Or.inr rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori i j i (j + 1) x), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, x, hx⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · exfalso
        obtain ⟨-, hY⟩ := Prod.mk.inj h0
        exact hx (hY ▸ ⟨x, Or.inr rfl⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (vert_notin_hori i j i (j + 1) x'), lengtht_cons]
        have := hInHori x' s' h' ⟨x, hx⟩
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (hori_notin_hori_succ i j y'), lengtht_cons]
        have := hInVert y' s' h' ⟨x, hx⟩
        omega

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

theorem local_i_Suc_j_hori_ALL {r : Type _} [Inhabited r]
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1) ∧
          (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j + 1)) ∈ Faiures_out_hori (r := r) y (i, j + 1) (peF_rec m (i, j + 1)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
              lengtht s3 ≤ 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro y s3 h hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_hori_ne y (by omega : j + 1 + 1 ≠ j + 1)), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j + 1)) ∈ Faiures_out_vert (r := r) x (i, j + 1) (peF_rec m (i, j + 1)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
              lengtht s3 ≤ 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro x s3 h hz
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) (j + 1) i (j + 1) x), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i, j + 1)) ∈ Faiures_out (r := r) x y (i, j + 1) (peF_rec m (i, j + 1)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
              lengtht s2 ≤ 1 + 4 * lengtht (s2 rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro x y s2 h hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) (j + 1) i (j + 1) x), lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_hori_ne y (by omega : j + 1 + 1 ≠ j + 1)), lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i, j + 1)) ∈ Faiures_in_hori (r := r) x (i, j + 1) (peF_rec m (i, j + 1)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
              2 + lengtht s' ≤ 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro x s' h hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          have hcon := hz (default : r)
          rw [hY] at hcon
          simp at hcon
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (hori_mem_range i j y), lengtht_cons, lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i, j + 1)) ∈ Faiures_in_vert (r := r) y (i, j + 1) (peF_rec m (i, j + 1)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1)) →
              lengtht s' ≤ 2 + 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro y s' h hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori i (j + 1) i (j + 1) x), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, hz⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · exfalso
        obtain ⟨-, hY⟩ := Prod.mk.inj h0
        have hcon := hz (default : r)
        rw [hY] at hcon
        simp at hcon
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (vert_notin_hori i (j + 1) i (j + 1) x'), lengtht_cons]
        have := hInHori x' s' h' hz
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_in_appt (hori_mem_range i j y'), lengtht_cons, lengtht_cons]
        have := hInVert y' s' h' hz
        omega

theorem local_i_Suc_j_hori {r : Type _} [Inhabited r]
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

theorem local_i_j_vert_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
        Nat.succ (Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))))) ≤
          lengtht s := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_hori (r := r) y (i, j) (peF_rec m (i, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
              3 + 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s3 := by
        rintro y s3 h hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert i (j + 1) (i + 1) j y), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_vert (r := r) x (i, j) (peF_rec m (i, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
              4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) ≤ 1 + lengtht s3 := by
        rintro x s3 h hz
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (vert_mem_range i j x), lengtht_cons, lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i, j)) ∈ Faiures_out (r := r) x y (i, j) (peF_rec m (i, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
              4 * lengtht (s2 rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s2 := by
        rintro x y s2 h hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (vert_mem_range i j x), lengtht_cons, lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert i (j + 1) (i + 1) j y), lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_hori (r := r) x (i, j) (peF_rec m (i, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
              1 + 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s' := by
        rintro x s' h hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inr (Or.inr rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert i j (i + 1) j y), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_vert (r := r) y (i, j) (peF_rec m (i, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i, j)) →
              1 + 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s' := by
        rintro y s' h hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inr (Or.inl rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_vert_succ i j x), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, hz⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · exfalso
        obtain ⟨-, hY⟩ := Prod.mk.inj h0
        obtain ⟨z, hzz⟩ := hz
        exact hzz (by rw [hY]; exact ⟨z, Or.inl rfl⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (vert_notin_vert_succ i j x'), lengtht_cons]
        have := hInHori x' s' h' hz
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (hori_notin_vert i j (i + 1) j y'), lengtht_cons]
        have := hInVert y' s' h' hz
        omega

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

theorem local_Suc_i_j_vert_ALL {r : Type _} [Inhabited r]
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j) ∧
          (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
        Nat.succ (lengtht s) ≤ 4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i + 1, j)) ∈ Faiures_out_hori (r := r) y (i + 1, j) (peF_rec m (i + 1, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
              lengtht s3 ≤ 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro y s3 h hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert (i + 1) (j + 1) (i + 1) j y), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i + 1, j)) ∈ Faiures_out_vert (r := r) x (i + 1, j) (peF_rec m (i + 1, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
              lengtht s3 ≤ 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro x s3 h hz
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_vert_ne x (by omega : i + 1 + 1 ≠ i + 1)), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i + 1, j)) ∈ Faiures_out (r := r) x y (i + 1, j) (peF_rec m (i + 1, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
              lengtht s2 ≤ 1 + 4 * lengtht (s2 rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro x y s2 h hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_vert_ne x (by omega : i + 1 + 1 ≠ i + 1)), lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert (i + 1) (j + 1) (i + 1) j y), lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i + 1, j)) ∈ Faiures_in_hori (r := r) x (i + 1, j) (peF_rec m (i + 1, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
              lengtht s' ≤ 2 + 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro x s' h hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert (i + 1) j (i + 1) j y), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i + 1, j)) ∈ Faiures_in_vert (r := r) y (i + 1, j) (peF_rec m (i + 1, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j)) →
              2 + lengtht s' ≤ 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro y s' h hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          have hcon := hz (default : r)
          rw [hY] at hcon
          simp at hcon
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (vert_mem_range i j x), lengtht_cons, lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, hz⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · exfalso
        obtain ⟨-, hY⟩ := Prod.mk.inj h0
        have hcon := hz (default : r)
        rw [hY] at hcon
        simp at hcon
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_in_appt (vert_mem_range i j x'), lengtht_cons, lengtht_cons]
        have := hInHori x' s' h' hz
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (hori_notin_vert (i + 1) j (i + 1) j y'), lengtht_cons]
        have := hInVert y' s' h' hz
        omega

theorem local_Suc_i_j_vert {r : Type _} [Inhabited r]
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

theorem local_i_j_hori_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1)))) := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_hori (r := r) y (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
              2 + lengtht s3 ≤ 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro y s3 h3 hx
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h3
        rcases h3 with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          have := hx y
          rw [hY] at this
          simp at this
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (hori_mem_range i j y), lengtht_cons, lengtht_cons]
          have := ih s4 ⟨h4, hx⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_vert (r := r) x (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
              lengtht s3 ≤ 2 + 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro x s3 h3 hx
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h3
        rcases h3 with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) j i (j + 1) x), lengtht_cons]
          have := ih s4 ⟨h4, hx⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i, j)) ∈ Faiures_out (r := r) x y (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
              1 + lengtht s2 ≤ 4 * lengtht (s2 rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro x y s2 h2 hx
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h2
        rcases h2 with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          have := hx y
          rw [hY] at this
          simp at this
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) j i (j + 1) x), lengtht_cons]
          have := hOutHori y s3 h3 hx
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (hori_mem_range i j y), lengtht_cons, lengtht_cons]
          have := hOutVert x s3 h3 hx
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_hori (r := r) x (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
              lengtht s' ≤ 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro x s' h' hx
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h'
        rcases h' with h0 | ⟨y, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_hori_succ i j y), lengtht_cons]
          have := hOut x y s2 h2 hx
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_vert (r := r) y (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j)) →
              lengtht s' ≤ 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) := by
        rintro y s' h' hx
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h'
        rcases h' with h0 | ⟨x, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori i j i (j + 1) x), lengtht_cons]
          have := hOut x y s2 h2 hx
          omega
      rintro s ⟨hs, hx⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
        simp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (vert_notin_hori i j i (j + 1) x'), lengtht_cons]
        have := hInHori x' s' h' hx
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (hori_notin_hori_succ i j y'), lengtht_cons]
        have := hInVert y' s' h' hx
        omega

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

theorem local_i_Suc_j_hori_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1) ∧
          (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
        4 * lengtht (s rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j + 1)) ∈ Faiures_out_hori (r := r) y (i, j + 1) (peF_rec m (i, j + 1)) →
            (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
              1 + 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s3 := by
        rintro y s3 h hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inr (Or.inl rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_hori_ne y (by omega : j + 1 + 1 ≠ j + 1)), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j + 1)) ∈ Faiures_out_vert (r := r) x (i, j + 1) (peF_rec m (i, j + 1)) →
            (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
              1 + 4 * lengtht (s3 rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s3 := by
        rintro x s3 h hz
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inl rfl⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) (j + 1) i (j + 1) x), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i, j + 1)) ∈ Faiures_out (r := r) x y (i, j + 1) (peF_rec m (i, j + 1)) →
            (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
              2 + 4 * lengtht (s2 rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s2 := by
        rintro x y s2 h hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inl rfl⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori (i + 1) (j + 1) i (j + 1) x), lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_hori_ne y (by omega : j + 1 + 1 ≠ j + 1)), lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i, j + 1)) ∈ Faiures_in_hori (r := r) x (i, j + 1) (peF_rec m (i, j + 1)) →
            (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
              4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) ≤ 1 + lengtht s' := by
        rintro x s' h hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (hori_mem_range i j y), lengtht_cons, lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i, j + 1)) ∈ Faiures_in_vert (r := r) y (i, j + 1) (peF_rec m (i, j + 1)) →
            (∃ x, Ev (Event.hori (i, j + 1) x) ∉ Yf (i, j + 1)) →
              3 + 4 * lengtht (s' rest-tr Set.range (Event.hori (i, j + 1))) ≤ lengtht s' := by
        rintro y s' h hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inl rfl⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_hori i (j + 1) i (j + 1) x), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, hz⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
        simp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (vert_notin_hori i (j + 1) i (j + 1) x'), lengtht_cons]
        have := hInHori x' s' h' hz
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_in_appt (hori_mem_range i j y'), lengtht_cons, lengtht_cons]
        have := hInVert y' s' h' hz
        omega

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

theorem local_i_j_vert_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i, j)) ∈ peF_rec (r := r) n (i, j) ∧
          (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
        lengtht s ≤ Nat.succ (4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j)))) := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_hori (r := r) y (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
              lengtht s3 ≤ 2 + 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro y s3 h hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert i (j + 1) (i + 1) j y), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i, j)) ∈ Faiures_out_vert (r := r) x (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
              2 + lengtht s3 ≤ 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro x s3 h hz
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          have hcon := hz x
          rw [hY] at hcon
          simp at hcon
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (vert_mem_range i j x), lengtht_cons, lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i, j)) ∈ Faiures_out (r := r) x y (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
              1 + lengtht s2 ≤ 4 * lengtht (s2 rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro x y s2 h hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          have hcon := hz x
          rw [hY] at hcon
          simp at hcon
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (vert_mem_range i j x), lengtht_cons, lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert i (j + 1) (i + 1) j y), lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_hori (r := r) x (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
              lengtht s' ≤ 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro x s' h hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert i j (i + 1) j y), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i, j)) ∈ Faiures_in_vert (r := r) y (i, j) (peF_rec m (i, j)) →
            (∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i, j)) →
              lengtht s' ≤ 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) := by
        rintro y s' h hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_vert_succ i j x), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, hz⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
        simp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (vert_notin_vert_succ i j x'), lengtht_cons]
        have := hInHori x' s' h' hz
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (hori_notin_vert i j (i + 1) j y'), lengtht_cons]
        have := hInVert y' s' h' hz
        omega

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

theorem local_Suc_i_j_vert_rev_ALL {r : Type _}
    (n i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ s : traceType (Event r),
      (s, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j) ∧
          (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
        4 * lengtht (s rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s := by
  induction n with
  | zero =>
      rintro s ⟨hs, -⟩
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (s3 : traceType (Event r)),
          (s3, Yf (i + 1, j)) ∈ Faiures_out_hori (r := r) y (i + 1, j) (peF_rec m (i + 1, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
              1 + 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s3 := by
        rintro y s3 h hz
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inl rfl⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert (i + 1) (j + 1) (i + 1) j y), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOutVert : ∀ (x : r) (s3 : traceType (Event r)),
          (s3, Yf (i + 1, j)) ∈ Faiures_out_vert (r := r) x (i + 1, j) (peF_rec m (i + 1, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
              1 + 4 * lengtht (s3 rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s3 := by
        rintro x s3 h hz
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inr (Or.inl rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_vert_ne x (by omega : i + 1 + 1 ≠ i + 1)), lengtht_cons]
          have := ih s4 ⟨h4, hz⟩
          omega
      have hOut : ∀ (x y : r) (s2 : traceType (Event r)),
          (s2, Yf (i + 1, j)) ∈ Faiures_out (r := r) x y (i + 1, j) (peF_rec m (i + 1, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
              2 + 4 * lengtht (s2 rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s2 := by
        rintro x y s2 h hz
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inr (Or.inl rfl)⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (vert_notin_vert_ne x (by omega : i + 1 + 1 ≠ i + 1)), lengtht_cons]
          have := hOutHori y s3 h3 hz
          omega
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert (i + 1) (j + 1) (i + 1) j y), lengtht_cons]
          have := hOutVert x s3 h3 hz
          omega
      have hInHori : ∀ (x : r) (s' : traceType (Event r)),
          (s', Yf (i + 1, j)) ∈ Faiures_in_hori (r := r) x (i + 1, j) (peF_rec m (i + 1, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
              3 + 4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) ≤ lengtht s' := by
        rintro x s' h hz
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · exfalso
          obtain ⟨-, hY⟩ := Prod.mk.inj h0
          obtain ⟨z, hzz⟩ := hz
          exact hzz (by rw [hY]; exact ⟨z, Or.inl rfl⟩)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_notin (hori_notin_vert (i + 1) j (i + 1) j y), lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      have hInVert : ∀ (y : r) (s' : traceType (Event r)),
          (s', Yf (i + 1, j)) ∈ Faiures_in_vert (r := r) y (i + 1, j) (peF_rec m (i + 1, j)) →
            (∃ x, Ev (Event.vert (i + 1, j) x) ∉ Yf (i + 1, j)) →
              4 * lengtht (s' rest-tr Set.range (Event.vert (i + 1, j))) ≤ 1 + lengtht s' := by
        rintro y s' h hz
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
          simp
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
          rw [rest_tr_in_appt (vert_mem_range i j x), lengtht_cons, lengtht_cons]
          have := hOut x y s2 h2 hz
          omega
      rintro s ⟨hs, hz⟩
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h0
        simp
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_in_appt (vert_mem_range i j x'), lengtht_cons, lengtht_cons]
        have := hInHori x' s' h' hz
        omega
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
        rw [rest_tr_notin (hori_notin_vert (i + 1) j (i + 1) j y'), lengtht_cons]
        have := hInVert y' s' h' hz
        omega

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

/-- Every refusal set occurring in `peF_rec _ (i, j+1)` either contains the whole
    incoming horizontal channel or none of it, so one refused event forces all. -/
theorem hori_refusal_saturated {r : Type _} (i j : Nat) :
    ∀ (n : Nat) (Y : Set (event (Event r))) (s : traceType (Event r)),
      (s, Y) ∈ peF_rec (r := r) n (i, j + 1) →
        ∀ a b, Ev (Event.hori (i, j + 1) a) ∈ Y → Ev (Event.hori (i, j + 1) b) ∈ Y := by
  intro n
  induction n with
  | zero =>
      intro Y s hs
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_out_hori (r := r) y (i, j + 1) (peF_rec m (i, j + 1)) →
            ∀ a b, Ev (Event.hori (i, j + 1) a) ∈ Y →
              Ev (Event.hori (i, j + 1) b) ∈ Y := by
        rintro y Y s h
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inr (Or.inl rfl)⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact ih Y s4 h4
      have hOutVert : ∀ (x : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_out_vert (r := r) x (i, j + 1) (peF_rec m (i, j + 1)) →
            ∀ a b, Ev (Event.hori (i, j + 1) a) ∈ Y →
              Ev (Event.hori (i, j + 1) b) ∈ Y := by
        rintro x Y s h
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inl rfl⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact ih Y s4 h4
      have hOut : ∀ (x y : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_out (r := r) x y (i, j + 1) (peF_rec m (i, j + 1)) →
            ∀ a b, Ev (Event.hori (i, j + 1) a) ∈ Y →
              Ev (Event.hori (i, j + 1) b) ∈ Y := by
        rintro x y Y s h
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inl rfl⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOutHori y Y s3 h3
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOutVert x Y s3 h3
      have hInHori : ∀ (x : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_in_hori (r := r) x (i, j + 1) (peF_rec m (i, j + 1)) →
            ∀ a b, Ev (Event.hori (i, j + 1) a) ∈ Y →
              Ev (Event.hori (i, j + 1) b) ∈ Y := by
        rintro x Y s h
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          intro a b ha
          exact absurd ha (by simp)
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOut x y Y s2 h2
      have hInVert : ∀ (y : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_in_vert (r := r) y (i, j + 1) (peF_rec m (i, j + 1)) →
            ∀ a b, Ev (Event.hori (i, j + 1) a) ∈ Y →
              Ev (Event.hori (i, j + 1) b) ∈ Y := by
        rintro y Y s h
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inl rfl⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOut x y Y s2 h2
      intro Y s hs
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
        intro a b ha
        exact absurd ha (by simp)
      · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        exact hInHori x' Y s' h'
      · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        exact hInVert y' Y s' h'

/-- Every refusal set occurring in `peF_rec _ (i+1, j)` either contains the whole
    incoming vertical channel or none of it, so one refused event forces all. -/
theorem vert_refusal_saturated {r : Type _} (i j : Nat) :
    ∀ (n : Nat) (Y : Set (event (Event r))) (s : traceType (Event r)),
      (s, Y) ∈ peF_rec (r := r) n (i + 1, j) →
        ∀ a b, Ev (Event.vert (i + 1, j) a) ∈ Y → Ev (Event.vert (i + 1, j) b) ∈ Y := by
  intro n
  induction n with
  | zero =>
      intro Y s hs
      exact absurd hs (by simp [peF_rec])
  | succ m ih =>
      have hOutHori : ∀ (y : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_out_hori (r := r) y (i + 1, j) (peF_rec m (i + 1, j)) →
            ∀ a b, Ev (Event.vert (i + 1, j) a) ∈ Y →
              Ev (Event.vert (i + 1, j) b) ∈ Y := by
        rintro y Y s h
        simp only [Faiures_out_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inl rfl⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact ih Y s4 h4
      have hOutVert : ∀ (x : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_out_vert (r := r) x (i + 1, j) (peF_rec m (i + 1, j)) →
            ∀ a b, Ev (Event.vert (i + 1, j) a) ∈ Y →
              Ev (Event.vert (i + 1, j) b) ∈ Y := by
        rintro x Y s h
        simp only [Faiures_out_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨s4, Y4, heq, h4⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inr (Or.inl rfl)⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact ih Y s4 h4
      have hOut : ∀ (x y : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_out (r := r) x y (i + 1, j) (peF_rec m (i + 1, j)) →
            ∀ a b, Ev (Event.vert (i + 1, j) a) ∈ Y →
              Ev (Event.vert (i + 1, j) b) ∈ Y := by
        rintro x y Y s h
        simp only [Faiures_out, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with (h0 | ⟨s3, Y3, heq, h3⟩) | ⟨s3, Y3, heq, h3⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inr (Or.inl rfl)⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOutHori y Y s3 h3
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOutVert x Y s3 h3
      have hInHori : ∀ (x : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_in_hori (r := r) x (i + 1, j) (peF_rec m (i + 1, j)) →
            ∀ a b, Ev (Event.vert (i + 1, j) a) ∈ Y →
              Ev (Event.vert (i + 1, j) b) ∈ Y := by
        rintro x Y s h
        simp only [Faiures_in_hori, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨y, s2, Y2, heq, h2⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          exact fun a b _ => ⟨b, Or.inl rfl⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOut x y Y s2 h2
      have hInVert : ∀ (y : r) (Y : Set (event (Event r))) (s : traceType (Event r)),
          (s, Y) ∈ Faiures_in_vert (r := r) y (i + 1, j) (peF_rec m (i + 1, j)) →
            ∀ a b, Ev (Event.vert (i + 1, j) a) ∈ Y →
              Ev (Event.vert (i + 1, j) b) ∈ Y := by
        rintro y Y s h
        simp only [Faiures_in_vert, Set.mem_union, Set.mem_setOf_eq,
          Set.mem_singleton_iff] at h
        rcases h with h0 | ⟨x, s2, Y2, heq, h2⟩
        · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
          intro a b ha
          exact absurd ha (by simp)
        · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hOut x y Y s2 h2
      intro Y s hs
      rw [peF_rec] at hs
      simp only [Faiures_in_def, Set.mem_union, Set.mem_setOf_eq,
        Set.mem_singleton_iff] at hs
      rcases hs with (h0 | ⟨x', s', Y', heq, h'⟩) | ⟨y', s', Y', heq, h'⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h0
        intro a b ha
        exact absurd ha (by simp)
      · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        exact hInHori x' Y s' h'
      · obtain ⟨-, rfl⟩ := Prod.mk.inj heq
        exact hInVert y' Y s' h'

theorem EX1_ungranted_hori_lm2 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ n x,
      Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1) ∧
          (∃ t : traceType (Event r), (t, Yf (i, j + 1)) ∈ peF_rec (r := r) n (i, j + 1)) →
        ∀ x, Ev (Event.hori (i, j + 1) x) ∈ Yf (i, j + 1) := by
  rintro n x ⟨hx, t, ht⟩ b
  exact hori_refusal_saturated i j n (Yf (i, j + 1)) t ht x b hx

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

theorem EX1_ungranted_vert_lm2 {r : Type _}
    (i j : Nat)
    (Yf : index_type → Set (event (Event r))) :
    ∀ n x,
      Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j) ∧
          (∃ t : traceType (Event r), (t, Yf (i + 1, j)) ∈ peF_rec (r := r) n (i + 1, j)) →
        ∀ x, Ev (Event.vert (i + 1, j) x) ∈ Yf (i + 1, j) := by
  rintro n x ⟨hx, t, ht⟩ b
  exact vert_refusal_saturated i j n (Yf (i + 1, j)) t ht x b hx

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

theorem local_hori_lm {r : Type _} [Inhabited r]
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
          4 * lengtht (t rest-tr Set.range (Event.hori (i, j + 1))) := by
  rintro ⟨⟨⟨⟨-, hst⟩, -, -, -, hne⟩, hsub⟩, -⟩
  have hA : Set.range (Event.hori (i, j + 1) (r := r)) ⊆ Alpha_pe (r := r) (i, j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inr (Or.inr (Or.inr rfl))⟩
  have hB : Set.range (Event.hori (i, j + 1) (r := r)) ⊆ Alpha_pe (r := r) (i, j + 1) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inr (Or.inl rfl)⟩
  have h1 := (hst (i, j) (by simp)).1
  have h2 := (hst (i, j + 1) (by simp)).1
  refine ⟨?_, ?_⟩
  · have h := local_i_j_hori _ Yf i j h1 (EX1_request_hori i j Yf hne)
    rwa [rest_tr_of_rest_tr_subset2 hA] at h
  · have h := local_i_Suc_j_hori _ Yf i j h2 (EX1_ungranted_hori i j _ Yf hne hsub h2)
    rwa [rest_tr_of_rest_tr_subset2 hB] at h

/- local_hori -/

theorem local_hori {r : Type _} [Inhabited r]
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
        (lengtht (t rest-tr (Alpha_pe (r := r) (i, j)))) := by
  intro h
  exact EX1_cal1 _ _ _ (local_hori_lm N i j t Yf h).1 (local_hori_lm N i j t Yf h).2

/- (****** vert ******) -/

theorem local_vert_lm {r : Type _} [Inhabited r]
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
          4 * lengtht (t rest-tr Set.range (Event.vert (i + 1, j))) := by
  rintro ⟨⟨⟨⟨-, hst⟩, -, -, -, hne⟩, hsub⟩, -⟩
  have hA : Set.range (Event.vert (i + 1, j) (r := r)) ⊆ Alpha_pe (r := r) (i, j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inr (Or.inr (Or.inl rfl))⟩
  have hB : Set.range (Event.vert (i + 1, j) (r := r)) ⊆ Alpha_pe (r := r) (i + 1, j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inl rfl⟩
  have h1 := (hst (i, j) (by simp)).1
  have h2 := (hst (i + 1, j) (by simp)).1
  refine ⟨?_, ?_⟩
  · have h := local_i_j_vert _ Yf i j h1 (EX1_request_vert i j Yf hne)
    rwa [rest_tr_of_rest_tr_subset2 hA] at h
  · have h := local_Suc_i_j_vert _ Yf i j h2 (EX1_ungranted_vert i j _ Yf hne hsub h2)
    rwa [rest_tr_of_rest_tr_subset2 hB] at h

/- local_vert -/

theorem local_vert {r : Type _} [Inhabited r]
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
        (lengtht (t rest-tr (Alpha_pe (r := r) (i, j)))) := by
  intro h
  exact EX1_cal1 _ _ _ (local_vert_lm N i j t Yf h).1 (local_vert_lm N i j t Yf h).2

/- (****** hori rev ******) -/

theorem local_hori_rev_lm {r : Type _}
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
          lengtht (t rest-tr Alpha_pe (r := r) (i, j + 1)) := by
  rintro ⟨⟨⟨⟨-, hst⟩, -, -, -, hne⟩, hsub⟩, -⟩
  have hA : Set.range (Event.hori (i, j + 1) (r := r)) ⊆ Alpha_pe (r := r) (i, j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inr (Or.inr (Or.inr rfl))⟩
  have hB : Set.range (Event.hori (i, j + 1) (r := r)) ⊆ Alpha_pe (r := r) (i, j + 1) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inr (Or.inl rfl)⟩
  have h1 := (hst (i, j) (by simp)).1
  have h2 := (hst (i, j + 1) (by simp)).1
  refine ⟨?_, ?_⟩
  · have h := local_i_j_hori_rev _ Yf i j h1 (EX1_ungranted_hori_rev i j _ Yf hne hsub h2)
    rwa [rest_tr_of_rest_tr_subset2 hA] at h
  · have h := local_i_Suc_j_hori_rev _ Yf i j h2 (EX1_request_hori_rev i j Yf hne)
    rwa [rest_tr_of_rest_tr_subset2 hB] at h

/- local_hori_rev -/

theorem local_hori_rev {r : Type _}
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
        ) := by
  intro h
  exact EX1_cal1_rev _ _ _ (local_hori_rev_lm N i j t Yf h).2 (local_hori_rev_lm N i j t Yf h).1

/- (****** vert rev ******) -/

theorem local_vert_rev_lm {r : Type _}
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
          lengtht (t rest-tr Alpha_pe (r := r) (i + 1, j)) := by
  rintro ⟨⟨⟨⟨-, hst⟩, -, -, -, hne⟩, hsub⟩, -⟩
  have hA : Set.range (Event.vert (i + 1, j) (r := r)) ⊆ Alpha_pe (r := r) (i, j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inr (Or.inr (Or.inl rfl))⟩
  have hB : Set.range (Event.vert (i + 1, j) (r := r)) ⊆ Alpha_pe (r := r) (i + 1, j) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, Or.inl rfl⟩
  have h1 := (hst (i, j) (by simp)).1
  have h2 := (hst (i + 1, j) (by simp)).1
  refine ⟨?_, ?_⟩
  · have h := local_i_j_vert_rev _ Yf i j h1 (EX1_ungranted_vert_rev i j _ Yf hne hsub h2)
    rwa [rest_tr_of_rest_tr_subset2 hA] at h
  · have h := local_Suc_i_j_vert_rev _ Yf i j h2 (EX1_request_vert_rev i j Yf hne)
    rwa [rest_tr_of_rest_tr_subset2 hB] at h

/- local_vert_rev -/

theorem local_vert_rev {r : Type _}
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
        ) := by
  intro h
  exact EX1_cal1_rev _ _ _ (local_vert_rev_lm N i j t Yf h).2 (local_vert_rev_lm N i j t Yf h).1

end SA_local
