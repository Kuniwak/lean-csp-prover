           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |

            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.Domain_T
import LeanCspProver.CSP.RS

noncomputable section

/- 
(*****************************************************************

         1. 
         2. 
         3. 
         4. 

 *****************************************************************)
-/

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `UnionT` and `InterT`.             -/
/-                  `Union (B \` A) = (UN x:A. B x)`                  -/
/-                  `Inter (B \` A) = (INT x:A. B x)`                 -/

/- 
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
-/
/- no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
-/

/- (**********************************************************
           Definitions (Restriction in domT)
 **********************************************************) -/

def restT (T : domTType α) (n : Nat) : Set (traceType α) :=
  {s | s :t T ∧ lengtht s <= n}

@[simp]
theorem restT_def {T : domTType α} {n : Nat} :
    restT T n = {s | s :t T ∧ lengtht s <= n} :=
  rfl

def LimitT (Ts : infinite_seq (domTType α)) : Set (traceType α) :=
  {s | s :t Ts (lengtht s)}

@[simp]
theorem LimitT_def {Ts : infinite_seq (domTType α)} :
    LimitT Ts = {s | s :t Ts (lengtht s)} :=
  rfl

def Limit_domT (Ts : infinite_seq (domTType α)) : domTType α :=
  Abs_domT (LimitT Ts)

@[simp]
theorem Limit_domT_def {Ts : infinite_seq (domTType α)} :
    Limit_domT Ts = Abs_domT (LimitT Ts) :=
  rfl

instance : Inhabited (domTType α) where
  default := Abs_domT ({<>} : Set (traceType α))

/- isabelle 2009-2 -/

instance instRs0DomT : rs0 (domTType α) where
  restriction T n := Abs_domT (restT T n)

@[simp]
theorem rest_domT_def {T : domTType α} {n : Nat} :
    T .|. n = Abs_domT (restT T n) :=
  rfl

/- isabelle 2009-1
defs (overloaded)
  rest_domT_def : "T .|. n == Abs_domT (T restT n)"
-/

/- (**********************************************************
              Lemmas (Restriction in Dom_T)
 **********************************************************) -/

/- (*** restT_def in domT ***) -/

@[simp]
theorem restT_in {T : domTType α} {n : Nat} :
    restT T n ∈ domT (α := α) := by
  change HC_T1 (restT T n)
  constructor
  · intro hEmpty
    have hNil : <> ∈ restT T n := by
      exact ⟨nilt_in_T (T := T), by simp⟩
    rw [hEmpty] at hNil
    cases hNil
  · intro s t hst
    rcases hst with ⟨ht, hp⟩
    exact ⟨memT_prefix_closed ht.1 hp, le_trans (length_of_prefix hp) ht.2⟩

/- (*** restT in domT ***) -/

theorem restT_def_in {T : domTType α} {n : Nat} :
    ({s | s :t T ∧ lengtht s <= n} : Set (traceType α)) ∈ domT (α := α) := by
  change restT T n ∈ domT (α := α)
  exact restT_in

/- (*********************************************************
                     .|. on dom_T
 *********************************************************) -/

theorem rest_domT_iff {T : domTType α} {n : Nat} :
    T .|. n = CollectT (fun s => s :t T ∧ lengtht s <= n) := by
  rw [rest_domT_def, CollectT, restT]

theorem in_rest_domT {s : traceType α} {T : domTType α} {n : Nat} :
    s :t T .|. n ↔ (s :t T ∧ lengtht s <= n) := by
  rw [memT, rest_domT_def, Abs_domT_inverse restT_in]
  rfl

theorem rest_domT_eq_iff {T S : domTType α} {n m : Nat} :
    (T .|. n = S .|. m) ↔
      ∀ s, (s :t T ∧ lengtht s <= n) ↔ (s :t S ∧ lengtht s <= m) := by
  constructor
  · intro h s
    constructor
    · intro hs
      have hsRest : s :t T .|. n := (in_rest_domT (s := s) (T := T) (n := n)).2 hs
      have hsRest' : s :t S .|. m := by
        simpa [h] using hsRest
      exact (in_rest_domT (s := s) (T := S) (n := m)).1 hsRest'
    · intro hs
      have hsRest : s :t S .|. m := (in_rest_domT (s := s) (T := S) (n := m)).2 hs
      have hsRest' : s :t T .|. n := by
        simpa [h] using hsRest
      exact (in_rest_domT (s := s) (T := T) (n := n)).1 hsRest'
  · intro h
    apply (Rep_domT_inject).mp
    ext s
    simpa [memT] using
      (in_rest_domT (s := s) (T := T) (n := n)).trans
        ((h s).trans ((in_rest_domT (s := s) (T := S) (n := m)).symm))

/- (*********************************************************
                     Dom_T --> RS
 *********************************************************) -/

/- (*******************************
        zero_eq_rs_domT
 *******************************) -/

/- (*** restT 0 ***) -/

theorem zero_domT {T : domTType α} :
    restT T 0 = ({<>} : Set (traceType α)) := by
  ext s
  constructor
  · intro hs
    have hlen : lengtht s = 0 := Nat.le_zero.mp hs.2
    simpa [lengtht_zero] using hlen
  · intro hs
    subst hs
    exact ⟨nilt_in_T (T := T), by simp⟩

/- (*** zero_eq_rs_domT ***) -/

theorem zero_rs_domT {T : domTType α} :
    T .|. 0 = Abs_domT ({<>} : Set (traceType α)) := by
  apply (Rep_domT_inject).mp
  rw [rest_domT_def, Abs_domT_inverse restT_in, Abs_domT_inverse nilt_set_in, zero_domT]

theorem zero_eq_rs_domT (T S : domTType α) :
    T .|. 0 = S .|. 0 := by
  rw [zero_rs_domT, zero_rs_domT]

/- (*******************************
         min_rs_domT
 *******************************) -/

theorem min_rs_domT (T : domTType α) (m n : Nat) :
    ((T .|. m) .|. n) = T .|. (min m n) := by
  apply (Rep_domT_inject).mp
  ext s
  constructor
  · intro hs
    rcases (in_rest_domT (s := s) (T := T .|. m) (n := n)).1 hs with ⟨hsm, hsn⟩
    rcases (in_rest_domT (s := s) (T := T) (n := m)).1 hsm with ⟨hsBase, hsmLen⟩
    exact (in_rest_domT (s := s) (T := T) (n := min m n)).2 ⟨hsBase, le_min hsmLen hsn⟩
  · intro hs
    rcases (in_rest_domT (s := s) (T := T) (n := min m n)).1 hs with ⟨hsBase, hsMin⟩
    rcases le_min_iff.mp hsMin with ⟨hsmLen, hsn⟩
    exact (in_rest_domT (s := s) (T := T .|. m) (n := n)).2
      ⟨(in_rest_domT (s := s) (T := T) (n := m)).2 ⟨hsBase, hsmLen⟩, hsn⟩

/- (*******************************
         diff_rs_domT
 *******************************) -/

/- (*** contra = ***) -/

theorem contra_diff_rs_domT {T S : domTType α} :
    (∀ n, T .|. n = S .|. n) → T = S := by
  intro hEq
  apply (Rep_domT_inject).mp
  ext s
  have hs := (rest_domT_eq_iff (T := T) (S := S) (n := lengtht s) (m := lengtht s)).1
    (hEq (lengtht s)) s
  simpa using hs

/- (*** diff_rs_domT ***) -/

theorem diff_rs_domT {T S : domTType α} :
    T ≠ S → ∃ n, T .|. n ≠ S .|. n := by
  classical
  intro hneq
  by_contra hnot
  apply hneq
  apply contra_diff_rs_domT
  intro n
  by_contra hne
  exact hnot ⟨n, hne⟩

/- (***************************************************************
                       domT ==> RS
 ***************************************************************) -/

instance instRsDomT : rs (domTType α) where
  zero_eq_rs := zero_eq_rs_domT
  min_rs := min_rs_domT
  diff_rs := by
    intro T S
    exact diff_rs_domT

/- (************************************************************
                        domT ==> MS
 ************************************************************) -/

instance instMs0DomT : ms0 (domTType α) where
  distance := distance_rs

@[simp]
theorem domT_distance_def {T S : domTType α} :
    distance T S = distance_rs T S :=
  rfl

instance instMsDomT : ms (domTType α) where
  positive_ms := by
    intro T S
    simpa [domT_distance_def] using positive_rs T S
  diagonal_ms := by
    intro T S
    simpa [domT_distance_def] using (diagonal_rs (x := T) (y := S))
  symmetry_ms := by
    intro T S
    simpa [domT_distance_def] using symmetry_rs T S
  triangle_inequality_ms := by
    intro T S R
    simpa [domT_distance_def] using triangle_inequality_rs T S R

/- (************************************************************
                 i.e.  domT ==> MS & RS 
 ************************************************************) -/

instance instMs0RsDomT : ms0_rs (domTType α) where
  to_distance_rs := by
    intro T S
    rfl

instance instMsRsDomT : ms_rs (domTType α) where

/- (***********************************************************
                      lemmas (Limit)
 ***********************************************************) -/

/- (*** normal_seq lemma ***) -/

theorem normal_seq_domT {Ts : infinite_seq (domTType α)}
    {s : traceType α} {n : Nat} :
    normal Ts → lengtht s <= n → ((s :t Ts (lengtht s)) ↔ (s :t Ts n)) := by
  intro hnormal hle
  have hrest :
      Ts (lengtht s) .|. lengtht s = Ts n .|. lengtht s := by
    apply distance_rs_le_1_if
    calc
      distance_rs (Ts (lengtht s)) (Ts n) = distance (Ts (lengtht s)) (Ts n) := by
        symm
        exact ms0_rs.to_distance_rs _ _
      _ <= (1 / 2 : ℝ) ^ min (lengtht s) n := hnormal _ _
      _ = (1 / 2 : ℝ) ^ lengtht s := by
        simp [Nat.min_eq_left hle]
  have hEq :
      (s :t Ts (lengtht s) .|. lengtht s) ↔ (s :t Ts n .|. lengtht s) := by
    simpa using Iff.of_eq (congrArg (fun T => s :t T) hrest)
  constructor
  · intro hs
    exact ((in_rest_domT).1 (hEq.1 ((in_rest_domT).2 ⟨hs, le_rfl⟩))).1
  · intro hs
    exact ((in_rest_domT).1 (hEq.2 ((in_rest_domT).2 ⟨hs, le_rfl⟩))).1

theorem normal_seq_domT_only_if {Ts : infinite_seq (domTType α)}
    {s : traceType α} {n : Nat}
    (hnormal : normal Ts) (hle : lengtht s <= n) (hs : s :t Ts (lengtht s)) :
    s :t Ts n := by
  exact (normal_seq_domT (Ts := Ts) hnormal hle).1 hs

theorem normal_seq_domT_if {Ts : infinite_seq (domTType α)}
    {s : traceType α} {n : Nat}
    (hnormal : normal Ts) (hle : lengtht s <= n) (hs : s :t Ts n) :
    s :t Ts (lengtht s) := by
  exact (normal_seq_domT (Ts := Ts) hnormal hle).2 hs

/- (*** LimitT_def in domT ***) -/

@[simp]
theorem LimitT_in {Ts : infinite_seq (domTType α)} :
    normal Ts → LimitT Ts ∈ domT (α := α) := by
  intro hnormal
  change HC_T1 (LimitT Ts)
  constructor
  · intro hEmpty
    have hNil : <> ∈ LimitT Ts := by
      simp [LimitT, nilt_in_T]
    rw [hEmpty] at hNil
    cases hNil
  · intro s t hst
    have hsLong : s :t Ts (lengtht t) := memT_prefix_closed hst.1 hst.2
    have hlen : lengtht s <= lengtht t := length_of_prefix hst.2
    exact normal_seq_domT_if (Ts := Ts) hnormal hlen hsLong

/- (*** :t Limit_domT ***) -/

theorem Limit_domT_memT {Ts : infinite_seq (domTType α)} :
    normal Ts → ((s :t Limit_domT Ts) ↔ (s :t Ts (lengtht s))) := by
  intro hnormal
  rw [Limit_domT_def, memT, Abs_domT_inverse (LimitT_in hnormal)]
  rfl

/- (*** Limit_domT lemma ***) -/

theorem Limit_domT_Limit_lm {Ts : infinite_seq (domTType α)} :
    normal Ts → ∀ n, (Limit_domT Ts) .|. n = (Ts n) .|. n := by
  intro hnormal n
  apply (rest_domT_eq_iff).2
  intro s
  constructor
  · intro hs
    rcases hs with ⟨hsLim, hsLen⟩
    have hsBase : s :t Ts (lengtht s) := (Limit_domT_memT (Ts := Ts) hnormal).1 hsLim
    exact ⟨normal_seq_domT_only_if (Ts := Ts) hnormal hsLen hsBase, hsLen⟩
  · intro hs
    rcases hs with ⟨hsBase, hsLen⟩
    exact ⟨(Limit_domT_memT (Ts := Ts) hnormal).2
      (normal_seq_domT_if (Ts := Ts) hnormal hsLen hsBase), hsLen⟩

/- (*** (normal) Ts converges to (Limit_domT Ts) ***) -/

theorem Limit_domT_Limit {Ts : infinite_seq (domTType α)} :
    normal Ts → Ts convergeTo (Limit_domT Ts) := by
  intro hnormal
  apply rest_Limit (y := Limit_domT Ts)
  · intro x y
    exact ms0_rs.to_distance_rs x y
  · exact Limit_domT_Limit_lm hnormal

/- (*** (cauchy) Ts converges to (Limit_domT NF Ts) ***) -/

theorem cauchy_Limit_domT_Limit {Ts : infinite_seq (domTType α)} :
    cauchy Ts → Ts convergeTo (Limit_domT (NF Ts)) := by
  intro hcauchy
  exact normal_form_seq_same_Limit_if (xs := Ts) (y := Limit_domT (NF Ts)) hcauchy
    (Limit_domT_Limit (Ts := NF Ts) (normal_form_seq_normal hcauchy))

/- (***************************************
     Dom_T --> Complete Metric Space
 ***************************************) -/

theorem domT_cms {Ts : infinite_seq (domTType α)} :
    cauchy Ts → ∃ T, Ts convergeTo T := by
  intro hcauchy
  exact ⟨Limit_domT (NF Ts), cauchy_Limit_domT_Limit hcauchy⟩

/- (************************************************************
                   domT ==> CMS and RS
 ************************************************************) -/

instance instCmsDomT : cms (domTType α) where
  complete_ms := by
    intro Ts
    exact domT_cms

instance instCmsRsDomT : cms_rs (domTType α) where

/- (*** (normal) Limit Ts = Limit_domT Ts ***) -/

theorem Limit_domT_Limit_eq {Ts : infinite_seq (domTType α)} :
    normal Ts → Limit Ts = Limit_domT Ts := by
  intro hnormal
  exact unique_convergence (Limit_is (normal_cauchy hnormal)) (Limit_domT_Limit hnormal)

/- ----------------------------------------------------------*
 |                                                          |
 |                       cms rs order                       |
 |                                                          |
 *---------------------------------------------------------- -/

instance instMsRsOrder0DomT : ms_rs_order0 (domTType α) where

instance instMsRsOrderDomT : ms_rs_order (domTType α) where
  rs_order_iff := by
    intro T S
    constructor
    · intro hrest
      exact subdomTI (fun t ht => by
        have htRest : t :t T .|. lengtht t := (in_rest_domT).2 ⟨ht, le_rfl⟩
        have htRest' : t :t S .|. lengtht t := hrest _ htRest
        exact ((in_rest_domT).1 htRest').1)
    · intro hle n
      exact subdomTI (fun t ht => by
        rcases (in_rest_domT).1 ht with ⟨htBase, htLen⟩
        exact (in_rest_domT).2 ⟨hle htBase, htLen⟩)

instance instCmsRsOrderDomT : cms_rs_order (domTType α) where

/- (****************** to add them again ******************) -/

/- 
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
-/
/- 
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
-/

end
