           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
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
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.Set_F
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
/-  because they unexpectly rewrite UnionT and InterT.                 -/
/-                  Union (B ` A) = (UN x:A. B x)                      -/
/-                  Inter (B ` A) = (INT x:A. B x)                     -/
/- 
declare Union_image_eq [simp del]
declare Inter_image_eq [simp del]
-/
/- no simp rules in Isabelle 2017 
declare Sup_image_eq [simp del]
declare Inf_image_eq [simp del]
-/

def tickTrace : traceType α :=
  Abs_trace [event.Tick]

def restCond (s : traceType α) (n : Nat) : Prop :=
  LT.lt (lengtht s) n ∨
    (lengtht s = n ∧ Exists fun s' => s = s' ^^^ (tickTrace (α := α)) ∧ noTick s')

private theorem restCond_mono {s : traceType α} {m n : Nat} :
    m ≤ n → restCond s m → restCond s n := by
  intro hmn hm
  rcases hm with hlt | ⟨heq, htick⟩
  · exact Or.inl (lt_of_lt_of_le hlt hmn)
  · by_cases hEq : m = n
    · subst hEq
      exact Or.inr ⟨heq, htick⟩
    · exact Or.inl (heq ▸ Nat.lt_of_le_of_ne hmn hEq)

/-(*********************************************************
                 Restriction in Set_F
 *********************************************************)-/

def restF (F : setFType α) (n : Nat) : Set (failure α) :=
  {u | u :f F ∧ restCond u.1 n}

@[simp]
theorem restF_def {F : setFType α} {n : Nat} :
    restF F n = {u | u :f F ∧ restCond u.1 n} :=
  rfl

def LimitF (Fs : infinite_seq (setFType α)) : Set (failure α) :=
  {u | u :f Fs (Nat.succ (lengtht u.1)) ∨
      (u :f Fs (lengtht u.1) ∧
        Exists fun s' => u.1 = s' ^^^ (tickTrace (α := α)) ∧ noTick s')}

@[simp]
theorem LimitF_def {Fs : infinite_seq (setFType α)} :
    LimitF Fs =
      {u | u :f Fs (Nat.succ (lengtht u.1)) ∨
          (u :f Fs (lengtht u.1) ∧
            Exists fun s' => u.1 = s' ^^^ (tickTrace (α := α)) ∧ noTick s')} :=
  rfl

def Limit_setF (Fs : infinite_seq (setFType α)) : setFType α :=
  Abs_setF (LimitF Fs)

@[simp]
theorem Limit_setF_def {Fs : infinite_seq (setFType α)} :
    Limit_setF Fs = Abs_setF (LimitF Fs) :=
  rfl

instance : Inhabited (setFType α) where
  default := {}f

/- isabelle 2009-2 -/

instance instRs0SetF : rs0 (setFType α) where
  restriction F n := Abs_setF (restF F n)

@[simp]
theorem rest_setF_def {F : setFType α} {n : Nat} :
    F .|. n = Abs_setF (restF F n) :=
  rfl

/- isabelle 2009-1
defs (overloaded)
  rest_setF_def : "F .|. n == Abs_setF (F restF n)"
-/

/- --------------------------------------------------------*
 |  The reason why restF deals specially with [Tick]      |
 |  can be found in the proof of lemma "restFpair_T3_F4"  |
 |  in Domain_F_cms.thy.                                  |
 *-------------------------------------------------------- -/

/-(*********************************************************
              Lemmas (Restriction in Set_F)
 *********************************************************)-/

/- (*** restF_def in setF ***) -/

@[simp]
theorem restF_in {F : setFType α} {n : Nat} :
    restF F n ∈ setF (α := α) := by
  intro s X Y hs hYX
  exact ⟨memF_F2 hs.1 hYX, hs.2⟩

/-(*********************************************************
                     .|. on setF
 *********************************************************)-/

theorem rest_setF_iff {F : setFType α} {n : Nat} :
    F .|. n = CollectF (fun f => f :f F ∧ restCond f.1 n) := by
  apply (Rep_setF_inject).mp
  rw [rest_setF_def, CollectF]
  simp [restF]

theorem in_rest_setF {F : setFType α} {s : traceType α} {X : Set (event α)} {n : Nat} :
    (s, X) :f F .|. n ↔ (s, X) :f F ∧ restCond s n := by
  rw [memF, rest_setF_def, Abs_setF_inverse restF_in]
  rfl

theorem rest_setF_eq_iff {F E : setFType α} {n m : Nat} :
    (F .|. n = E .|. m) ↔
      ∀ s X, ((s, X) :f F ∧ restCond s n) ↔ ((s, X) :f E ∧ restCond s m) := by
  constructor
  · intro h s X
    have hEqProp : ((s, X) :f F ∧ restCond s n) = ((s, X) :f E ∧ restCond s m) := by
      simpa only [in_rest_setF] using congrArg (fun G => (s, X) :f G) h
    exact hEqProp ▸ Iff.rfl
  · intro h
    apply (Rep_setF_inject).mp
    ext f
    rcases f with ⟨s, X⟩
    change (s, X) :f F .|. n ↔ (s, X) :f E .|. m
    simpa only [in_rest_setF] using h s X

/- (*** F .|. = E .|. --> F = E ***) -/

theorem rest_setF_eq {F E : setFType α} {s : traceType α} {X : Set (event α)} :
    (s, X) :f F →
      restF F (Nat.succ (lengtht s)) = restF E (Nat.succ (lengtht s)) →
      (s, X) :f E := by
  intro hs hEq
  have hsRest : (s, X) ∈ restF F (Nat.succ (lengtht s)) := by
    refine ⟨hs, ?_⟩
    unfold restCond
    exact Or.inl (Nat.lt_succ_self _)
  have hsRest' : (s, X) ∈ restF E (Nat.succ (lengtht s)) := by
    exact hEq ▸ hsRest
  exact hsRest'.1

/-(*********************************************************
                     SetF --> RS
 *********************************************************)-/

/-(*******************************
        zero_eq_rs_setF
 *******************************)-/

/- (*** (contra) restF 0 ***) -/

theorem contra_zero_setF {F : setFType α} {n : Nat} :
    restF F n ≠ ∅ → 0 < n := by
  intro hne
  cases n with
  | zero =>
      exfalso
      apply hne
      ext f
      rcases f with ⟨s, X⟩
      constructor
      · intro hs
        rcases hs.2 with hlt | ⟨hlen, s', hsEq, hsNo⟩
        · exact False.elim (Nat.not_lt_zero _ hlt)
        · have hlen' :
            lengtht (s' ^^^ (tickTrace (α := α))) = Nat.succ (lengtht s') := by
            simpa using (lengtht_app_event_Suc_last (s := s') (a := event.Tick) hsNo)
          rw [hsEq] at hlen
          have hzero : Nat.succ (lengtht s') = 0 := Eq.trans hlen'.symm hlen
          exact Nat.succ_ne_zero _ hzero
      · intro hs
        exact False.elim hs
  | succ n =>
      exact Nat.succ_pos _

/- (*** restF 0 ***) -/

theorem zero_setF {F : setFType α} :
    restF F 0 = ∅ := by
  ext f
  rcases f with ⟨s, X⟩
  constructor
  · intro hs
    rcases hs.2 with hlt | ⟨hlen, s', hsEq, hsNo⟩
    · exact False.elim (Nat.not_lt_zero _ hlt)
    · have hlen' :
          lengtht (s' ^^^ (tickTrace (α := α))) = Nat.succ (lengtht s') := by
        simpa using (lengtht_app_event_Suc_last (s := s') (a := event.Tick) hsNo)
      rw [hsEq] at hlen
      have hzero : Nat.succ (lengtht s') = 0 := Eq.trans hlen'.symm hlen
      exact Nat.succ_ne_zero _ hzero
  · intro hs
    exact False.elim hs

/- (*** zero_eq_rs_setF ***) -/

theorem zero_rs_setF {F : setFType α} :
    F .|. 0 = {}f := by
  apply (Rep_setF_inject).mp
  rw [rest_setF_def, empF]
  rw [Abs_setF_inverse restF_in, Abs_setF_inverse emptyset_in_setF, zero_setF]

theorem zero_eq_rs_setF (F E : setFType α) :
    F .|. 0 = E .|. 0 := by
  rw [zero_rs_setF, zero_rs_setF]

/-(*******************************
         min_rs_setF
 *******************************)-/

theorem min_rs_setF (F : setFType α) (m n : Nat) :
    ((F .|. m) .|. n) = F .|. (min m n) := by
  apply (rest_setF_eq_iff).2
  intro s X
  constructor
  · intro h
    rcases h with ⟨hsm, hsn⟩
    rcases (in_rest_setF).1 hsm with ⟨hs, hsm'⟩
    have hm : restCond s m := hsm'
    have hn : restCond s n := hsn
    by_cases hmn : m ≤ n
    · exact ⟨hs, by simpa [Nat.min_eq_left hmn] using hm⟩
    · have hnm : n ≤ m := Nat.le_of_lt (lt_of_not_ge hmn)
      exact ⟨hs, by simpa [Nat.min_eq_right hnm] using hn⟩
  · intro h
    rcases h with ⟨hs, hmin⟩
    refine ⟨(in_rest_setF).2 ⟨hs, ?_⟩, ?_⟩
    · exact restCond_mono (Nat.min_le_left m n) hmin
    · exact restCond_mono (Nat.min_le_right m n) hmin

/-(*******************************
        diff_rs_setF
 *******************************)-/

/- (*** contra <= ***) -/

theorem contra_diff_rs_setF_left {F E : setFType α} :
    (∀ n, F .|. n = E .|. n) → F ≤ E := by
  intro hEq
  apply subsetFI
  intro s X hs
  have hsRest : (s, X) :f F .|. Nat.succ (lengtht s) := by
    refine (in_rest_setF).2 ⟨hs, ?_⟩
    unfold restCond
    exact Or.inl (Nat.lt_succ_self _)
  have hsRest' : (s, X) :f E .|. Nat.succ (lengtht s) := by
    simpa [hEq (Nat.succ (lengtht s))] using hsRest
  exact ((in_rest_setF).1 hsRest').1

/- (*** contra = ***) -/

theorem contra_diff_rs_setF {F E : setFType α} :
    (∀ n, F .|. n = E .|. n) → F = E := by
  intro hEq
  apply le_antisymm
  · exact contra_diff_rs_setF_left hEq
  · exact contra_diff_rs_setF_left (F := E) (E := F) (fun n => (hEq n).symm)

/- (*** diff_rs_setF ***) -/

theorem diff_rs_setF {F E : setFType α} :
    F ≠ E → ∃ n : Nat, F .|. n ≠ E .|. n := by
  intro hneq
  by_contra hnot
  apply hneq
  apply contra_diff_rs_setF
  intro n
  by_contra hne
  exact hnot ⟨n, hne⟩

/- (***************************************************************
                        setF ==> RS
 ***************************************************************) -/

instance instRsSetF : rs (setFType α) where
  zero_eq_rs := zero_eq_rs_setF
  min_rs := min_rs_setF
  diff_rs := by
    intro F E
    exact diff_rs_setF

/- (************************************************************
                        setF ==> MS
 ************************************************************) -/

instance instMs0SetF : ms0 (setFType α) where
  distance := distance_rs

@[simp]
theorem setF_distance_def {F E : setFType α} :
    distance F E = distance_rs F E :=
  rfl

instance instMsSetF : ms (setFType α) where
  positive_ms := by
    intro F E
    simpa [setF_distance_def] using positive_rs F E
  diagonal_ms := by
    intro F E
    simpa [setF_distance_def] using (diagonal_rs (x := F) (y := E))
  symmetry_ms := by
    intro F E
    simpa [setF_distance_def] using symmetry_rs F E
  triangle_inequality_ms := by
    intro F E R
    simpa [setF_distance_def] using triangle_inequality_rs F E R

/- (************************************************************
                 i.e.  setF ==> MS & RS 
 ************************************************************) -/

instance instMs0RsSetF : ms0_rs (setFType α) where
  to_distance_rs := by
    intro F E
    rfl

instance instMsRsSetF : ms_rs (setFType α) where

/- (***********************************************************
                      lemmas (Limit)
 ***********************************************************) -/

/- (*** normal_seq lemma ***) -/

theorem normal_seq_setF_less {Fs : infinite_seq (setFType α)}
    {s : traceType α} {X : Set (event α)} {n : Nat}
    (hnormal : normal Fs) (hlt : LT.lt (lengtht s) n) :
    ((s, X) :f Fs (Nat.succ (lengtht s))) ↔ ((s, X) :f Fs n) := by
  have hrest :
      Fs (Nat.succ (lengtht s)) .|. Nat.succ (lengtht s) =
        Fs n .|. Nat.succ (lengtht s) := by
    apply distance_rs_le_1_if
    calc
      distance_rs (Fs (Nat.succ (lengtht s))) (Fs n) =
          distance (Fs (Nat.succ (lengtht s))) (Fs n) := by
            symm
            exact ms0_rs.to_distance_rs _ _
      _ ≤ (1 / 2 : ℝ) ^ min (Nat.succ (lengtht s)) n := hnormal _ _
      _ = (1 / 2 : ℝ) ^ Nat.succ (lengtht s) := by
            simp [Nat.min_eq_left (Nat.succ_le_of_lt hlt)]
  have hEq :
      ((s, X) :f Fs (Nat.succ (lengtht s)) .|. Nat.succ (lengtht s)) ↔
        ((s, X) :f Fs n .|. Nat.succ (lengtht s)) := by
    simpa using congrArg (fun F => (s, X) :f F) hrest
  have hcond : restCond s (Nat.succ (lengtht s)) := by
    unfold restCond
    exact Or.inl (Nat.lt_succ_self _)
  constructor
  · intro hs
    exact ((in_rest_setF).1 (hEq.1 ((in_rest_setF).2 ⟨hs, hcond⟩))).1
  · intro hs
    exact ((in_rest_setF).1 (hEq.2 ((in_rest_setF).2 ⟨hs, hcond⟩))).1

theorem normal_seq_setF_less_only_if {Fs : infinite_seq (setFType α)}
    {s : traceType α} {X : Set (event α)} {n : Nat}
    (hnormal : normal Fs) (hlt : LT.lt (lengtht s) n)
    (hs : (s, X) :f Fs (Nat.succ (lengtht s))) :
    (s, X) :f Fs n := by
  exact (normal_seq_setF_less (Fs := Fs) hnormal hlt).1 hs

/- (*** normal_seq lemma (Tick)*** ) -/

theorem normal_seq_setF_Tick {Fs : infinite_seq (setFType α)}
    {s' : traceType α} {X : Set (event α)} {n : Nat}
    (hnormal : normal Fs) (hle : lengtht (s' ^^^ (tickTrace (α := α))) <= n) (hno : noTick s') :
    ((s' ^^^ (tickTrace (α := α)), X) :f Fs (lengtht (s' ^^^ (tickTrace (α := α))))) ↔
      ((s' ^^^ (tickTrace (α := α)), X) :f Fs n) := by
  have hrest :
      Fs (lengtht (s' ^^^ (tickTrace (α := α)))) .|. lengtht (s' ^^^ (tickTrace (α := α))) =
        Fs n .|. lengtht (s' ^^^ (tickTrace (α := α))) := by
    apply distance_rs_le_1_if
    calc
      distance_rs (Fs (lengtht (s' ^^^ (tickTrace (α := α))))) (Fs n) =
          distance (Fs (lengtht (s' ^^^ (tickTrace (α := α))))) (Fs n) := by
            symm
            exact ms0_rs.to_distance_rs _ _
      _ ≤ (1 / 2 : ℝ) ^ min (lengtht (s' ^^^ (tickTrace (α := α)))) n := hnormal _ _
      _ = (1 / 2 : ℝ) ^ lengtht (s' ^^^ (tickTrace (α := α))) := by
            simp [Nat.min_eq_left hle]
  have hcond :
      restCond (s' ^^^ (tickTrace (α := α))) (lengtht (s' ^^^ (tickTrace (α := α)))) := by
    exact Or.inr ⟨rfl, s', rfl, hno⟩
  have hEq :
      ((s' ^^^ (tickTrace (α := α)), X) :f
          Fs (lengtht (s' ^^^ (tickTrace (α := α)))) .|.
            lengtht (s' ^^^ (tickTrace (α := α)))) ↔
        ((s' ^^^ (tickTrace (α := α)), X) :f Fs n .|. lengtht (s' ^^^ (tickTrace (α := α)))) := by
    simpa using
      congrArg (fun F => (s' ^^^ (tickTrace (α := α)), X) :f F) hrest
  constructor
  · intro hs
    exact ((in_rest_setF).1 (hEq.1 ((in_rest_setF).2 ⟨hs, hcond⟩))).1
  · intro hs
    exact ((in_rest_setF).1 (hEq.2 ((in_rest_setF).2 ⟨hs, hcond⟩))).1

theorem normal_seq_setF_Tick_only_if {Fs : infinite_seq (setFType α)}
    {s' : traceType α} {X : Set (event α)} {n : Nat}
    (hnormal : normal Fs) (hle : lengtht (s' ^^^ (tickTrace (α := α))) <= n)
    (hs :
      (s' ^^^ (tickTrace (α := α)), X) :f
        Fs (lengtht (s' ^^^ (tickTrace (α := α)))))
    (hno : noTick s') :
    (s' ^^^ (tickTrace (α := α)), X) :f Fs n := by
  exact (normal_seq_setF_Tick (Fs := Fs) hnormal hle hno).1 hs

theorem normal_seq_setF_Tick_only_ifE {Fs : infinite_seq (setFType α)}
    {s' : traceType α} {X : Set (event α)} {n : Nat} {R : Prop}
    (hs : (s' ^^^ (tickTrace (α := α)), X) :f Fs n)
    (hnormal : normal Fs) (hle : lengtht (s' ^^^ (tickTrace (α := α))) <= n) (hno : noTick s')
    (hR : (s' ^^^ (tickTrace (α := α)), X) :f Fs (lengtht (s' ^^^ (tickTrace (α := α)))) → R) :
    R := by
  exact hR ((normal_seq_setF_Tick (Fs := Fs) hnormal hle hno).2 hs)

/- (*** LimitF_def in setF ***) -/

@[simp]
theorem LimitF_in {Fs : infinite_seq (setFType α)} :
    LimitF Fs ∈ setF (α := α) := by
  intro s X Y hs hYX
  rcases hs with hs | hs
  · exact Or.inl (memF_F2 hs hYX)
  · exact Or.inr ⟨memF_F2 hs.1 hYX, hs.2⟩

/- (*** Limit_setF_memF ***) -/

theorem Limit_setF_memF {Fs : infinite_seq (setFType α)} :
    ((s, X) :f Limit_setF Fs) ↔
      ((s, X) :f Fs (Nat.succ (lengtht s)) ∨
        (s, X) :f Fs (lengtht s) ∧
          ∃ s', s = s' ^^^ (tickTrace (α := α)) ∧ noTick s') := by
  rw [Limit_setF_def, memF, Abs_setF_inverse LimitF_in]
  rfl

/- (*** Limit_setF lemma ***) -/

theorem Limit_setF_Limit_lm {Fs : infinite_seq (setFType α)} :
    normal Fs → ∀ n, (Limit_setF Fs) .|. n = (Fs n) .|. n := by
  intro hnormal n
  apply (rest_setF_eq_iff).2
  intro s X
  constructor
  · intro hs
    rcases hs with ⟨hsLim, hcond⟩
    rcases (Limit_setF_memF).1 hsLim with hsSucc | ⟨hsLen, hsTick⟩
    · rcases hcond with hlt | ⟨hlen, s', hsEq, hno⟩
      · exact ⟨normal_seq_setF_less_only_if (Fs := Fs) hnormal hlt hsSucc, Or.inl hlt⟩
      · subst hsEq
        have hsBase :
            (s' ^^^ (tickTrace (α := α)), X) :f
              Fs (lengtht (s' ^^^ (tickTrace (α := α)))) :=
          (normal_seq_setF_Tick
            (Fs := Fs)
            (n := Nat.succ (lengtht (s' ^^^ (tickTrace (α := α)))))
            hnormal
            (Nat.le_succ _) hno).2 hsSucc
        exact ⟨by simpa [hlen] using hsBase, Or.inr ⟨hlen, s', rfl, hno⟩⟩
    · rcases hcond with hlt | ⟨hlen, s', hsEq, hno⟩
      · rcases hsTick with ⟨u, huEq, huNo⟩
        subst huEq
        have hle : lengtht (u ^^^ (tickTrace (α := α))) ≤ n := by
          exact le_of_lt hlt
        have hsBase : (u ^^^ (tickTrace (α := α)), X) :f Fs n :=
          normal_seq_setF_Tick_only_if (Fs := Fs) hnormal hle hsLen huNo
        exact ⟨hsBase, Or.inl hlt⟩
      · subst hsEq
        exact ⟨by simpa [hlen] using hsLen, Or.inr ⟨hlen, s', rfl, hno⟩⟩
  · intro hs
    rcases hs with ⟨hsBase, hcond⟩
    rcases hcond with hlt | ⟨hlen, s', hsEq, hno⟩
    · refine ⟨(Limit_setF_memF).2 ?_, Or.inl hlt⟩
      exact Or.inl ((normal_seq_setF_less (Fs := Fs) hnormal hlt).2 hsBase)
    · subst hsEq
      refine ⟨(Limit_setF_memF).2 ?_, Or.inr ⟨hlen, s', rfl, hno⟩⟩
      exact Or.inr ⟨by simpa [hlen] using hsBase, ⟨s', rfl, hno⟩⟩

/- (*** (normal) Fs converges to (Limit_setF Fs) ***) -/

theorem Limit_setF_Limit {Fs : infinite_seq (setFType α)} :
    normal Fs → Fs convergeTo (Limit_setF Fs) := by
  intro hnormal
  apply rest_Limit (y := Limit_setF Fs)
  · intro x y
    exact ms0_rs.to_distance_rs x y
  · exact Limit_setF_Limit_lm hnormal

/- (*** (cauchy) Fs converges to (Limit_setF NF Fs) ***) -/

theorem cauchy_Limit_setF_Limit {Fs : infinite_seq (setFType α)} :
    cauchy Fs → Fs convergeTo (Limit_setF (NF Fs)) := by
  intro hcauchy
  exact normal_form_seq_same_Limit_if (xs := Fs) (y := Limit_setF (NF Fs)) hcauchy
    (Limit_setF_Limit (Fs := NF Fs) (normal_form_seq_normal hcauchy))

/- (************************************
    SetF --> Complete Metric Space
 ************************************) -/

theorem setF_cms {Fs : infinite_seq (setFType α)} :
    cauchy Fs → ∃ F, Fs convergeTo F := by
  intro hcauchy
  exact ⟨Limit_setF (NF Fs), cauchy_Limit_setF_Limit hcauchy⟩

/- (************************************************************
                   setF ==> CMS and RS
 ************************************************************) -/

instance instCmsSetF : cms (setFType α) where
  complete_ms := by
    intro Fs
    exact setF_cms

instance instCmsRsSetF : cms_rs (setFType α) where

/- (*** (normal) Limit Fs = Limit_setF Fs ***) -/

theorem Limit_setF_Limit_eq {Fs : infinite_seq (setFType α)} :
    normal Fs → Limit Fs = Limit_setF Fs := by
  intro hnormal
  exact unique_convergence (Limit_is (normal_cauchy hnormal)) (Limit_setF_Limit hnormal)

/- ----------------------------------------------------------*
 |                                                          |
 |                       cms rs order                       |
 |                                                          |
 *---------------------------------------------------------- -/

instance instMsRsOrder0SetF : ms_rs_order0 (setFType α) where

instance instMsRsOrderSetF : ms_rs_order (setFType α) where
  rs_order_iff := by
    intro F E
    constructor
    · intro hrest
      exact subsetFI (fun s X hs => by
        have hsRest : (s, X) :f F .|. Nat.succ (lengtht s) := by
          refine (in_rest_setF).2 ⟨hs, ?_⟩
          unfold restCond
          exact Or.inl (Nat.lt_succ_self _)
        have hsRest' : (s, X) :f E .|. Nat.succ (lengtht s) := hrest _ hsRest
        exact ((in_rest_setF).1 hsRest').1)
    · intro hle n
      exact subsetFI (fun s X hs => by
        rcases (in_rest_setF).1 hs with ⟨hsBase, hcond⟩
        exact (in_rest_setF).2 ⟨hle hsBase, hcond⟩)

instance instCmsRsOrderSetF : cms_rs_order (setFType α) where

end
