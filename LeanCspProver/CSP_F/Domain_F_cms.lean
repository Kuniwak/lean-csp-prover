           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
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
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2018         |
            |               February 2019  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.Domain_F
import LeanCspProver.CSP_T.Domain_T_cms
import LeanCspProver.CSP_F.Set_F_cms
import LeanCspProver.CSP.RS_pair
import LeanCspProver.CSP.RS_prod

open Classical

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
/- no simp rules in Isabelle 2017 -/

/-
(*********************************************************
                 Restriction in Dom_F
 *********************************************************)
-/

def restTF (F : domFType α) (n : Nat) : domTsetF α :=
  (Rep_domF F) .|. n

@[simp]
theorem restTF_def {F : domFType α} {n : Nat} :
    restTF F n = (Rep_domF F) .|. n :=
  rfl

def LimitTF (Fs : infinite_seq (domFType α)) : domTsetF α :=
  pair_Limit (Rep_domF ∘ Fs)

@[simp]
theorem LimitTF_def {Fs : infinite_seq (domFType α)} :
    LimitTF Fs = pair_Limit (Rep_domF ∘ Fs) :=
  rfl

def Limit_domF (Fs : infinite_seq (domFType α)) : domFType α :=
  Abs_domF (LimitTF Fs)

@[simp]
theorem Limit_domF_def {Fs : infinite_seq (domFType α)} :
    Limit_domF Fs = Abs_domF (LimitTF Fs) :=
  rfl

instance : Inhabited (domFType α) where
  default := Abs_domF ((Abs_domT ({<>} : Set (traceType α))), ({}f : setFType α))

/- isabelle 2009-2 -/

instance instRs0DomF : rs0 (domFType α) where
  restriction F n := Abs_domF (restTF F n)

@[simp]
theorem rest_domF_def {F : domFType α} {n : Nat} :
    F .|. n = Abs_domF (restTF F n) :=
  rfl

private theorem restCond_le {s : traceType α} {n : Nat} :
    restCond s n → lengtht s ≤ n := by
  intro hs
  rcases hs with hlt | ⟨heq, -⟩
  · exact Nat.le_of_lt hlt
  · exact heq.le

private theorem restCond_notick_lt {s : traceType α} {n : Nat}
    (hrest : restCond s n) (hNo : noTick s) :
    LT.lt (lengtht s) n := by
  rcases hrest with hlt | ⟨heq, s', hsEq, hsNo⟩
  · exact hlt
  · subst hsEq
    have hTickNo : noTick (tickTrace (α := α)) :=
      (decompo_appt_noTick_only_if
        (s := s') (t := tickTrace (α := α)) (Or.inl hsNo) hNo).2
    exact False.elim (not_noTick_Tick hTickNo)

private theorem restCond_tick {s : traceType α} {n : Nat}
    (hNo : noTick s) (hlen : lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)) ≤ n) :
    restCond (s ^^^ (Abs_trace [event.Tick] : traceType α)) n := by
  have hEqLen :
      lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)) = Nat.succ (lengtht s) := by
    simpa using (lengtht_app_event_Suc_last (s := s) (a := event.Tick) hNo)
  rcases lt_or_eq_of_le hlen with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, s, rfl, hNo⟩

private theorem restCond_of_tick_le {s : traceType α} {n : Nat}
    (hNo : noTick s) (hlen : lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)) ≤ n) :
    restCond s n := by
  have hEqLen :
      lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)) = Nat.succ (lengtht s) := by
    simpa using (lengtht_app_event_Suc_last (s := s) (a := event.Tick) hNo)
  have hle : Nat.succ (lengtht s) ≤ n := by
    simpa [hEqLen] using hlen
  exact Or.inl (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle)

/-
(*********************************************************
              Lemmas (Restriction in Dom_F)
 *********************************************************)
-/

/- (*** restTF (T2) ***) -/

theorem restTF_T2 {F : domFType α} {n : Nat} :
    HC_T2 (restTF F n) := by
  intro s X hsX
  rcases (in_rest_setF (F := (Rep_domF F).2) (s := s) (X := X) (n := n)).1 hsX with ⟨hsBase, hrest⟩
  exact (in_rest_domT (T := (Rep_domF F).1) (s := s) (n := n)).2
    ⟨domTsetF_T2 (TF := Rep_domF F) F.2 hsBase, restCond_le (α := α) hrest⟩

/- (*** restTF (F3) ***) -/

theorem restTF_F3 {F : domFType α} {n : Nat} :
    HC_F3 (restTF F n) := by
  intro s X Y hsX hNo hY
  rcases (in_rest_setF (F := (Rep_domF F).2) (s := s) (X := X) (n := n)).1 hsX with ⟨hsBase, hrest⟩
  have hlt : LT.lt (lengtht s) n := restCond_notick_lt hrest hNo
  have hYBase :
      ∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) (Rep_domF F).1 := by
    intro a ha hmem
    apply hY a ha
    refine (in_rest_domT (T := (Rep_domF F).1)
      (s := s ^^^ (Abs_trace [a] : traceType α)) (n := n)).2 ?_
    constructor
    · exact hmem
    · have hlen :
          lengtht (s ^^^ (Abs_trace [a] : traceType α)) = Nat.succ (lengtht s) := by
        simpa using (lengtht_app_event_Suc_last (s := s) (a := a) hNo)
      exact hlen ▸ Nat.succ_le_of_lt hlt
  refine (in_rest_setF (F := (Rep_domF F).2) (s := s) (X := X ∪ Y) (n := n)).2 ?_
  exact ⟨domTsetF_F3 (TF := Rep_domF F) F.2 hsBase hNo hYBase, hrest⟩

/- (*** restTF (T3_F4) ***) -/

theorem restTF_T3_F4 {F : domFType α} {n : Nat} :
    HC_T3_F4 (restTF F n) := by
  intro s hs
  rcases (in_rest_domT (T := (Rep_domF F).1)
    (s := s ^^^ (Abs_trace [event.Tick] : traceType α)) (n := n)).1 hs.1 with
    ⟨hTickBase, hlen⟩
  rcases domTsetF_T3_F4 (TF := Rep_domF F) F.2 hTickBase hs.2 with ⟨hF4, hT3⟩
  constructor
  · refine (in_rest_setF (F := (Rep_domF F).2) (s := s) (X := Evset) (n := n)).2 ?_
    exact ⟨hF4, restCond_of_tick_le hs.2 hlen⟩
  · intro X
    refine (in_rest_setF (F := (Rep_domF F).2)
      (s := s ^^^ (Abs_trace [event.Tick] : traceType α)) (X := X) (n := n)).2 ?_
    exact ⟨hT3 X, restCond_tick hs.2 hlen⟩

/- (*** restTF in domF ***) -/

@[simp]
theorem restTF_in {F : domFType α} {n : Nat} :
    restTF F n ∈ domF (α := α) := by
  rw [domF_iff]
  exact ⟨restTF_T2 (F := F) (n := n), restTF_F3 (F := F) (n := n), restTF_T3_F4 (F := F) (n := n)⟩

/-
(*********************************************************
                     Dom_F --> RS
 *********************************************************)
-/

/- (*** rest_domF --> restTF ***) -/

theorem Rep_rest_domF {F E : domFType α} {n m : Nat} :
    ((F .|. n : domFType α) = E .|. m) ↔
      ((Rep_domF F) .|. n = (Rep_domF E) .|. m) := by
  constructor
  · intro h
    have hRep : Rep_domF (F .|. n) = Rep_domF (E .|. m) := congrArg Rep_domF h
    rw [rest_domF_def, rest_domF_def] at hRep
    rw [Abs_domF_inverse (SF := restTF F n) (restTF_in (F := F) (n := n)),
      Abs_domF_inverse (SF := restTF E m) (restTF_in (F := E) (n := m))] at hRep
    simpa [restTF_def] using hRep
  · intro h
    apply (Rep_domF_inject (SF := F .|. n) (SE := E .|. m)).mp
    rw [rest_domF_def, rest_domF_def]
    rw [Abs_domF_inverse (SF := restTF F n) (restTF_in (F := F) (n := n)),
      Abs_domF_inverse (SF := restTF E m) (restTF_in (F := E) (n := m))]
    simpa [restTF_def] using h

/- (*** zero_eq_rs_domF ***) -/

theorem zero_eq_rs_domF (F E : domFType α) :
    F .|. 0 = E .|. 0 := by
  exact (Rep_rest_domF (F := F) (E := E) (n := 0) (m := 0)).2 (rs.zero_eq_rs _ _)

/- (*** min_rs_domF ***) -/

theorem min_rs_domF (F : domFType α) (m n : Nat) :
    ((F .|. m) .|. n) = F .|. (min m n) := by
  exact (Rep_rest_domF (F := F .|. m) (E := F) (n := n) (m := min m n)).2 <| by
    rw [rest_domF_def]
    rw [Abs_domF_inverse (SF := restTF F m) (restTF_in (F := F) (n := m))]
    simpa [restTF_def] using (rs.min_rs (Rep_domF F) m n)

/- (*** diff_rs_domF ***) -/

theorem diff_rs_domF {F E : domFType α} :
    F ≠ E → ∃ n : Nat, F .|. n ≠ E .|. n := by
  intro hneq
  by_contra h
  apply hneq
  apply (Rep_domF_inject (SF := F) (SE := E)).mp
  apply contra_diff_rs
  intro n
  have hEq : F .|. n = E .|. n := by
    by_contra hEq
    exact h ⟨n, hEq⟩
  exact (Rep_rest_domF (F := F) (E := E) (n := n) (m := n)).1 hEq

/-
(***************************************************************
                        domF ==> RS
 ***************************************************************)
-/

instance instRsDomF : rs (domFType α) where
  zero_eq_rs := zero_eq_rs_domF
  min_rs := min_rs_domF
  diff_rs := by
    intro F E
    exact diff_rs_domF

/-
(************************************************************
                        domF ==> MS
 ************************************************************)
-/

instance instMs0DomF : ms0 (domFType α) where
  distance := distance_rs

@[simp]
theorem domF_distance_def {F E : domFType α} :
    distance F E = distance_rs F E :=
  rfl

instance instMsDomF : ms (domFType α) where
  positive_ms := by
    intro F E
    simpa [domF_distance_def] using positive_rs F E
  diagonal_ms := by
    intro F E
    simpa [domF_distance_def] using (diagonal_rs (x := F) (y := E))
  symmetry_ms := by
    intro F E
    simpa [domF_distance_def] using symmetry_rs F E
  triangle_inequality_ms := by
    intro F E G
    simpa [domF_distance_def] using triangle_inequality_rs F E G

/-
(************************************************************
                 i.e.  domF ==> MS & RS
 ************************************************************)
-/

instance instMs0RsDomF : ms0_rs (domFType α) where
  to_distance_rs := by
    intro F E
    rfl

instance instMsRsDomF : ms_rs (domFType α) where

/- (**********************************************************
                      .|. decompo
 **********************************************************) -/

theorem rest_decompo_domF {SF1 SF2 : domFType α} {n m : Nat} :
    (SF1 .|. n = SF2 .|. m) ↔
      (fstF SF1 .|. n = fstF SF2 .|. m ∧ sndF SF1 .|. n = sndF SF2 .|. m) := by
  constructor
  · intro h
    have hRep := (Rep_rest_domF (F := SF1) (E := SF2) (n := n) (m := m)).1 h
    have hRep' :
        ((fstF SF1 .|. n), (sndF SF1 .|. n)) = ((fstF SF2 .|. m), (sndF SF2 .|. m)) := by
      simpa [restTF_def, fstF, sndF, pair_restriction_def] using hRep
    exact pair_eq_decompo.mp hRep'
  · rintro ⟨hfst, hsnd⟩
    have hRep :
        ((fstF SF1 .|. n), (sndF SF1 .|. n)) = ((fstF SF2 .|. m), (sndF SF2 .|. m)) :=
      pair_eq_decompo.mpr ⟨hfst, hsnd⟩
    exact (Rep_rest_domF (F := SF1) (E := SF2) (n := n) (m := m)).2 <| by
      simpa [restTF_def, fstF, sndF, pair_restriction_def] using hRep

/-
(***********************************************************
                    lemmas (distance)
 ***********************************************************)
-/

/- (*** distance ***) -/

theorem distance_Rep_domF {F E : domFType α} :
    distance F E = distance (Rep_domF F) (Rep_domF E) := by
  calc
    distance F E = distance_rs F E := ms0_rs.to_distance_rs _ _
    _ = distance_rs (Rep_domF F) (Rep_domF E) := by
      apply rest_distance_eq
      intro n
      simpa using (Rep_rest_domF (F := F) (E := E) (n := n) (m := n))
    _ = distance (Rep_domF F) (Rep_domF E) := by
      symm
      exact ms0_rs.to_distance_rs _ _

theorem distance_Abs_domF {T1 T2 : domTType α} {F1 F2 : setFType α}
    (h1 : (T1, F1) ∈ domF (α := α)) (h2 : (T2, F2) ∈ domF (α := α)) :
    distance (Abs_domF (T1, F1)) (Abs_domF (T2, F2)) =
      distance ((T1, F1) : domTsetF α) ((T2, F2) : domTsetF α) := by
  calc
    distance (Abs_domF (T1, F1)) (Abs_domF (T2, F2)) =
        distance (Rep_domF (Abs_domF (T1, F1))) (Rep_domF (Abs_domF (T2, F2))) :=
      distance_Rep_domF
    _ = distance ((T1, F1) : domTsetF α) ((T2, F2) : domTsetF α) := by
      simp [h1, h2]

/- (*** normal ***) -/

theorem normal_domF {Fs : infinite_seq (domFType α)} :
    normal Fs = normal (Rep_domF ∘ Fs) := by
  apply propext
  constructor
  · intro h n m
    calc
      distance ((Rep_domF ∘ Fs) n) ((Rep_domF ∘ Fs) m) =
          distance (Fs n) (Fs m) := by
            simpa [Function.comp] using (distance_Rep_domF (F := Fs n) (E := Fs m)).symm
      _ ≤ (1 / 2 : ℝ) ^ min n m := h n m
  · intro h n m
    calc
      distance (Fs n) (Fs m) = distance ((Rep_domF ∘ Fs) n) ((Rep_domF ∘ Fs) m) := by
        simpa [Function.comp] using (distance_Rep_domF (F := Fs n) (E := Fs m))
      _ ≤ (1 / 2 : ℝ) ^ min n m := h n m

theorem normal_domF_only_if {Fs : infinite_seq (domFType α)} :
    normal Fs → normal (Rep_domF ∘ Fs) := by
  simpa [normal_domF]

theorem normal_of_domF {Fs : infinite_seq (domFType α)} :
    normal Fs → (normal (fstF ∘ Fs) ∧ normal (sndF ∘ Fs)) := by
  intro hnormal
  have hrep : normal (Rep_domF ∘ Fs) := normal_domF_only_if hnormal
  rw [pair_normal_seq_compo_iff] at hrep
  simpa [fstF, sndF, Function.comp] using hrep

/- (*** cauchy ***) -/

theorem cauchy_domF {Fs : infinite_seq (domFType α)} :
    cauchy Fs = cauchy (Rep_domF ∘ Fs) := by
  apply propext
  constructor
  · intro h delta hdelta
    rcases h delta hdelta with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro i j hij
    calc
      distance ((Rep_domF ∘ Fs) i) ((Rep_domF ∘ Fs) j) =
          distance (Fs i) (Fs j) := by
            simpa [Function.comp] using (distance_Rep_domF (F := Fs i) (E := Fs j)).symm
      _ < delta := hn i j hij
  · intro h delta hdelta
    rcases h delta hdelta with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    intro i j hij
    calc
      distance (Fs i) (Fs j) = distance ((Rep_domF ∘ Fs) i) ((Rep_domF ∘ Fs) j) := by
        simpa [Function.comp] using (distance_Rep_domF (F := Fs i) (E := Fs j))
      _ < delta := hn i j hij

theorem cauchy_domF_only_if {Fs : infinite_seq (domFType α)} :
    cauchy Fs → cauchy (Rep_domF ∘ Fs) := by
  simpa [cauchy_domF]

theorem cauchy_of_domF {Fs : infinite_seq (domFType α)} :
    cauchy Fs → (cauchy (fstF ∘ Fs) ∧ cauchy (sndF ∘ Fs)) := by
  intro hcauchy
  have hrep : cauchy (Rep_domF ∘ Fs) := cauchy_domF_only_if hcauchy
  constructor
  · simpa [fstF, Function.comp] using (pair_cauchy_seq_fst hrep)
  · simpa [sndF, Function.comp] using (pair_cauchy_seq_snd hrep)

/-
(***********************************************************
                      lemmas (Limit)
 ***********************************************************)
-/

/- (*** convergeTo domF ***) -/

theorem convergeTo_domF {Fs : infinite_seq (domFType α)} {TF : domTsetF α}
    (hconv : (Rep_domF ∘ Fs) convergeTo TF) (hTF : TF ∈ domF (α := α)) :
    Fs convergeTo Abs_domF TF := by
  intro eps heps
  rcases hconv eps heps with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro m hm
  calc
    distance (Abs_domF TF) (Fs m) = distance TF (Rep_domF (Fs m)) := by
      simpa [hTF] using (distance_Rep_domF (F := Abs_domF TF) (E := Fs m))
    _ < eps := hn m hm

/- (*** LimitTF ***) -/

theorem LimitTF_iff {Fs : infinite_seq (domFType α)} :
    normal (Rep_domF ∘ Fs) →
      pair_Limit (Rep_domF ∘ Fs) =
        (Limit_domT (fstF ∘ Fs), Limit_setF (sndF ∘ Fs)) := by
  intro hnormal
  rw [pair_normal_seq_compo_iff] at hnormal
  rcases hnormal with ⟨hfst, hsnd⟩
  simp [pair_Limit_def, fstF, sndF, Function.comp, Limit_domT_Limit_eq hfst, Limit_setF_Limit_eq hsnd]

/- (*******************************
      LimitTF in domF
 *******************************) -/

/- (*** F4 ***) -/

theorem LimitTF_F4 {Fs : infinite_seq (domFType α)} :
    normal Fs → HC_F4 (Limit_domT (fstF ∘ Fs), Limit_setF (sndF ∘ Fs)) := by
  intro hnormal s hs
  rcases normal_of_domF (Fs := Fs) hnormal with ⟨hfst, hsnd⟩
  have hTickBase :
      memT (s ^^^ (Abs_trace [event.Tick] : traceType α)) ((fstF ∘ Fs) (lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)))) :=
    (Limit_domT_memT (Ts := fstF ∘ Fs) hfst).1 hs.1
  have hF4Base :
      (s, Evset) :f (sndF ∘ Fs) (lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α))) :=
    pairF_domF_F4 (SF := Fs (lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)))) hTickBase hs.2
  refine (Limit_setF_memF (Fs := sndF ∘ Fs)).2 ?_
  left
  have hlen :
      lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)) = Nat.succ (lengtht s) := by
    simpa using (lengtht_app_event_Suc_last (s := s) (a := event.Tick) hs.2)
  simpa [Function.comp, hlen] using hF4Base

/- (*** T3 ***) -/

theorem LimitTF_T3 {Fs : infinite_seq (domFType α)} :
    normal Fs → HC_T3 (Limit_domT (fstF ∘ Fs), Limit_setF (sndF ∘ Fs)) := by
  intro hnormal s hs X
  rcases normal_of_domF (Fs := Fs) hnormal with ⟨hfst, _hsnd⟩
  have hTickBase :
      memT (s ^^^ (Abs_trace [event.Tick] : traceType α)) ((fstF ∘ Fs) (lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)))) :=
    (Limit_domT_memT (Ts := fstF ∘ Fs) hfst).1 hs.1
  have hBase :
      (s ^^^ (Abs_trace [event.Tick] : traceType α), X) :f
        (sndF ∘ Fs) (lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α))) :=
    pairF_domF_T3 (SF := Fs (lengtht (s ^^^ (Abs_trace [event.Tick] : traceType α)))) hTickBase hs.2
  refine (Limit_setF_memF (Fs := sndF ∘ Fs)).2 ?_
  right
  exact ⟨hBase, ⟨s, rfl, hs.2⟩⟩

/- (*** F3 ***) -/

theorem LimitTF_F3 {Fs : infinite_seq (domFType α)} :
    normal Fs → HC_F3 (Limit_domT (fstF ∘ Fs), Limit_setF (sndF ∘ Fs)) := by
  intro hnormal s X Y hsX hNo hY
  rcases normal_of_domF (Fs := Fs) hnormal with ⟨hfst, _hsnd⟩
  rcases (Limit_setF_memF (Fs := sndF ∘ Fs)).1 hsX with hsSucc | ⟨hsLen, hsTick⟩
  · have hYBase :
        ∀ a, a ∈ Y →
          ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) ((fstF ∘ Fs) (Nat.succ (lengtht s))) := by
      intro a ha hmem
      apply hY a ha
      have hlen :
          lengtht (s ^^^ (Abs_trace [a] : traceType α)) = Nat.succ (lengtht s) := by
        simpa using (lengtht_app_event_Suc_last (s := s) (a := a) hNo)
      exact (Limit_domT_memT (Ts := fstF ∘ Fs) hfst).2 (by simpa [Function.comp, hlen] using hmem)
    have hBase :
        (s, X ∪ Y) :f (sndF ∘ Fs) (Nat.succ (lengtht s)) :=
      pairF_domF_F3 (SF := Fs (Nat.succ (lengtht s))) hsSucc hNo hYBase
    refine (Limit_setF_memF (Fs := sndF ∘ Fs)).2 ?_
    left
    exact hBase
  · rcases hsTick with ⟨s', hsEq, hsNo⟩
    subst hsEq
    have hFalse : False := by
      have hTickNo : noTick (tickTrace (α := α)) :=
        (decompo_appt_noTick_only_if
          (s := s') (t := tickTrace (α := α)) (Or.inl hsNo) hNo).2
      exact not_noTick_Tick hTickNo
    exact False.elim hFalse

/- (*** T2 ***) -/

theorem LimitTF_T2 {Fs : infinite_seq (domFType α)} :
    normal Fs → HC_T2 (Limit_domT (fstF ∘ Fs), Limit_setF (sndF ∘ Fs)) := by
  intro hnormal s X hsX
  rcases normal_of_domF (Fs := Fs) hnormal with ⟨hfst, _hsnd⟩
  rcases (Limit_setF_memF (Fs := sndF ∘ Fs)).1 hsX with hsSucc | ⟨hsLen, hsTick⟩
  · have hsBase : memT s ((fstF ∘ Fs) (Nat.succ (lengtht s))) :=
      pairF_domF_T2 (SF := Fs (Nat.succ (lengtht s))) hsSucc
    have hsLen : memT s ((fstF ∘ Fs) (lengtht s)) :=
      normal_seq_domT_if (Ts := fstF ∘ Fs) hfst (Nat.le_succ _) hsBase
    exact (Limit_domT_memT (Ts := fstF ∘ Fs) hfst).2 hsLen
  · have hsBase : memT s ((fstF ∘ Fs) (lengtht s)) :=
      pairF_domF_T2 (SF := Fs (lengtht s)) hsLen
    exact (Limit_domT_memT (Ts := fstF ∘ Fs) hfst).2 hsBase

/- (*** LimitTF in ***)

lemma LimitTF_in:
  "normal Fs ==> LimitTF Fs : domF"
-/

theorem LimitTF_in {Fs : infinite_seq (domFType α)} :
    normal Fs → LimitTF Fs ∈ domF (α := α) := by
  intro hnormal
  have hrep : normal (Rep_domF ∘ Fs) := normal_domF_only_if hnormal
  rw [LimitTF_def, LimitTF_iff (Fs := Fs) hrep, domF_iff]
  refine ⟨LimitTF_T2 (Fs := Fs) hnormal, LimitTF_F3 (Fs := Fs) hnormal, ?_⟩
  exact (HC_T3_F4_iff
    (TF := (Limit_domT (fstF ∘ Fs), Limit_setF (sndF ∘ Fs)))).2
      ⟨LimitTF_T3 (Fs := Fs) hnormal, LimitTF_F4 (Fs := Fs) hnormal⟩

/- (*** (normal) Fs converges to (Limit_domF Fs) ***) -/

theorem Limit_domF_Limit {Fs : infinite_seq (domFType α)} :
    normal Fs → Fs convergeTo (Limit_domF Fs) := by
  intro hnormal
  apply convergeTo_domF
  · simpa [LimitTF_def] using
      (pair_cms_cauchy_Limit (xcs := Rep_domF ∘ Fs)
        (normal_cauchy (normal_domF_only_if hnormal)))
  · simpa [LimitTF_def] using LimitTF_in (Fs := Fs) hnormal

/- (*** (cauchy) Fs converges to (Limit_domF NF Fs) ***) -/

theorem cauchy_Limit_domF_Limit {Fs : infinite_seq (domFType α)} :
    cauchy Fs → Fs convergeTo (Limit_domF (NF Fs)) := by
  intro hcauchy
  exact normal_form_seq_same_Limit_if (xs := Fs) (y := Limit_domF (NF Fs)) hcauchy
    (Limit_domF_Limit (Fs := NF Fs) (normal_form_seq_normal hcauchy))

/-
(**************************************
    Dom_F --> Complete Metric Space
 **************************************)
-/

theorem domF_cms {Fs : infinite_seq (domFType α)} :
    cauchy Fs → ∃ F, Fs convergeTo F := by
  intro hcauchy
  exact ⟨Limit_domF (NF Fs), cauchy_Limit_domF_Limit hcauchy⟩

/-
(************************************************************
                   domF ==> CMS and RS
 ************************************************************)
-/

instance instCmsDomF : cms (domFType α) where
  complete_ms := by
    intro Fs
    exact domF_cms

instance instCmsRsDomF : cms_rs (domFType α) where

/- (*** (normal) Limit Fs = Limit_domF Fs ***) -/

theorem Limit_domF_Limit_eq {Fs : infinite_seq (domFType α)} :
    normal Fs → Limit Fs = Limit_domF Fs := by
  intro hnormal
  exact unique_convergence (Limit_is (normal_cauchy hnormal)) (Limit_domF_Limit hnormal)

/-
(************************************************************
                 .|. domF decompostion
 ************************************************************)
-/

theorem rest_domF_decompo_sub {δ : Type _} {f : δ → domTType α} {g : δ → setFType α}
    {x1 x2 : δ} {n : Nat}
    (hfg : ∀ x, (f x, g x) ∈ domF (α := α)) :
    (((f x1 ,, g x1) .|. n) <= ((f x2 ,, g x2) .|. n)) ↔
      (f x1 .|. n <= f x2 .|. n ∧ g x1 .|. n <= g x2 .|. n) := by
  rw [subdomF_def, rest_domF_def, rest_domF_def]
  rw [Abs_domF_inverse (SF := restTF (f x1 ,, g x1) n) (restTF_in (F := f x1 ,, g x1) (n := n)),
    Abs_domF_inverse (SF := restTF (f x2 ,, g x2) n) (restTF_in (F := f x2 ,, g x2) (n := n))]
  simp [pairF, restTF_def, pair_restriction_def, order_pair_def,
    Abs_domF_inverse (SF := (f x1, g x1)) (hfg x1),
    Abs_domF_inverse (SF := (f x2, g x2)) (hfg x2)]

theorem rest_domF_decompo {δ : Type _} {f : δ → domTType α} {g : δ → setFType α}
    {x1 x2 : δ} {n : Nat}
    (hfg : ∀ x, (f x, g x) ∈ domF (α := α)) :
    (((f x1 ,, g x1) .|. n) = ((f x2 ,, g x2) .|. n)) ↔
      (f x1 .|. n = f x2 .|. n ∧ g x1 .|. n = g x2 .|. n) := by
  constructor
  · intro h
    have hRep := (Rep_rest_domF (F := f x1 ,, g x1) (E := f x2 ,, g x2) (n := n) (m := n)).1 h
    have hPair :
        ((f x1 .|. n), (g x1 .|. n)) = ((f x2 .|. n), (g x2 .|. n)) := by
      simpa [pairF, restTF_def, pair_restriction_def,
        Abs_domF_inverse (SF := (f x1, g x1)) (hfg x1),
        Abs_domF_inverse (SF := (f x2, g x2)) (hfg x2)] using hRep
    exact pair_eq_decompo.mp hPair
  · rintro ⟨hf, hg⟩
    have hPair :
        ((f x1 .|. n), (g x1 .|. n)) = ((f x2 .|. n), (g x2 .|. n)) :=
      pair_eq_decompo.mpr ⟨hf, hg⟩
    exact (Rep_rest_domF (F := f x1 ,, g x1) (E := f x2 ,, g x2) (n := n) (m := n)).2 <| by
      simpa [pairF, restTF_def, pair_restriction_def,
        Abs_domF_inverse (SF := (f x1, g x1)) (hfg x1),
        Abs_domF_inverse (SF := (f x2, g x2)) (hfg x2)] using hPair

/-
(************************************************************
                  map domF decompostion
 ************************************************************)
-/

theorem map_alpha_Abs_domF {β : Type _} [ms β]
    {f : β → domTType α} {g : β → setFType α} {alpha : ℝ}
    (hfg : ∀ x, (f x, g x) ∈ domF (α := α)) :
    map_alpha (fun x => f x ,, g x) alpha = map_alpha (f ** g) alpha := by
  apply propext
  unfold map_alpha
  constructor
  · intro h
    constructor
    · exact h.1
    · intro x y
      simpa [pair_fun, pairF, distance_Abs_domF (hfg x) (hfg y)] using h.2 x y
  · intro h
    constructor
    · exact h.1
    · intro x y
      simpa [pair_fun, pairF, distance_Abs_domF (hfg x) (hfg y)] using h.2 x y

theorem map_alpha_domF_decompo {β : Type _} [ms_rs β]
    {f : β → domTType α} {g : β → setFType α} {alpha : ℝ}
    (hfg : ∀ x : β, (f x, g x) ∈ domF (α := α)) :
    map_alpha (fun x => f x ,, g x) alpha =
      (map_alpha f alpha ∧ map_alpha g alpha) := by
  rw [map_alpha_Abs_domF (α := α) (β := β) hfg, pair_map_alpha_compo]

theorem non_expanding_domF_decompo {β : Type _} [ms_rs β]
    {f : β → domTType α} {g : β → setFType α}
    (hfg : ∀ x : β, (f x, g x) ∈ domF (α := α)) :
    non_expanding (fun x => f x ,, g x) =
      (non_expanding f ∧ non_expanding g) := by
  simpa [non_expanding] using
    (map_alpha_domF_decompo (α := α) (β := β) (f := f) (g := g) (alpha := (1 : ℝ)) hfg)

theorem contraction_alpha_domF_decompo {β : Type _} [ms_rs β]
    {f : β → domTType α} {g : β → setFType α} {alpha : ℝ}
    (hfg : ∀ x : β, (f x, g x) ∈ domF (α := α)) :
    contraction_alpha (fun x => f x ,, g x) alpha =
      (contraction_alpha f alpha ∧ contraction_alpha g alpha) := by
  apply propext
  simp [contraction_alpha, map_alpha_domF_decompo (α := α) (β := β) (f := f) (g := g)
    (alpha := alpha) hfg, and_left_comm, and_assoc]

/-
(**********************************************************
                non expanding (op o fstF)
 **********************************************************)
-/

theorem non_expanding_Rep_domF :
    non_expanding (Rep_domF (α := α)) := by
  constructor
  · norm_num
  · intro x y
    rw [← distance_Rep_domF]
    simpa using (le_rfl : distance x y ≤ distance x y)

theorem non_expanding_fstF :
    non_expanding (fstF (α := α)) := by
  unfold fstF
  exact compo_non_expand fst_non_expand non_expanding_Rep_domF

theorem non_expanding_sndF :
    non_expanding (sndF (α := α)) := by
  unfold sndF
  exact compo_non_expand snd_non_expand non_expanding_Rep_domF

theorem non_expanding_op_fstF {ι : Type _} [Nonempty ι] :
    non_expanding (fun (x : ι → domFType α) => fstF ∘ x) := by
  rw [prod_non_expand]
  intro i
  simpa [proj_fun, Function.comp] using
    (compo_non_expand (f := fstF (α := α)) (g := proj_fun i) non_expanding_fstF (proj_non_expand i))

theorem non_expanding_op_sndF {ι : Type _} [Nonempty ι] :
    non_expanding (fun (x : ι → domFType α) => sndF ∘ x) := by
  rw [prod_non_expand]
  intro i
  simpa [proj_fun, Function.comp] using
    (compo_non_expand (f := sndF (α := α)) (g := proj_fun i) non_expanding_sndF (proj_non_expand i))

/- (*** distance ***) -/

theorem distance_fstF_compo_le {ι : Type _} [Nonempty ι]
    {x y : ι → domFType α} :
    distance (fstF ∘ x) (fstF ∘ y) <= distance x y := by
  have hnon := non_expanding_op_fstF (α := α) (ι := ι)
  simpa [non_expanding] using hnon.2 x y

theorem alpha_distance_fstF_compo_le {ι : Type _} [Nonempty ι]
    {x y : ι → domFType α} {alpha : ℝ} :
    0 <= alpha → alpha * distance (fstF ∘ x) (fstF ∘ y) <= alpha * distance x y := by
  intro hAlpha
  exact mul_le_mul_of_nonneg_left (distance_fstF_compo_le (α := α) (ι := ι) (x := x) (y := y)) hAlpha

/- ----------------------------------------------------------*
 |                                                          |
 |                       cms rs order                       |
 |                                                          |
 *---------------------------------------------------------- -/

instance instMsRsOrder0DomF : ms_rs_order0 (domFType α) where

private theorem rest_subdomF_decompo {SF1 SF2 : domFType α} {n : Nat} :
    (SF1 .|. n <= SF2 .|. n) ↔
      (fstF SF1 .|. n <= fstF SF2 .|. n ∧ sndF SF1 .|. n <= sndF SF2 .|. n) := by
  rw [subdomF_def, rest_domF_def, rest_domF_def]
  rw [Abs_domF_inverse (SF := restTF SF1 n) (restTF_in (F := SF1) (n := n)),
    Abs_domF_inverse (SF := restTF SF2 n) (restTF_in (F := SF2) (n := n))]
  simp [restTF_def, fstF, sndF, pair_restriction_def, order_pair_def]

instance instMsRsOrderDomF : ms_rs_order (domFType α) where
  rs_order_iff := by
    intro F E
    constructor
    · intro hrest
      exact (subdomF_decompo (SF := F) (SE := E)).2
        ⟨(ms_rs_order.rs_order_iff (fstF F) (fstF E)).1 (fun n =>
            (rest_subdomF_decompo (SF1 := F) (SF2 := E) (n := n)).1 (hrest n) |>.1),
          (ms_rs_order.rs_order_iff (sndF F) (sndF E)).1 (fun n =>
            (rest_subdomF_decompo (SF1 := F) (SF2 := E) (n := n)).1 (hrest n) |>.2)⟩
    · intro hle n
      rcases (subdomF_decompo (SF := F) (SE := E)).1 hle with ⟨hfst, hsnd⟩
      exact (rest_subdomF_decompo (SF1 := F) (SF2 := E) (n := n)).2
        ⟨(ms_rs_order.rs_order_iff (fstF F) (fstF E)).2 hfst n,
          (ms_rs_order.rs_order_iff (sndF F) (sndF E)).2 hsnd n⟩

instance instCmsRsOrderDomF : cms_rs_order (domFType α) where

/- ----------------------------------------------------------*
 |                                                          |
 |  i.e. lemma "continuous_rs (Ref_fun (S::'a domF))"       |
 |       by (simp add: continuous_rs_Ref_fun)               |
 |                                                          |
 |  see RS.thy                                              |
 |                                                          |
 *---------------------------------------------------------- -/

end
