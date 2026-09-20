           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DM.DM1_Imp_def

open fpmode
open DM1_Imp_def

noncomputable section

namespace DM2_para

private abbrev TH0P : proc ImpName Event := proc.Proc_name ImpName.TH0

private abbrev TH1P : proc ImpName Event := proc.Proc_name ImpName.TH1

private abbrev VARP (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.VAR n)

private abbrev EAT0P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT0 n)

private abbrev EAT1P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT1 n)

private abbrev Par0 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH0 Q

private abbrev Par1 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH1 Q

private abbrev Pref (e : Event) (P : proc ImpName Event) : proc ImpName Event := proc.Act_prefix e P

/- *****************************************************************

         1. expands parallel operators in Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- *********************************************************
        private lemmas used by the proved theorems below
 ********************************************************* -/

private theorem decide_self (a : Event) : decide (a = a) = true := by
  simp

private theorem decide_ne (a b : Event) (h : ¬a = b) : decide (a = b) = false := by
  simp [h]

/- computation lemmas for `getInt` -/

private theorem getInt_RD0 (m : Int) : getInt (Event.RD0 m) = m := rfl

private theorem getInt_RD1 (m : Int) : getInt (Event.RD1 m) = m := rfl

private theorem getInt_WR0 (m : Int) : getInt (Event.WR0 m) = m := rfl

private theorem getInt_WR1 (m : Int) : getInt (Event.WR1 m) = m := rfl

/- `Function.invFun` computation for the receiving prefixes over `RD0`/`RD1` -/

private theorem RD0_inj : Function.Injective Event.RD0 := by
  intro a b h
  injection h

private theorem RD1_inj : Function.Injective Event.RD1 := by
  intro a b h
  injection h

private theorem invFun_RD0 (m : Int) : Function.invFun Event.RD0 (Event.RD0 m) = m :=
  Function.leftInverse_invFun RD0_inj m

private theorem invFun_RD1 (m : Int) : Function.invFun Event.RD1 (Event.RD1 m) = m :=
  Function.leftInverse_invFun RD1_inj m

/- channel membership facts -/

private theorem RD0_in_CH0 (m : Int) : Event.RD0 m ∈ CH0 := Or.inl ⟨m, rfl⟩

private theorem WR0_in_CH0 (m : Int) : Event.WR0 m ∈ CH0 := Or.inr ⟨m, rfl⟩

private theorem RD1_in_CH1 (m : Int) : Event.RD1 m ∈ CH1 := Or.inl ⟨m, rfl⟩

private theorem WR1_in_CH1 (m : Int) : Event.WR1 m ∈ CH1 := Or.inr ⟨m, rfl⟩

/- computation lemmas for the `decide`d `CH0`-membership test in `TH0_VAR` -/

private theorem in_CH0_RD0 (m : Int) :
    (by classical
        exact decide
          (Event.RD0 m ∈ Set.range Event.RD0 ∨ Event.RD0 m ∈ Set.range Event.WR0) : Bool)
      = true := by
  simp

private theorem in_CH0_RD1 (m : Int) :
    (by classical
        exact decide
          (Event.RD1 m ∈ Set.range Event.RD0 ∨ Event.RD1 m ∈ Set.range Event.WR0) : Bool)
      = false := by
  simp

private theorem in_CH0_WR1 (m : Int) :
    (by classical
        exact decide
          (Event.WR1 m ∈ Set.range Event.RD0 ∨ Event.WR1 m ∈ Set.range Event.WR0) : Bool)
      = false := by
  simp

/- reduction of `proc.IF` under a literal condition -/

private theorem IF_true (P Q : proc ImpName Event) :
    eqF (IF true THEN P ELSE Q) MF MF P :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem IF_false (P Q : proc ImpName Event) :
    eqF (IF false THEN P ELSE Q) MF MF Q :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

/- index set produced by `cspF_Parallel_step` for `$TH0 |[CH0]| $VAR n` -/

private theorem idxA_TH0 (n : Int) :
    ((CH0 ∩ Set.range Event.RD0 ∩
          (Set.insert (Event.RD1 n)
            (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)))) ∪
        (Set.range Event.RD0 \ CH0) ∪
        ((Set.insert (Event.RD1 n)
            (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1))) \ CH0)) =
      Set.insert (Event.RD0 n) (Set.insert (Event.RD1 n) (Set.range Event.WR1)) := by
  ext e
  cases e <;> simp [Set.insert, Set.mem_setOf_eq, CH0, Set.mem_range]

/- the index set produced by `cspF_Parallel_step` when both components offer
   a single event that is not synchronised by `CH1` -/
private theorem pair_free_index (a b : Event) (ha : a ∉ CH1) (hb : b ∉ CH1) :
    ((CH1 ∩ ({a} : Set Event) ∩ ({b} : Set Event)) ∪ (({a} : Set Event) \ CH1) ∪
        (({b} : Set Event) \ CH1)) = ({a, b} : Set Event) := by
  ext e
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · rintro ((⟨⟨-, rfl⟩, -⟩ | ⟨rfl, -⟩) | ⟨rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inr ⟨rfl, ha⟩)
    · exact Or.inr ⟨rfl, hb⟩

private theorem pair_End1_Back0 :
    ({Event.Back0, Event.End1} : Set Event) = ({Event.End1, Event.Back0} : Set Event) := by
  ext e
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact or_comm

/- A prefixed left component pulls out of `|[CH1]|` when the right component
   is (`eqF` to) a prefix choice over synchronised `CH1` events only: the
   prefix blocks every synchronisation, so the right component cannot move. -/
private theorem pull_left_prefix {Z : Set Event} {Qf : Event → proc ImpName Event}
    (a : Event) (P R : proc ImpName Event)
    (hR : eqF R MF MF (proc.Ext_pre_choice Z Qf))
    (haC : a ∉ CH1) (hZC : Z ⊆ CH1) :
    eqF ((proc.Ext_pre_choice ({a} : Set Event) (fun _ => P)) |[CH1]| R) MF MF
      (a ~> (P |[CH1]| R)) := by
  have hidx : ((CH1 ∩ ({a} : Set Event) ∩ Z) ∪ (({a} : Set Event) \ CH1) ∪ (Z \ CH1)) =
      ({a} : Set Event) := by
    ext e
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Set.mem_singleton_iff]
    constructor
    · rintro ((⟨⟨-, rfl⟩, -⟩ | ⟨rfl, -⟩) | ⟨heZ, heC⟩)
      · rfl
      · rfl
      · exact absurd (hZC heZ) heC
    · rintro rfl
      exact Or.inl (Or.inr ⟨rfl, haC⟩)
  have hstep := cspF_Parallel_step (X := CH1) (Y := ({a} : Set Event)) (Z := Z)
    (Pf := fun _ => P) (Qf := Qf) (M := (MF : ImpName → domFType Event))
  rw [hidx] at hstep
  refine cspF_trans_left_eq (cspF_Parallel_cong rfl cspF_reflex_eq_P hR) ?_
  refine cspF_trans_left_eq hstep ?_
  refine cspF_trans_left_eq (cspF_Ext_pre_choice_cong rfl ?_) (cspF_sym cspF_Act_prefix_step)
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [procIte_neg haC, procIte_neg (fun h => haC (hZC h.2)),
    procIte_pos (show x ∈ ({x} : Set Event) from rfl)]
  exact cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hR)

/- Lean note:
   Isabelle's prefix `a -> P` binds *tighter* than the parallel operator
   `|[X]|` (80 vs 76), so the original

     THEN IF EVEN (getInt x)
          THEN (Eat0  -> ($(EAT0 n)) |[CH0]| ($(VAR n)))
          ELSE (Back0 -> ($TH0) |[CH0]| ($(VAR n)))

   reads `(Eat0 -> $(EAT0 n)) |[CH0]| $(VAR n)`: after the synchronised
   `RD0 n` only the TH0 component has moved, and `$(VAR n)` keeps running
   in parallel (it can still perform its unsynchronised `RD1`/`WR1`
   events). The port bracketed it as `Eat0 ~> ($(EAT0 n) |[CH0]| $(VAR n))`,
   which would force the whole system to perform `Eat0` before `$(VAR n)`
   may move again — a different (and false) proposition. Repaired to the
   Isabelle parse; same precedence bug class as `Parallel_F3_lm1` in the
   core. -/


/- Generic step for a prefixed TH0-side component running against `$(VAR n)`:
   the prefix is not in `CH0`, so it and `$(VAR n)`'s own `RD1`/`WR1` events
   interleave freely, and only after the prefix has occurred does the
   left component continue. -/

private theorem prefix_Par0_VAR (a : Event) (P : proc ImpName Event) (n : Int)
    (haC0 : a ∉ CH0) (haC1 : a ∉ CH1) :
    eqF ((a ~> P) |[CH0]| (proc.Proc_name (ImpName.VAR n))) MF MF
      (proc.Ext_pre_choice
        (Set.insert a (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = a)
          THEN (P |[CH0]| (proc.Proc_name (ImpName.VAR n)))
          ELSE
            IF decide (x = Event.RD1 n)
            THEN ((a ~> P) |[CH0]| (proc.Proc_name (ImpName.VAR n)))
            ELSE ((a ~> P) |[CH0]| (proc.Proc_name (ImpName.VAR (getInt x)))))) := by
  have haRD1 : a ≠ Event.RD1 n := by
    intro h
    exact haC1 (h ▸ RD1_in_CH1 n)
  have haWR1 : ∀ m : Int, a ≠ Event.WR1 m := by
    intro m h
    exact haC1 (h ▸ WR1_in_CH1 m)
  have hidx :
      ((CH0 ∩ ({a} : Set Event) ∩
            (Set.insert (Event.RD1 n)
              (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)))) ∪
          (({a} : Set Event) \ CH0) ∪
          ((Set.insert (Event.RD1 n)
              (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1))) \ CH0)) =
        Set.insert a (Set.insert (Event.RD1 n) (Set.range Event.WR1)) := by
    ext e
    constructor
    · rintro ((⟨⟨-, he⟩, -⟩ | ⟨he, -⟩) | ⟨he, heC⟩)
      · exact Or.inl he
      · exact Or.inl he
      · rcases he with he | he
        · exact Or.inr (Or.inl he)
        rcases he with he | he
        · exact absurd (he ▸ RD0_in_CH0 n) heC
        rcases he with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · exact absurd (WR0_in_CH0 m) heC
        · exact Or.inr (Or.inr ⟨m, rfl⟩)
    · rintro (rfl | he)
      · exact Or.inl (Or.inr ⟨rfl, haC0⟩)
      · refine Or.inr ⟨?_, ?_⟩
        · rcases he with rfl | ⟨m, rfl⟩
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr ⟨m, rfl⟩))
        · rcases he with rfl | ⟨m, rfl⟩
          · rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> exact Event.noConfusion hk
          · rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> exact Event.noConfusion hk
  have hstep := cspF_Parallel_step
    (X := CH0) (Y := ({a} : Set Event))
    (Z := Set.insert (Event.RD1 n)
      (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)))
    (Pf := fun _ => P)
    (Qf := fun x =>
      IF is_WR01 x
      THEN proc.Proc_name (ImpName.VAR (getInt x))
      ELSE proc.Proc_name (ImpName.VAR n))
    (M := (MF : ImpName → domFType Event))
  rw [hidx] at hstep
  refine cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_Act_prefix_step (VAR n)) ?_
  refine cspF_trans_left_eq hstep ?_
  refine cspF_Ext_pre_choice_cong rfl (fun x hx => ?_)
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · -- x = a : unsynchronised, the left component continues
    rw [procIte_neg haC0,
      procIte_neg (fun h => haRD1 (by
        rcases h.2 with h' | h' | h'
        · exact h'
        · exact absurd (h' ▸ RD0_in_CH0 n) haC0
        · rcases h' with ⟨m, rfl⟩ | ⟨m, rfl⟩
          · exact absurd (WR0_in_CH0 m) haC0
          · exact absurd rfl (haWR1 m))),
      procIte_pos (show x ∈ ({x} : Set Event) from rfl), decide_self x]
    refine cspF_trans_right_eq (cspF_sym (IF_true _ _)) ?_
    exact cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym (VAR n))
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · -- x = RD1 n : only `$(VAR n)` moves, keeping its value
    rw [procIte_neg (by simp [CH0, Set.mem_range]),
      procIte_neg (by simp [Set.mem_singleton_iff, haRD1.symm]),
      procIte_neg (by simp [Set.mem_singleton_iff, haRD1.symm]),
      decide_ne _ _ haRD1.symm]
    refine cspF_trans_right_eq (cspF_sym (IF_false _ _)) ?_
    rw [decide_self (Event.RD1 n)]
    refine cspF_trans_right_eq (cspF_sym (IF_true _ _)) ?_
    have hQ : eqF
        (IF is_WR01 (Event.RD1 n)
          THEN proc.Proc_name (ImpName.VAR (getInt (Event.RD1 n)))
          ELSE proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
        (proc.Proc_name (ImpName.VAR n) : proc ImpName Event) := by
      rw [is_WR01_RD1]
      exact IF_false _ _
    exact cspF_Parallel_cong rfl (cspF_sym cspF_Act_prefix_step) hQ
  · -- x = WR1 m : only `$(VAR n)` moves, taking the new value
    rcases hx with ⟨m, rfl⟩
    rw [procIte_neg (by simp [CH0, Set.mem_range]),
      procIte_neg (by simp [Set.mem_singleton_iff, (haWR1 m).symm]),
      procIte_neg (by simp [Set.mem_singleton_iff, (haWR1 m).symm]),
      decide_ne _ _ (haWR1 m).symm]
    refine cspF_trans_right_eq (cspF_sym (IF_false _ _)) ?_
    rw [decide_ne _ _ (by intro h; exact Event.noConfusion h)]
    refine cspF_trans_right_eq (cspF_sym (IF_false _ _)) ?_
    rw [getInt_WR1 m]
    have hQ : eqF
        (IF is_WR01 (Event.WR1 m)
          THEN proc.Proc_name (ImpName.VAR (getInt (Event.WR1 m)))
          ELSE proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
        (proc.Proc_name (ImpName.VAR m) : proc ImpName Event) := by
      rw [is_WR01_WR1]
      refine cspF_trans_left_eq (IF_true _ _) ?_
      rw [getInt_WR1 m]
      exact cspF_reflex_eq_P
    exact cspF_Parallel_cong rfl (cspF_sym cspF_Act_prefix_step) hQ

/- (*** TH0 VAR step 1 ***) -/

theorem TH0_VAR (n : Int) :
    eqF
      ((proc.Proc_name ImpName.TH0) |[CH0]| (proc.Proc_name (ImpName.VAR n)))
      MF MF
      (proc.Ext_pre_choice
        (Set.insert (Event.RD0 n) (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF (by
              classical
              exact decide (x ∈ Set.range Event.RD0 ∨ x ∈ Set.range Event.WR0))
          THEN
            IF EVEN (getInt x)
            THEN
              (Event.Eat0 ~> proc.Proc_name (ImpName.EAT0 n)) |[CH0]|
                (proc.Proc_name (ImpName.VAR n))
            ELSE
              (Event.Back0 ~> proc.Proc_name ImpName.TH0) |[CH0]|
                (proc.Proc_name (ImpName.VAR n))
          ELSE
            ((proc.Proc_name ImpName.TH0) |[CH0]|
              (proc.Proc_name (ImpName.VAR (getInt x)))))) := by
  -- unwind $TH0 into an external prefix choice over `range RD0`
  have hTH0 : eqF (proc.Proc_name ImpName.TH0 : proc ImpName Event) MF MF
      (proc.Ext_pre_choice (Set.range Event.RD0) fun x =>
        IF EVEN (Function.invFun Event.RD0 x)
        THEN Event.Eat0 ~> proc.Proc_name (ImpName.EAT0 (Function.invFun Event.RD0 x))
        ELSE Event.Back0 ~> proc.Proc_name ImpName.TH0) := by
    have h := «cspF_unwind» (Pf := Impfun) (p0 := ImpName.TH0) rfl
      (Or.inr (Or.inl ⟨rfl, guarded_Imp⟩))
    simpa [Impfun, Rec_prefix, Set.image_univ] using h
  have hstep := cspF_Parallel_step
    (X := CH0) (Y := Set.range Event.RD0)
    (Z := Set.insert (Event.RD1 n)
      (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)))
    (Pf := fun x =>
      IF EVEN (Function.invFun Event.RD0 x)
      THEN Event.Eat0 ~> proc.Proc_name (ImpName.EAT0 (Function.invFun Event.RD0 x))
      ELSE Event.Back0 ~> proc.Proc_name ImpName.TH0)
    (Qf := fun x =>
      IF is_WR01 x
      THEN proc.Proc_name (ImpName.VAR (getInt x))
      ELSE proc.Proc_name (ImpName.VAR n))
    (M := (MF : ImpName → domFType Event))
  rw [idxA_TH0 n] at hstep
  refine cspF_trans_left_eq (cspF_Parallel_cong rfl hTH0 (VAR n)) ?_
  refine cspF_trans_left_eq hstep ?_
  refine cspF_Ext_pre_choice_cong rfl (fun x hx => ?_)
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · -- x = RD0 n : synchronised, TH0 makes its internal decision
    rw [procIte_pos (RD0_in_CH0 n), in_CH0_RD0 n, invFun_RD0 n, getInt_RD0 n]
    refine cspF_trans_right_eq (cspF_sym (IF_true _ _)) ?_
    have hQ : eqF
        (IF is_WR01 (Event.RD0 n)
          THEN proc.Proc_name (ImpName.VAR (getInt (Event.RD0 n)))
          ELSE proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
        (proc.Proc_name (ImpName.VAR n) : proc ImpName Event) := by
      rw [is_WR01_RD0]
      exact IF_false _ _
    refine cspF_trans_left_eq (cspF_Parallel_cong rfl cspF_reflex_eq_P hQ) ?_
    by_cases hE : EVEN n = true
    · rw [hE]
      refine cspF_trans_left_eq (cspF_Parallel_cong rfl (IF_true _ _) cspF_reflex_eq_P) ?_
      exact cspF_sym (IF_true _ _)
    · rw [Bool.not_eq_true] at hE
      rw [hE]
      refine cspF_trans_left_eq (cspF_Parallel_cong rfl (IF_false _ _) cspF_reflex_eq_P) ?_
      exact cspF_sym (IF_false _ _)
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · -- x = RD1 n : not in CH0, only VAR moves; VAR keeps its value
    rw [procIte_neg (by simp [CH0, Set.mem_range]),
      procIte_neg (by simp [Set.mem_range]),
      procIte_neg (by simp [Set.mem_range]),
      in_CH0_RD1 n, getInt_RD1 n]
    refine cspF_trans_right_eq (cspF_sym (IF_false _ _)) ?_
    have hQ : eqF
        (IF is_WR01 (Event.RD1 n)
          THEN proc.Proc_name (ImpName.VAR (getInt (Event.RD1 n)))
          ELSE proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
        (proc.Proc_name (ImpName.VAR n) : proc ImpName Event) := by
      rw [is_WR01_RD1]
      exact IF_false _ _
    exact cspF_Parallel_cong rfl (cspF_sym hTH0) hQ
  · -- x = WR1 m : not in CH0, VAR takes the new value
    rcases hx with ⟨m, rfl⟩
    rw [procIte_neg (by simp [CH0, Set.mem_range]),
      procIte_neg (by simp [Set.mem_range]),
      procIte_neg (by simp [Set.mem_range]),
      in_CH0_WR1 m, getInt_WR1 m]
    refine cspF_trans_right_eq (cspF_sym (IF_false _ _)) ?_
    have hQ : eqF
        (IF is_WR01 (Event.WR1 m)
          THEN proc.Proc_name (ImpName.VAR (getInt (Event.WR1 m)))
          ELSE proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
        (proc.Proc_name (ImpName.VAR m) : proc ImpName Event) := by
      rw [is_WR01_WR1]
      refine cspF_trans_left_eq (IF_true _ _) ?_
      rw [getInt_WR1 m]
      exact cspF_reflex_eq_P
    exact cspF_Parallel_cong rfl (cspF_sym hTH0) hQ

abbrev TH0_VAR_simp := TH0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules4` and `fold_Imp_rules4`
   are represented by `TH0_VAR_simp` together with the earlier simp lemmas
   from `DM1_Imp_def` and their `cspF_sym` images. -/

/- (*** TH0 VAR TH1 step 1 ***) -/

axiom TH0_VAR_TH1 (n : Int) :
    eqF (Par1 (Par0 TH0P (VARP n)) TH1P) MF MF
      (proc.Ext_pre_choice ({Event.RD0 n, Event.RD1 n} : Set Event) (fun x =>
        IF decide (x = Event.RD0 n)
        THEN
          IF EVEN n
          THEN Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) TH1P)
        ELSE
          IF ODD n
          THEN Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))
          ELSE Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)))

abbrev TH0_VAR_TH1_simp := TH0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules5` and `fold_Imp_rules5`
   are represented by `TH0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR step 2 ***) -/

/- Lean note:
   Isabelle's prefix binds tighter than `|[X]|` (80 vs 76), so
   `(Eat0 -> ($(EAT0 n)) |[CH0]| ($(VAR n)))` is
   `(Eat0 -> $(EAT0 n)) |[CH0]| $(VAR n)`; the port bracketed it as
   `Eat0 ~> ($(EAT0 n) |[CH0]| $(VAR n))`. Repaired (same class as
   `TH0_VAR` above). -/

theorem Eat0_VAR (n : Int) :
    eqF (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) MF MF
      (proc.Ext_pre_choice
        (Set.insert Event.Eat0 (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.Eat0)
          THEN Par0 (EAT0P n) (VARP n)
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)
            ELSE Par0 (Pref Event.Eat0 (EAT0P n)) (VARP (getInt x)))) :=
  prefix_Par0_VAR Event.Eat0 (EAT0P n) n
    (by simp [CH0, Set.mem_range]) (by simp [CH1, Set.mem_range])

abbrev Eat0_VAR_simp := Eat0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules6` and `fold_Imp_rules6`
   are represented by `Eat0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** Back0 VAR step 2 ***) -/

/- Lean note:
   Same precedence repair as `Eat0_VAR`:
   `(Back0 -> ($TH0) |[CH0]| ($(VAR n)))` is
   `(Back0 -> $TH0) |[CH0]| $(VAR n)`. -/

theorem Back0_VAR (n : Int) :
    eqF (Par0 (Pref Event.Back0 TH0P) (VARP n)) MF MF
      (proc.Ext_pre_choice
        (Set.insert Event.Back0 (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.Back0)
          THEN Par0 TH0P (VARP n)
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Par0 (Pref Event.Back0 TH0P) (VARP n)
            ELSE Par0 (Pref Event.Back0 TH0P) (VARP (getInt x)))) :=
  prefix_Par0_VAR Event.Back0 TH0P n
    (by simp [CH0, Set.mem_range]) (by simp [CH1, Set.mem_range])

abbrev Back0_VAR_simp := Back0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules7` and `fold_Imp_rules7`
   are represented by `Back0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** Eat0 VAR TH1 step 2 ***) -/

axiom Eat0_VAR_TH1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref Event.Eat0 (Par0 (EAT0P n) (VARP n))) TH1P) MF MF
        (proc.Ext_pre_choice ({Event.Eat0, Event.RD1 n} : Set Event) (fun x =>
          IF decide (x = Event.Eat0)
          THEN Par1 (Par0 (EAT0P n) (VARP n)) TH1P
          ELSE Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev Eat0_VAR_TH1_simp := Eat0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules8` and `fold_Imp_rules8`
   are represented by `Eat0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (****************************) -/
/- (*** Back0 VAR TH1 step 2 ***) -/

axiom Back0_VAR_TH1 (n : Int) :
    eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) TH1P) MF MF
      (proc.Ext_pre_choice ({Event.Back0, Event.RD1 n} : Set Event) (fun x =>
        IF decide (x = Event.Back0)
        THEN Par1 (Par0 TH0P (VARP n)) TH1P
        ELSE
          IF ODD n
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev Back0_VAR_TH1_simp := Back0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules9` and `fold_Imp_rules9`
   are represented by `Back0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR Eat1 step 2 ***) -/

axiom TH0_VAR_Eat1 (n : Int) :
    ODD n →
      eqF (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))) MF MF
        (proc.Ext_pre_choice ({Event.Eat1, Event.RD0 n} : Set Event) (fun x =>
          IF decide (x = Event.Eat1)
          THEN Par1 (Par0 TH0P (VARP n)) (EAT1P n)
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))))

abbrev TH0_VAR_Eat1_simp := TH0_VAR_Eat1

/- The Isabelle theorem bundles `unfold_Imp_rules10` and `fold_Imp_rules10`
   are represented by `TH0_VAR_Eat1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (****************************) -/
/- (*** TH0 VAR Back1 step 2 ***) -/

axiom TH0_VAR_Back1 (n : Int) :
    eqF (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)) MF MF
      (proc.Ext_pre_choice ({Event.Back1, Event.RD0 n} : Set Event) (fun x =>
        IF decide (x = Event.Back1)
        THEN Par1 (Par0 TH0P (VARP n)) TH1P
        ELSE
          IF EVEN n
          THEN Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev TH0_VAR_Back1_simp := TH0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules11` and `fold_Imp_rules11`
   are represented by `TH0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR step 3 ***) -/

axiom EAT0_VAR (n : Int) :
    eqF (Par0 (EAT0P n) (VARP n)) MF MF
      (proc.Ext_pre_choice
        (Set.insert Event.End0 (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.End0)
          THEN Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Par0 (EAT0P n) (VARP n)
            ELSE Par0 (EAT0P n) (VARP (getInt x))))

abbrev EAT0_VAR_simp := EAT0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules12` and `fold_Imp_rules12`
   are represented by `EAT0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** EAT0 VAR TH1 step 3 ***) -/

axiom EAT0_VAR_TH1 (n : Int) :
    EVEN n →
      eqF (Par1 (Par0 (EAT0P n) (VARP n)) TH1P) MF MF
        (proc.Ext_pre_choice ({Event.End0, Event.RD1 n} : Set Event) (fun x =>
          IF decide (x = Event.End0)
          THEN Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) TH1P)
          ELSE Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)))

abbrev EAT0_VAR_TH1_simp := EAT0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules13` and `fold_Imp_rules13`
   are represented by `EAT0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR Back1 step 3 ***) -/

axiom Eat0_VAR_Back1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref Event.Eat0 (Par0 (EAT0P n) (VARP n))) (Pref Event.Back1 TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.Eat0, Event.Back1} : Set Event) (fun x =>
          IF decide (x = Event.Eat0)
          THEN Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)
          ELSE Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)))

abbrev Eat0_VAR_Back1_simp := Eat0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules14` and `fold_Imp_rules14`
   are represented by `Eat0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR EAT1 step 3 ***) -/

axiom TH0_VAR_EAT1 (n : Int) :
    ODD n →
      eqF (Par1 (Par0 TH0P (VARP n)) (EAT1P n)) MF MF
        (proc.Ext_pre_choice ({Event.End1, Event.RD0 n} : Set Event) (fun x =>
          IF decide (x = Event.End1)
          THEN Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (EAT1P n))))

abbrev TH0_VAR_EAT1_simp := TH0_VAR_EAT1

/- The Isabelle theorem bundles `unfold_Imp_rules15` and `fold_Imp_rules15`
   are represented by `TH0_VAR_EAT1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR Eat1 step 3 ***) -/

axiom Back0_VAR_Eat1 (n : Int) :
    ODD n →
      eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (Pref Event.Eat1 (EAT1P n))) MF MF
        (proc.Ext_pre_choice ({Event.Eat1, Event.Back0} : Set Event) (fun x =>
          IF decide (x = Event.Eat1)
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (EAT1P n))
          ELSE Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))))

abbrev Back0_VAR_Eat1_simp := Back0_VAR_Eat1

/- The Isabelle theorem bundles `unfold_Imp_rules16` and `fold_Imp_rules16`
   are represented by `Back0_VAR_Eat1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR Back1 step 3 ***) -/

axiom Back0_VAR_Back1 (n : Int) :
    eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (Pref Event.Back1 TH1P)) MF MF
      (proc.Ext_pre_choice ({Event.Back0, Event.Back1} : Set Event) (fun x =>
        IF decide (x = Event.Back0)
        THEN Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)
        ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) TH1P)))

abbrev Back0_VAR_Back1_simp := Back0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules17` and `fold_Imp_rules17`
   are represented by `Back0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR step 4 ***) -/

axiom WR0_VAR (n : Int) :
    eqF (Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))) MF MF
      (proc.Ext_pre_choice
        (Set.insert (Event.WR0 (n / 2)) (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.WR0 (n / 2))
          THEN Par0 TH0P (VARP (n / 2))
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))
            ELSE Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP (getInt x)))))

abbrev WR0_VAR_simp := WR0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules18` and `fold_Imp_rules18`
   are represented by `WR0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** WR0 VAR TH1 step 4 ***) -/

axiom WR0_VAR_TH1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))) TH1P) MF MF
        (proc.Ext_pre_choice ({Event.WR0 (n / 2), Event.RD1 n} : Set Event) (fun x =>
          IF decide (x = Event.WR0 (n / 2))
          THEN Par1 (Par0 TH0P (VARP (n / 2))) TH1P
          ELSE Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev WR0_VAR_TH1_simp := WR0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules19` and `fold_Imp_rules19`
   are represented by `WR0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR Back1 step 4 ***) -/

axiom EAT0_VAR_Back1 (n : Int) :
    EVEN n →
      eqF (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.End0, Event.Back1} : Set Event) (fun x =>
          IF decide (x = Event.End0)
          THEN Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))
          ELSE Par1 (Par0 (EAT0P n) (VARP n)) TH1P))

abbrev EAT0_VAR_Back1_simp := EAT0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules20` and `fold_Imp_rules20`
   are represented by `EAT0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR EAT1 step 4 ***) -/

axiom TH0_VAR_WR1 (n : Int) :
    ODD n →
      eqF (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.WR1 (3 * n + 1), Event.RD0 n} : Set Event) (fun x =>
          IF decide (x = Event.WR1 (3 * n + 1))
          THEN Par1 (Par0 TH0P (VARP (3 * n + 1))) TH1P
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))

abbrev TH0_VAR_WR1_simp := TH0_VAR_WR1

/- The Isabelle theorem bundles `unfold_Imp_rules21` and `fold_Imp_rules21`
   are represented by `TH0_VAR_WR1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR EAT1 step 4 ***) -/

axiom Back0_VAR_EAT1 (n : Int) :
    ODD n →
      eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (EAT1P n)) MF MF
        (proc.Ext_pre_choice ({Event.End1, Event.Back0} : Set Event) (fun x =>
          IF decide (x = Event.End1)
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))
          ELSE Par1 (Par0 TH0P (VARP n)) (EAT1P n)))

abbrev Back0_VAR_EAT1_simp := Back0_VAR_EAT1

/- The Isabelle theorem bundles `unfold_Imp_rules22` and `fold_Imp_rules22`
   are represented by `Back0_VAR_EAT1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR Back1 step 5 ***) -/

axiom WR0_VAR_Back1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))) (Pref Event.Back1 TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.WR0 (n / 2), Event.Back1} : Set Event) (fun x =>
          IF decide (x = Event.WR0 (n / 2))
          THEN Par1 (Par0 TH0P (VARP (n / 2))) (Pref Event.Back1 TH1P)
          ELSE Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) TH1P)))

abbrev WR0_VAR_Back1_simp := WR0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules23` and `fold_Imp_rules23`
   are represented by `WR0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR WR1 step 5 ***) -/

axiom Back0_VAR_WR1 (n : Int) :
    ODD n →
      eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (Pref (Event.WR1 (3 * n + 1)) TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.WR1 (3 * n + 1), Event.Back0} : Set Event) (fun x =>
          IF decide (x = Event.WR1 (3 * n + 1))
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP (3 * n + 1))) TH1P)
          ELSE Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)))

abbrev Back0_VAR_WR1_simp := Back0_VAR_WR1

/- The Isabelle theorem bundles `unfold_Imp_rules24` and `fold_Imp_rules24`
   are represented by `Back0_VAR_WR1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

end DM2_para
