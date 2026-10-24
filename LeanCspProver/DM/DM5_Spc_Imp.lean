           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007 (modified)      |
            |                 July 2009 (modified)      |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DM.DM4_Spc_def

open fpmode
open DM1_Imp_def
open DM4_Spc_def

noncomputable section

namespace DM5_Spc_Imp

private abbrev TH0P : proc ImpName Event := proc.Proc_name ImpName.TH0

private abbrev TH1P : proc ImpName Event := proc.Proc_name ImpName.TH1

private abbrev VARP (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.VAR n)

private abbrev EAT0P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT0 n)

private abbrev EAT1P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT1 n)

private abbrev Par0 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH0 Q

private abbrev Par1 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH1 Q

private abbrev Pref (e : Event) (P : proc ImpName Event) : proc ImpName Event := proc.Act_prefix e P

private abbrev Hide (P : proc ImpName Event) : proc ImpName Event :=
  proc.Hiding P (CH0 ∪ CH1)

private abbrev SpcSub (p : SpcName) : proc ImpName Event :=
  (Spcfun p) << Spc_to_Imp

/- ---------- picking one summand of `Spc_to_Imp` ---------- -/

private theorem NUM_inj : Function.Injective Event.NUM := by
  intro a b h
  cases h
  rfl

private theorem l1 {P1 P2 Q : proc ImpName Event} (h : refF P1 MF MF Q) :
    refF (P1 |~| P2) MF MF Q :=
  cspF_Int_choice_left1 h

private theorem l2 {P1 P2 Q : proc ImpName Event} (h : refF P2 MF MF Q) :
    refF (P1 |~| P2) MF MF Q :=
  cspF_Int_choice_left2 h

private theorem pickN {X : Set Int} {Pf : Int → proc ImpName Event} {Q : proc ImpName Event}
    (x : Int) (hx : x ∈ X) (h : refF (Pf x) MF MF Q) :
    refF (Rep_int_choice_f Event.NUM X Pf) MF MF Q :=
  cspF_Rep_int_choice_f_left_x NUM_inj hx h

private theorem spc1 (x : Int) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF (Hide (Par1 (Par0 TH0P (VARP x)) TH1P)) :=
  l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1
    (pickN x (Set.mem_univ x) cspF_reflex_ref_P)))))))))))

private theorem spc2 (x : Int) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) TH1P)) :=
  l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1
    (l2 (pickN x (Set.mem_univ x) cspF_reflex_ref_P)))))))))))

private theorem spc3 (x : Int) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 TH0P (VARP x)) (Pref Event.Back1 TH1P))) :=
  l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1
    (l2 (pickN x (Set.mem_univ x) cspF_reflex_ref_P))))))))))

private theorem spc4 (x : Int) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref Event.Back1 TH1P))) :=
  l1 (l1 (l1 (l1 (l1 (l1 (l1 (l1
    (l2 (pickN x (Set.mem_univ x) cspF_reflex_ref_P)))))))))

private theorem spc5 (x : Int) (hx : EVEN x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P x)) (VARP x)) (Pref Event.Back1 TH1P))) :=
  l1 (l1 (l1 (l1 (l1 (l1 (l1
    (l2 (pickN x hx cspF_reflex_ref_P))))))))

private theorem spc6 (x : Int) (hx : ODD x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref Event.Eat1 (EAT1P x)))) :=
  l1 (l1 (l1 (l1 (l1 (l1
    (l2 (pickN x hx cspF_reflex_ref_P)))))))

private theorem spc7 (x : Int) (hx : EVEN x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P x)) (VARP x)) TH1P)) :=
  l1 (l1 (l1 (l1 (l1
    (l2 (pickN x hx cspF_reflex_ref_P))))))

private theorem spc8 (x : Int) (hx : ODD x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 TH0P (VARP x)) (Pref Event.Eat1 (EAT1P x)))) :=
  l1 (l1 (l1 (l1
    (l2 (pickN x hx cspF_reflex_ref_P)))))

private theorem spc9 (x : Int) (hx : EVEN x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref (Event.WR0 (x / 2)) TH0P) (VARP x)) TH1P)) :=
  l1 (l1 (l1
    (l2 (pickN x hx cspF_reflex_ref_P))))

private theorem spc10 (x : Int) (hx : EVEN x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref (Event.WR0 (x / 2)) TH0P) (VARP x)) (Pref Event.Back1 TH1P))) :=
  l1 (l1
    (l2 (pickN x hx cspF_reflex_ref_P)))

private theorem spc11 (x : Int) (hx : ODD x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 TH0P (VARP x)) (Pref (Event.WR1 (3 * x + 1)) TH1P))) :=
  l1 (l2 (pickN x hx cspF_reflex_ref_P))

private theorem spc12 (x : Int) (hx : ODD x) :
    refF (Spc_to_Imp SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref (Event.WR1 (3 * x + 1)) TH1P))) :=
  l2 (pickN x hx cspF_reflex_ref_P)

private theorem spcE1 (x : Int) (hx : EVEN x) :
    refF (Spc_to_Imp SpcName.EAT0_TH1) MF MF (Hide (Par1 (Par0 (EAT0P x) (VARP x)) TH1P)) :=
  l1 (pickN x hx cspF_reflex_ref_P)

private theorem spcE2 (x : Int) (hx : EVEN x) :
    refF (Spc_to_Imp SpcName.EAT0_TH1) MF MF
      (Hide (Par1 (Par0 (EAT0P x) (VARP x)) (Pref Event.Back1 TH1P))) :=
  l2 (pickN x hx cspF_reflex_ref_P)

private theorem spcT1 (x : Int) (hx : ODD x) :
    refF (Spc_to_Imp SpcName.TH0_EAT1) MF MF (Hide (Par1 (Par0 TH0P (VARP x)) (EAT1P x))) :=
  l1 (pickN x hx cspF_reflex_ref_P)

private theorem spcT2 (x : Int) (hx : ODD x) :
    refF (Spc_to_Imp SpcName.TH0_EAT1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (EAT1P x))) :=
  l2 (pickN x hx cspF_reflex_ref_P)

/- ---------- spec side: one step of `SpcSub` ---------- -/

private abbrev bodyTT : Event → proc ImpName Event := fun x =>
  IF decide (x = Event.Eat0) THEN Spc_to_Imp SpcName.EAT0_TH1
  ELSE IF decide (x = Event.Eat1) THEN Spc_to_Imp SpcName.TH0_EAT1
  ELSE Spc_to_Imp SpcName.TH0_TH1

private abbrev bodyET : Event → proc ImpName Event := fun x =>
  IF decide (x = Event.End0) THEN Spc_to_Imp SpcName.TH0_TH1
  ELSE Spc_to_Imp SpcName.EAT0_TH1

private abbrev bodyTE : Event → proc ImpName Event := fun x =>
  IF decide (x = Event.End1) THEN Spc_to_Imp SpcName.TH0_TH1
  ELSE Spc_to_Imp SpcName.TH0_EAT1

private theorem SpcSub_TT : SpcSub SpcName.TH0_TH1 = Int_pre_choice OBS bodyTT := by
  change ((Int_pre_choice OBS fun x =>
      IF decide (x = Event.Eat0) THEN proc.Proc_name SpcName.EAT0_TH1
      ELSE IF decide (x = Event.Eat1) THEN proc.Proc_name SpcName.TH0_EAT1
      ELSE proc.Proc_name SpcName.TH0_TH1) << Spc_to_Imp) = _
  rw [Subst_procfun_Int_pre_choice]
  rfl

private theorem SpcSub_ET :
    SpcSub SpcName.EAT0_TH1 = Int_pre_choice (OBS \ {Event.Eat1}) bodyET := by
  change ((Int_pre_choice (OBS \ {Event.Eat1}) fun x =>
      IF decide (x = Event.End0) THEN proc.Proc_name SpcName.TH0_TH1
      ELSE proc.Proc_name SpcName.EAT0_TH1) << Spc_to_Imp) = _
  rw [Subst_procfun_Int_pre_choice]
  rfl

private theorem SpcSub_TE :
    SpcSub SpcName.TH0_EAT1 = Int_pre_choice (OBS \ {Event.Eat0}) bodyTE := by
  change ((Int_pre_choice (OBS \ {Event.Eat0}) fun x =>
      IF decide (x = Event.End1) THEN proc.Proc_name SpcName.TH0_TH1
      ELSE proc.Proc_name SpcName.TH0_EAT1) << Spc_to_Imp) = _
  rw [Subst_procfun_Int_pre_choice]
  rfl

private theorem IF_true' (P Q : proc ImpName Event) :
    eqF (IF true THEN P ELSE Q) MF MF P :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem IF_false' (P Q : proc ImpName Event) :
    eqF (IF false THEN P ELSE Q) MF MF Q :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem bodyTT_Eat0 : eqF (bodyTT Event.Eat0) MF MF (Spc_to_Imp SpcName.EAT0_TH1) :=
  IF_true' _ _

private theorem bodyTT_Eat1 : eqF (bodyTT Event.Eat1) MF MF (Spc_to_Imp SpcName.TH0_EAT1) :=
  cspF_trans_left_eq (IF_false' _ _) (IF_true' _ _)

private theorem bodyTT_oth {a : Event} (h0 : ¬ a = Event.Eat0) (h1 : ¬ a = Event.Eat1) :
    eqF (bodyTT a) MF MF (Spc_to_Imp SpcName.TH0_TH1) := by
  change eqF (IF decide (a = Event.Eat0) THEN _ ELSE IF decide (a = Event.Eat1) THEN _ ELSE _)
    MF MF _
  rw [decide_eq_false h0, decide_eq_false h1]
  exact cspF_trans_left_eq (IF_false' _ _) (IF_false' _ _)

private theorem bodyET_End0 : eqF (bodyET Event.End0) MF MF (Spc_to_Imp SpcName.TH0_TH1) :=
  IF_true' _ _

private theorem bodyET_oth {a : Event} (h : ¬ a = Event.End0) :
    eqF (bodyET a) MF MF (Spc_to_Imp SpcName.EAT0_TH1) := by
  change eqF (IF decide (a = Event.End0) THEN _ ELSE _) MF MF _
  rw [decide_eq_false h]
  exact IF_false' _ _

private theorem bodyTE_End1 : eqF (bodyTE Event.End1) MF MF (Spc_to_Imp SpcName.TH0_TH1) :=
  IF_true' _ _

private theorem bodyTE_oth {a : Event} (h : ¬ a = Event.End1) :
    eqF (bodyTE a) MF MF (Spc_to_Imp SpcName.TH0_EAT1) := by
  change eqF (IF decide (a = Event.End1) THEN _ ELSE _) MF MF _
  rw [decide_eq_false h]
  exact IF_false' _ _

/- ---------- the two implementation shapes ---------- -/

/- the implementation offers exactly `a`; the specification offers at least it. -/

private theorem one {X : Set Event} {Pf : Event → proc ImpName Event}
    {a : Event} {P : proc ImpName Event} (ha : a ∈ X)
    (hP : refF (Pf a) MF MF P) :
    refF (Int_pre_choice X Pf) MF MF (Pref a P) := by
  refine cspF_rw_right_ref cspF_Act_prefix_step ?_
  refine cspF_Int_Ext_pre_choice_subset (by simp) (Set.singleton_subset_iff.mpr ha) ?_
  intro e he
  rw [Set.mem_singleton_iff] at he
  subst he
  exact hP

/- the implementation offers exactly `a` and `b`. -/

private theorem two {X : Set Event} {Pf : Event → proc ImpName Event}
    {a b : Event} {P Q : proc ImpName Event}
    (hab : a ≠ b) (ha : a ∈ X) (hb : b ∈ X)
    (hP : refF (Pf a) MF MF P) (hQ : refF (Pf b) MF MF Q) :
    refF (Int_pre_choice X Pf) MF MF ((Pref a P) [+] (Pref b Q)) := by
  have hfold :
      eqF ((Pref a P) [+] (Pref b Q)) MF MF
        (proc.Ext_pre_choice (({a} : Set Event) ∪ ({b} : Set Event)) fun x =>
          procIte (x ∈ ({a} : Set Event) ∧ x ∈ ({b} : Set Event)) (P |~| Q)
            (procIte (x ∈ ({a} : Set Event)) P Q)) :=
    cspF_trans_left_eq
      (cspF_Ext_choice_cong cspF_Act_prefix_step cspF_Act_prefix_step)
      cspF_Ext_choice_step
  refine cspF_rw_right_ref hfold ?_
  rw [Set.singleton_union]
  refine cspF_Int_Ext_pre_choice_subset (Set.insert_nonempty a {b}).ne_empty ?_ ?_
  · rintro e he
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ha
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact hb
  · intro e he
    rcases Set.mem_insert_iff.mp he with rfl | he
    · rw [procIte_neg (fun hc => hab (Set.mem_singleton_iff.mp hc.2)),
        procIte_pos (Set.mem_singleton_iff.mpr rfl)]
      exact hP
    · rw [Set.mem_singleton_iff] at he
      subst he
      rw [procIte_neg (fun hc => hab (Set.mem_singleton_iff.mp hc.1).symm),
        procIte_neg (fun hc => hab (Set.mem_singleton_iff.mp hc).symm)]
      exact hQ

/- right-hand `IF` and parity bridges -/

private theorem ref_IF {S A B : proc ImpName Event} {c : Bool}
    (hA : c = true → refF S MF MF A) (hB : c = false → refF S MF MF B) :
    refF S MF MF (IF c THEN A ELSE B) := by
  cases c
  · exact cspF_rw_right_ref (IF_false' A B) (hB rfl)
  · exact cspF_rw_right_ref (IF_true' A B) (hA rfl)

private theorem EVEN_of_not_ODD {n : Int} (h : ¬ ODD n) : EVEN n := by
  have h' := EVEN_not_ODD n
  rw [Bool.not_eq_true] at h
  rw [h] at h'
  simpa using h'

private theorem not_ODD_of_EVEN {n : Int} (h : EVEN n) : ¬ ODD n := by
  have h' := EVEN_not_ODD n
  rw [h] at h'
  simp at h'
  simp [h']

/- *****************************************************************

         1. proves lemma for Spc <=F Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- (*** Back0_Back1 ***) -/

theorem Back0_Back1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref Event.Back1 TH1P))) := by
  rw [SpcSub_TT]
  refine cspF_rw_right_ref (DM3_hide.Back0_VAR_Back1_HIDE x) ?_
  exact two (by simp) (by simp) (by simp)
    (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc3 x))
    (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc2 x))

abbrev Back0_Back1_simp := Back0_Back1

/- (*** Eat0_Back1 ***) -/

theorem Eat0_Back1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P x)) (VARP x)) (Pref Event.Back1 TH1P))) := by
  intro h
  have hE : EVEN x := EVEN_of_not_ODD h
  rw [SpcSub_TT]
  refine cspF_rw_right_ref (DM3_hide.Eat0_VAR_Back1_HIDE x hE) ?_
  exact two (by simp) (by simp) (by simp)
    (cspF_rw_left_ref bodyTT_Eat0 (spcE2 x hE))
    (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc7 x hE))

abbrev Eat0_Back1_simp := Eat0_Back1

/- (*** Back0_Eat1 ***) -/

theorem Back0_Eat1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref Event.Eat1 (EAT1P x)))) := by
  intro hO
  rw [SpcSub_TT]
  refine cspF_rw_right_ref (DM3_hide.Back0_VAR_Eat1_HIDE x hO) ?_
  exact two (by simp) (by simp) (by simp)
    (cspF_rw_left_ref bodyTT_Eat1 (spcT2 x hO))
    (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc8 x hO))

abbrev Back0_Eat1_simp := Back0_Eat1

theorem EAT0_Back1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.EAT0_TH1) MF MF
        (Hide (Par1 (Par0 (EAT0P x) (VARP x)) (Pref Event.Back1 TH1P))) := by
  intro h
  have hE : EVEN x := EVEN_of_not_ODD h
  rw [SpcSub_ET]
  refine cspF_rw_right_ref (DM3_hide.EAT0_VAR_Back1_HIDE x hE) ?_
  exact two (by simp) (by simp) (by simp)
    (cspF_rw_left_ref bodyET_End0 (spc10 x hE))
    (cspF_rw_left_ref (bodyET_oth (by simp)) (spcE1 x hE))

abbrev EAT0_Back1_simp := EAT0_Back1

/- (*** Back0_EAT1 ***) -/

theorem Back0_EAT1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_EAT1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (EAT1P x))) := by
  intro hO
  rw [SpcSub_TE]
  refine cspF_rw_right_ref (DM3_hide.Back0_VAR_EAT1_HIDE x hO) ?_
  exact two (by simp) (by simp) (by simp)
    (cspF_rw_left_ref bodyTE_End1 (spc12 x hO))
    (cspF_rw_left_ref (bodyTE_oth (by simp)) (spcT1 x hO))

abbrev Back0_EAT1_simp := Back0_EAT1

/- (*** Back0_TH1  ***) -/

/- declare SpcDef.simps [simp del] -/

theorem Back0_TH1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) TH1P)) := by
  refine cspF_rw_right_ref (DM3_hide.Back0_VAR_TH1_HIDE x) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (ref_IF (fun hO => Back0_Eat1 x hO) (fun _ => Back0_Back1 x))
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc1 x))

abbrev Back0_TH1_simp := Back0_TH1

/- (*** TH0_Back1  ***) -/

theorem TH0_Back1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 TH0P (VARP x)) (Pref Event.Back1 TH1P))) := by
  refine cspF_rw_right_ref (DM3_hide.TH0_VAR_Back1_HIDE x) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_
    (ref_IF (fun hE => Eat0_Back1 x (not_ODD_of_EVEN hE)) (fun _ => Back0_Back1 x))
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc1 x))

abbrev TH0_Back1_simp := TH0_Back1

/- (*** TH0_Eat1 ***) -/

theorem TH0_Eat1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 TH0P (VARP x)) (Pref Event.Eat1 (EAT1P x)))) := by
  intro hO
  refine cspF_rw_right_ref (DM3_hide.TH0_VAR_Eat1_HIDE x hO) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (Back0_Eat1 x hO)
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref bodyTT_Eat1 (spcT1 x hO))

abbrev TH0_Eat1_simp := TH0_Eat1

/- (*** Eat0_TH1 ***) -/

theorem Eat0_TH1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P x)) (VARP x)) TH1P)) := by
  intro h
  have hE : EVEN x := EVEN_of_not_ODD h
  refine cspF_rw_right_ref (DM3_hide.Eat0_VAR_TH1_HIDE x hE) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (Eat0_Back1 x h)
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref bodyTT_Eat0 (spcE1 x hE))

abbrev Eat0_TH1_simp := Eat0_TH1

/- (*** TH0_TH1 ***) -/

theorem TH0_TH1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF (Hide (Par1 (Par0 TH0P (VARP x)) TH1P)) := by
  refine cspF_rw_right_ref (DM3_hide.TH0_VAR_TH1_HIDE x) ?_
  refine cspF_Int_choice_right
    (ref_IF (fun hE => Eat0_TH1 x (not_ODD_of_EVEN hE)) (fun _ => Back0_TH1 x))
    (ref_IF (fun hO => TH0_Eat1 x hO) (fun _ => TH0_Back1 x))

abbrev TH0_TH1_simp := TH0_TH1

/- (*** Back0_TH0_TH1 ***) -/

theorem Back0_TH0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP (3 * x + 1))) TH1P))) := by
  intro _
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc1 (3 * x + 1)))

abbrev Back0_TH0_WR1_simp := Back0_TH0_WR1

/- (*** Back1_TH0_TH1 ***) -/

theorem Back1_TH0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Pref Event.Back1 (Hide (Par1 (Par0 TH0P (VARP (3 * x + 1))) TH1P))) := by
  intro _
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc1 (3 * x + 1)))

abbrev Back1_TH0_WR1_simp := Back1_TH0_WR1

/- (*** Back0_WR1 ***) -/

theorem Back0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x))
          (Pref (Event.WR1 (3 * x + 1)) TH1P))) := by
  intro hO
  refine cspF_rw_right_ref (DM3_hide.Back0_VAR_WR1_HIDE x hO) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (Back0_TH1 (3 * x + 1))
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc11 x hO))

abbrev Back0_WR1_simp := Back0_WR1

/- (*** WR0_Back1 ***) -/

theorem WR0_Back1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref (Event.WR0 (x / 2)) TH0P) (VARP x)) (Pref Event.Back1 TH1P))) := by
  intro h
  have hE : EVEN x := EVEN_of_not_ODD h
  refine cspF_rw_right_ref (DM3_hide.WR0_VAR_Back1_HIDE x hE) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (TH0_Back1 (x / 2))
  rw [SpcSub_TT]
  exact one (by simp) (cspF_rw_left_ref (bodyTT_oth (by simp) (by simp)) (spc9 x hE))

abbrev WR0_Back1_simp := WR0_Back1

/- (*** TH0_WR1 ***) -/

theorem TH0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 TH0P (VARP x)) (Pref (Event.WR1 (3 * x + 1)) TH1P))) := by
  intro hO
  refine cspF_rw_right_ref (DM3_hide.TH0_VAR_WR1_HIDE x hO) ?_
  exact cspF_Int_choice_right (TH0_TH1 (3 * x + 1)) (Back0_WR1 x hO)

abbrev TH0_WR1_simp := TH0_WR1

/- (*** WR0_TH1 ***) -/

theorem WR0_TH1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref (Event.WR0 (x / 2)) TH0P) (VARP x)) TH1P)) := by
  intro h
  have hE : EVEN x := EVEN_of_not_ODD h
  refine cspF_rw_right_ref (DM3_hide.WR0_VAR_TH1_HIDE x hE) ?_
  exact cspF_Int_choice_right (TH0_TH1 (x / 2)) (WR0_Back1 x h)

abbrev WR0_TH1_simp := WR0_TH1

/- (*** EAT0_TH1 ***) -/

theorem EAT0_TH1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.EAT0_TH1) MF MF (Hide (Par1 (Par0 (EAT0P x) (VARP x)) TH1P)) := by
  intro h
  have hE : EVEN x := EVEN_of_not_ODD h
  refine cspF_rw_right_ref (DM3_hide.EAT0_VAR_TH1_HIDE x hE) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (EAT0_Back1 x h)
  rw [SpcSub_ET]
  exact one (by simp) (cspF_rw_left_ref bodyET_End0 (spc9 x hE))

abbrev EAT0_TH1_simp := EAT0_TH1

/- (*** TH0_EAT1 ***) -/

theorem TH0_EAT1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_EAT1) MF MF (Hide (Par1 (Par0 TH0P (VARP x)) (EAT1P x))) := by
  intro hO
  refine cspF_rw_right_ref (DM3_hide.TH0_VAR_EAT1_HIDE x hO) ?_
  rw [Timeout]
  refine cspF_Timeout_right ?_ (Back0_EAT1 x hO)
  rw [SpcSub_TE]
  exact one (by simp) (cspF_rw_left_ref bodyTE_End1 (spc11 x hO))

abbrev TH0_EAT1_simp := TH0_EAT1

/- *********************************************************
                  ALL n. Spc <=F Imp n
 ********************************************************* -/

private theorem r2 {S Q1 Q2 : proc ImpName Event}
    (h1 : refF S MF MF Q1) (h2 : refF S MF MF Q2) :
    refF S MF MF (Q1 |~| Q2) :=
  cspF_Int_choice_right h1 h2

private theorem rN {X : Set Int} {Pf : Int → proc ImpName Event} {S : proc ImpName Event}
    (h : ∀ n, n ∈ X → refF S MF MF (Pf n)) :
    refF S MF MF (Rep_int_choice_f Event.NUM X Pf) :=
  cspF_Rep_int_choice_f_right NUM_inj h

theorem Spc_ref_Seq (n : Int) :
    refF Spc (MF : SpcName → domFType Event) (MF : ImpName → domFType Event) (Imp n) := by
  rw [Spc_def]
  refine cspF_fp_induct_ref_left (Pf := Spcfun) (f := Spc_to_Imp) (p0 := SpcName.TH0_TH1)
    rfl (Or.inl rfl) guarded_Spc (spc1 n) ?_
  intro p
  cases p
  · exact r2 (r2 (r2 (r2 (r2 (r2 (r2 (r2 (r2 (r2 (r2
      (rN (fun m _ => TH0_TH1 m))
      (rN (fun m _ => Back0_TH1 m)))
      (rN (fun m _ => TH0_Back1 m)))
      (rN (fun m _ => Back0_Back1 m)))
      (rN (fun m hm => Eat0_Back1 m (not_ODD_of_EVEN hm))))
      (rN (fun m hm => Back0_Eat1 m hm)))
      (rN (fun m hm => Eat0_TH1 m (not_ODD_of_EVEN hm))))
      (rN (fun m hm => TH0_Eat1 m hm)))
      (rN (fun m hm => WR0_TH1 m (not_ODD_of_EVEN hm))))
      (rN (fun m hm => WR0_Back1 m (not_ODD_of_EVEN hm))))
      (rN (fun m hm => TH0_WR1 m hm)))
      (rN (fun m hm => Back0_WR1 m hm))
  · exact r2 (rN (fun m hm => EAT0_TH1 m (not_ODD_of_EVEN hm)))
      (rN (fun m hm => EAT0_Back1 m (not_ODD_of_EVEN hm)))
  · exact r2 (rN (fun m hm => TH0_EAT1 m hm))
      (rN (fun m hm => Back0_EAT1 m hm))

end DM5_Spc_Imp
