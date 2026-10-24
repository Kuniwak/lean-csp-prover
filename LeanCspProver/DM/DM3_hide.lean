           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |                April 2020  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DM.DM2_para

open fpmode
open DM1_Imp_def

noncomputable section

namespace DM3_hide

private abbrev TH0P : proc ImpName Event := proc.Proc_name ImpName.TH0

private abbrev TH1P : proc ImpName Event := proc.Proc_name ImpName.TH1

private abbrev VARP (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.VAR n)

private abbrev EAT0P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT0 n)

private abbrev EAT1P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT1 n)

private abbrev Par0 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH0 Q

private abbrev Par1 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH1 Q

private abbrev Pref (e : Event) (P : proc ImpName Event) : proc ImpName Event := proc.Act_prefix e P

/- Lean note:
   Isabelle's hiding syntax `P -- X` is written as `proc.Hiding P X` in Lean.
   The fixed hidden alphabet in this file is abbreviated by `Hide`. -/

private abbrev Hide (P : proc ImpName Event) : proc ImpName Event :=
  proc.Hiding P (CH0 ∪ CH1)

private theorem decide_self (a : Event) : decide (a = a) = true := by simp

private theorem decide_ne (a b : Event) (h : ¬a = b) : decide (a = b) = false := by simp [h]

private theorem IF_true (P Q : proc ImpName Event) :
    eqF (IF true THEN P ELSE Q) MF MF P :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem IF_false (P Q : proc ImpName Event) :
    eqF (IF false THEN P ELSE Q) MF MF Q :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem Hide_IF (c : Bool) (P Q : proc ImpName Event) :
    eqF (Hide (IF c THEN P ELSE Q)) MF MF (IF c THEN Hide P ELSE Hide Q) := by
  cases c
  · exact cspF_trans_left_eq (cspF_Hiding_cong rfl (IF_false P Q)) (cspF_sym (IF_false _ _))
  · exact cspF_trans_left_eq (cspF_Hiding_cong rfl (IF_true P Q)) (cspF_sym (IF_true _ _))

/- membership in the hidden alphabet -/

private theorem RD0_in_CH (m : Int) : Event.RD0 m ∈ CH0 ∪ CH1 := Or.inl (Or.inl ⟨m, rfl⟩)
private theorem WR0_in_CH (m : Int) : Event.WR0 m ∈ CH0 ∪ CH1 := Or.inl (Or.inr ⟨m, rfl⟩)
private theorem RD1_in_CH (m : Int) : Event.RD1 m ∈ CH0 ∪ CH1 := Or.inr (Or.inl ⟨m, rfl⟩)
private theorem WR1_in_CH (m : Int) : Event.WR1 m ∈ CH0 ∪ CH1 := Or.inr (Or.inr ⟨m, rfl⟩)

private theorem Eat0_notin_CH : Event.Eat0 ∉ CH0 ∪ CH1 := by simp
private theorem Back0_notin_CH : Event.Back0 ∉ CH0 ∪ CH1 := by simp
private theorem End0_notin_CH : Event.End0 ∉ CH0 ∪ CH1 := by simp
private theorem Eat1_notin_CH : Event.Eat1 ∉ CH0 ∪ CH1 := by simp
private theorem Back1_notin_CH : Event.Back1 ∉ CH0 ∪ CH1 := by simp
private theorem End1_notin_CH : Event.End1 ∉ CH0 ∪ CH1 := by simp

/- ---------- the pair index set after one `Hiding` step ---------- -/

private theorem hide_vis_vis {L P Q : proc ImpName Event} {a b : Event}
    (ha : a ∉ CH0 ∪ CH1) (hb : b ∉ CH0 ∪ CH1) (hab : a ≠ b)
    (h : eqF L MF MF (proc.Ext_pre_choice ({a, b} : Set Event)
      (fun x => IF decide (x = a) THEN P ELSE Q))) :
    eqF (Hide L) MF MF ((Pref a (Hide P)) [+] (Pref b (Hide Q))) := by
  have hdisj : ({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he, hc⟩
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact ha hc
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact hb hc
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl h) ?_
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_pos hdisj]
  have hfold :
      eqF ((Pref a (Hide P)) [+] (Pref b (Hide Q))) MF MF
        (proc.Ext_pre_choice (({a} : Set Event) ∪ ({b} : Set Event)) fun x =>
          procIte (x ∈ ({a} : Set Event) ∧ x ∈ ({b} : Set Event))
            ((Hide P) |~| (Hide Q))
            (procIte (x ∈ ({a} : Set Event)) (Hide P) (Hide Q))) :=
    cspF_trans_left_eq
      (cspF_Ext_choice_cong cspF_Act_prefix_step cspF_Act_prefix_step)
      cspF_Ext_choice_step
  refine cspF_trans_left_eq ?_ (cspF_sym hfold)
  rw [Set.singleton_union]
  refine cspF_Ext_pre_choice_cong rfl (fun x hx => ?_)
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · rw [procIte_neg (fun hc => hab (Set.mem_singleton_iff.mp hc.2)),
      procIte_pos (Set.mem_singleton_iff.mpr rfl), decide_self]
    exact cspF_Hiding_cong rfl (IF_true P Q)
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [procIte_neg (fun hc => hab (Set.mem_singleton_iff.mp hc.1).symm),
      procIte_neg (fun hc => hab (Set.mem_singleton_iff.mp hc).symm),
      decide_ne x a (Ne.symm hab)]
    exact cspF_Hiding_cong rfl (IF_false P Q)

private theorem hide_vis_hid {L P Q : proc ImpName Event} {a b : Event}
    (ha : a ∉ CH0 ∪ CH1) (hb : b ∈ CH0 ∪ CH1) (hab : a ≠ b)
    (h : eqF L MF MF (proc.Ext_pre_choice ({a, b} : Set Event)
      (fun x => IF decide (x = a) THEN P ELSE Q))) :
    eqF (Hide L) MF MF (Timeout (Pref a (Hide P)) (Hide Q)) := by
  have hnotdisj : ¬ (({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ∅) := by
    intro hc
    have hm : b ∈ ({a, b} : Set Event) ∩ (CH0 ∪ CH1) := ⟨Or.inr rfl, hb⟩
    rw [hc] at hm
    exact hm
  have hdiff : ({a, b} : Set Event) \ (CH0 ∪ CH1) = ({a} : Set Event) := by
    ext e
    constructor
    · rintro ⟨he, hc⟩
      rcases Set.mem_insert_iff.mp he with rfl | he
      · rfl
      · rw [Set.mem_singleton_iff] at he
        subst he
        exact absurd hb hc
    · rintro rfl
      exact ⟨Or.inl rfl, ha⟩
  have hinter : ({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ({b} : Set Event) := by
    ext e
    constructor
    · rintro ⟨he, hc⟩
      rcases Set.mem_insert_iff.mp he with rfl | he
      · exact absurd hc ha
      · exact he
    · rintro rfl
      exact ⟨Or.inr rfl, hb⟩
  rw [Timeout]
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl h) ?_
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_neg hnotdisj, hdiff, hinter]
  refine cspF_Timeout_cong ?_ ?_
  · refine cspF_trans_left_eq (cspF_Ext_pre_choice_cong (Qf := fun _ => Hide P) rfl
      (fun x hx => ?_)) (cspF_sym cspF_Act_prefix_step)
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [decide_self]
    exact cspF_Hiding_cong rfl (IF_true P Q)
  · refine cspF_trans_left_eq (cspF_Rep_int_choice_cong_com (Qf := fun _ => Hide Q) rfl
      (fun x hx => ?_)) (cspF_Rep_int_choice_com_unit (by simp))
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [decide_ne x a (Ne.symm hab)]
    exact cspF_Hiding_cong rfl (IF_false P Q)

private theorem hide_hid_vis {L P Q : proc ImpName Event} {a b : Event}
    (ha : a ∈ CH0 ∪ CH1) (hb : b ∉ CH0 ∪ CH1) (hab : a ≠ b)
    (h : eqF L MF MF (proc.Ext_pre_choice ({a, b} : Set Event)
      (fun x => IF decide (x = a) THEN P ELSE Q))) :
    eqF (Hide L) MF MF (Timeout (Pref b (Hide Q)) (Hide P)) := by
  have hnotdisj : ¬ (({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ∅) := by
    intro hc
    have hm : a ∈ ({a, b} : Set Event) ∩ (CH0 ∪ CH1) := ⟨Or.inl rfl, ha⟩
    rw [hc] at hm
    exact hm
  have hdiff : ({a, b} : Set Event) \ (CH0 ∪ CH1) = ({b} : Set Event) := by
    ext e
    constructor
    · rintro ⟨he, hc⟩
      rcases Set.mem_insert_iff.mp he with rfl | he
      · exact absurd ha hc
      · exact he
    · rintro rfl
      exact ⟨Or.inr rfl, hb⟩
  have hinter : ({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ({a} : Set Event) := by
    ext e
    constructor
    · rintro ⟨he, hc⟩
      rcases Set.mem_insert_iff.mp he with rfl | he
      · rfl
      · rw [Set.mem_singleton_iff] at he
        subst he
        exact absurd hc hb
    · rintro rfl
      exact ⟨Or.inl rfl, ha⟩
  rw [Timeout]
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl h) ?_
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_neg hnotdisj, hdiff, hinter]
  refine cspF_Timeout_cong ?_ ?_
  · refine cspF_trans_left_eq (cspF_Ext_pre_choice_cong (Qf := fun _ => Hide Q) rfl
      (fun x hx => ?_)) (cspF_sym cspF_Act_prefix_step)
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [decide_ne x a (Ne.symm hab)]
    exact cspF_Hiding_cong rfl (IF_false P Q)
  · refine cspF_trans_left_eq (cspF_Rep_int_choice_cong_com (Qf := fun _ => Hide P) rfl
      (fun x hx => ?_)) (cspF_Rep_int_choice_com_unit (by simp))
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [decide_self]
    exact cspF_Hiding_cong rfl (IF_true P Q)

private theorem hide_hid_hid {L P Q : proc ImpName Event} {a b : Event}
    (ha : a ∈ CH0 ∪ CH1) (hb : b ∈ CH0 ∪ CH1) (hab : a ≠ b)
    (h : eqF L MF MF (proc.Ext_pre_choice ({a, b} : Set Event)
      (fun x => IF decide (x = a) THEN P ELSE Q))) :
    eqF (Hide L) MF MF ((Hide P) |~| (Hide Q)) := by
  have hnotdisj : ¬ (({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ∅) := by
    intro hc
    have hm : a ∈ ({a, b} : Set Event) ∩ (CH0 ∪ CH1) := ⟨Or.inl rfl, ha⟩
    rw [hc] at hm
    exact hm
  have hdiff : ({a, b} : Set Event) \ (CH0 ∪ CH1) = (∅ : Set Event) := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he, hc⟩
    rcases Set.mem_insert_iff.mp he with rfl | he
    · exact hc ha
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact hc hb
  have hinter : ({a, b} : Set Event) ∩ (CH0 ∪ CH1) = ({a, b} : Set Event) := by
    ext e
    constructor
    · rintro ⟨he, -⟩
      exact he
    · intro he
      rcases Set.mem_insert_iff.mp he with rfl | he
      · exact ⟨Or.inl rfl, ha⟩
      · rw [Set.mem_singleton_iff] at he
        subst he
        exact ⟨Or.inr rfl, hb⟩
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl h) ?_
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_neg hnotdisj, hdiff, hinter]
  refine cspF_trans_left_eq
    (cspF_Timeout_cong (cspF_sym (cspF_STOP_step (M1 := MF) (M2 := MF))) cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq cspF_STOP_Timeout ?_
  refine cspF_trans_left_eq cspF_Rep_int_choice_com_insert ?_
  refine cspF_Int_choice_cong ?_ ?_
  · rw [decide_self]
    exact cspF_Hiding_cong rfl (IF_true P Q)
  · refine cspF_trans_left_eq (cspF_Rep_int_choice_cong_com (Qf := fun _ => Hide Q) rfl
      (fun x hx => ?_)) (cspF_Rep_int_choice_com_unit (by simp))
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [decide_ne x a (Ne.symm hab)]
    exact cspF_Hiding_cong rfl (IF_false P Q)

/- *****************************************************************

         1. expands hiding operators in Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- (******************** Hiding ********************) -/

/- (*** Back0 VAR Back1 HIDE ***) -/

theorem Back0_VAR_Back1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
      ((Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)))) [+]
        (Pref Event.Back1 (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P)))) :=
  hide_vis_vis Back0_notin_CH Back1_notin_CH (by simp) (DM2_para.Back0_VAR_Back1 n)

abbrev Back0_VAR_Back1_HIDE_simp := Back0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules25` and `fold_Imp_rules25`
   are represented by `Back0_VAR_Back1_HIDE_simp` together with the earlier
   simp lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR Back1 HIDE ***) -/

theorem Eat0_VAR_Back1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
        ((Pref Event.Eat0 (Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)))) [+]
          (Pref Event.Back1 (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P)))) :=
  fun hE => hide_vis_vis Eat0_notin_CH Back1_notin_CH (by simp) (DM2_para.Eat0_VAR_Back1 n hE)

abbrev Eat0_VAR_Back1_HIDE_simp := Eat0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules26` and `fold_Imp_rules26`
   are represented by `Eat0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR Eat1 HIDE ***) -/

theorem Back0_VAR_Eat1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n)))) MF MF
        ((Pref Event.Eat1 (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n)))) [+]
          (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))))) :=
  fun hO => hide_vis_vis Eat1_notin_CH Back0_notin_CH (by simp) (DM2_para.Back0_VAR_Eat1 n hO)

abbrev Back0_VAR_Eat1_HIDE_simp := Back0_VAR_Eat1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules27` and `fold_Imp_rules27`
   are represented by `Back0_VAR_Eat1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR Back1 HIDE ***) -/

theorem EAT0_VAR_Back1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
        ((Pref Event.End0
            (Hide (Par1
              (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n))
              (Pref Event.Back1 TH1P)))) [+]
          (Pref Event.Back1 (Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)))) :=
  fun hE => hide_vis_vis End0_notin_CH Back1_notin_CH (by simp) (DM2_para.EAT0_VAR_Back1 n hE)

abbrev EAT0_VAR_Back1_HIDE_simp := EAT0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules28` and `fold_Imp_rules28`
   are represented by `EAT0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR EAT1 HIDE ***) -/

theorem Back0_VAR_EAT1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n))) MF MF
        ((Pref Event.End1
            (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n))
              (Pref (Event.WR1 (3 * n + 1)) TH1P)))) [+]
          (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n))))) :=
  fun hO => hide_vis_vis End1_notin_CH Back0_notin_CH (by simp) (DM2_para.Back0_VAR_EAT1 n hO)

abbrev Back0_VAR_EAT1_HIDE_simp := Back0_VAR_EAT1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules29` and `fold_Imp_rules29`
   are represented by `Back0_VAR_EAT1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (**************************) -/
/- (*** Back0 VAR TH1 HIDE ***) -/

theorem Back0_VAR_TH1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P)) MF MF
      (Timeout
        (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) TH1P)))
        (IF ODD n
        THEN Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n)))
        ELSE Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P)))) := by
  refine cspF_trans_left_eq
    (hide_vis_hid Back0_notin_CH (RD1_in_CH n) (by simp) (DM2_para.Back0_VAR_TH1 n)) ?_
  rw [Timeout, Timeout]
  exact cspF_Timeout_cong cspF_reflex_eq_P (Hide_IF _ _ _)

abbrev Back0_VAR_TH1_HIDE_simp := Back0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules30` and `fold_Imp_rules30`
   are represented by `Back0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (**************************) -/
/- (*** TH0 VAR Back1 HIDE ***) -/

theorem TH0_VAR_Back1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))) MF MF
      (Timeout
        (Pref Event.Back1 (Hide (Par1 (Par0 TH0P (VARP n)) TH1P)))
        (IF EVEN n
        THEN Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P))
        ELSE Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P)))) := by
  refine cspF_trans_left_eq
    (hide_vis_hid Back1_notin_CH (RD0_in_CH n) (by simp) (DM2_para.TH0_VAR_Back1 n)) ?_
  rw [Timeout, Timeout]
  exact cspF_Timeout_cong cspF_reflex_eq_P (Hide_IF _ _ _)

abbrev TH0_VAR_Back1_HIDE_simp := TH0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules31` and `fold_Imp_rules31`
   are represented by `TH0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR TH1 HIDE ***) -/

theorem Eat0_VAR_TH1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P)) MF MF
        (Timeout
          (Pref Event.Eat0 (Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)))
          (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P)))) :=
  fun hE => hide_vis_hid Eat0_notin_CH (RD1_in_CH n) (by simp) (DM2_para.Eat0_VAR_TH1 n hE)

abbrev Eat0_VAR_TH1_HIDE_simp := Eat0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules32` and `fold_Imp_rules32`
   are represented by `Eat0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR Eat1 HIDE ***) -/

theorem TH0_VAR_Eat1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))) MF MF
        (Timeout
          (Pref Event.Eat1 (Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n))))
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n))))) :=
  fun hO => hide_vis_hid Eat1_notin_CH (RD0_in_CH n) (by simp) (DM2_para.TH0_VAR_Eat1 n hO)

abbrev TH0_VAR_Eat1_HIDE_simp := TH0_VAR_Eat1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules33` and `fold_Imp_rules33`
   are represented by `TH0_VAR_Eat1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR TH1 HIDE ***) -/

theorem EAT0_VAR_TH1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)) MF MF
        (Timeout
          (Pref Event.End0
            (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)))
          (Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)))) :=
  fun hE => hide_vis_hid End0_notin_CH (RD1_in_CH n) (by simp) (DM2_para.EAT0_VAR_TH1 n hE)

abbrev EAT0_VAR_TH1_HIDE_simp := EAT0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules34` and `fold_Imp_rules34`
   are represented by `EAT0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR EAT1 HIDE ***) -/

theorem TH0_VAR_EAT1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n))) MF MF
        (Timeout
          (Pref Event.End1
            (Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n)))) :=
  fun hO => hide_vis_hid End1_notin_CH (RD0_in_CH n) (by simp) (DM2_para.TH0_VAR_EAT1 n hO)

abbrev TH0_VAR_EAT1_HIDE_simp := TH0_VAR_EAT1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules35` and `fold_Imp_rules35`
   are represented by `TH0_VAR_EAT1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR TH1 HIDE step 1 ***) -/

theorem TH0_VAR_TH1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 TH0P (VARP n)) TH1P)) MF MF
      ((IF EVEN n
        THEN Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P)
        ELSE Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P)) |~|
       (IF ODD n
        THEN Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))
        ELSE Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)))) := by
  refine cspF_trans_left_eq
    (hide_hid_hid (RD0_in_CH n) (RD1_in_CH n) (by simp) (DM2_para.TH0_VAR_TH1 n)) ?_
  exact cspF_Int_choice_cong (Hide_IF _ _ _) (Hide_IF _ _ _)

abbrev TH0_VAR_TH1_HIDE_simp := TH0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules36` and `fold_Imp_rules36`
   are represented by `TH0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR Back1 HIDE ***) -/

theorem WR0_VAR_Back1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1
        (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n))
        (Pref Event.Back1 TH1P))) MF MF
        (Timeout
          (Pref Event.Back1
            (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)))
          (Hide (Par1 (Par0 TH0P (VARP (n / 2))) (Pref Event.Back1 TH1P)))) :=
  fun hE => hide_hid_vis (WR0_in_CH (n / 2)) Back1_notin_CH (by simp)
    (DM2_para.WR0_VAR_Back1 n hE)

abbrev WR0_VAR_Back1_HIDE_simp := WR0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules37` and `fold_Imp_rules37`
   are represented by `WR0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR WR1 HIDE ***) -/

theorem Back0_VAR_WR1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1
        (Par0 (Pref Event.Back0 TH0P) (VARP n))
        (Pref (Event.WR1 (3 * n + 1)) TH1P))) MF MF
        (Timeout
          (Pref Event.Back0
            (Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP (3 * n + 1))) TH1P))) :=
  fun hO => hide_hid_vis (WR1_in_CH (3 * n + 1)) Back0_notin_CH (by simp)
    (DM2_para.Back0_VAR_WR1 n hO)

abbrev Back0_VAR_WR1_HIDE_simp := Back0_VAR_WR1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules38` and `fold_Imp_rules38`
   are represented by `Back0_VAR_WR1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR TH1 HIDE ***) -/

theorem WR0_VAR_TH1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)) MF MF
        ((Hide (Par1 (Par0 TH0P (VARP (n / 2))) TH1P)) |~|
          (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n))
            (Pref Event.Back1 TH1P)))) :=
  fun hE => hide_hid_hid (WR0_in_CH (n / 2)) (RD1_in_CH n) (by simp)
    (DM2_para.WR0_VAR_TH1 n hE)

abbrev WR0_VAR_TH1_HIDE_simp := WR0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules39` and `fold_Imp_rules39`
   are represented by `WR0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR WR1 HIDE ***) -/

theorem TH0_VAR_WR1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))) MF MF
        ((Hide (Par1 (Par0 TH0P (VARP (3 * n + 1))) TH1P)) |~|
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n))
            (Pref (Event.WR1 (3 * n + 1)) TH1P)))) :=
  fun hO => hide_hid_hid (WR1_in_CH (3 * n + 1)) (RD0_in_CH n) (by simp)
    (DM2_para.TH0_VAR_WR1 n hO)

abbrev TH0_VAR_WR1_HIDE_simp := TH0_VAR_WR1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules` and `fold_Imp_rules` are
   represented by `TH0_VAR_WR1_HIDE_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

end DM3_hide
