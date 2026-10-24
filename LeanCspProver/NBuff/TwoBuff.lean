           /- -------------------------------------------*
            |                2 Buffers                  |
            |                                           |
            |                June 2009                  |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

open fpmode

noncomputable section

namespace TwoBuff

local infix:50 " =F " => eqFfix

/- =============================================================*
 |                                                             |
 |                           Process                           |
 |                                                             |
 *============================================================= -/

/- *********************************************************
               process names and events
 ********************************************************* -/

inductive Event where
  | inC
  | outC
  | midC
deriving DecidableEq, Inhabited

inductive PN where
  | Buff1
  | Buff1'
  | Buff2
  | Buff2'
  | Buff2''
deriving DecidableEq, Inhabited

/- *********************************************************
                  Recursivey Process
 ********************************************************* -/

def PNdef : PN → proc PN Event
  | PN.Buff1 =>
      Event.inC ~> proc.Proc_name PN.Buff1'
  | PN.Buff1' =>
      Event.outC ~> proc.Proc_name PN.Buff1
  | PN.Buff2 =>
      Event.inC ~> proc.Proc_name PN.Buff2'
  | PN.Buff2' =>
      (Event.inC ~> proc.Proc_name PN.Buff2'') [+]
        (Event.outC ~> proc.Proc_name PN.Buff2)
  | PN.Buff2'' =>
      Event.outC ~> proc.Proc_name PN.Buff2'

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_PNdef : HasPNfun PN Event where
  PNfun := PNdef

@[simp]
theorem Set_PNdef_def (pn : PN) :
    PNfun pn = PNdef pn :=
  rfl

/- ------------------ *
      guardedness
 * ------------------ -/

@[simp] theorem guardedfun_PN :
    guardedfun PNdef := by
  intro pn
  cases pn <;> simp [PNdef, guarded, noHide]

/- Lean note:
   Isabelle's overloaded constant `FPmode` is represented by a typeclass
   instance. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

/- *********************************************************
                     Composition
 ********************************************************* -/

abbrev Link (P Q : proc PN Event) : proc PN Event :=
  proc.Hiding
    ((P[[Event.outC <--> Event.midC]]) |[({Event.midC} : Set Event)]|
      (Q[[Event.inC <--> Event.midC]]))
    ({Event.midC} : Set Event)

infixr:76 " <---> " => Link

abbrev LinkBuff2 : proc PN Event :=
  proc.Proc_name PN.Buff1 <---> proc.Proc_name PN.Buff1

/- *********************************************************
                  for automatising
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare simp_event_set [simp]` has no direct Lean analogue. -/

theorem Link_cong {P Q R : proc PN Event} :
    Q =F R -> P <---> Q =F P <---> R := by
  intro hQR
  unfold Link
  apply cspF_Hiding_cong rfl
  apply cspF_Parallel_cong rfl
  · exact cspF_Renaming_cong rfl cspF_reflex_eq_P
  · exact cspF_Renaming_cong rfl hQR

/- *********************************************************
                    verification
 ********************************************************* -/

def Buff2_to_LinkBuff2 : PN → proc PN Event
  | PN.Buff1 => proc.Proc_name PN.Buff1
  | PN.Buff1' => proc.Proc_name PN.Buff1'
  | PN.Buff2 => LinkBuff2
  | PN.Buff2' => proc.Proc_name PN.Buff1' <---> proc.Proc_name PN.Buff1
  | PN.Buff2'' => proc.Proc_name PN.Buff1' <---> proc.Proc_name PN.Buff1'

/- Lean note:
   The Isabelle proof is `cspF_fp_induct_left` + `cspF_auto`; here the hnf
   expansions of the linked buffers (hLinkE1/E2/E3 below) are hand-written
   with the Renaming/Parallel/Hiding step laws, following the recipe of
   `Spc_to_Imp_step` in Test_infinite. -/

private abbrev B1 : proc PN Event := proc.Proc_name PN.Buff1

private abbrev B1' : proc PN Event := proc.Proc_name PN.Buff1'

private abbrev rL : Set (Event × Event) := Event.outC <--> Event.midC

private abbrev rR : Set (Event × Event) := Event.inC <--> Event.midC

/- evaluation of the two renaming functions -/

private theorem renL_inC :
    Renaming1_event_fun Event.outC Event.midC Event.inC = Event.inC := by
  simp [Renaming1_event_fun]

private theorem renL_outC :
    Renaming1_event_fun Event.outC Event.midC Event.outC = Event.midC := by
  simp [Renaming1_event_fun]

private theorem renR_inC :
    Renaming1_event_fun Event.inC Event.midC Event.inC = Event.midC := by
  simp [Renaming1_event_fun]

private theorem renR_outC :
    Renaming1_event_fun Event.inC Event.midC Event.outC = Event.outC := by
  simp [Renaming1_event_fun]

/- a functional renaming maps a single prefix to a single prefix -/

private theorem Renaming_prefix {f : Event → Event} (c : Event) (P : proc PN Event) :
    eqF ((c ~> P)[[fun_to_rel f]]) MF MF ((f c) ~> (P[[fun_to_rel f]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Act_prefix_step) ?_
  refine cspF_trans_left_eq cspF_Renaming_step ?_
  have hidx : {y | ∃ x, x ∈ ({c} : Set Event) ∧ (x, y) ∈ fun_to_rel f} =
      ({f c} : Set Event) := by
    ext y
    constructor
    · rintro ⟨x, hx, hxy⟩
      have hxc : x = c := hx
      subst hxc
      exact hxy
    · intro hy
      exact ⟨c, rfl, hy⟩
  rw [hidx]
  refine cspF_trans_left_eq
    (cspF_Ext_pre_choice_cong rfl (fun y hy => ?_)) (cspF_sym cspF_Act_prefix_step)
  have hyc : y = f c := hy
  subst hyc
  have hset : {x | x ∈ ({c} : Set Event) ∧ (x, f c) ∈ fun_to_rel f} =
      ({c} : Set Event) := by
    ext x
    constructor
    · rintro ⟨hx, -⟩
      exact hx
    · intro hx
      have hxc : x = c := hx
      subst hxc
      exact ⟨rfl, rfl⟩
  rw [hset]
  exact cspF_Rep_int_choice_com_unit (by simp)

/- the four unwound-and-renamed buffers -/

private theorem hB1L :
    (B1[[rL]]) =F (Event.inC ~> (B1'[[rL]])) := by
  have h1 : (B1[[rL]]) =F ((Event.inC ~> B1')[[rL]]) :=
    cspF_Renaming_cong rfl («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩)))
  have h2 := Renaming_prefix (f := Renaming1_event_fun Event.outC Event.midC) Event.inC B1'
  rw [renL_inC] at h2
  exact cspF_trans_left_eq h1 h2

private theorem hB1'L :
    (B1'[[rL]]) =F (Event.midC ~> (B1[[rL]])) := by
  have h1 : (B1'[[rL]]) =F ((Event.outC ~> B1)[[rL]]) :=
    cspF_Renaming_cong rfl («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩)))
  have h2 := Renaming_prefix (f := Renaming1_event_fun Event.outC Event.midC) Event.outC B1
  rw [renL_outC] at h2
  exact cspF_trans_left_eq h1 h2

private theorem hB1R :
    (B1[[rR]]) =F (Event.midC ~> (B1'[[rR]])) := by
  have h1 : (B1[[rR]]) =F ((Event.inC ~> B1')[[rR]]) :=
    cspF_Renaming_cong rfl («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩)))
  have h2 := Renaming_prefix (f := Renaming1_event_fun Event.inC Event.midC) Event.inC B1'
  rw [renR_inC] at h2
  exact cspF_trans_left_eq h1 h2

private theorem hB1'R :
    (B1'[[rR]]) =F (Event.outC ~> (B1[[rR]])) := by
  have h1 : (B1'[[rR]]) =F ((Event.outC ~> B1)[[rR]]) :=
    cspF_Renaming_cong rfl («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩)))
  have h2 := Renaming_prefix (f := Renaming1_event_fun Event.inC Event.midC) Event.outC B1
  rw [renR_outC] at h2
  exact cspF_trans_left_eq h1 h2

/- index-set computations for the Parallel/Hiding steps -/

private theorem setE1 :
    ((({Event.midC} : Set Event) ∩ {Event.inC} ∩ {Event.midC}) ∪
        (({Event.inC} : Set Event) \ {Event.midC}) ∪
        (({Event.midC} : Set Event) \ {Event.midC})) = ({Event.inC} : Set Event) := by
  ext e
  cases e <;> simp

private theorem setE2a :
    ((({Event.midC} : Set Event) ∩ {Event.midC} ∩ {Event.midC}) ∪
        (({Event.midC} : Set Event) \ {Event.midC}) ∪
        (({Event.midC} : Set Event) \ {Event.midC})) = ({Event.midC} : Set Event) := by
  ext e
  cases e <;> simp

private theorem setE2b :
    ((({Event.midC} : Set Event) ∩ {Event.inC} ∩ {Event.outC}) ∪
        (({Event.inC} : Set Event) \ {Event.midC}) ∪
        (({Event.outC} : Set Event) \ {Event.midC})) =
      (({Event.inC} : Set Event) ∪ {Event.outC}) := by
  ext e
  cases e <;> simp

private theorem setE3 :
    ((({Event.midC} : Set Event) ∩ {Event.midC} ∩ {Event.outC}) ∪
        (({Event.midC} : Set Event) \ {Event.midC}) ∪
        (({Event.outC} : Set Event) \ {Event.midC})) = ({Event.outC} : Set Event) := by
  ext e
  cases e <;> simp

private theorem set_in_mid :
    (({Event.inC} : Set Event) ∩ {Event.midC}) = ∅ := by
  ext e
  cases e <;> simp

private theorem set_inout_mid :
    ((({Event.inC} : Set Event) ∪ {Event.outC}) ∩ {Event.midC}) = ∅ := by
  ext e
  cases e <;> simp

private theorem set_out_mid :
    (({Event.outC} : Set Event) ∩ {Event.midC}) = ∅ := by
  ext e
  cases e <;> simp

private theorem set_mid_mid_ne :
    ¬ ((({Event.midC} : Set Event) ∩ {Event.midC}) = ∅) := by
  intro h
  have hm : Event.midC ∈ ({Event.midC} : Set Event) ∩ {Event.midC} := ⟨rfl, rfl⟩
  rw [h] at hm
  exact hm

private theorem set_mid_diff :
    (({Event.midC} : Set Event) \ {Event.midC}) = ∅ := by
  ext e
  cases e <;> simp

private theorem set_mid_inter :
    (({Event.midC} : Set Event) ∩ {Event.midC}) = ({Event.midC} : Set Event) := by
  ext e
  cases e <;> simp

/- E1: $Buff1 <---> $Buff1  =F  inC -> ($Buff1' <---> $Buff1) -/

private theorem hLinkE1 :
    (B1 <---> B1) =F (Event.inC ~> (B1' <---> B1)) := by
  have hL' : (B1[[rL]]) =F
      proc.Ext_pre_choice ({Event.inC} : Set Event) (fun _ => B1'[[rL]]) :=
    cspF_trans_left_eq hB1L cspF_Act_prefix_step
  have hR' : (B1[[rR]]) =F
      proc.Ext_pre_choice ({Event.midC} : Set Event) (fun _ => B1'[[rR]]) :=
    cspF_trans_left_eq hB1R cspF_Act_prefix_step
  have hstep := cspF_Parallel_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.inC} : Set Event))
    (Z := ({Event.midC} : Set Event))
    (Pf := fun _ => B1'[[rL]]) (Qf := fun _ => B1'[[rR]])
    (M := (MF : PN → domFType Event))
  rw [setE1] at hstep
  have hPar : ((B1[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]])) =F
      proc.Ext_pre_choice ({Event.inC} : Set Event)
        (fun _ => (B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]])) := by
    refine cspF_trans_left_eq (cspF_Parallel_cong rfl hL' hR') ?_
    refine cspF_trans_left_eq hstep ?_
    refine cspF_Ext_pre_choice_cong rfl (fun a ha => ?_)
    have hac : a = Event.inC := ha
    subst hac
    rw [procIte_neg (by simp), procIte_neg (by simp),
      procIte_pos (show Event.inC ∈ ({Event.inC} : Set Event) from rfl)]
    exact cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hR')
  have hHide := cspF_Hiding_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.inC} : Set Event))
    (Pf := fun _ => (B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]]))
    (M := (MF : PN → domFType Event))
  rw [procIte_pos set_in_mid] at hHide
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl hPar) ?_
  refine cspF_trans_left_eq hHide ?_
  exact cspF_sym cspF_Act_prefix_step

/- E2a: $Buff1' <---> $Buff1  =F  $Buff1 <---> $Buff1'  (hidden midC transfer) -/

private theorem hLinkE2a :
    (B1' <---> B1) =F (B1 <---> B1') := by
  have hL' : (B1'[[rL]]) =F
      proc.Ext_pre_choice ({Event.midC} : Set Event) (fun _ => B1[[rL]]) :=
    cspF_trans_left_eq hB1'L cspF_Act_prefix_step
  have hR' : (B1[[rR]]) =F
      proc.Ext_pre_choice ({Event.midC} : Set Event) (fun _ => B1'[[rR]]) :=
    cspF_trans_left_eq hB1R cspF_Act_prefix_step
  have hstep := cspF_Parallel_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.midC} : Set Event))
    (Z := ({Event.midC} : Set Event))
    (Pf := fun _ => B1[[rL]]) (Qf := fun _ => B1'[[rR]])
    (M := (MF : PN → domFType Event))
  rw [setE2a] at hstep
  have hPar : ((B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]])) =F
      proc.Ext_pre_choice ({Event.midC} : Set Event)
        (fun _ => (B1[[rL]]) |[({Event.midC} : Set Event)]| (B1'[[rR]])) := by
    refine cspF_trans_left_eq (cspF_Parallel_cong rfl hL' hR') ?_
    refine cspF_trans_left_eq hstep ?_
    refine cspF_Ext_pre_choice_cong rfl (fun a ha => ?_)
    have hac : a = Event.midC := ha
    subst hac
    rw [procIte_pos (show Event.midC ∈ ({Event.midC} : Set Event) from rfl)]
    exact cspF_reflex_eq_P
  have hHide := cspF_Hiding_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.midC} : Set Event))
    (Pf := fun _ => (B1[[rL]]) |[({Event.midC} : Set Event)]| (B1'[[rR]]))
    (M := (MF : PN → domFType Event))
  rw [procIte_neg set_mid_mid_ne, set_mid_diff, set_mid_inter] at hHide
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl hPar) ?_
  refine cspF_trans_left_eq hHide ?_
  refine cspF_trans_left_eq
    (cspF_Timeout_cong (cspF_sym cspF_STOP_step)
      (cspF_Rep_int_choice_com_unit (by simp))) ?_
  exact cspF_STOP_Timeout

/- E2b: $Buff1 <---> $Buff1'  =F
        (inC -> ($Buff1' <---> $Buff1')) [+] (outC -> ($Buff1 <---> $Buff1)) -/

private theorem hLinkE2b :
    (B1 <---> B1') =F
      ((Event.inC ~> (B1' <---> B1')) [+] (Event.outC ~> (B1 <---> B1))) := by
  have hL' : (B1[[rL]]) =F
      proc.Ext_pre_choice ({Event.inC} : Set Event) (fun _ => B1'[[rL]]) :=
    cspF_trans_left_eq hB1L cspF_Act_prefix_step
  have hR' : (B1'[[rR]]) =F
      proc.Ext_pre_choice ({Event.outC} : Set Event) (fun _ => B1[[rR]]) :=
    cspF_trans_left_eq hB1'R cspF_Act_prefix_step
  have hstep := cspF_Parallel_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.inC} : Set Event))
    (Z := ({Event.outC} : Set Event))
    (Pf := fun _ => B1'[[rL]]) (Qf := fun _ => B1[[rR]])
    (M := (MF : PN → domFType Event))
  rw [setE2b] at hstep
  -- the target external choice, in prefix-choice normal form
  have hT : ((Event.inC ~> (B1' <---> B1')) [+] (Event.outC ~> (B1 <---> B1))) =F
      proc.Ext_pre_choice (({Event.inC} : Set Event) ∪ {Event.outC}) (fun x =>
        procIte (x ∈ ({Event.inC} : Set Event) ∧ x ∈ ({Event.outC} : Set Event))
          ((B1' <---> B1') |~| (B1 <---> B1))
          (procIte (x ∈ ({Event.inC} : Set Event))
            (B1' <---> B1') (B1 <---> B1))) := by
    refine cspF_trans_left_eq
      (cspF_Ext_choice_cong cspF_Act_prefix_step cspF_Act_prefix_step) ?_
    exact cspF_Ext_choice_step
  have hHide := cspF_Hiding_step
    (X := ({Event.midC} : Set Event))
    (Y := (({Event.inC} : Set Event) ∪ {Event.outC}))
    (Pf := fun x =>
      procIte (x ∈ ({Event.midC} : Set Event))
        ((B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]]))
        (procIte (x ∈ ({Event.inC} : Set Event) ∧ x ∈ ({Event.outC} : Set Event))
          (((B1'[[rL]]) |[({Event.midC} : Set Event)]|
              proc.Ext_pre_choice ({Event.outC} : Set Event) (fun _ => B1[[rR]])) |~|
            ((proc.Ext_pre_choice ({Event.inC} : Set Event) (fun _ => B1'[[rL]]))
              |[({Event.midC} : Set Event)]| (B1[[rR]])))
          (procIte (x ∈ ({Event.inC} : Set Event))
            ((B1'[[rL]]) |[({Event.midC} : Set Event)]|
              proc.Ext_pre_choice ({Event.outC} : Set Event) (fun _ => B1[[rR]]))
            ((proc.Ext_pre_choice ({Event.inC} : Set Event) (fun _ => B1'[[rL]]))
              |[({Event.midC} : Set Event)]| (B1[[rR]])))))
    (M := (MF : PN → domFType Event))
  rw [procIte_pos set_inout_mid] at hHide
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_trans_left_eq (cspF_Parallel_cong rfl hL' hR') hstep)) ?_
  refine cspF_trans_left_eq hHide ?_
  refine cspF_trans_right_eq (cspF_sym hT) ?_
  refine cspF_Ext_pre_choice_cong rfl (fun a ha => ?_)
  rcases ha with ha | ha
  · have hac : a = Event.inC := ha
    subst hac
    simp only [
      procIte_neg (show ¬(Event.inC ∈ ({Event.midC} : Set Event)) by simp),
      procIte_neg (show ¬(Event.inC ∈ ({Event.inC} : Set Event) ∧
        Event.inC ∈ ({Event.outC} : Set Event)) by simp),
      procIte_pos (show Event.inC ∈ ({Event.inC} : Set Event) from rfl)]
    exact cspF_Hiding_cong rfl
      (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hR'))
  · have hac : a = Event.outC := ha
    subst hac
    simp only [
      procIte_neg (show ¬(Event.outC ∈ ({Event.midC} : Set Event)) by simp),
      procIte_neg (show ¬(Event.outC ∈ ({Event.inC} : Set Event) ∧
        Event.outC ∈ ({Event.outC} : Set Event)) by simp),
      procIte_neg (show ¬(Event.outC ∈ ({Event.inC} : Set Event)) by simp)]
    exact cspF_Hiding_cong rfl
      (cspF_Parallel_cong rfl (cspF_sym hL') cspF_reflex_eq_P)

private theorem hLinkE2 :
    (B1' <---> B1) =F
      ((Event.inC ~> (B1' <---> B1')) [+] (Event.outC ~> (B1 <---> B1))) :=
  cspF_trans_left_eq hLinkE2a hLinkE2b

/- E3: $Buff1' <---> $Buff1'  =F  outC -> ($Buff1' <---> $Buff1) -/

private theorem hLinkE3 :
    (B1' <---> B1') =F (Event.outC ~> (B1' <---> B1)) := by
  have hL' : (B1'[[rL]]) =F
      proc.Ext_pre_choice ({Event.midC} : Set Event) (fun _ => B1[[rL]]) :=
    cspF_trans_left_eq hB1'L cspF_Act_prefix_step
  have hR' : (B1'[[rR]]) =F
      proc.Ext_pre_choice ({Event.outC} : Set Event) (fun _ => B1[[rR]]) :=
    cspF_trans_left_eq hB1'R cspF_Act_prefix_step
  have hstep := cspF_Parallel_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.midC} : Set Event))
    (Z := ({Event.outC} : Set Event))
    (Pf := fun _ => B1[[rL]]) (Qf := fun _ => B1[[rR]])
    (M := (MF : PN → domFType Event))
  rw [setE3] at hstep
  have hPar : ((B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1'[[rR]])) =F
      proc.Ext_pre_choice ({Event.outC} : Set Event)
        (fun _ => (B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]])) := by
    refine cspF_trans_left_eq (cspF_Parallel_cong rfl hL' hR') ?_
    refine cspF_trans_left_eq hstep ?_
    refine cspF_Ext_pre_choice_cong rfl (fun a ha => ?_)
    have hac : a = Event.outC := ha
    subst hac
    rw [procIte_neg (by simp), procIte_neg (by simp), procIte_neg (by simp)]
    exact cspF_Parallel_cong rfl (cspF_sym hL') cspF_reflex_eq_P
  have hHide := cspF_Hiding_step
    (X := ({Event.midC} : Set Event)) (Y := ({Event.outC} : Set Event))
    (Pf := fun _ => (B1'[[rL]]) |[({Event.midC} : Set Event)]| (B1[[rR]]))
    (M := (MF : PN → domFType Event))
  rw [procIte_pos set_out_mid] at hHide
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl hPar) ?_
  refine cspF_trans_left_eq hHide ?_
  exact cspF_sym cspF_Act_prefix_step

theorem Buff2_eq_LinkBuff2 :
    (proc.Proc_name PN.Buff2 : proc PN Event) =F LinkBuff2 := by
  refine cspF_fp_induct_eq_left (Pf := PNdef) (f := Buff2_to_LinkBuff2)
    rfl (Or.inl rfl) guardedfun_PN cspF_reflex_eq_P (fun pn => ?_)
  cases pn with
  | Buff1 =>
      exact cspF_sym («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩)))
  | Buff1' =>
      exact cspF_sym («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩)))
  | Buff2 =>
      exact cspF_sym hLinkE1
  | Buff2' =>
      exact cspF_sym hLinkE2
  | Buff2'' =>
      exact cspF_sym hLinkE3

end TwoBuff
