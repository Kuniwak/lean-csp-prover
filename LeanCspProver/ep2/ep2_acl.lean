           /- -------------------------------------------*
            |                 (a part of) ep2            |
            |                  September 2004            |
            |                   December 2004 (modified) |
            |                   November 2005 (modified) |
            |                      April 2006 (modified) |
            |                      March 2007  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2009          |
            |                       June 2009  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2012          |
            |                   November 2012  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2016          |
            |                        May 2016  (modified)|
            |                                            |
            |  Markus Roggenbach (Univ of Wales Swansea, |
            |  UK)                                       |
            |  Yoshinao Isobe    (AIST, Japan)           |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

open fpmode

noncomputable section

namespace ep2_acl

local notation:50 P " <=F " Q => refF P MF MF Q

private noncomputable def decideMem {α : Type _} (x : α) (X : Set α) : Bool := by
  classical
  exact decide (x ∈ X)

/- *********************************************************
          automatic unfolding syntactic-sugar
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare csp_prefix_ss_def [simp]` has no direct Lean analogue
   here. -/

/- *********************************************************
              data type passed on channels
 ********************************************************* -/

/- Lean note:
   Isabelle's `typedecl` (an unspecified nonempty type) and its unspecified
   default elements were ported as `axiom`s. They are now `opaque`
   `NonemptyType`s — the same abstraction without extending the axiom
   base. -/

private opaque D_SI_Init_SessionStart_spec : NonemptyType.{0}
private opaque D_SI_Init_SessionEnd_spec : NonemptyType.{0}
private opaque D_SI_Init_ConfigDataRequest_spec : NonemptyType.{0}
private opaque D_SI_Init_ConfigDataResponse_spec : NonemptyType.{0}
private opaque D_SI_Init_ConfigDataNotification_spec : NonemptyType.{0}
private opaque D_SI_Init_ConfigDataAcknowledge_spec : NonemptyType.{0}
private opaque D_SI_Init_RemoveConfigDataNotification_spec : NonemptyType.{0}
private opaque D_SI_Init_RemoveConfigDataAcknowledge_spec : NonemptyType.{0}
private opaque D_SI_Init_ActivateConfigDataNotification_spec : NonemptyType.{0}
private opaque D_SI_Init_ActivateConfigDataAcknowledge_spec : NonemptyType.{0}

def D_SI_Init_SessionStart : Type := D_SI_Init_SessionStart_spec.type
def D_SI_Init_SessionEnd : Type := D_SI_Init_SessionEnd_spec.type
def D_SI_Init_ConfigDataRequest : Type := D_SI_Init_ConfigDataRequest_spec.type
def D_SI_Init_ConfigDataResponse : Type := D_SI_Init_ConfigDataResponse_spec.type
def D_SI_Init_ConfigDataNotification : Type := D_SI_Init_ConfigDataNotification_spec.type
def D_SI_Init_ConfigDataAcknowledge : Type := D_SI_Init_ConfigDataAcknowledge_spec.type
def D_SI_Init_RemoveConfigDataNotification : Type :=
  D_SI_Init_RemoveConfigDataNotification_spec.type
def D_SI_Init_RemoveConfigDataAcknowledge : Type := D_SI_Init_RemoveConfigDataAcknowledge_spec.type
def D_SI_Init_ActivateConfigDataNotification : Type :=
  D_SI_Init_ActivateConfigDataNotification_spec.type
def D_SI_Init_ActivateConfigDataAcknowledge : Type :=
  D_SI_Init_ActivateConfigDataAcknowledge_spec.type

noncomputable def default_D_SI_Init_SessionStart : D_SI_Init_SessionStart :=
  Classical.choice D_SI_Init_SessionStart_spec.property
noncomputable def default_D_SI_Init_SessionEnd : D_SI_Init_SessionEnd :=
  Classical.choice D_SI_Init_SessionEnd_spec.property
noncomputable def default_D_SI_Init_ConfigDataRequest : D_SI_Init_ConfigDataRequest :=
  Classical.choice D_SI_Init_ConfigDataRequest_spec.property
noncomputable def default_D_SI_Init_ConfigDataResponse : D_SI_Init_ConfigDataResponse :=
  Classical.choice D_SI_Init_ConfigDataResponse_spec.property
noncomputable def default_D_SI_Init_ConfigDataNotification : D_SI_Init_ConfigDataNotification :=
  Classical.choice D_SI_Init_ConfigDataNotification_spec.property
noncomputable def default_D_SI_Init_ConfigDataAcknowledge : D_SI_Init_ConfigDataAcknowledge :=
  Classical.choice D_SI_Init_ConfigDataAcknowledge_spec.property
noncomputable def default_D_SI_Init_RemoveConfigDataNotification :
    D_SI_Init_RemoveConfigDataNotification :=
  Classical.choice D_SI_Init_RemoveConfigDataNotification_spec.property
noncomputable def default_D_SI_Init_RemoveConfigDataAcknowledge :
    D_SI_Init_RemoveConfigDataAcknowledge :=
  Classical.choice D_SI_Init_RemoveConfigDataAcknowledge_spec.property
noncomputable def default_D_SI_Init_ActivateConfigDataNotification :
    D_SI_Init_ActivateConfigDataNotification :=
  Classical.choice D_SI_Init_ActivateConfigDataNotification_spec.property
noncomputable def default_D_SI_Init_ActivateConfigDataAcknowledge :
    D_SI_Init_ActivateConfigDataAcknowledge :=
  Classical.choice D_SI_Init_ActivateConfigDataAcknowledge_spec.property

instance : Inhabited D_SI_Init_SessionStart where
  default := default_D_SI_Init_SessionStart

instance : Inhabited D_SI_Init_SessionEnd where
  default := default_D_SI_Init_SessionEnd

instance : Inhabited D_SI_Init_ConfigDataRequest where
  default := default_D_SI_Init_ConfigDataRequest

instance : Inhabited D_SI_Init_ConfigDataResponse where
  default := default_D_SI_Init_ConfigDataResponse

instance : Inhabited D_SI_Init_ConfigDataNotification where
  default := default_D_SI_Init_ConfigDataNotification

instance : Inhabited D_SI_Init_ConfigDataAcknowledge where
  default := default_D_SI_Init_ConfigDataAcknowledge

instance : Inhabited D_SI_Init_RemoveConfigDataNotification where
  default := default_D_SI_Init_RemoveConfigDataNotification

instance : Inhabited D_SI_Init_RemoveConfigDataAcknowledge where
  default := default_D_SI_Init_RemoveConfigDataAcknowledge

instance : Inhabited D_SI_Init_ActivateConfigDataNotification where
  default := default_D_SI_Init_ActivateConfigDataNotification

instance : Inhabited D_SI_Init_ActivateConfigDataAcknowledge where
  default := default_D_SI_Init_ActivateConfigDataAcknowledge

noncomputable instance : DecidableEq D_SI_Init_SessionStart := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_SessionEnd := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_ConfigDataRequest := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_ConfigDataResponse := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_ConfigDataNotification := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_ConfigDataAcknowledge := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_RemoveConfigDataNotification := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_RemoveConfigDataAcknowledge := Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_ActivateConfigDataNotification :=
  Classical.decEq _
noncomputable instance : DecidableEq D_SI_Init_ActivateConfigDataAcknowledge :=
  Classical.decEq _

inductive D_SI_Init where
  | SStart : D_SI_Init_SessionStart → D_SI_Init
  | SEnd : D_SI_Init_SessionEnd → D_SI_Init
  | CDReq : D_SI_Init_ConfigDataRequest → D_SI_Init
  | CDRes : D_SI_Init_ConfigDataResponse → D_SI_Init
  | CDN : D_SI_Init_ConfigDataNotification → D_SI_Init
  | CDA : D_SI_Init_ConfigDataAcknowledge → D_SI_Init
  | RCDN : D_SI_Init_RemoveConfigDataNotification → D_SI_Init
  | RCDA : D_SI_Init_RemoveConfigDataAcknowledge → D_SI_Init
  | ACDN : D_SI_Init_ActivateConfigDataNotification → D_SI_Init
  | ACDA : D_SI_Init_ActivateConfigDataAcknowledge → D_SI_Init

instance : Inhabited D_SI_Init where
  default := D_SI_Init.SStart default

noncomputable instance : DecidableEq D_SI_Init := Classical.decEq _

/- Lean note:
   Isabelle's `typedecl` (an unspecified nonempty type) and its unspecified
   default elements were ported as `axiom`s. They are now `opaque`
   `NonemptyType`s — the same abstraction without extending the axiom
   base. -/

private opaque TerminalState_spec : NonemptyType.{0}
private opaque Trigger_spec : NonemptyType.{0}
private opaque Message_spec : NonemptyType.{0}

def TerminalState : Type := TerminalState_spec.type
def Trigger : Type := Trigger_spec.type
def Message : Type := Message_spec.type

noncomputable def default_TerminalState : TerminalState :=
  Classical.choice TerminalState_spec.property
noncomputable def default_Trigger : Trigger :=
  Classical.choice Trigger_spec.property
noncomputable def default_Message : Message :=
  Classical.choice Message_spec.property

instance : Inhabited TerminalState where
  default := default_TerminalState

instance : Inhabited Trigger where
  default := default_Trigger

instance : Inhabited Message where
  default := default_Message

noncomputable instance : DecidableEq TerminalState := Classical.decEq _
noncomputable instance : DecidableEq Trigger := Classical.decEq _
noncomputable instance : DecidableEq Message := Classical.decEq _

/- *********************************************************
                     event (channel)
 ********************************************************* -/

inductive Event where
  | C_SI_Init : D_SI_Init → Event
  | C_TerminalDisplay : Message → Event
  | PairTT : TerminalState × Trigger → Event

instance : Inhabited Event where
  default := Event.C_SI_Init default

noncomputable instance : DecidableEq Event := Classical.decEq _

/- *********************************************************
         abstract component description level
 ********************************************************* -/

inductive ACName where
  | TInit
  | TConfigurationManagement
  | AcquirerInit
  | ConfigurationManagement

instance : Inhabited ACName where
  default := ACName.TInit

noncomputable instance : DecidableEq ACName := Classical.decEq _

def ACfun : ACName → proc ACName Event
  | ACName.TInit =>
      Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.SStart) fun _ =>
        proc.Proc_name ACName.TConfigurationManagement
  | ACName.TConfigurationManagement =>
      Rec_prefix Event.C_SI_Init Set.univ fun x =>
        IF decideMem x (Set.range D_SI_Init.CDReq) THEN
          (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDRes) fun _ =>
            proc.Proc_name ACName.TConfigurationManagement)
        ELSE IF decideMem x (Set.range D_SI_Init.CDN) THEN
          (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDA) fun _ =>
            proc.Proc_name ACName.TConfigurationManagement)
        ELSE IF decideMem x (Set.range D_SI_Init.RCDN) THEN
          (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDA) fun _ =>
            proc.Proc_name ACName.TConfigurationManagement)
        ELSE IF decideMem x (Set.range D_SI_Init.ACDN) THEN
          (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDA) fun _ =>
            proc.Proc_name ACName.TConfigurationManagement)
        ELSE IF decideMem x (Set.range D_SI_Init.SEnd) THEN
          proc.SKIP
        ELSE
          proc.STOP
  | ACName.AcquirerInit =>
      Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.SStart) fun _ =>
        proc.Proc_name ACName.ConfigurationManagement
  | ACName.ConfigurationManagement =>
      (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.SEnd) fun _ =>
        proc.SKIP) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDReq) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.CDRes) fun _ =>
            proc.Proc_name ACName.ConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.CDA) fun _ =>
            proc.Proc_name ACName.ConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDA) fun _ =>
            proc.Proc_name ACName.ConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDA) fun _ =>
            proc.Proc_name ACName.ConfigurationManagement)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_ACfun : HasPNfun ACName Event where
  PNfun := ACfun

@[simp]
theorem Set_ACfun_def (pn : ACName) :
    PNfun pn = ACfun pn :=
  rfl

def AC : proc ACName Event :=
  (proc.Proc_name ACName.TInit) |[Set.range Event.C_SI_Init]| (proc.Proc_name ACName.AcquirerInit)

theorem AC_def :
    AC =
      (proc.Proc_name ACName.TInit) |[Set.range Event.C_SI_Init]|
        (proc.Proc_name ACName.AcquirerInit) :=
  rfl

/- *********************************************************
              gProc lemmas (routine work)
 ********************************************************* -/

@[simp] theorem guarded_AC :
    guardedfun ACfun := by
  intro pn
  cases pn <;>
    simp [ACfun, Rec_prefix, guarded, noHide]

/- *********************************************************
               abstract level (deadlock free)
 ********************************************************* -/

abbrev REQs : Set D_SI_Init :=
  (Set.range D_SI_Init.CDReq) ∪ (Set.range D_SI_Init.CDN) ∪
    (Set.range D_SI_Init.RCDN) ∪ (Set.range D_SI_Init.ACDN)

abbrev RESs : Set D_SI_Init :=
  (Set.range D_SI_Init.CDRes) ∪ (Set.range D_SI_Init.CDA) ∪
    (Set.range D_SI_Init.RCDA) ∪ (Set.range D_SI_Init.ACDA)

inductive AbsName where
  | Abstract
  | Loop

instance : Inhabited AbsName where
  default := AbsName.Abstract

noncomputable instance : DecidableEq AbsName := Classical.decEq _

def Absfun : AbsName → proc AbsName Event
  | AbsName.Abstract =>
      Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.SStart) fun _ =>
        proc.Proc_name AbsName.Loop
  | AbsName.Loop =>
      (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.SEnd) fun _ =>
        proc.SKIP) |~|
        (Nondet_send_prefix Event.C_SI_Init REQs fun _ =>
          Nondet_send_prefix Event.C_SI_Init RESs fun _ =>
            proc.Proc_name AbsName.Loop)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Absfun : HasPNfun AbsName Event where
  PNfun := Absfun

@[simp]
theorem Set_Absfun_def (pn : AbsName) :
    PNfun pn = Absfun pn :=
  rfl

def Abs : proc AbsName Event :=
  proc.Proc_name AbsName.Abstract

theorem Abs_def :
    Abs = proc.Proc_name AbsName.Abstract :=
  rfl

/- *********************************************************
               gProc lemmas (routine work)
 ********************************************************* -/

@[simp] theorem guarded_Abs :
    guardedfun Absfun := by
  intro pn
  cases pn <;>
    simp [Absfun, guarded, noHide]

/- *********************************************************
        relating function between AbsName and ACName
 ********************************************************* -/

def Abs_to_AC : AbsName → proc ACName Event
  | AbsName.Abstract =>
      (proc.Proc_name ACName.TInit) |[Set.range Event.C_SI_Init]|
        (proc.Proc_name ACName.AcquirerInit)
  | AbsName.Loop =>
      (proc.Proc_name ACName.TConfigurationManagement) |[Set.range Event.C_SI_Init]|
        (proc.Proc_name ACName.ConfigurationManagement)

/- *********************************************************
           a theorem for verifying Abs <=F AC
               (i.e. AC is deadlock-free)
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare inj_on_def [simp]` has no direct Lean analogue here. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

private theorem inj_C_SI_Init : Function.Injective Event.C_SI_Init := by
  intro a b h
  cases h
  rfl

private theorem unwAC (pn : ACName) :
    eqF (proc.Proc_name pn : proc ACName Event) MF MF (ACfun pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guarded_AC⟩))

private theorem range_ne {γ : Type _} [Inhabited γ] (f : γ → D_SI_Init) :
    Set.range f ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp ⟨f default, default, rfl⟩

/- ---------- evaluating the guard chain of `$TConfigurationManagement` ---------- -/

private theorem IF_chain_true {b : Bool} {P Q : proc ACName Event} (hb : b = true) :
    eqF (IF b THEN P ELSE Q) MF MF P := by
  rw [hb]
  exact cspF_IF_True

private theorem IF_chain_false {b : Bool} {P Q R : proc ACName Event} (hb : b = false)
    (h : eqF Q MF MF R) : eqF (IF b THEN P ELSE Q) MF MF R := by
  rw [hb]
  exact cspF_trans_left_eq cspF_IF_False h

/- ---------- the fixed-point induction ---------- -/

theorem ep2_abs :
    Abs <=F AC := by
  rw [Abs_def, AC_def]
  refine cspF_fp_induct_ref_left (Pf := Absfun) (f := Abs_to_AC)
    rfl (Or.inl rfl) guarded_Abs cspF_reflex_ref_P ?_
  intro pn
  cases pn with
  | Abstract =>
      refine cspF_rw_right_ref
        (cspF_Parallel_cong rfl (unwAC ACName.TInit) (unwAC ACName.AcquirerInit)) ?_
      simp only [Absfun, ACfun, Abs_to_AC, Subst_procfun_Nondet_send_prefix, Subst_procfun]
      refine cspF_rw_right_ref
        (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.C_SI_Init)
          (A := Set.range D_SI_Init.SStart) (B := Set.range D_SI_Init.SStart)
          (Pf := fun _ => proc.Proc_name ACName.TConfigurationManagement)
          (Qf := fun _ => proc.Proc_name ACName.ConfigurationManagement)
          (Set.image_subset_range _ _) (subset_refl _) (range_ne D_SI_Init.SStart)) ?_
      exact cspF_reflex_ref_P
  | Loop =>
      refine cspF_rw_right_ref
        (cspF_Parallel_cong rfl (unwAC ACName.TConfigurationManagement)
          (unwAC ACName.ConfigurationManagement)) ?_
      simp only [Absfun, ACfun, Abs_to_AC, Subst_procfun_Nondet_send_prefix, Subst_procfun]
      -- split the five alternatives offered by `$ConfigurationManagement`
      refine cspF_rw_right_ref cspF_Parallel_dist_r ?_
      refine cspF_Int_choice_right ?_ ?_
      · refine cspF_rw_right_ref cspF_Parallel_dist_r ?_
        refine cspF_Int_choice_right ?_ ?_
        · refine cspF_rw_right_ref cspF_Parallel_dist_r ?_
          refine cspF_Int_choice_right ?_ ?_
          · refine cspF_rw_right_ref cspF_Parallel_dist_r ?_
            refine cspF_Int_choice_right ?_ ?_
            · -- session end: both sides terminate
              refine cspF_Int_choice_left1 ?_
              refine cspF_rw_right_ref
                (cspF_Parallel_Rec_Nondet_send_prefix (f := Event.C_SI_Init)
                  (A := Set.univ) (B := Set.range D_SI_Init.SEnd)
                  (Set.image_subset_range _ _) (Set.subset_univ _)
                  (range_ne D_SI_Init.SEnd)) ?_
              refine cspF_Nondet_send_prefix_mono inj_C_SI_Init rfl rfl (fun x hx => ?_)
              obtain ⟨s, rfl⟩ := hx
              refine cspF_rw_right_ref
                (cspF_Parallel_cong rfl
                  (IF_chain_false (by simp [decideMem])
                    (IF_chain_false (by simp [decideMem])
                      (IF_chain_false (by simp [decideMem])
                        (IF_chain_false (by simp [decideMem])
                          (IF_chain_true (by simp [decideMem]))))))
                  cspF_reflex_eq_P) ?_
              exact cspF_rw_right_ref cspF_Parallel_term cspF_reflex_ref_P
            · -- configuration data request / response
              refine cspF_Int_choice_left2 ?_
              refine cspF_rw_right_ref
                (cspF_Parallel_Rec_Nondet_send_prefix (f := Event.C_SI_Init)
                  (A := Set.univ) (B := Set.range D_SI_Init.CDReq)
                  (Set.image_subset_range _ _) (Set.subset_univ _)
                  (range_ne D_SI_Init.CDReq)) ?_
              refine cspF_Nondet_send_prefix_subset inj_C_SI_Init
                (fun _ h => Or.inl (Or.inl (Or.inl h))) (fun x hx => ?_)
              obtain ⟨c, rfl⟩ := hx
              refine cspF_rw_right_ref
                (cspF_Parallel_cong rfl (IF_chain_true (by simp [decideMem]))
                  cspF_reflex_eq_P) ?_
              refine cspF_rw_right_ref
                (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.C_SI_Init)
                  (A := Set.range D_SI_Init.CDRes) (B := Set.range D_SI_Init.CDRes)
                  (Set.image_subset_range _ _) (subset_refl _)
                  (range_ne D_SI_Init.CDRes)) ?_
              exact cspF_Nondet_send_prefix_subset inj_C_SI_Init
                (fun _ h => Or.inl (Or.inl (Or.inl h))) (fun _ _ => cspF_reflex_ref_P)
          · -- configuration data notification / acknowledge
            refine cspF_Int_choice_left2 ?_
            refine cspF_rw_right_ref
              (cspF_Parallel_Rec_Nondet_send_prefix (f := Event.C_SI_Init)
                (A := Set.univ) (B := Set.range D_SI_Init.CDN)
                (Set.image_subset_range _ _) (Set.subset_univ _)
                (range_ne D_SI_Init.CDN)) ?_
            refine cspF_Nondet_send_prefix_subset inj_C_SI_Init
              (fun _ h => Or.inl (Or.inl (Or.inr h))) (fun x hx => ?_)
            obtain ⟨c, rfl⟩ := hx
            refine cspF_rw_right_ref
              (cspF_Parallel_cong rfl
                (IF_chain_false (by simp [decideMem]) (IF_chain_true (by simp [decideMem])))
                cspF_reflex_eq_P) ?_
            refine cspF_rw_right_ref
              (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.C_SI_Init)
                (A := Set.range D_SI_Init.CDA) (B := Set.range D_SI_Init.CDA)
                (Set.image_subset_range _ _) (subset_refl _)
                (range_ne D_SI_Init.CDA)) ?_
            exact cspF_Nondet_send_prefix_subset inj_C_SI_Init
              (fun _ h => Or.inl (Or.inl (Or.inr h))) (fun _ _ => cspF_reflex_ref_P)
        · -- remove configuration data
          refine cspF_Int_choice_left2 ?_
          refine cspF_rw_right_ref
            (cspF_Parallel_Rec_Nondet_send_prefix (f := Event.C_SI_Init)
              (A := Set.univ) (B := Set.range D_SI_Init.RCDN)
              (Set.image_subset_range _ _) (Set.subset_univ _)
              (range_ne D_SI_Init.RCDN)) ?_
          refine cspF_Nondet_send_prefix_subset inj_C_SI_Init
            (fun _ h => Or.inl (Or.inr h)) (fun x hx => ?_)
          obtain ⟨c, rfl⟩ := hx
          refine cspF_rw_right_ref
            (cspF_Parallel_cong rfl
              (IF_chain_false (by simp [decideMem])
                (IF_chain_false (by simp [decideMem])
                  (IF_chain_true (by simp [decideMem]))))
              cspF_reflex_eq_P) ?_
          refine cspF_rw_right_ref
            (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.C_SI_Init)
              (A := Set.range D_SI_Init.RCDA) (B := Set.range D_SI_Init.RCDA)
              (Set.image_subset_range _ _) (subset_refl _)
              (range_ne D_SI_Init.RCDA)) ?_
          exact cspF_Nondet_send_prefix_subset inj_C_SI_Init
            (fun _ h => Or.inl (Or.inr h)) (fun _ _ => cspF_reflex_ref_P)
      · -- activate configuration data
        refine cspF_Int_choice_left2 ?_
        refine cspF_rw_right_ref
          (cspF_Parallel_Rec_Nondet_send_prefix (f := Event.C_SI_Init)
            (A := Set.univ) (B := Set.range D_SI_Init.ACDN)
            (Set.image_subset_range _ _) (Set.subset_univ _)
            (range_ne D_SI_Init.ACDN)) ?_
        refine cspF_Nondet_send_prefix_subset inj_C_SI_Init
          (fun _ h => Or.inr h) (fun x hx => ?_)
        obtain ⟨c, rfl⟩ := hx
        refine cspF_rw_right_ref
          (cspF_Parallel_cong rfl
            (IF_chain_false (by simp [decideMem])
              (IF_chain_false (by simp [decideMem])
                (IF_chain_false (by simp [decideMem])
                  (IF_chain_true (by simp [decideMem])))))
            cspF_reflex_eq_P) ?_
        refine cspF_rw_right_ref
          (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.C_SI_Init)
            (A := Set.range D_SI_Init.ACDA) (B := Set.range D_SI_Init.ACDA)
            (Set.image_subset_range _ _) (subset_refl _)
            (range_ne D_SI_Init.ACDA)) ?_
        exact cspF_Nondet_send_prefix_subset inj_C_SI_Init
          (fun _ h => Or.inr h) (fun _ _ => cspF_reflex_ref_P)

end ep2_acl
