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

axiom D_SI_Init_SessionStart : Type
axiom D_SI_Init_SessionEnd : Type
axiom D_SI_Init_ConfigDataRequest : Type
axiom D_SI_Init_ConfigDataResponse : Type
axiom D_SI_Init_ConfigDataNotification : Type
axiom D_SI_Init_ConfigDataAcknowledge : Type
axiom D_SI_Init_RemoveConfigDataNotification : Type
axiom D_SI_Init_RemoveConfigDataAcknowledge : Type
axiom D_SI_Init_ActivateConfigDataNotification : Type
axiom D_SI_Init_ActivateConfigDataAcknowledge : Type

axiom default_D_SI_Init_SessionStart : D_SI_Init_SessionStart
axiom default_D_SI_Init_SessionEnd : D_SI_Init_SessionEnd
axiom default_D_SI_Init_ConfigDataRequest : D_SI_Init_ConfigDataRequest
axiom default_D_SI_Init_ConfigDataResponse : D_SI_Init_ConfigDataResponse
axiom default_D_SI_Init_ConfigDataNotification : D_SI_Init_ConfigDataNotification
axiom default_D_SI_Init_ConfigDataAcknowledge : D_SI_Init_ConfigDataAcknowledge
axiom default_D_SI_Init_RemoveConfigDataNotification : D_SI_Init_RemoveConfigDataNotification
axiom default_D_SI_Init_RemoveConfigDataAcknowledge : D_SI_Init_RemoveConfigDataAcknowledge
axiom default_D_SI_Init_ActivateConfigDataNotification :
  D_SI_Init_ActivateConfigDataNotification
axiom default_D_SI_Init_ActivateConfigDataAcknowledge :
  D_SI_Init_ActivateConfigDataAcknowledge

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

axiom TerminalState : Type
axiom Trigger : Type
axiom Message : Type

axiom default_TerminalState : TerminalState
axiom default_Trigger : Trigger
axiom default_Message : Message

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

@[simp] axiom guarded_AC :
    guardedfun ACfun

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

@[simp] axiom guarded_Abs :
    guardedfun Absfun

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

/- Lean note:
   The original Isabelle proof uses fixed-point induction across
   `AbsName` and `ACName`. The current Lean port keeps this heterogeneous
   fixed-point argument as an axiom for now. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

axiom ep2_abs :
    Abs <=F AC

end ep2_acl
