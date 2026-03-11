           /- -------------------------------------------*
            |                 (a part of) ep2            |
            |                  September 2004            |
            |                   December 2004 (modified) |
            |                   November 2005 (modified) |
            |                      April 2006 (modified) |
            |                      March 2007 (modified) |
            |                                            |
            |        CSP-Prover on Isabelle2009          |
            |                       June 2009  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2016          |
            |                        May 2016  (modified)|
            |                                            |
            |  Markus Roggenbach (Univ of Wales Swansea, |
            |  UK)                                       |
            |  Yoshinao Isobe    (AIST, Japan)           |
            *------------------------------------------- -/

import LeanCspProver.ep2.ep2_acl

open fpmode
open ep2_acl

noncomputable section

namespace ep2_ccl

local notation:50 P " <=F " Q => refF P MF MF Q

private noncomputable def decideMem {α : Type _} (x : α) (X : Set α) : Bool := by
  classical
  exact decide (x ∈ X)

/- *********************************************************
                    functions
 ********************************************************* -/

/- pair -/
def state : TerminalState × Trigger → TerminalState
  | (s, _) => s

theorem state_def (p : TerminalState × Trigger) :
    state p = Prod.fst p := by
  cases p
  rfl

def trigger : TerminalState × Trigger → Trigger
  | (_, t) => t

theorem trigger_def (p : TerminalState × Trigger) :
    trigger p = Prod.snd p := by
  cases p
  rfl

/- Session start -/
axiom sessionStart : Trigger → D_SI_Init_SessionStart

/- ConfigDataRequest -/
axiom configDataResponse :
  D_SI_Init_ConfigDataRequest × TerminalState →
    D_SI_Init_ConfigDataResponse

/- ConfigDataNotification -/
axiom configDataAcknowledge : D_SI_Init_ConfigDataAcknowledge
axiom configData :
  D_SI_Init_ConfigDataNotification × TerminalState →
    TerminalState

/- ConfigDataRemove -/
axiom removeDataAcknowledge : D_SI_Init_RemoveConfigDataAcknowledge
axiom removeData :
  D_SI_Init_RemoveConfigDataNotification × TerminalState →
    TerminalState

/- ActivateConfigDataNotification -/
axiom activateDataAcknowledge : D_SI_Init_ActivateConfigDataAcknowledge
axiom activateData :
  D_SI_Init_ActivateConfigDataNotification × TerminalState →
    TerminalState

/- Message -/
axiom AcqConnectionFailed : Message
axiom InitialisationFinished : Message
axiom InitialisationFailed : Message

/- *********************************************************
         concrete component description level
 ********************************************************* -/

inductive CCName where
  | CTInit : TerminalState × Trigger → CCName
  | CTConfigurationManagement : TerminalState × Trigger → CCName
  | CAcquirerInit
  | CConfigurationManagement

instance : Inhabited CCName where
  default := CCName.CTInit default

noncomputable instance : DecidableEq CCName := Classical.decEq _

def CCfun : CCName → proc CCName Event
  | CCName.CTInit p =>
      Event.C_SI_Init (D_SI_Init.SStart (sessionStart (trigger p))) ~>
        proc.Proc_name (CCName.CTConfigurationManagement p)
  | CCName.CTConfigurationManagement p =>
      Rec_prefix Event.C_SI_Init Set.univ fun x =>
        IF decideMem x (Set.range D_SI_Init.CDReq) THEN
          (Event.C_SI_Init
              (D_SI_Init.CDRes
                (configDataResponse (Function.invFun D_SI_Init.CDReq x, state p))) ~>
            proc.Proc_name (CCName.CTConfigurationManagement p))
        ELSE IF decideMem x (Set.range D_SI_Init.CDN) THEN
          (Event.C_SI_Init (D_SI_Init.CDA configDataAcknowledge) ~>
            proc.Proc_name
              (CCName.CTConfigurationManagement
                (configData (Function.invFun D_SI_Init.CDN x, state p), trigger p)))
        ELSE IF decideMem x (Set.range D_SI_Init.RCDN) THEN
          (Event.C_SI_Init (D_SI_Init.RCDA removeDataAcknowledge) ~>
            proc.Proc_name
              (CCName.CTConfigurationManagement
                (removeData (Function.invFun D_SI_Init.RCDN x, state p), trigger p)))
        ELSE IF decideMem x (Set.range D_SI_Init.ACDN) THEN
          (Event.C_SI_Init (D_SI_Init.ACDA activateDataAcknowledge) ~>
            proc.Proc_name
              (CCName.CTConfigurationManagement
                (activateData (Function.invFun D_SI_Init.ACDN x, state p), trigger p)))
        ELSE IF decideMem x (Set.range D_SI_Init.SEnd) THEN
          (Event.C_TerminalDisplay InitialisationFinished ~> proc.SKIP)
        ELSE
          proc.STOP
  | CCName.CAcquirerInit =>
      Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.SStart) fun _ =>
        proc.Proc_name CCName.CConfigurationManagement
  | CCName.CConfigurationManagement =>
      (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.SEnd) fun _ =>
        proc.SKIP) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDReq) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.CDRes) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.CDA) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDA) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDA) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement)

instance Set_CCfun : HasPNfun CCName Event where
  PNfun := CCfun

@[simp]
theorem Set_CCfun_def (pn : CCName) :
    PNfun pn = CCfun pn :=
  rfl

def CC : (TerminalState × Trigger) → proc CCName Event :=
  fun p =>
    (proc.Hiding
      (proc.Proc_name (CCName.CTInit p))
      (Set.range Event.C_TerminalDisplay)) |[Set.range Event.C_SI_Init]|
      (proc.Proc_name CCName.CAcquirerInit)

theorem CC_def (p : TerminalState × Trigger) :
    CC p =
      (proc.Hiding
        (proc.Proc_name (CCName.CTInit p))
        (Set.range Event.C_TerminalDisplay)) |[Set.range Event.C_SI_Init]|
        (proc.Proc_name CCName.CAcquirerInit) :=
  rfl

/- *********************************************************
                gProc lemmas (routine work)
 ********************************************************* -/

@[simp] axiom guarded_CC :
    guardedfun CCfun

/- *********************************************************
        relating function between AbsName and ACName
 ********************************************************* -/

def AC_to_CC : ACName → proc CCName Event
  | ACName.TInit =>
      Nondet_send_prefix Event.PairTT Set.univ fun p =>
        proc.Hiding
          (proc.Proc_name (CCName.CTInit p))
          (Set.range Event.C_TerminalDisplay)
  | ACName.TConfigurationManagement =>
      Nondet_send_prefix Event.PairTT Set.univ fun p =>
        proc.Hiding
          (proc.Proc_name (CCName.CTConfigurationManagement p))
          (Set.range Event.C_TerminalDisplay)
  | ACName.AcquirerInit =>
      proc.Proc_name CCName.CAcquirerInit
  | ACName.ConfigurationManagement =>
      proc.Proc_name CCName.CConfigurationManagement

/- *********************************************************
           a theorem for verifying !!p. AC <=F CC p
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare inj_on_def [simp]` has no direct Lean analogue here. -/

axiom ep2_ccl_terminal_step1 :
    (ACfun ACName.TInit) << AC_to_CC <=F AC_to_CC ACName.TInit

axiom ep2_ccl_terminal_step2 :
    (ACfun ACName.TConfigurationManagement) << AC_to_CC <=F
      AC_to_CC ACName.TConfigurationManagement

axiom ACDef_AC_to_CC (p : ACName) :
    (ACfun p) << AC_to_CC <=F AC_to_CC p

/- ****************************
      !!p. AC p <=F CC p
 **************************** -/

axiom ep2_acl_ccl :
    ∀ p, AC <=F CC p

/- ****************************
      !!p. Abs <=F CC p
 **************************** -/

theorem ep2_abs_ccl :
    ∀ p, Abs <=F CC p := by
  intro p
  exact cspF_trans_left_ref ep2_abs (ep2_acl_ccl p)

/- Lean note:
   Isabelle's `declare inj_on_def [simp del]` has no direct Lean analogue
   here. -/

end ep2_ccl
