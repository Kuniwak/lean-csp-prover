           /- -------------------------------------------*
            |                 (a part of) ep2            |
            |                  September 2004            |
            |                   December 2004 (modified) |
            |                   November 2005 (modified) |
            |                      April 2006 (modified) |
            |                      March 2007  (modified)|
            |                     August 2007  (modified)|
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

import LeanCspProver.DFP
import LeanCspProver.ep2.ep2_nucleus

open fpmode

noncomputable section

namespace ep2_nucleusDF

local notation:50 P " <=F " Q => refF P MF MF Q

abbrev NEvent := ep2_nucleus.Event
abbrev NACName := ep2_nucleus.ACName

/- *********************************************************
                     abstract level
 ********************************************************* -/

inductive AbsName where
  | Abstract
  | Loop

instance : Inhabited AbsName where
  default := AbsName.Abstract

noncomputable instance : DecidableEq AbsName := Classical.decEq _

def Absfun : AbsName → proc AbsName NEvent
  | AbsName.Abstract =>
      Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ =>
        proc.Proc_name AbsName.Loop
  | AbsName.Loop =>
      proc.SKIP |~|
        (Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ =>
          proc.Proc_name AbsName.Loop)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Absfun : HasPNfun AbsName NEvent where
  PNfun := Absfun

@[simp]
theorem Set_Absfun_def (pn : AbsName) :
    PNfun pn = Absfun pn :=
  rfl

def Abs : proc AbsName NEvent :=
  proc.Proc_name AbsName.Abstract

theorem Abs_def :
    Abs = proc.Proc_name AbsName.Abstract :=
  rfl

/- *********************************************************
               guard lemmas (routine work)
 ********************************************************* -/

@[simp]
axiom guardedfun_Abs :
    guardedfun Absfun

/- *********************************************************
        relating function between ACName and AbsName
 ********************************************************* -/

def Abs_to_AC : AbsName → proc NACName NEvent
  | AbsName.Abstract =>
      (proc.Proc_name ep2_nucleus.ACName.Acquirer) |[Set.range ep2_nucleus.Event.c]|
        (proc.Proc_name ep2_nucleus.ACName.Terminal)
  | AbsName.Loop =>
      (proc.Proc_name ep2_nucleus.ACName.AcConfigManagement) |[Set.range ep2_nucleus.Event.c]|
        (proc.Proc_name ep2_nucleus.ACName.TerminalConfigManagement)

/- *********************************************************
           a theorem for verifying Abs <=F AC
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare simp_event_set [simp]` has no direct Lean analogue
   here. -/

/- Lean note:
   The original Isabelle proof uses fixed-point induction across
   `AbsName` and `ACName`. The current Lean port keeps this
   heterogeneous fixed-point argument as an axiom for now. -/

axiom ep2_Abs_AC :
    Abs <=F ep2_nucleus.AC

/- *********************************************************
        relating function between ACName and AbsName
 ********************************************************* -/

def Abs_to_DF : AbsName → proc DFtickName NEvent
  | AbsName.Abstract => proc.Proc_name DFtickName.DFtick
  | AbsName.Loop => proc.Proc_name DFtickName.DFtick

/- *********************************************************
           a theorem for verifying Abs <=F AC
 ********************************************************* -/

/- Lean note:
   The original Isabelle proof uses fixed-point induction from `DFtick`
   to `Abs`. The current Lean port keeps this heterogeneous fixed-point
   argument as an axiom for now. -/

axiom ep2_DF_Abs :
    (proc.Proc_name DFtickName.DFtick : proc DFtickName NEvent) <=F Abs

/- -------------------------------------------------------*
 |                 AC is Deadlock-free.                  |
 *------------------------------------------------------- -/

theorem AC_isDeadlockFree :
    isDeadlockFree ep2_nucleus.AC := by
  exact (DeadlockFree_DFtick_ref (P := ep2_nucleus.AC)).2
    (cspF_trans_left_ref ep2_DF_Abs ep2_Abs_AC)

end ep2_nucleusDF
