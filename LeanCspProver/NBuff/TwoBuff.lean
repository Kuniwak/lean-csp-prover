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

@[simp] axiom guardedfun_PN :
    guardedfun PNdef

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

axiom Buff2_eq_LinkBuff2 :
    (proc.Proc_name PN.Buff2 : proc PN Event) =F LinkBuff2

end TwoBuff
