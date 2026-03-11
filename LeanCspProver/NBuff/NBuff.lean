           /- -------------------------------------------*
            |                N Buffers                  |
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

namespace NBuff

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
  | Buff : Nat → Nat → PN
deriving DecidableEq, Inhabited

/- *********************************************************
                  Recursivey Process
 ********************************************************* -/

def PNdef : PN → proc PN Event
  | PN.Buff1 =>
      Event.inC ~> proc.Proc_name PN.Buff1'
  | PN.Buff1' =>
      Event.outC ~> proc.Proc_name PN.Buff1
  | PN.Buff N k =>
      if (Nat.blt 0 N && Nat.ble k N) then
        ((if Nat.blt k N then
            Event.inC ~> proc.Proc_name (PN.Buff N (Nat.succ k))
          else
            proc.STOP) [+]
         (if Nat.blt 0 k then
            Event.outC ~> proc.Proc_name (PN.Buff N (k - 1))
          else
            proc.STOP))
      else
        proc.STOP

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

private abbrev Buff1P : proc PN Event :=
  proc.Proc_name PN.Buff1

private abbrev Buff1'P : proc PN Event :=
  proc.Proc_name PN.Buff1'

private abbrev BuffP (N k : Nat) : proc PN Event :=
  proc.Proc_name (PN.Buff N k)

abbrev Link (P Q : proc PN Event) : proc PN Event :=
  proc.Hiding
    ((P[[Event.outC <--> Event.midC]]) |[({Event.midC} : Set Event)]|
      (Q[[Event.inC <--> Event.midC]]))
    ({Event.midC} : Set Event)

infixr:76 " <---> " => Link

def LinkBuff : Nat → Nat → proc PN Event
  | 0, _ => proc.STOP
  | Nat.succ n, k =>
      if (n = 0) then
        if Nat.blt 0 k then Buff1'P else Buff1P
      else
        if Nat.blt n k then Buff1'P <---> LinkBuff n (k - 1) else Buff1P <---> LinkBuff n k

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
                  data tranfer
 ********************************************************* -/

axiom internal_data_transfer {N k : Nat} :
    Nat.lt k N ->
      (Buff1'P <---> BuffP N k) =F
        (Buff1P <---> BuffP N (Nat.succ k))

/- *********************************************************
                 one step concurrency
 ********************************************************* -/

def Buff_to_Link_Buff : PN → proc PN Event
  | PN.Buff1 => Buff1P
  | PN.Buff1' => Buff1'P
  | PN.Buff N k =>
      if (Nat.blt 0 N && Nat.ble k N) then
        if (N = Nat.succ 0) then
          if Nat.blt k N then Buff1P else Buff1'P
        else
          if Nat.blt k N then Buff1P <---> BuffP (N - 1) k else Buff1'P <---> BuffP (N - 1) (k - 1)
      else
        proc.STOP

axiom LinkBuff_eq_Buff_step_k {N k : Nat} :
    Nat.lt 0 N -> k <= Nat.succ N ->
      BuffP N k =F Buff_to_Link_Buff (PN.Buff N k)

/- --------------------- *
 |        one step       |
 * --------------------- -/

axiom LinkBuff_eq_Buff_step (N : Nat) :
    BuffP (Nat.succ N) 0 =F
      (if (N = 0) then Buff1P else Buff1P <---> BuffP N 0)

/- --------------------- *
 |          main         |
 * --------------------- -/

axiom LinkBuff_eq_Buff :
    ∀ N, BuffP N 0 =F LinkBuff N 0

end NBuff
