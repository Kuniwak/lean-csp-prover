           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DM.DM3_hide

open fpmode
open DM1_Imp_def

noncomputable section

namespace DM4_Spc_def

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

private abbrev RepNum (X : Set Int) (Pf : Int → proc ImpName Event) : proc ImpName Event :=
  Rep_int_choice_f Event.NUM X Pf

/- *****************************************************************

         1. defines Spc
         2.
         3.
         4.

 ***************************************************************** -/

/- *********************************************************
                     specification
 ********************************************************* -/

inductive SpcName where
  | TH0_TH1
  | EAT0_TH1
  | TH0_EAT1
deriving DecidableEq, Inhabited

def Spcfun : SpcName → proc SpcName Event
  | SpcName.TH0_TH1 =>
      proc.Ext_pre_choice OBS fun x =>
        IF decide (x = Event.Eat0) THEN proc.Proc_name SpcName.EAT0_TH1
        ELSE IF decide (x = Event.Eat1) THEN proc.Proc_name SpcName.TH0_EAT1
        ELSE proc.Proc_name SpcName.TH0_TH1
  | SpcName.EAT0_TH1 =>
      proc.Ext_pre_choice (OBS \ {Event.Eat1}) fun x =>
        IF decide (x = Event.End0) THEN proc.Proc_name SpcName.TH0_TH1
        ELSE proc.Proc_name SpcName.EAT0_TH1
  | SpcName.TH0_EAT1 =>
      proc.Ext_pre_choice (OBS \ {Event.Eat0}) fun x =>
        IF decide (x = Event.End1) THEN proc.Proc_name SpcName.TH0_TH1
        ELSE proc.Proc_name SpcName.TH0_EAT1

/- 
defs (overloaded)
Set_Spcfun_def [simp]: "PNfun == Spcfun"
-/
/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Spcfun : HasPNfun SpcName Event where
  PNfun := Spcfun

@[simp]
theorem Set_Spcfun_def (pn : SpcName) :
    PNfun (p := SpcName) (α := Event) pn = Spcfun pn :=
  rfl

def Spc : proc SpcName Event :=
  proc.Proc_name SpcName.TH0_TH1

theorem Spc_def :
    Spc = proc.Proc_name SpcName.TH0_TH1 :=
  rfl

/- *********************************************************
        Lemmas for   ALL n.  verify Spc <=sf Imp n
 ********************************************************* -/

/- (*** relation between Spcfun and ImpDef ***) -/

def Spc_to_Imp : SpcName → proc ImpName Event
  | SpcName.TH0_TH1 =>
      RepNum Set.univ (fun n => Hide (Par1 (Par0 TH0P (VARP n)) TH1P)) |~|
      RepNum Set.univ (fun n => Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P)) |~|
      RepNum Set.univ (fun n => Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))) |~|
      RepNum Set.univ
        (fun n => Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P))) |~|
      RepNum EVENs
        (fun n =>
          Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P))) |~|
      RepNum ODDs
        (fun n =>
          Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n)))) |~|
      RepNum EVENs
        (fun n => Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P)) |~|
      RepNum ODDs
        (fun n => Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))) |~|
      RepNum EVENs
        (fun n => Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)) |~|
      RepNum EVENs
        (fun n =>
          Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) (Pref Event.Back1 TH1P))) |~|
      RepNum ODDs
        (fun n => Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))) |~|
      RepNum ODDs
        (fun n =>
          Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)))
  | SpcName.EAT0_TH1 =>
      RepNum EVENs (fun n => Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)) |~|
      RepNum EVENs (fun n => Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)))
  | SpcName.TH0_EAT1 =>
      RepNum ODDs (fun n => Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n))) |~|
      RepNum ODDs (fun n => Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n)))

/- *********************************************************
                gProc lemmas (routine work)
 ********************************************************* -/

@[simp]
axiom guarded_Spc :
    guardedfun (p := SpcName) (q := SpcName) (α := Event) Spcfun

end DM4_Spc_def
