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

/- *****************************************************************

         1. proves lemma for Spc <=F Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- (*** Back0_Back1 ***) -/

axiom Back0_Back1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref Event.Back1 TH1P)))

abbrev Back0_Back1_simp := Back0_Back1

/- (*** Eat0_Back1 ***) -/

axiom Eat0_Back1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P x)) (VARP x)) (Pref Event.Back1 TH1P)))

abbrev Eat0_Back1_simp := Eat0_Back1

/- (*** Back0_Eat1 ***) -/

axiom Back0_Eat1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (Pref Event.Eat1 (EAT1P x))))

abbrev Back0_Eat1_simp := Back0_Eat1

axiom EAT0_Back1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.EAT0_TH1) MF MF
        (Hide (Par1 (Par0 (EAT0P x) (VARP x)) (Pref Event.Back1 TH1P)))

abbrev EAT0_Back1_simp := EAT0_Back1

/- (*** Back0_EAT1 ***) -/

axiom Back0_EAT1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_EAT1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) (EAT1P x)))

abbrev Back0_EAT1_simp := Back0_EAT1

/- (*** Back0_TH1  ***) -/

/- declare SpcDef.simps [simp del] -/

axiom Back0_TH1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x)) TH1P))

abbrev Back0_TH1_simp := Back0_TH1

/- (*** TH0_Back1  ***) -/

axiom TH0_Back1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 TH0P (VARP x)) (Pref Event.Back1 TH1P)))

abbrev TH0_Back1_simp := TH0_Back1

/- (*** TH0_Eat1 ***) -/

axiom TH0_Eat1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 TH0P (VARP x)) (Pref Event.Eat1 (EAT1P x))))

abbrev TH0_Eat1_simp := TH0_Eat1

/- (*** Eat0_TH1 ***) -/

axiom Eat0_TH1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P x)) (VARP x)) TH1P))

abbrev Eat0_TH1_simp := Eat0_TH1

/- (*** TH0_TH1 ***) -/

axiom TH0_TH1 (x : Int) :
    refF (SpcSub SpcName.TH0_TH1) MF MF
      (Hide (Par1 (Par0 TH0P (VARP x)) TH1P))

abbrev TH0_TH1_simp := TH0_TH1

/- (*** Back0_TH0_TH1 ***) -/

axiom Back0_TH0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP (3 * x + 1))) TH1P)))

abbrev Back0_TH0_WR1_simp := Back0_TH0_WR1

/- (*** Back1_TH0_TH1 ***) -/

axiom Back1_TH0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Pref Event.Back1 (Hide (Par1 (Par0 TH0P (VARP (3 * x + 1))) TH1P)))

abbrev Back1_TH0_WR1_simp := Back1_TH0_WR1

/- (*** Back0_WR1 ***) -/

axiom Back0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP x))
          (Pref (Event.WR1 (3 * x + 1)) TH1P)))

abbrev Back0_WR1_simp := Back0_WR1

/- (*** WR0_Back1 ***) -/

axiom WR0_Back1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref (Event.WR0 (x / 2)) TH0P) (VARP x)) (Pref Event.Back1 TH1P)))

abbrev WR0_Back1_simp := WR0_Back1

/- (*** TH0_WR1 ***) -/

axiom TH0_WR1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 TH0P (VARP x)) (Pref (Event.WR1 (3 * x + 1)) TH1P)))

abbrev TH0_WR1_simp := TH0_WR1

/- (*** WR0_TH1 ***) -/

axiom WR0_TH1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.TH0_TH1) MF MF
        (Hide (Par1 (Par0 (Pref (Event.WR0 (x / 2)) TH0P) (VARP x)) TH1P))

abbrev WR0_TH1_simp := WR0_TH1

/- (*** EAT0_TH1 ***) -/

axiom EAT0_TH1 (x : Int) :
    ¬ ODD x →
      refF (SpcSub SpcName.EAT0_TH1) MF MF
        (Hide (Par1 (Par0 (EAT0P x) (VARP x)) TH1P))

abbrev EAT0_TH1_simp := EAT0_TH1

/- (*** TH0_EAT1 ***) -/

axiom TH0_EAT1 (x : Int) :
    ODD x →
      refF (SpcSub SpcName.TH0_EAT1) MF MF
        (Hide (Par1 (Par0 TH0P (VARP x)) (EAT1P x)))

abbrev TH0_EAT1_simp := TH0_EAT1

/- *********************************************************
                  ALL n. Spc <=F Imp n
 ********************************************************* -/

axiom Spc_ref_Seq (n : Int) :
    refF Spc (MF : SpcName → domFType Event) (MF : ImpName → domFType Event) (Imp n)

end DM5_Spc_Imp
