           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DM.DM1_Imp_def

open fpmode
open DM1_Imp_def

noncomputable section

namespace DM2_para

private abbrev TH0P : proc ImpName Event := proc.Proc_name ImpName.TH0

private abbrev TH1P : proc ImpName Event := proc.Proc_name ImpName.TH1

private abbrev VARP (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.VAR n)

private abbrev EAT0P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT0 n)

private abbrev EAT1P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT1 n)

private abbrev Par0 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH0 Q

private abbrev Par1 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH1 Q

private abbrev Pref (e : Event) (P : proc ImpName Event) : proc ImpName Event := proc.Act_prefix e P

/- *****************************************************************

         1. expands parallel operators in Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- (*** TH0 VAR step 1 ***) -/

axiom TH0_VAR (n : Int) :
    eqF
      ((proc.Proc_name ImpName.TH0) |[CH0]| (proc.Proc_name (ImpName.VAR n)))
      MF MF
      (proc.Ext_pre_choice
        (Set.insert (Event.RD0 n) (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF (by
              classical
              exact decide (x ∈ Set.range Event.RD0 ∨ x ∈ Set.range Event.WR0))
          THEN
            IF EVEN (getInt x)
            THEN
              Event.Eat0 ~>
                ((proc.Proc_name (ImpName.EAT0 n)) |[CH0]| (proc.Proc_name (ImpName.VAR n)))
            ELSE
              Event.Back0 ~>
                ((proc.Proc_name ImpName.TH0) |[CH0]| (proc.Proc_name (ImpName.VAR n)))
          ELSE
            ((proc.Proc_name ImpName.TH0) |[CH0]|
              (proc.Proc_name (ImpName.VAR (getInt x))))))

abbrev TH0_VAR_simp := TH0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules4` and `fold_Imp_rules4`
   are represented by `TH0_VAR_simp` together with the earlier simp lemmas
   from `DM1_Imp_def` and their `cspF_sym` images. -/

/- (*** TH0 VAR TH1 step 1 ***) -/

axiom TH0_VAR_TH1 (n : Int) :
    eqF (Par1 (Par0 TH0P (VARP n)) TH1P) MF MF
      (proc.Ext_pre_choice ({Event.RD0 n, Event.RD1 n} : Set Event) (fun x =>
        IF decide (x = Event.RD0 n)
        THEN
          IF EVEN n
          THEN Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) TH1P)
        ELSE
          IF ODD n
          THEN Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))
          ELSE Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)))

abbrev TH0_VAR_TH1_simp := TH0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules5` and `fold_Imp_rules5`
   are represented by `TH0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR step 2 ***) -/

axiom Eat0_VAR (n : Int) :
    eqF (Pref Event.Eat0 (Par0 (EAT0P n) (VARP n))) MF MF
      (proc.Ext_pre_choice
        (Set.insert Event.Eat0 (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.Eat0)
          THEN Par0 (EAT0P n) (VARP n)
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Pref Event.Eat0 (Par0 (EAT0P n) (VARP n))
            ELSE Pref Event.Eat0 (Par0 (EAT0P n) (VARP (getInt x)))))

abbrev Eat0_VAR_simp := Eat0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules6` and `fold_Imp_rules6`
   are represented by `Eat0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** Back0 VAR step 2 ***) -/

axiom Back0_VAR (n : Int) :
    eqF (Pref Event.Back0 (Par0 TH0P (VARP n))) MF MF
      (proc.Ext_pre_choice
        (Set.insert Event.Back0 (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.Back0)
          THEN Par0 TH0P (VARP n)
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Pref Event.Back0 (Par0 TH0P (VARP n))
            ELSE Pref Event.Back0 (Par0 TH0P (VARP (getInt x)))))

abbrev Back0_VAR_simp := Back0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules7` and `fold_Imp_rules7`
   are represented by `Back0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** Eat0 VAR TH1 step 2 ***) -/

axiom Eat0_VAR_TH1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref Event.Eat0 (Par0 (EAT0P n) (VARP n))) TH1P) MF MF
        (proc.Ext_pre_choice ({Event.Eat0, Event.RD1 n} : Set Event) (fun x =>
          IF decide (x = Event.Eat0)
          THEN Par1 (Par0 (EAT0P n) (VARP n)) TH1P
          ELSE Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev Eat0_VAR_TH1_simp := Eat0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules8` and `fold_Imp_rules8`
   are represented by `Eat0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (****************************) -/
/- (*** Back0 VAR TH1 step 2 ***) -/

axiom Back0_VAR_TH1 (n : Int) :
    eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) TH1P) MF MF
      (proc.Ext_pre_choice ({Event.Back0, Event.RD1 n} : Set Event) (fun x =>
        IF decide (x = Event.Back0)
        THEN Par1 (Par0 TH0P (VARP n)) TH1P
        ELSE
          IF ODD n
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev Back0_VAR_TH1_simp := Back0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules9` and `fold_Imp_rules9`
   are represented by `Back0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR Eat1 step 2 ***) -/

axiom TH0_VAR_Eat1 (n : Int) :
    ODD n →
      eqF (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))) MF MF
        (proc.Ext_pre_choice ({Event.Eat1, Event.RD0 n} : Set Event) (fun x =>
          IF decide (x = Event.Eat1)
          THEN Par1 (Par0 TH0P (VARP n)) (EAT1P n)
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))))

abbrev TH0_VAR_Eat1_simp := TH0_VAR_Eat1

/- The Isabelle theorem bundles `unfold_Imp_rules10` and `fold_Imp_rules10`
   are represented by `TH0_VAR_Eat1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (****************************) -/
/- (*** TH0 VAR Back1 step 2 ***) -/

axiom TH0_VAR_Back1 (n : Int) :
    eqF (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)) MF MF
      (proc.Ext_pre_choice ({Event.Back1, Event.RD0 n} : Set Event) (fun x =>
        IF decide (x = Event.Back1)
        THEN Par1 (Par0 TH0P (VARP n)) TH1P
        ELSE
          IF EVEN n
          THEN Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev TH0_VAR_Back1_simp := TH0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules11` and `fold_Imp_rules11`
   are represented by `TH0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR step 3 ***) -/

axiom EAT0_VAR (n : Int) :
    eqF (Par0 (EAT0P n) (VARP n)) MF MF
      (proc.Ext_pre_choice
        (Set.insert Event.End0 (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.End0)
          THEN Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Par0 (EAT0P n) (VARP n)
            ELSE Par0 (EAT0P n) (VARP (getInt x))))

abbrev EAT0_VAR_simp := EAT0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules12` and `fold_Imp_rules12`
   are represented by `EAT0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** EAT0 VAR TH1 step 3 ***) -/

axiom EAT0_VAR_TH1 (n : Int) :
    EVEN n →
      eqF (Par1 (Par0 (EAT0P n) (VARP n)) TH1P) MF MF
        (proc.Ext_pre_choice ({Event.End0, Event.RD1 n} : Set Event) (fun x =>
          IF decide (x = Event.End0)
          THEN Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) TH1P)
          ELSE Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)))

abbrev EAT0_VAR_TH1_simp := EAT0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules13` and `fold_Imp_rules13`
   are represented by `EAT0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR Back1 step 3 ***) -/

axiom Eat0_VAR_Back1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref Event.Eat0 (Par0 (EAT0P n) (VARP n))) (Pref Event.Back1 TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.Eat0, Event.Back1} : Set Event) (fun x =>
          IF decide (x = Event.Eat0)
          THEN Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)
          ELSE Pref Event.Eat0 (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)))

abbrev Eat0_VAR_Back1_simp := Eat0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules14` and `fold_Imp_rules14`
   are represented by `Eat0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR EAT1 step 3 ***) -/

axiom TH0_VAR_EAT1 (n : Int) :
    ODD n →
      eqF (Par1 (Par0 TH0P (VARP n)) (EAT1P n)) MF MF
        (proc.Ext_pre_choice ({Event.End1, Event.RD0 n} : Set Event) (fun x =>
          IF decide (x = Event.End1)
          THEN Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (EAT1P n))))

abbrev TH0_VAR_EAT1_simp := TH0_VAR_EAT1

/- The Isabelle theorem bundles `unfold_Imp_rules15` and `fold_Imp_rules15`
   are represented by `TH0_VAR_EAT1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR Eat1 step 3 ***) -/

axiom Back0_VAR_Eat1 (n : Int) :
    ODD n →
      eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (Pref Event.Eat1 (EAT1P n))) MF MF
        (proc.Ext_pre_choice ({Event.Eat1, Event.Back0} : Set Event) (fun x =>
          IF decide (x = Event.Eat1)
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (EAT1P n))
          ELSE Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))))

abbrev Back0_VAR_Eat1_simp := Back0_VAR_Eat1

/- The Isabelle theorem bundles `unfold_Imp_rules16` and `fold_Imp_rules16`
   are represented by `Back0_VAR_Eat1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR Back1 step 3 ***) -/

axiom Back0_VAR_Back1 (n : Int) :
    eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (Pref Event.Back1 TH1P)) MF MF
      (proc.Ext_pre_choice ({Event.Back0, Event.Back1} : Set Event) (fun x =>
        IF decide (x = Event.Back0)
        THEN Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)
        ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) TH1P)))

abbrev Back0_VAR_Back1_simp := Back0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules17` and `fold_Imp_rules17`
   are represented by `Back0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR step 4 ***) -/

axiom WR0_VAR (n : Int) :
    eqF (Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))) MF MF
      (proc.Ext_pre_choice
        (Set.insert (Event.WR0 (n / 2)) (Set.insert (Event.RD1 n) (Set.range Event.WR1)))
        (fun x =>
          IF decide (x = Event.WR0 (n / 2))
          THEN Par0 TH0P (VARP (n / 2))
          ELSE
            IF decide (x = Event.RD1 n)
            THEN Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))
            ELSE Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP (getInt x)))))

abbrev WR0_VAR_simp := WR0_VAR

/- The Isabelle theorem bundles `unfold_Imp_rules18` and `fold_Imp_rules18`
   are represented by `WR0_VAR_simp` together with the preceding simp lemmas
   and their `cspF_sym` images. -/

/- (*** WR0 VAR TH1 step 4 ***) -/

axiom WR0_VAR_TH1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))) TH1P) MF MF
        (proc.Ext_pre_choice ({Event.WR0 (n / 2), Event.RD1 n} : Set Event) (fun x =>
          IF decide (x = Event.WR0 (n / 2))
          THEN Par1 (Par0 TH0P (VARP (n / 2))) TH1P
          ELSE Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev WR0_VAR_TH1_simp := WR0_VAR_TH1

/- The Isabelle theorem bundles `unfold_Imp_rules19` and `fold_Imp_rules19`
   are represented by `WR0_VAR_TH1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR Back1 step 4 ***) -/

axiom EAT0_VAR_Back1 (n : Int) :
    EVEN n →
      eqF (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.End0, Event.Back1} : Set Event) (fun x =>
          IF decide (x = Event.End0)
          THEN Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))
          ELSE Par1 (Par0 (EAT0P n) (VARP n)) TH1P))

abbrev EAT0_VAR_Back1_simp := EAT0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules20` and `fold_Imp_rules20`
   are represented by `EAT0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR EAT1 step 4 ***) -/

axiom TH0_VAR_WR1 (n : Int) :
    ODD n →
      eqF (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.WR1 (3 * n + 1), Event.RD0 n} : Set Event) (fun x =>
          IF decide (x = Event.WR1 (3 * n + 1))
          THEN Par1 (Par0 TH0P (VARP (3 * n + 1))) TH1P
          ELSE Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))

abbrev TH0_VAR_WR1_simp := TH0_VAR_WR1

/- The Isabelle theorem bundles `unfold_Imp_rules21` and `fold_Imp_rules21`
   are represented by `TH0_VAR_WR1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR EAT1 step 4 ***) -/

axiom Back0_VAR_EAT1 (n : Int) :
    ODD n →
      eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (EAT1P n)) MF MF
        (proc.Ext_pre_choice ({Event.End1, Event.Back0} : Set Event) (fun x =>
          IF decide (x = Event.End1)
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))
          ELSE Par1 (Par0 TH0P (VARP n)) (EAT1P n)))

abbrev Back0_VAR_EAT1_simp := Back0_VAR_EAT1

/- The Isabelle theorem bundles `unfold_Imp_rules22` and `fold_Imp_rules22`
   are represented by `Back0_VAR_EAT1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR Back1 step 5 ***) -/

axiom WR0_VAR_Back1 (n : Int) :
    EVEN n →
      eqF (Par1 (Pref (Event.WR0 (n / 2)) (Par0 TH0P (VARP n))) (Pref Event.Back1 TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.WR0 (n / 2), Event.Back1} : Set Event) (fun x =>
          IF decide (x = Event.WR0 (n / 2))
          THEN Par1 (Par0 TH0P (VARP (n / 2))) (Pref Event.Back1 TH1P)
          ELSE Pref (Event.WR0 (n / 2)) (Par1 (Par0 TH0P (VARP n)) TH1P)))

abbrev WR0_VAR_Back1_simp := WR0_VAR_Back1

/- The Isabelle theorem bundles `unfold_Imp_rules23` and `fold_Imp_rules23`
   are represented by `WR0_VAR_Back1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR WR1 step 5 ***) -/

axiom Back0_VAR_WR1 (n : Int) :
    ODD n →
      eqF (Par1 (Pref Event.Back0 (Par0 TH0P (VARP n))) (Pref (Event.WR1 (3 * n + 1)) TH1P)) MF MF
        (proc.Ext_pre_choice ({Event.WR1 (3 * n + 1), Event.Back0} : Set Event) (fun x =>
          IF decide (x = Event.WR1 (3 * n + 1))
          THEN Pref Event.Back0 (Par1 (Par0 TH0P (VARP (3 * n + 1))) TH1P)
          ELSE Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P)))

abbrev Back0_VAR_WR1_simp := Back0_VAR_WR1

/- The Isabelle theorem bundles `unfold_Imp_rules24` and `fold_Imp_rules24`
   are represented by `Back0_VAR_WR1_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

end DM2_para
