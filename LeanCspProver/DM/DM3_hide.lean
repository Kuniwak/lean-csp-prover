           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                March 2007  (modified)     |
            |                April 2020  (modified)     |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DM.DM2_para

open fpmode
open DM1_Imp_def

noncomputable section

namespace DM3_hide

private abbrev TH0P : proc ImpName Event := proc.Proc_name ImpName.TH0

private abbrev TH1P : proc ImpName Event := proc.Proc_name ImpName.TH1

private abbrev VARP (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.VAR n)

private abbrev EAT0P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT0 n)

private abbrev EAT1P (n : Int) : proc ImpName Event := proc.Proc_name (ImpName.EAT1 n)

private abbrev Par0 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH0 Q

private abbrev Par1 (P Q : proc ImpName Event) : proc ImpName Event := proc.Parallel P CH1 Q

private abbrev Pref (e : Event) (P : proc ImpName Event) : proc ImpName Event := proc.Act_prefix e P

/- Lean note:
   Isabelle's hiding syntax `P -- X` is written as `proc.Hiding P X` in Lean.
   The fixed hidden alphabet in this file is abbreviated by `Hide`. -/

private abbrev Hide (P : proc ImpName Event) : proc ImpName Event :=
  proc.Hiding P (CH0 ∪ CH1)

/- *****************************************************************

         1. expands hiding operators in Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- (******************** Hiding ********************) -/

/- (*** Back0 VAR Back1 HIDE ***) -/

axiom Back0_VAR_Back1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
      ((Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P)))) [+]
        (Pref Event.Back1 (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P))))

abbrev Back0_VAR_Back1_HIDE_simp := Back0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules25` and `fold_Imp_rules25`
   are represented by `Back0_VAR_Back1_HIDE_simp` together with the earlier
   simp lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR Back1 HIDE ***) -/

axiom Eat0_VAR_Back1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
        ((Pref Event.Eat0 (Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P)))) [+]
          (Pref Event.Back1 (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P))))

abbrev Eat0_VAR_Back1_HIDE_simp := Eat0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules26` and `fold_Imp_rules26`
   are represented by `Eat0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR Eat1 HIDE ***) -/

axiom Back0_VAR_Eat1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n)))) MF MF
        ((Pref Event.Eat1 (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n)))) [+]
          (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n))))))

abbrev Back0_VAR_Eat1_HIDE_simp := Back0_VAR_Eat1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules27` and `fold_Imp_rules27`
   are represented by `Back0_VAR_Eat1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR Back1 HIDE ***) -/

axiom EAT0_VAR_Back1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
        ((Pref Event.End0
            (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) (Pref Event.Back1 TH1P)))) [+]
          (Pref Event.Back1 (Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P))))

abbrev EAT0_VAR_Back1_HIDE_simp := EAT0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules28` and `fold_Imp_rules28`
   are represented by `EAT0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR EAT1 HIDE ***) -/

axiom Back0_VAR_EAT1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n))) MF MF
        ((Pref Event.End1
            (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n))
              (Pref (Event.WR1 (3 * n + 1)) TH1P)))) [+]
          (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n)))))

abbrev Back0_VAR_EAT1_HIDE_simp := Back0_VAR_EAT1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules29` and `fold_Imp_rules29`
   are represented by `Back0_VAR_EAT1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (**************************) -/
/- (*** Back0 VAR TH1 HIDE ***) -/

axiom Back0_VAR_TH1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P)) MF MF
      (Timeout
        (Pref Event.Back0 (Hide (Par1 (Par0 TH0P (VARP n)) TH1P)))
        (IF ODD n
        THEN Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n)))
        ELSE Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev Back0_VAR_TH1_HIDE_simp := Back0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules30` and `fold_Imp_rules30`
   are represented by `Back0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (**************************) -/
/- (*** TH0 VAR Back1 HIDE ***) -/

axiom TH0_VAR_Back1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))) MF MF
      (Timeout
        (Pref Event.Back1 (Hide (Par1 (Par0 TH0P (VARP n)) TH1P)))
        (IF EVEN n
        THEN Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P))
        ELSE Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev TH0_VAR_Back1_HIDE_simp := TH0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules31` and `fold_Imp_rules31`
   are represented by `TH0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Eat0 VAR TH1 HIDE ***) -/

axiom Eat0_VAR_TH1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P)) MF MF
        (Timeout
          (Pref Event.Eat0 (Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)))
          (Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev Eat0_VAR_TH1_HIDE_simp := Eat0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules32` and `fold_Imp_rules32`
   are represented by `Eat0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR Eat1 HIDE ***) -/

axiom TH0_VAR_Eat1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))) MF MF
        (Timeout
          (Pref Event.Eat1 (Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n))))
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref Event.Eat1 (EAT1P n)))))

abbrev TH0_VAR_Eat1_HIDE_simp := TH0_VAR_Eat1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules33` and `fold_Imp_rules33`
   are represented by `TH0_VAR_Eat1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** EAT0 VAR TH1 HIDE ***) -/

axiom EAT0_VAR_TH1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (EAT0P n) (VARP n)) TH1P)) MF MF
        (Timeout
          (Pref Event.End0
            (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)))
          (Hide (Par1 (Par0 (EAT0P n) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev EAT0_VAR_TH1_HIDE_simp := EAT0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules34` and `fold_Imp_rules34`
   are represented by `EAT0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR EAT1 HIDE ***) -/

axiom TH0_VAR_EAT1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 TH0P (VARP n)) (EAT1P n))) MF MF
        (Timeout
          (Pref Event.End1
            (Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (EAT1P n))))

abbrev TH0_VAR_EAT1_HIDE_simp := TH0_VAR_EAT1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules35` and `fold_Imp_rules35`
   are represented by `TH0_VAR_EAT1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR TH1 HIDE step 1 ***) -/

axiom TH0_VAR_TH1_HIDE (n : Int) :
    eqF (Hide (Par1 (Par0 TH0P (VARP n)) TH1P)) MF MF
      ((IF EVEN n
        THEN Hide (Par1 (Par0 (Pref Event.Eat0 (EAT0P n)) (VARP n)) TH1P)
        ELSE Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) TH1P)) |~|
       (IF ODD n
        THEN Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Eat1 (EAT1P n)))
        ELSE Hide (Par1 (Par0 TH0P (VARP n)) (Pref Event.Back1 TH1P))))

abbrev TH0_VAR_TH1_HIDE_simp := TH0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules36` and `fold_Imp_rules36`
   are represented by `TH0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR Back1 HIDE ***) -/

axiom WR0_VAR_Back1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) (Pref Event.Back1 TH1P))) MF MF
        (Timeout
          (Pref Event.Back1
            (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)))
          (Hide (Par1 (Par0 TH0P (VARP (n / 2))) (Pref Event.Back1 TH1P))))

abbrev WR0_VAR_Back1_HIDE_simp := WR0_VAR_Back1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules37` and `fold_Imp_rules37`
   are represented by `WR0_VAR_Back1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** Back0 VAR WR1 HIDE ***) -/

axiom Back0_VAR_WR1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))) MF MF
        (Timeout
          (Pref Event.Back0
            (Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP (3 * n + 1))) TH1P)))

abbrev Back0_VAR_WR1_HIDE_simp := Back0_VAR_WR1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules38` and `fold_Imp_rules38`
   are represented by `Back0_VAR_WR1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** WR0 VAR TH1 HIDE ***) -/

axiom WR0_VAR_TH1_HIDE (n : Int) :
    EVEN n →
      eqF (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) TH1P)) MF MF
        ((Hide (Par1 (Par0 TH0P (VARP (n / 2))) TH1P)) |~|
          (Hide (Par1 (Par0 (Pref (Event.WR0 (n / 2)) TH0P) (VARP n)) (Pref Event.Back1 TH1P))))

abbrev WR0_VAR_TH1_HIDE_simp := WR0_VAR_TH1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules39` and `fold_Imp_rules39`
   are represented by `WR0_VAR_TH1_HIDE_simp` together with the preceding
   simp lemmas and their `cspF_sym` images. -/

/- (*** TH0 VAR WR1 HIDE ***) -/

axiom TH0_VAR_WR1_HIDE (n : Int) :
    ODD n →
      eqF (Hide (Par1 (Par0 TH0P (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))) MF MF
        ((Hide (Par1 (Par0 TH0P (VARP (3 * n + 1))) TH1P)) |~|
          (Hide (Par1 (Par0 (Pref Event.Back0 TH0P) (VARP n)) (Pref (Event.WR1 (3 * n + 1)) TH1P))))

abbrev TH0_VAR_WR1_HIDE_simp := TH0_VAR_WR1_HIDE

/- The Isabelle theorem bundles `unfold_Imp_rules` and `fold_Imp_rules` are
   represented by `TH0_VAR_WR1_HIDE_simp` together with the preceding simp
   lemmas and their `cspF_sym` images. -/

end DM3_hide
