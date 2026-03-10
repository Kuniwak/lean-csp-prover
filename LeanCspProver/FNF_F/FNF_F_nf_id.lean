           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_nf_def

open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {p : Type u} {α : Type v}

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion`.                     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`               -/
/-                                                                   -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there  -/
/-  is nothing to disable or re-enable here.                         -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`     -/
/- Isabelle 2017                                                      -/
/-                                                                    -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is -/
/-  nothing to disable or re-enable here.                             -/

/-
(*****************************************************************

         1. =F --> =
         2.
         3.

 *****************************************************************)
-/

/- (*---------------------------------------------------------*
 |              syntactically identical ?                  |
 *---------------------------------------------------------*) -/

/- (*===========================================================*
 |                      fnfF_nat_proc                        |
 *===========================================================*) -/

/- (*** Q ***) -/

axiom fnfF_syntactical_equality_Q_lm
    {A1 A2 : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    refF
      ((((proc.Ext_pre_choice A1 Pf1) [+] proc.DIV) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
      M1 M2
      ((((proc.Ext_pre_choice A2 Pf2) [+] proc.SKIP) |~|
        Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
      False

axiom fnfF_syntactical_equality_Q
    {Q1 Q2 : proc p α} {A1 A2 : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    (Q1 = proc.SKIP ∨ Q1 = proc.DIV) →
      (Q2 = proc.SKIP ∨ Q2 = proc.DIV) →
        eqF
          ((((proc.Ext_pre_choice A1 Pf1) [+] Q1) |~|
            Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
          M1 M2
          ((((proc.Ext_pre_choice A2 Pf2) [+] Q2) |~|
            Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
          Q1 = Q2

/- (*** A ***) -/

axiom fnfF_syntactical_equality_Union_lm
    {A1 A2 : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A1 →
      Set.sUnion Ys2 ⊆ A2 →
        (Q = proc.SKIP ∨ Q = proc.DIV) →
          refF
            ((((proc.Ext_pre_choice A1 Pf1) [+] Q) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A2 Pf2) [+] Q) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            A2 ⊆ A1

axiom fnfF_syntactical_equality_Union
    {A1 A2 : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A1 →
      Set.sUnion Ys2 ⊆ A2 →
        (Q = proc.SKIP ∨ Q = proc.DIV) →
          eqF
            ((((proc.Ext_pre_choice A1 Pf1) [+] Q) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A2 Pf2) [+] Q) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            A1 = A2

/- (*** Yf ***) -/

axiom fnfF_syntactical_equality_Yf_DIV_lm
    {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)} {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A →
      Set.sUnion Ys2 ⊆ A →
        fnfF_set_condition A Ys1 →
          refF
            ((((proc.Ext_pre_choice A Pf1) [+] proc.DIV) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A Pf2) [+] proc.DIV) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            Ys2 ⊆ Ys1

axiom fnfF_syntactical_equality_Yf_SKIP_lm
    {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)} {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A →
      Set.sUnion Ys2 ⊆ A →
        fnfF_set_condition A Ys1 →
          refF
            ((((proc.Ext_pre_choice A Pf1) [+] proc.SKIP) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A Pf2) [+] proc.SKIP) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            Ys2 ⊆ Ys1

axiom fnfF_syntactical_equality_Yf
    {A : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A →
      Set.sUnion Ys2 ⊆ A →
        fnfF_set_condition A Ys1 →
          fnfF_set_condition A Ys2 →
            (Q = proc.SKIP ∨ Q = proc.DIV) →
              eqF
                ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
                  Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
                M1 M2
                ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
                  Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
                Ys1 = Ys2

/- (*** Pf ***) -/

/- T DIV -/

axiom fnfF_syntactical_equality_Pf_T_DIV_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domTType α} :
    a ∈ A →
      refT
        ((((proc.Ext_pre_choice A Pf1) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refT (Pf1 a) M1 M2 (Pf2 a)

/- T SKIP -/

axiom fnfF_syntactical_equality_Pf_T_SKIP_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domTType α} :
    a ∈ A →
      refT
        ((((proc.Ext_pre_choice A Pf1) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refT (Pf1 a) M1 M2 (Pf2 a)

/- F DIV -/

axiom fnfF_syntactical_equality_Pf_F_DIV_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domFType α} :
    a ∈ A →
      refF
        ((((proc.Ext_pre_choice A Pf1) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refF (Pf1 a) M1 M2 (Pf2 a)

/- F SKIP -/

axiom fnfF_syntactical_equality_Pf_F_SKIP_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domFType α} :
    a ∈ A →
      refF
        ((((proc.Ext_pre_choice A Pf1) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refF (Pf1 a) M1 M2 (Pf2 a)

axiom fnfF_syntactical_equality_Pf
    {a : α} {A : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)}
    {M1 M2 : p → domFType α} :
    a ∈ A →
      (Q = proc.SKIP ∨ Q = proc.DIV) →
        eqF
          ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
            Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
          M1 M2
          ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
            Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
          eqF (Pf1 a) M1 M2 (Pf2 a)

/- (*------------------------------------------------------------------*
 |                fnfF_proc ---> syntactical equality               |
 *------------------------------------------------------------------*) -/

axiom fnfF_syntactical_equality_only_if_lm
    {P1 : proc p α} {M1 M2 : p → domFType α} :
    fnfF_proc P1 →
      ∀ P2 : proc p α, (fnfF_proc P2 ∧ eqF P1 M1 M2 P2) → P1 = P2

theorem fnfF_syntactical_equality_only_if
    {P1 P2 : proc p α} {M1 M2 : p → domFType α} :
    fnfF_proc P1 →
      fnfF_proc P2 →
        eqF P1 M1 M2 P2 →
          P1 = P2 := by
  intro hP1 hP2 hEq
  exact fnfF_syntactical_equality_only_if_lm hP1 P2 ⟨hP2, hEq⟩

/- (*--------------------------*
 |         theorem          |
 *--------------------------*) -/

theorem fnfF_syntactical_equality [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    fnfF_proc P1 →
      fnfF_proc P2 →
        (eqFfix P1 P2 ↔ P1 = P2) := by
  intro hP1 hP2
  constructor
  · intro hEq
    exact fnfF_syntactical_equality_only_if hP1 hP2 hEq
  · intro hEq
    subst P2
    simpa [eqFfix] using (cspF_reflex_eq_P (P := P1) (M := MF))

/- (*===========================================================*
 |                        XfnfF_proc                         |
 *===========================================================*) -/

axiom XfnfF_syntactical_equality [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    P1 ∈ XfnfF_proc (p := p) (α := α) →
      P2 ∈ XfnfF_proc (p := p) (α := α) →
        (eqFfix P1 P2 ↔ P1 = P2)

/- (****************** to add them again ******************) -/

/- Lean has no direct analogue of Isabelle's local `declare if_split [split]`
   or `declare disj_not1 [simp]` commands. -/
