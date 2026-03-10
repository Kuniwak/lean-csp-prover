           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               Februaru 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_ext

open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {p : Type u} {α : Type v}

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion` and `Set.sInter`.     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`                 -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there is -/
/-  nothing to disable or re-enable here.                              -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`      -/
/- Isabelle 2017: `split_if --> if_split`                              -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is  -/
/-  nothing to disable or re-enable here.                              -/

/-
(*****************************************************************

         1. full sequentialization for Hiding (P -- X)
         2.
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                     Hiding P -- X                          |
 |                                                            |
 *============================================================* -/

def Pfun_Hiding (X : Set α) : proc p α → proc p α :=
  fun P1 => proc.Hiding P1 X

theorem Pfun_Hiding_def
    (X : Set α) :
    Pfun_Hiding (p := p) (α := α) X =
      (fun P1 => proc.Hiding P1 X) :=
  rfl

def SP_step_Hiding [Inhabited α]
    (X : Set α) :
    Set α → (α → proc p α) → proc p α → (α → proc p α) → proc p α :=
  fun A1 _Pf1 Q1 SPf =>
    if Q1 = proc.STOP then
      if A1 ∩ X = ∅ then
        (proc.Ext_pre_choice A1 SPf) [+] Q1
      else
        fsfF_Timeout
          ((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1)
          (fsfF_Rep_int_choice_com (A1 ∩ X) SPf)
    else
      fsfF_Int_choice
        (((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1))
        (fsfF_Rep_int_choice_com (A1 ∩ X) SPf)

theorem SP_step_Hiding_def [Inhabited α]
    (X : Set α) :
    SP_step_Hiding (p := p) (α := α) X =
      (fun A1 _Pf1 Q1 SPf =>
        if Q1 = proc.STOP then
          if A1 ∩ X = ∅ then
            (proc.Ext_pre_choice A1 SPf) [+] Q1
          else
            fsfF_Timeout
              ((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1)
              (fsfF_Rep_int_choice_com (A1 ∩ X) SPf)
        else
          fsfF_Int_choice
            (((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1))
            (fsfF_Rep_int_choice_com (A1 ∩ X) SPf)) :=
  rfl

def fsfF_Hiding [Inhabited α]
    (P1 : proc p α) (X : Set α) : proc p α :=
  fsfF_induct1 (Pfun_Hiding X) (SP_step_Hiding X) P1

theorem fsfF_Hiding_def [Inhabited α]
    (P1 : proc p α) (X : Set α) :
    fsfF_Hiding (p := p) (α := α) P1 X =
      fsfF_induct1 (Pfun_Hiding X) (SP_step_Hiding X) P1 :=
  rfl

notation:84 P " --seq " X => fsfF_Hiding P X

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Hiding_in [Inhabited α]
    {P1 : proc p α} {X : Set α} :
    fsfF_proc P1 →
      fsfF_proc (fsfF_Hiding P1 X) := by
  intro hP1
  rw [fsfF_Hiding_def]
  refine fsfF_induct1_in hP1 ?_
  intro A1 Pf1 Q1 SPf hPf1 hSPf hQ1
  cases hQ1 with
  | inl hQ1 =>
      subst hQ1
      simp [SP_step_Hiding_def]
      apply fsfF_Int_choice_in
      · refine fsfF_proc.fsfF_proc_ext ?_ (Or.inl rfl)
        intro a ha
        exact hSPf a ha.1
      · apply fsfF_Rep_int_choice_com_in
        intro a ha
        exact hSPf a ha.1
  | inr hQ1 =>
      cases hQ1 with
      | inl hQ1 =>
          subst hQ1
          simp [SP_step_Hiding_def]
          apply fsfF_Int_choice_in
          · refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inl rfl)
            intro a ha
            exact hSPf a ha.1
          · apply fsfF_Rep_int_choice_com_in
            intro a ha
            exact hSPf a ha.1
      | inr hQ1 =>
          subst hQ1
          by_cases hEmpty : A1 ∩ X = ∅
          · simp [SP_step_Hiding_def, hEmpty]
            exact fsfF_proc.fsfF_proc_ext hSPf (Or.inr <| Or.inr rfl)
          · simp [SP_step_Hiding_def, hEmpty]
            apply fsfF_Timeout_in
            · refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
              intro a ha
              exact hSPf a ha.1
            · apply fsfF_Rep_int_choice_com_in
              intro a ha
              exact hSPf a ha.1

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fsfF_Hiding_eqF [Inhabited α]
    [HasPNfun p α] [HasFPmode]
    {P1 : proc p α} {X : Set α} :
    eqFfix (proc.Hiding P1 X) (fsfF_Hiding P1 X) := by
  rw [fsfF_Hiding_def]
  refine cspF_fsfF_induct1_eqF
    (Pfun := Pfun_Hiding X)
    (SP_step := SP_step_Hiding X)
    (P1 := P1) ?_ ?_ ?_
  · intro C1 Rf1 hC1
    simpa [Pfun_Hiding_def] using
      (cspF_Hiding_Dist_sum (C := C1) (Pf := Rf1) (X := X) (M := MF))
  · intro A1 Pf1 Q1 hQ1
    cases hQ1 with
    | inl hQ1 =>
        subst hQ1
        let Pskip : proc p α :=
          ((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [+]
            (proc.SKIP : proc p α))
        let Rhide : proc p α :=
          Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X)
        let SRhide : proc p α :=
          fsfF_Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X)
        have hHideStep :
            eqFfix (proc.Hiding ((proc.Ext_pre_choice A1 Pf1) [+] (proc.SKIP : proc p α)) X)
              (Pskip |~| Rhide) :=
          cspF_SKIP_or_DIV_Hiding_step (Q := (proc.SKIP : proc p α))
            (Y := A1) (X := X) (Pf := Pf1) (M := MF) (Or.inl rfl)
        have hIntCong :
            eqFfix (Pskip |~| Rhide) (fsfF_Int_choice Pskip SRhide) :=
          cspF_trans_left_eq
            (cspF_Int_choice_cong
              cspF_reflex_eq_P
              (cspF_fsfF_Rep_int_choice_com_eqF
                (X := A1 ∩ X)
                (SPf := fun a => proc.Hiding (Pf1 a) X)))
            cspF_fsfF_Int_choice_eqF
        simpa [SP_step_Hiding_def, Pfun_Hiding_def, Pskip, Rhide, SRhide] using
          (cspF_trans_left_eq hHideStep hIntCong)
    | inr hQ1 =>
        cases hQ1 with
        | inl hQ1 =>
            subst hQ1
            let Pdiv : proc p α :=
              ((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [+]
                (proc.DIV : proc p α))
            let Rhide : proc p α :=
              Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X)
            let SRhide : proc p α :=
              fsfF_Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X)
            have hHideStep :
                eqFfix (proc.Hiding ((proc.Ext_pre_choice A1 Pf1) [+] (proc.DIV : proc p α)) X)
                  (Pdiv |~| Rhide) :=
              cspF_SKIP_or_DIV_Hiding_step (Q := (proc.DIV : proc p α))
                (Y := A1) (X := X) (Pf := Pf1) (M := MF) (Or.inr rfl)
            have hIntCong :
                eqFfix (Pdiv |~| Rhide) (fsfF_Int_choice Pdiv SRhide) :=
              cspF_trans_left_eq
                (cspF_Int_choice_cong
                  cspF_reflex_eq_P
                  (cspF_fsfF_Rep_int_choice_com_eqF
                    (X := A1 ∩ X)
                    (SPf := fun a => proc.Hiding (Pf1 a) X)))
                cspF_fsfF_Int_choice_eqF
            simpa [SP_step_Hiding_def, Pfun_Hiding_def, Pdiv, Rhide, SRhide] using
              (cspF_trans_left_eq hHideStep hIntCong)
        | inr hQ1 =>
            subst hQ1
            by_cases hEmpty : A1 ∩ X = ∅
            · have hHideUnit :
                  eqFfix (proc.Hiding ((proc.Ext_pre_choice A1 Pf1) [+] (proc.STOP : proc p α)) X)
                    (proc.Hiding (proc.Ext_pre_choice A1 Pf1) X) :=
                cspF_Hiding_cong rfl cspF_Ext_choice_unit_r
              have hHideStep :
                  eqFfix (proc.Hiding (proc.Ext_pre_choice A1 Pf1) X)
                    (proc.Ext_pre_choice A1 (fun a => proc.Hiding (Pf1 a) X)) := by
                simpa [procIte, hEmpty] using
                  (cspF_Hiding_step (X := X) (Y := A1) (Pf := Pf1) (M := MF))
              have hStepUnit :
                  eqFfix (proc.Ext_pre_choice A1 (fun a => proc.Hiding (Pf1 a) X))
                    ((proc.Ext_pre_choice A1 (fun a => proc.Hiding (Pf1 a) X)) [+]
                      (proc.STOP : proc p α)) :=
                cspF_sym cspF_Ext_choice_unit_r
              simpa [SP_step_Hiding_def, hEmpty, Pfun_Hiding_def] using
                (cspF_trans_left_eq hHideUnit (cspF_trans_left_eq hHideStep hStepUnit))
            · have hHideUnit :
                  eqFfix (proc.Hiding ((proc.Ext_pre_choice A1 Pf1) [+] (proc.STOP : proc p α)) X)
                    (proc.Hiding (proc.Ext_pre_choice A1 Pf1) X) :=
                cspF_Hiding_cong rfl cspF_Ext_choice_unit_r
              have hHideStep :
                  eqFfix (proc.Hiding (proc.Ext_pre_choice A1 Pf1) X)
                    ((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [>
                      Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X)) := by
                simpa [procIte, hEmpty] using
                  (cspF_Hiding_step (X := X) (Y := A1) (Pf := Pf1) (M := MF))
              have hTimeoutCong :
                  eqFfix
                    ((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [>
                      Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X))
                    ((((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [+]
                        (proc.STOP : proc p α)) [>
                      fsfF_Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X))) :=
                cspF_Timeout_cong
                  (cspF_sym cspF_Ext_choice_unit_r)
                  (cspF_fsfF_Rep_int_choice_com_eqF
                    (X := A1 ∩ X)
                    (SPf := fun a => proc.Hiding (Pf1 a) X))
              have hTimeoutSeq :
                  eqFfix
                    ((((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [+]
                        (proc.STOP : proc p α)) [>
                      fsfF_Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X)))
                    ((((proc.Ext_pre_choice (A1 \ X) (fun a => proc.Hiding (Pf1 a) X)) [+]
                        (proc.STOP : proc p α)) [>seq
                      fsfF_Rep_int_choice_com (A1 ∩ X) (fun a => proc.Hiding (Pf1 a) X))) :=
                cspF_fsfF_Timeout_eqF
              simpa [SP_step_Hiding_def, hEmpty, Pfun_Hiding_def] using
                (cspF_trans_left_eq hHideUnit
                  (cspF_trans_left_eq hHideStep
                    (cspF_trans_left_eq hTimeoutCong hTimeoutSeq)))
  · intro A1 Pf1 Q1 SPf SQf hSPQ
    by_cases hStop : Q1 = proc.STOP
    · subst hStop
      by_cases hEmpty : A1 ∩ X = ∅
      · have hExt :
            eqFfix
              ((proc.Ext_pre_choice A1 SPf) [+] (proc.STOP : proc p α))
              ((proc.Ext_pre_choice A1 SQf) [+] (proc.STOP : proc p α)) :=
          cspF_Ext_choice_cong
            (cspF_Ext_pre_choice_cong rfl (fun a ha => hSPQ a ha))
            cspF_reflex_eq_STOP
        simpa [SP_step_Hiding_def, hEmpty] using hExt
      · have hExt :
            eqFfix
              (((proc.Ext_pre_choice (A1 \ X) SPf) [+] (proc.STOP : proc p α)))
              (((proc.Ext_pre_choice (A1 \ X) SQf) [+] (proc.STOP : proc p α))) :=
          cspF_Ext_choice_cong
            (cspF_Ext_pre_choice_cong rfl (fun a ha => hSPQ a ha.1))
            cspF_reflex_eq_STOP
        have hRepRaw :
            eqFfix
              (Rep_int_choice_com (A1 ∩ X) SPf)
              (Rep_int_choice_com (A1 ∩ X) SQf) :=
          cspF_Rep_int_choice_cong_com rfl (fun a ha => hSPQ a ha.1)
        have hRep :
            eqFfix
              (fsfF_Rep_int_choice_com (A1 ∩ X) SPf)
              (fsfF_Rep_int_choice_com (A1 ∩ X) SQf) :=
          cspF_trans_left_eq
            (cspF_sym
              (cspF_fsfF_Rep_int_choice_com_eqF
                (X := A1 ∩ X) (SPf := SPf)))
            (cspF_trans_left_eq hRepRaw
              (cspF_fsfF_Rep_int_choice_com_eqF
                (X := A1 ∩ X) (SPf := SQf)))
        have hSeqL :
            eqFfix
              ((((proc.Ext_pre_choice (A1 \ X) SPf) [+] (proc.STOP : proc p α)) [>seq
                fsfF_Rep_int_choice_com (A1 ∩ X) SPf))
              ((((proc.Ext_pre_choice (A1 \ X) SPf) [+] (proc.STOP : proc p α)) [>
                fsfF_Rep_int_choice_com (A1 ∩ X) SPf)) :=
          cspF_sym cspF_fsfF_Timeout_eqF
        have hStd :
            eqFfix
              ((((proc.Ext_pre_choice (A1 \ X) SPf) [+] (proc.STOP : proc p α)) [>
                fsfF_Rep_int_choice_com (A1 ∩ X) SPf))
              ((((proc.Ext_pre_choice (A1 \ X) SQf) [+] (proc.STOP : proc p α)) [>
                fsfF_Rep_int_choice_com (A1 ∩ X) SQf)) :=
          cspF_Timeout_cong hExt hRep
        have hSeqR :
            eqFfix
              ((((proc.Ext_pre_choice (A1 \ X) SQf) [+] (proc.STOP : proc p α)) [>
                fsfF_Rep_int_choice_com (A1 ∩ X) SQf))
              ((((proc.Ext_pre_choice (A1 \ X) SQf) [+] (proc.STOP : proc p α)) [>seq
                fsfF_Rep_int_choice_com (A1 ∩ X) SQf)) :=
          cspF_fsfF_Timeout_eqF
        simpa [SP_step_Hiding_def, hEmpty] using
          (cspF_trans_left_eq hSeqL (cspF_trans_left_eq hStd hSeqR))
    · have hExt :
          eqFfix
            (((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1))
            (((proc.Ext_pre_choice (A1 \ X) SQf) [+] Q1)) :=
        cspF_Ext_choice_cong
          (cspF_Ext_pre_choice_cong rfl (fun a ha => hSPQ a ha.1))
          cspF_reflex_eq_P
      have hRepRaw :
          eqFfix
            (Rep_int_choice_com (A1 ∩ X) SPf)
            (Rep_int_choice_com (A1 ∩ X) SQf) :=
        cspF_Rep_int_choice_cong_com rfl (fun a ha => hSPQ a ha.1)
      have hRep :
          eqFfix
            (fsfF_Rep_int_choice_com (A1 ∩ X) SPf)
            (fsfF_Rep_int_choice_com (A1 ∩ X) SQf) :=
        cspF_trans_left_eq
          (cspF_sym
            (cspF_fsfF_Rep_int_choice_com_eqF
              (X := A1 ∩ X) (SPf := SPf)))
          (cspF_trans_left_eq hRepRaw
            (cspF_fsfF_Rep_int_choice_com_eqF
              (X := A1 ∩ X) (SPf := SQf)))
      have hSeqL :
          eqFfix
            (fsfF_Int_choice
              (((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1))
              (fsfF_Rep_int_choice_com (A1 ∩ X) SPf))
            ((((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1) |~|
              fsfF_Rep_int_choice_com (A1 ∩ X) SPf)) :=
        cspF_sym cspF_fsfF_Int_choice_eqF
      have hStd :
          eqFfix
            ((((proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1) |~|
              fsfF_Rep_int_choice_com (A1 ∩ X) SPf))
            ((((proc.Ext_pre_choice (A1 \ X) SQf) [+] Q1) |~|
              fsfF_Rep_int_choice_com (A1 ∩ X) SQf)) :=
        cspF_Int_choice_cong hExt hRep
      have hSeqR :
          eqFfix
            ((((proc.Ext_pre_choice (A1 \ X) SQf) [+] Q1) |~|
              fsfF_Rep_int_choice_com (A1 ∩ X) SQf))
            (fsfF_Int_choice
              (((proc.Ext_pre_choice (A1 \ X) SQf) [+] Q1))
              (fsfF_Rep_int_choice_com (A1 ∩ X) SQf)) :=
        cspF_fsfF_Int_choice_eqF
      simpa [SP_step_Hiding_def, hStop] using
        (cspF_trans_left_eq hSeqL (cspF_trans_left_eq hStd hSeqR))

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
