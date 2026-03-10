           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               February 2005               |
            |                   June 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_fp
import LeanCspProver.CSP_F.CSP_F_law_ufp

open fpmode

noncomputable section

/-
(*****************************************************************

         1. cpo fixed point theory in CSP-Prover
         2.
         3.
         4.

 *****************************************************************)
-/

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq` or         -/
/-  `Inf_image_eq`, so there is nothing to disable or re-enable here.   -/

/- =======================================*
 |                                        |
 |                  CPO                   |
 |                                        |
 *======================================= -/

/- -------------*
 |  existency  |
 *------------- -/

theorem semF_hasLFP_cpo [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → hasLFP (semFfun Pf) := by
  intro hPf
  subst hPf
  exact Tarski_thm_EX (f := semFfun PNfun) continuous_semFfun

theorem semF_LFP_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      semF (proc.Proc_name p0 : proc p α) = LFP (semFfun Pf) p0 := by
  intro hPf hmode
  subst hPf
  rcases hmode with hmode | hmode
  · simp [semF_def, semFf_Proc_name, MF_def, semFfix_def, hmode]
  · simp [semF_def, semFf_Proc_name, MF_def, semFfix_def, hmode]

theorem semF_LFP_fun_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      (fun pn => semF (proc.Proc_name pn : proc p α)) = LFP (semFfun Pf) := by
  intro hPf hmode
  funext pn
  exact semF_LFP_cpo (Pf := Pf) (p0 := pn) hPf hmode

/- ---------*
 |    MF   |
 *--------- -/

theorem MF_fixed_point_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      semFfun Pf (MF : p → domFType α) = (MF : p → domFType α) := by
  intro hPf hmode
  subst hPf
  rw [MF_def]
  rcases hmode with hmode | hmode
  · simp [semFfix_def, hmode, LFP_fp (semF_hasLFP_cpo (Pf := PNfun) rfl)]
  · simp [semFfix_def, hmode, LFP_fp (semF_hasLFP_cpo (Pf := PNfun) rfl)]

/- ---------*
 | greatest |
 *--------- -/

axiom ALL_cspF_greatest_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} :
    Pf = PNfun → FPmode = CPOmode →
      (∀ pn, eqF ((Pf pn) << f) MF MF (f pn)) →
        ∀ pn, refF (f pn) MF MF (proc.Proc_name pn : proc p α)

theorem cspF_greatest_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {p0 : p} :
    Pf = PNfun → FPmode = CPOmode →
      (∀ pn, eqF ((Pf pn) << f) MF MF (f pn)) →
        refF (f p0) MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hgreatest
  exact ALL_cspF_greatest_cpo (Pf := Pf) (f := f) hPf hmode hgreatest p0

/- ------------------------------------------------------*
 |                                                      |
 |          Fixpoint unwind (CSP-Prover rule)           |
 |                                                      |
 *------------------------------------------------------ -/

axiom ALL_cspF_unwind_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF (Pf pn)

/-  csp law  -/

theorem cspF_unwind_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqF (proc.Proc_name p0 : proc p α) MF MF (Pf p0) := by
  intro hPf hmode
  exact ALL_cspF_unwind_cpo (Pf := Pf) hPf hmode p0

/- ------------------------------------------------------*
 |                                                      |
 |    fixed point inducntion (CSP-Prover intro rule)    |
 |                                                      |
 *------------------------------------------------------ -/

/- (*** right ***) -/

axiom cspF_fp_induct_cpo_ref_right_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      refF Q MF MF (f p0) →
        (∀ p, refF (f p) MF MF ((Pf p) << f)) →
          ∀ pn, refF Q MF MF (proc.Proc_name pn : proc p α)

/-  csp law  -/

theorem cspF_fp_induct_cpo_ref_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      refF Q MF MF (f p0) →
        (∀ p, refF (f p) MF MF ((Pf p) << f)) →
          refF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hQ hfix
  have hall :
      ∀ pn, refF Q MF MF (proc.Proc_name pn : proc p α) :=
    cspF_fp_induct_cpo_ref_right_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hmode hQ hfix
  exact hall p0

/- The Isabelle theorem bundle `cspF_fp_induct_cpo_right` is represented by
   `cspF_fp_induct_cpo_ref_right`. -/

/- =======================================*
 |                                        |
 |              LFP <--> UFP              |
 |                                        |
 |                MIXmode                 |
 |                                        |
 *======================================= -/

theorem semF_guarded_LFP_UFP [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf →
      LFP (semFfun Pf) = UFP (semFfun Pf) := by
  intro hPf hguard
  exact hasUFP_LFP_UFP (semF_hasUFP_cms (Pf := Pf) hPf hguard)

/- ----------- refinement ----------- -/

/- (*** left ***) -/

axiom cspF_fp_induct_mix_ref_left_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      refF (f p0) MF MF Q →
        (∀ p, refF ((Pf p) << f) MF MF (f p)) →
          ∀ pn, refF (proc.Proc_name pn : proc p α) MF MF Q

/-  csp law  -/

theorem cspF_fp_induct_mix_ref_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      refF (f p0) MF MF Q →
        (∀ p, refF ((Pf p) << f) MF MF (f p)) →
          refF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, refF (proc.Proc_name pn : proc p α) MF MF Q :=
    cspF_fp_induct_mix_ref_left_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

/- ----------- equality ----------- -/

/- (*** left ***) -/

axiom cspF_fp_induct_mix_eq_left_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      eqF (f p0) MF MF Q →
        (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
          ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF Q

/-  csp law  -/

theorem cspF_fp_induct_mix_eq_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      eqF (f p0) MF MF Q →
        (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
          eqF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF Q :=
    cspF_fp_induct_mix_eq_left_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

theorem cspF_fp_induct_mix_eq_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      eqF Q MF MF (f p0) →
        (∀ p, eqF (f p) MF MF ((Pf p) << f)) →
          eqF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hQ hfix
  apply cspF_sym
  apply cspF_fp_induct_mix_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
  · exact hPf
  · exact hguard
  · exact hmode
  · exact cspF_sym hQ
  · intro p
    exact cspF_sym (hfix p)

/- The Isabelle theorem bundle `cspF_fp_induct_mix_left` is represented by
   `cspF_fp_induct_mix_ref_left` and `cspF_fp_induct_mix_eq_left`. -/

/- The Isabelle theorem bundle `cspF_fp_induct_mix_right` is represented by
   `cspF_fp_induct_cpo_ref_right` and `cspF_fp_induct_mix_eq_right`. -/

/- =======================================*
 |                                        |
 |          mixing CPOmode and CMSmode    |
 |                                        |
 *======================================= -/

theorem cspF_unwind [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
        eqF (proc.Proc_name p0 : proc p α) MF MF (Pf p0) := by
  intro hPf hmode
  rcases hmode with hCPO | hrest
  · exact cspF_unwind_cpo (Pf := Pf) (p0 := p0) hPf (Or.inl hCPO)
  · rcases hrest with hCMS | hMIX
    · exact cspF_unwind_cms (Pf := Pf) (p0 := p0) hPf hCMS.2 hCMS.1
    · exact cspF_unwind_cpo (Pf := Pf) (p0 := p0) hPf (Or.inr hMIX)

theorem cspF_fp_induct_ref_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
        refF Q MF MF (f p0) →
          (∀ p, refF (f p) MF MF ((Pf p) << f)) →
            refF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hQ hfix
  rcases hmode with hCPO | hrest
  · exact cspF_fp_induct_cpo_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf (Or.inl hCPO) hQ hfix
  · rcases hrest with hCMS | hMIX
    · exact cspF_fp_induct_cms_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
        hPf hCMS.2 hCMS.1 hQ hfix
    · exact cspF_fp_induct_cpo_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
        hPf (Or.inr hMIX) hQ hfix

theorem cspF_fp_induct_ref_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CMSmode ∨ FPmode = MIXmode) →
        guardedfun Pf →
          refF (f p0) MF MF Q →
            (∀ p, refF ((Pf p) << f) MF MF (f p)) →
              refF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hmode hguard hp hfix
  rcases hmode with hCMS | hMIX
  · exact cspF_fp_induct_cms_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hCMS hp hfix
  · exact cspF_fp_induct_mix_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hMIX hp hfix

theorem cspF_fp_induct_eq_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CMSmode ∨ FPmode = MIXmode) →
        guardedfun Pf →
          eqF (f p0) MF MF Q →
            (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
              eqF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hmode hguard hp hfix
  rcases hmode with hCMS | hMIX
  · exact cspF_fp_induct_cms_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hCMS hp hfix
  · exact cspF_fp_induct_mix_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hMIX hp hfix

theorem cspF_fp_induct_eq_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CMSmode ∨ FPmode = MIXmode) →
        guardedfun Pf →
          eqF Q MF MF (f p0) →
            (∀ p, eqF (f p) MF MF ((Pf p) << f)) →
              eqF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hguard hQ hfix
  rcases hmode with hCMS | hMIX
  · exact cspF_fp_induct_cms_eq_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hCMS hQ hfix
  · exact cspF_fp_induct_mix_eq_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hMIX hQ hfix

/- The Isabelle theorem bundle `cspF_fp_induct_right` is represented by
   `cspF_fp_induct_ref_right` and `cspF_fp_induct_eq_right`. -/

/- The Isabelle theorem bundle `cspF_fp_induct_left` is represented by
   `cspF_fp_induct_ref_left` and `cspF_fp_induct_eq_left`. -/

end
