           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               February 2005               |
            |                   June 2005  (modified)   |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_continuous
import LeanCspProver.CSP_F.CSP_F_contraction
import LeanCspProver.CSP_F.CSP_F_mono
import LeanCspProver.CSP_F.CSP_F_law_decompo
import LeanCspProver.CSP_T.CSP_T_law_ufp

open Function
open SumType
open fpmode

noncomputable section

/-
(*****************************************************************

         1. cms fixed point theory in CSP-Prover
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
 |                  CMS                   |
 |                                        |
 *======================================= -/

/- -------------*
 |  existency  |
 *------------- -/

axiom semF_hasUFP_cms [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → hasUFP (semFfun Pf)

axiom semF_UFP_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semF (proc.Proc_name p0 : proc p α) = UFP (semFfun Pf) p0

theorem semF_UFP_fun_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (fun pn => semF (proc.Proc_name pn : proc p α)) = UFP (semFfun Pf) := by
  intro hPf hguard hmode
  funext pn
  exact semF_UFP_cms (Pf := Pf) (p0 := pn) hPf hguard hmode

/- ---------*
 |    MF   |
 *--------- -/

axiom MF_fixed_point_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semFfun Pf (MF : p → domFType α) = (MF : p → domFType α)

/- ---------*
 |  unique |
 *--------- -/

axiom ALL_cspF_unique_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
        ∀ pn, eqF (f pn) MF MF (proc.Proc_name pn : proc p α)

theorem cspF_unique_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
        eqF (f p0) MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hfix
  exact ALL_cspF_unique_cms (Pf := Pf) (f := f) hPf hguard hmode hfix p0

/- ------------------------------------------------------*
 |                                                      |
 |          Fixpoint unwind (CSP-Prover rule)           |
 |                                                      |
 *------------------------------------------------------ -/

axiom ALL_cspF_unwind_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF (Pf pn)

/-  csp law  -/

theorem cspF_unwind_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqF (proc.Proc_name p0 : proc p α) MF MF (Pf p0) := by
  intro hPf hguard hmode
  exact ALL_cspF_unwind_cms (Pf := Pf) hPf hguard hmode p0

/- ------------------------------------------------------*
 |                                                      |
 |    fixed point inducntion (CSP-Prover intro rule)    |
 |                                                      |
 *------------------------------------------------------ -/

/- ----------- refinement ----------- -/

/- (*** left ***) -/

axiom cspF_fp_induct_cms_ref_left_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refF (f p0) MF MF Q →
        (∀ p, refF ((Pf p) << f) MF MF (f p)) →
          ∀ pn, refF (proc.Proc_name pn : proc p α) MF MF Q

/-  csp law  -/

theorem cspF_fp_induct_cms_ref_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refF (f p0) MF MF Q →
        (∀ p, refF ((Pf p) << f) MF MF (f p)) →
          refF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, refF (proc.Proc_name pn : proc p α) MF MF Q :=
    cspF_fp_induct_cms_ref_left_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

/- (*** right ***) -/

axiom cspF_fp_induct_cms_ref_right_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refF Q MF MF (f p0) →
        (∀ p, refF (f p) MF MF ((Pf p) << f)) →
          ∀ pn, refF Q MF MF (proc.Proc_name pn : proc p α)

/-  csp law  -/

theorem cspF_fp_induct_cms_ref_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refF Q MF MF (f p0) →
        (∀ p, refF (f p) MF MF ((Pf p) << f)) →
          refF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, refF Q MF MF (proc.Proc_name pn : proc p α) :=
    cspF_fp_induct_cms_ref_right_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

/- ----------- equality ----------- -/

/- (*** left ***) -/

axiom cspF_fp_induct_cms_eq_left_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqF (f p0) MF MF Q →
        (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
          ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF Q

/-  csp law  -/

theorem cspF_fp_induct_cms_eq_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqF (f p0) MF MF Q →
        (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
          eqF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF Q :=
    cspF_fp_induct_cms_eq_left_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

theorem cspF_fp_induct_cms_eq_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqF Q MF MF (f p0) →
        (∀ p, eqF (f p) MF MF ((Pf p) << f)) →
          eqF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hQ hfix
  apply cspF_sym
  apply cspF_fp_induct_cms_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
  · exact hPf
  · exact hguard
  · exact hmode
  · exact cspF_sym hQ
  · intro p
    exact cspF_sym (hfix p)

/- The Isabelle theorem bundle `cspF_fp_induct_cms_left` is represented by
   `cspF_fp_induct_cms_ref_left` and `cspF_fp_induct_cms_eq_left`. -/

/- The Isabelle theorem bundle `cspF_fp_induct_cms_right` is represented by
   `cspF_fp_induct_cms_ref_right` and `cspF_fp_induct_cms_eq_right`. -/

end
