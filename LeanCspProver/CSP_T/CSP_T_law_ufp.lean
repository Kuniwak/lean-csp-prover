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

import LeanCspProver.CSP_T.CSP_T_continuous
import LeanCspProver.CSP_T.CSP_T_contraction
import LeanCspProver.CSP_T.CSP_T_mono
import LeanCspProver.CSP_T.CSP_T_law_decompo

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

axiom semT_hasUFP_cms [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → hasUFP (semTfun Pf)

axiom semT_UFP_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semT (proc.Proc_name p0 : proc p α) = UFP (semTfun Pf) p0

theorem semT_UFP_fun_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (fun pn => semT (proc.Proc_name pn : proc p α)) = UFP (semTfun Pf) := by
  intro hPf hguard hmode
  funext pn
  exact semT_UFP_cms (Pf := Pf) (p0 := pn) hPf hguard hmode

/- ---------*
 |    MT   |
 *--------- -/

axiom MT_fixed_point_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semTfun Pf (MT : p → domTType α) = (MT : p → domTType α)

/- ---------*
 |  unique |
 *--------- -/

axiom ALL_cspT_unique_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
        ∀ pn, eqT (f pn) MT MT (proc.Proc_name pn : proc p α)

theorem cspT_unique_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
        eqT (f p0) MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hfix
  exact ALL_cspT_unique_cms (Pf := Pf) (f := f) hPf hguard hmode hfix p0

/- ------------------------------------------------------*
 |                                                      |
 |          Fixpoint unwind (CSP-Prover rule)           |
 |                                                      |
 *------------------------------------------------------ -/

axiom ALL_cspT_unwind_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      ∀ pn, eqT (proc.Proc_name pn : proc p α) MT MT (Pf pn)

/-  csp law  -/

theorem cspT_unwind_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqT (proc.Proc_name p0 : proc p α) MT MT (Pf p0) := by
  intro hPf hguard hmode
  exact ALL_cspT_unwind_cms (Pf := Pf) hPf hguard hmode p0

/- ------------------------------------------------------*
 |                                                      |
 |    fixed point inducntion (CSP-Prover intro rule)    |
 |                                                      |
 *------------------------------------------------------ -/

/- ----------- refinement ----------- -/

/- (*** left ***) -/

axiom cspT_fp_induct_cms_ref_left_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refT (f p0) MT MT Q →
        (∀ p, refT ((Pf p) << f) MT MT (f p)) →
          ∀ pn, refT (proc.Proc_name pn : proc p α) MT MT Q

/-  csp law  -/

theorem cspT_fp_induct_cms_ref_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refT (f p0) MT MT Q →
        (∀ p, refT ((Pf p) << f) MT MT (f p)) →
          refT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, refT (proc.Proc_name pn : proc p α) MT MT Q :=
    cspT_fp_induct_cms_ref_left_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

/- (*** right ***) -/

axiom cspT_fp_induct_cms_ref_right_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refT Q MT MT (f p0) →
        (∀ p, refT (f p) MT MT ((Pf p) << f)) →
          ∀ pn, refT Q MT MT (proc.Proc_name pn : proc p α)

/-  csp law  -/

theorem cspT_fp_induct_cms_ref_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refT Q MT MT (f p0) →
        (∀ p, refT (f p) MT MT ((Pf p) << f)) →
          refT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, refT Q MT MT (proc.Proc_name pn : proc p α) :=
    cspT_fp_induct_cms_ref_right_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

/- ----------- equality ----------- -/

/- (*** left ***) -/

axiom cspT_fp_induct_cms_eq_left_ALL [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqT (f p0) MT MT Q →
        (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
          ∀ pn, eqT (proc.Proc_name pn : proc p α) MT MT Q

/-  csp law  -/

theorem cspT_fp_induct_cms_eq_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqT (f p0) MT MT Q →
        (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
          eqT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hguard hmode hp hfix
  have hall :
      ∀ pn, eqT (proc.Proc_name pn : proc p α) MT MT Q :=
    cspT_fp_induct_cms_eq_left_ALL (Pf := Pf) (f := f) (Q := Q)
      (p0 := p0) hPf hguard hmode hp hfix
  exact hall p0

theorem cspT_fp_induct_cms_eq_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqT Q MT MT (f p0) →
        (∀ p, eqT (f p) MT MT ((Pf p) << f)) →
          eqT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hQ hfix
  apply cspT_sym
  apply cspT_fp_induct_cms_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
  · exact hPf
  · exact hguard
  · exact hmode
  · exact cspT_sym hQ
  · intro p
    exact cspT_sym (hfix p)

/- The Isabelle theorem bundle `cspT_fp_induct_cms_left` is represented by
   `cspT_fp_induct_cms_ref_left` and `cspT_fp_induct_cms_eq_left`. -/

/- The Isabelle theorem bundle `cspT_fp_induct_cms_right` is represented by
   `cspT_fp_induct_cms_ref_right` and `cspT_fp_induct_cms_eq_right`. -/

end
