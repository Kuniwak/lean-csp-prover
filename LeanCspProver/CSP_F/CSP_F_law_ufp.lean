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

theorem semF_hasUFP_cms [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → hasUFP (semFfun Pf) := by
  intro hPf hguard
  subst hPf
  by_cases h : Nonempty p
  · haveI := h
    exact Banach_thm_EX (contraction_semFfun hguard)
  · haveI : IsEmpty p := not_nonempty_iff.mp h
    have hemp : ∀ F G : p → domFType α, F = G := fun F G => funext fun a => isEmptyElim a
    exact ⟨default, hemp _ _, fun y _ => hemp _ _⟩

theorem semF_UFP_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semF (proc.Proc_name p0 : proc p α) = UFP (semFfun Pf) p0 := by
  intro hPf hguard hmode; subst hPf
  have hMF : (MF : p → domFType α) = UFP (semFfun PNfun) := by
    rw [MF_def, semFfix_def, if_pos hmode]
  simp only [semF_def, semFf_Proc_name, hMF]

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

theorem MF_fixed_point_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semFfun Pf (MF : p → domFType α) = (MF : p → domFType α) := by
  intro hPf hguard hmode
  subst hPf
  by_cases h : Nonempty p
  · haveI := h
    have hMF : (MF : p → domFType α) = UFP (semFfun PNfun) := by
      rw [MF_def, semFfix_def, if_pos hmode]
    rw [hMF]; exact UFP_fp (Banach_thm_EX (contraction_semFfun hguard))
  · haveI : IsEmpty p := not_nonempty_iff.mp h
    exact funext fun a => isEmptyElim a

/- ---------*
 |  unique |
 *--------- -/

theorem ALL_cspF_unique_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
        ∀ pn, eqF (f pn) MF MF (proc.Proc_name pn : proc p α) := by
  intro hPf hguard hmode hfix pn; subst hPf
  have hg_fix : semFfun (PNfun : p → proc p α) (fun q => semF (f q)) = (fun q => semF (f q)) := by
    rw [← semF_subst_semFfun]; funext q; exact hfix q
  have hMF_fix : semFfun (PNfun : p → proc p α) MF = MF := MF_fixed_point_cms rfl hguard hmode
  have huniq : (fun q => semF (f q)) = (MF : p → domFType α) :=
    hasUFP_unique_solution (semF_hasUFP_cms rfl hguard) hg_fix hMF_fix
  rw [eqF_def, semFf_Proc_name]
  change semFf (f pn) MF = MF pn
  exact congrFun huniq pn

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

theorem ALL_cspF_unwind_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF (Pf pn) := by
  intro hPf hguard hmode pn
  subst hPf
  haveI : Nonempty p := ⟨pn⟩
  have hMF : (MF : p → domFType α) = UFP (semFfun PNfun) := by
    rw [MF_def, semFfix_def, if_pos hmode]
  have hfix : semFfun (PNfun : p → proc p α) MF = MF := by
    rw [hMF]; exact UFP_fp (Banach_thm_EX (contraction_semFfun hguard))
  rw [eqF_def, semFf_Proc_name]
  change (MF : p → domFType α) pn = semFf (PNfun pn) MF
  exact (congrFun hfix pn).symm

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

/- The Isabelle `_ALL` variants of the `fp_induct` laws differ from the plain
   ones only in using an object-level `ALL` hypothesis instead of a
   meta-level `!!`; in Lean both are `∀`, so the plain theorem below covers
   both.  (The former Lean `axiom … _ALL` here mis-translated the conclusion
   as `∀ pn, …`, which is not sound, and was used nowhere.) -/

/-  csp law  -/

theorem cspF_fp_induct_cms_ref_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refF (f p0) MF MF Q →
        (∀ p, refF ((Pf p) << f) MF MF (f p)) →
          refF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  subst hPf
  haveI : Nonempty p := ⟨p0⟩
  have hdist : ∀ x y : (p → domFType α), distance x y = distance_rs x y :=
    fun x y => ms0_rs.to_distance_rs x y
  have hconst : constructive_rs (semFfun (PNfun : p → proc p α)) :=
    contra_alpha_to_contst hdist hdist (contraction_alpha_semFfun hguard)
  have hmono : mono (semFfun (PNfun : p → proc p α)) := mono_semFfun
  set g : p → domFType α := fun q => semF (f q) with hg
  have hpre : g ≤ semFfun (PNfun : p → proc p α) g := by
    have hsub : semFfun (PNfun : p → proc p α) g = (fun q => semF ((PNfun q) << f)) := by
      rw [hg]; exact (semF_subst_semFfun).symm
    rw [hsub]; intro q
    simpa [refF_def, semF_def, hg] using hfix q
  have hfixMF : (MF : p → domFType α) = semFfun (PNfun : p → proc p α) MF :=
    (MF_fixed_point_cms rfl hguard hmode).symm
  have hle : g ≤ (MF : p → domFType α) :=
    cms_fixpoint_induction_ref (β := p → domFType α) hdist hdist hconst hmono hpre hfixMF
  simp only [refF_def, semFf_Proc_name]
  calc semFf Q MF
      ≤ semFf (f p0) MF := hp
    _ = g p0 := rfl
    _ ≤ (MF : p → domFType α) p0 := hle p0

/- (*** right ***) -/

/-  csp law  -/

theorem cspF_fp_induct_cms_ref_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refF Q MF MF (f p0) →
        (∀ p, refF (f p) MF MF ((Pf p) << f)) →
          refF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hp hfix
  subst hPf
  haveI : Nonempty p := ⟨p0⟩
  have hdist : ∀ x y : (p → domFType α), distance x y = distance_rs x y :=
    fun x y => ms0_rs.to_distance_rs x y
  have hconst : constructive_rs (semFfun (PNfun : p → proc p α)) :=
    contra_alpha_to_contst hdist hdist (contraction_alpha_semFfun hguard)
  have hmono : mono (semFfun (PNfun : p → proc p α)) := mono_semFfun
  set g : p → domFType α := fun q => semF (f q) with hg
  have hpre : semFfun (PNfun : p → proc p α) g ≤ g := by
    have hsub : semFfun (PNfun : p → proc p α) g = (fun q => semF ((PNfun q) << f)) := by
      rw [hg]; exact (semF_subst_semFfun).symm
    rw [hsub]; intro q
    simpa [refF_def, semF_def, hg] using hfix q
  have hfixMF : (MF : p → domFType α) = semFfun (PNfun : p → proc p α) MF :=
    (MF_fixed_point_cms rfl hguard hmode).symm
  have hle : (MF : p → domFType α) ≤ g :=
    cms_fixpoint_induction_rev (β := p → domFType α) hdist hdist hconst hmono hpre hfixMF
  simp only [refF_def, semFf_Proc_name]
  calc (MF : p → domFType α) p0
      ≤ g p0 := hle p0
    _ = semFf (f p0) MF := rfl
    _ ≤ semFf Q MF := hp

/- ----------- equality ----------- -/

/- (*** left ***) -/

/-  csp law  -/

theorem cspF_fp_induct_cms_eq_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqF (f p0) MF MF Q →
        (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
          eqF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  have e0 : semFf (f p0) MF = semFf Q MF := hp
  have hL : refF (proc.Proc_name p0 : proc p α) MF MF Q :=
    cspF_fp_induct_cms_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hmode (le_of_eq e0.symm) (fun q => le_of_eq (hfix q).symm)
  have hR : refF Q MF MF (proc.Proc_name p0 : proc p α) :=
    cspF_fp_induct_cms_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hmode (le_of_eq e0) (fun q => le_of_eq (hfix q))
  exact le_antisymm hR hL

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

/- Isabelle-name aliases for the `_ALL` variants: their only difference is an
   object-level `ALL` induction hypothesis instead of the meta-level `!!`,
   which in Lean is the same `∀`, so they coincide with the plain laws. -/
alias cspF_fp_induct_cms_ref_left_ALL := cspF_fp_induct_cms_ref_left
alias cspF_fp_induct_cms_ref_right_ALL := cspF_fp_induct_cms_ref_right
alias cspF_fp_induct_cms_eq_left_ALL := cspF_fp_induct_cms_eq_left

end
