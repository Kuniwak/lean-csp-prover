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

theorem semT_hasUFP_cms [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → hasUFP (semTfun Pf) := by
  intro hPf hguard; subst hPf
  by_cases h : Nonempty p
  · haveI := h; exact Banach_thm_EX (contraction_semTfun hguard)
  · haveI : IsEmpty p := not_nonempty_iff.mp h
    have hemp : ∀ F G : p → domTType α, F = G := fun F G => funext fun a => isEmptyElim a
    exact ⟨default, hemp _ _, fun y _ => hemp _ _⟩

theorem semT_UFP_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semT (proc.Proc_name p0 : proc p α) = UFP (semTfun Pf) p0 := by
  intro hPf hguard hmode; subst hPf
  have hMT : (MT : p → domTType α) = UFP (semTfun PNfun) := by
    rw [MT_def, semTfix_def, if_pos hmode]
  change (MT : p → domTType α) p0 = UFP (semTfun PNfun) p0
  rw [hMT]

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

theorem MT_fixed_point_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semTfun Pf (MT : p → domTType α) = (MT : p → domTType α) := by
  intro hPf hguard hmode; subst hPf
  by_cases h : Nonempty p
  · haveI := h
    have hMT : (MT : p → domTType α) = UFP (semTfun PNfun) := by
      rw [MT_def, semTfix_def, if_pos hmode]
    rw [hMT]; exact UFP_fp (Banach_thm_EX (contraction_semTfun hguard))
  · haveI : IsEmpty p := not_nonempty_iff.mp h
    exact funext fun a => isEmptyElim a

/- ---------*
 |  unique |
 *--------- -/

theorem ALL_cspT_unique_cms [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
        ∀ pn, eqT (f pn) MT MT (proc.Proc_name pn : proc p α) := by
  intro hPf hguard hmode hfix pn; subst hPf
  have hg_fix : semTfun (PNfun : p → proc p α) (fun q => semT (f q)) = (fun q => semT (f q)) := by
    rw [← semT_subst_semTfun]; funext q; exact hfix q
  have hMT_fix : semTfun (PNfun : p → proc p α) MT = MT := MT_fixed_point_cms rfl hguard hmode
  have huniq : (fun q => semT (f q)) = (MT : p → domTType α) :=
    hasUFP_unique_solution (semT_hasUFP_cms rfl hguard) hg_fix hMT_fix
  rw [eqT_def]
  change semTf (f pn) MT = (MT : p → domTType α) pn
  exact congrFun huniq pn

theorem cspT_unique_cms [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {p0 : p} :
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

theorem ALL_cspT_unwind_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      ∀ pn, eqT (proc.Proc_name pn : proc p α) MT MT (Pf pn) := by
  intro hPf hguard hmode pn; subst hPf
  haveI : Nonempty p := ⟨pn⟩
  have hMT : (MT : p → domTType α) = UFP (semTfun PNfun) := by
    rw [MT_def, semTfix_def, if_pos hmode]
  have hfix : semTfun (PNfun : p → proc p α) MT = MT := by
    rw [hMT]; exact UFP_fp (Banach_thm_EX (contraction_semTfun hguard))
  rw [eqT_def]
  change (MT : p → domTType α) pn = semTf (PNfun pn) MT
  exact (congrFun hfix pn).symm

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

/- The Isabelle `_ALL` variants of the `fp_induct` laws differ from the plain
   ones only in using an object-level `ALL` hypothesis instead of a
   meta-level `!!`; in Lean both are `∀`, so the plain theorem below covers
   both.  (The former Lean `axiom … _ALL` here mis-translated the conclusion
   as `∀ pn, …`, which is not sound, and was used nowhere.) -/

/-  csp law  -/

theorem cspT_fp_induct_cms_ref_left [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refT (f p0) MT MT Q →
        (∀ p, refT ((Pf p) << f) MT MT (f p)) →
          refT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hguard hmode hp hfix
  subst hPf
  haveI : Nonempty p := ⟨p0⟩
  have hdist : ∀ x y : (p → domTType α), distance x y = distance_rs x y :=
    fun x y => ms0_rs.to_distance_rs x y
  have hconst : constructive_rs (semTfun (PNfun : p → proc p α)) :=
    contra_alpha_to_contst hdist hdist (contraction_alpha_semTfun hguard)
  have hmono : mono (semTfun (PNfun : p → proc p α)) := mono_semTf
  set g : p → domTType α := fun q => semT (f q) with hg
  have hpre : g ≤ semTfun (PNfun : p → proc p α) g := by
    have hsub : semTfun (PNfun : p → proc p α) g = (fun q => semT ((PNfun q) << f)) := by
      rw [hg]; exact (semT_subst_semTfun).symm
    rw [hsub]; intro q
    simpa [refT_def, semT_def, hg] using hfix q
  have hfixMT : (MT : p → domTType α) = semTfun (PNfun : p → proc p α) MT :=
    (MT_fixed_point_cms rfl hguard hmode).symm
  have hle : g ≤ (MT : p → domTType α) :=
    cms_fixpoint_induction_ref (β := p → domTType α) hdist hdist hconst hmono hpre hfixMT
  rw [refT_def]
  change semTf Q MT ≤ (MT : p → domTType α) p0
  calc semTf Q MT
      ≤ semTf (f p0) MT := hp
    _ = g p0 := rfl
    _ ≤ (MT : p → domTType α) p0 := hle p0

/- (*** right ***) -/

/-  csp law  -/

theorem cspT_fp_induct_cms_ref_right [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      refT Q MT MT (f p0) →
        (∀ p, refT (f p) MT MT ((Pf p) << f)) →
          refT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hp hfix
  subst hPf
  haveI : Nonempty p := ⟨p0⟩
  have hdist : ∀ x y : (p → domTType α), distance x y = distance_rs x y :=
    fun x y => ms0_rs.to_distance_rs x y
  have hconst : constructive_rs (semTfun (PNfun : p → proc p α)) :=
    contra_alpha_to_contst hdist hdist (contraction_alpha_semTfun hguard)
  have hmono : mono (semTfun (PNfun : p → proc p α)) := mono_semTf
  set g : p → domTType α := fun q => semT (f q) with hg
  have hpre : semTfun (PNfun : p → proc p α) g ≤ g := by
    have hsub : semTfun (PNfun : p → proc p α) g = (fun q => semT ((PNfun q) << f)) := by
      rw [hg]; exact (semT_subst_semTfun).symm
    rw [hsub]; intro q
    simpa [refT_def, semT_def, hg] using hfix q
  have hfixMT : (MT : p → domTType α) = semTfun (PNfun : p → proc p α) MT :=
    (MT_fixed_point_cms rfl hguard hmode).symm
  have hle : (MT : p → domTType α) ≤ g :=
    cms_fixpoint_induction_rev (β := p → domTType α) hdist hdist hconst hmono hpre hfixMT
  rw [refT_def]
  change (MT : p → domTType α) p0 ≤ semTf Q MT
  calc (MT : p → domTType α) p0
      ≤ g p0 := hle p0
    _ = semTf (f p0) MT := rfl
    _ ≤ semTf Q MT := hp

/- ----------- equality ----------- -/

/- (*** left ***) -/

/-  csp law  -/

theorem cspT_fp_induct_cms_eq_left [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqT (f p0) MT MT Q →
        (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
          eqT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hguard hmode hp hfix
  have e0 : semTf (f p0) MT = semTf Q MT := hp
  have hL : refT (proc.Proc_name p0 : proc p α) MT MT Q :=
    cspT_fp_induct_cms_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hmode (le_of_eq e0.symm) (fun q => le_of_eq (hfix q).symm)
  have hR : refT Q MT MT (proc.Proc_name p0 : proc p α) :=
    cspT_fp_induct_cms_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hmode (le_of_eq e0) (fun q => le_of_eq (hfix q))
  exact le_antisymm hR hL

theorem cspT_fp_induct_cms_eq_right [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
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

/- Isabelle-name aliases for the `_ALL` variants: their only difference is an
   object-level `ALL` induction hypothesis instead of the meta-level `!!`,
   which in Lean is the same `∀`, so they coincide with the plain laws. -/
alias cspT_fp_induct_cms_ref_left_ALL := cspT_fp_induct_cms_ref_left
alias cspT_fp_induct_cms_ref_right_ALL := cspT_fp_induct_cms_ref_right
alias cspT_fp_induct_cms_eq_left_ALL := cspT_fp_induct_cms_eq_left

end
