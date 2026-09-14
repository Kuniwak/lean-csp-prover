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

theorem ALL_cspF_greatest_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} :
    Pf = PNfun → FPmode = CPOmode →
      (∀ pn, eqF ((Pf pn) << f) MF MF (f pn)) →
        ∀ pn, refF (f pn) MF MF (proc.Proc_name pn : proc p α) := by
  intro hPf hmode hgreat pn; subst hPf
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rw [hmode]; exact fun hc => fpmode.noConfusion hc
  have hMF : (MF : p → domFType α) = LFP (semFfun PNfun) := by
    rw [MF_def, semFfix_def, if_neg hne]
  have hg_fix : semFfun (PNfun : p → proc p α) (fun q => semF (f q)) = (fun q => semF (f q)) := by
    rw [← semF_subst_semFfun]; funext q; exact hgreat q
  have hle : LFP (semFfun (PNfun : p → proc p α)) ≤ (fun q => semF (f q)) :=
    LFP_least (semF_hasLFP_cpo rfl) hg_fix
  rw [refF_def, semFf_Proc_name]
  change (MF : p → domFType α) pn ≤ semFf (f pn) MF
  have hmf_le : (MF : p → domFType α) ≤ (fun q => semF (f q)) := hMF ▸ hle
  exact hmf_le pn

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

theorem ALL_cspF_unwind_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      ∀ pn, eqF (proc.Proc_name pn : proc p α) MF MF (Pf pn) := by
  intro hPf hmode pn; subst hPf
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rcases hmode with h | h <;> rw [h] <;> exact fun hc => fpmode.noConfusion hc
  have hMF : (MF : p → domFType α) = LFP (semFfun PNfun) := by
    rw [MF_def, semFfix_def, if_neg hne]
  have hfix : semFfun (PNfun : p → proc p α) MF = MF := by
    rw [hMF]; exact LFP_fp (semF_hasLFP_cpo rfl)
  rw [eqF_def, semFf_Proc_name]
  change (MF : p → domFType α) pn = semFf (PNfun pn) MF
  exact (congrFun hfix pn).symm

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

/- The Isabelle `_ALL` variants of the `fp_induct` laws differ from the plain
   ones only in using an object-level `ALL` hypothesis instead of a
   meta-level `!!`; in Lean both are `∀`, so the plain theorem below covers
   both.  (The former Lean `axiom … _ALL` here mis-translated the conclusion
   as `∀ pn, …`, which is not sound, and was used nowhere.) -/

/-  csp law  -/

theorem cspF_fp_induct_cpo_ref_right [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      refF Q MF MF (f p0) →
        (∀ p, refF (f p) MF MF ((Pf p) << f)) →
          refF Q MF MF (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hp hfix
  subst hPf
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rcases hmode with h | h <;> rw [h] <;> exact fun hc => fpmode.noConfusion hc
  have hMF : (MF : p → domFType α) = LFP (semFfun PNfun) := by
    rw [MF_def, semFfix_def, if_neg hne]
  have hcont : continuous (semFfun (PNfun : p → proc p α)) := continuous_semFfun
  set g : p → domFType α := fun q => semF (f q) with hg
  have hpre : semFfun (PNfun : p → proc p α) g ≤ g := by
    have hsub : semFfun (PNfun : p → proc p α) g = (fun q => semF ((PNfun q) << f)) := by
      rw [hg]; exact (semF_subst_semFfun).symm
    rw [hsub]; intro q
    simpa [refF_def, semF_def, hg] using hfix q
  have hle : LFP (semFfun (PNfun : p → proc p α)) ≤ g := cpo_fixpoint_induction_rev hcont hpre
  rw [refF_def]; simp only [semFf_Proc_name]
  calc (MF : p → domFType α) p0
      = LFP (semFfun (PNfun : p → proc p α)) p0 := by rw [hMF]
    _ ≤ g p0 := hle p0
    _ = semFf (f p0) MF := rfl
    _ ≤ semFf Q MF := hp

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

/-  csp law  -/

theorem cspF_fp_induct_mix_ref_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      refF (f p0) MF MF Q →
        (∀ p, refF ((Pf p) << f) MF MF (f p)) →
          refF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  subst hPf
  haveI : Nonempty p := ⟨p0⟩
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rw [hmode]; exact fun hc => fpmode.noConfusion hc
  have hMF : (MF : p → domFType α) = LFP (semFfun PNfun) := by
    rw [MF_def, semFfix_def, if_neg hne]
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
  have hfixMF : (MF : p → domFType α) = semFfun (PNfun : p → proc p α) MF := by
    rw [hMF]; exact (LFP_fp (Tarski_thm_EX continuous_semFfun)).symm
  have hle : g ≤ (MF : p → domFType α) :=
    cms_fixpoint_induction_ref (β := p → domFType α) hdist hdist hconst hmono hpre hfixMF
  rw [refF_def]; simp only [semFf_Proc_name]
  calc semFf Q MF
      ≤ semFf (f p0) MF := hp
    _ = g p0 := rfl
    _ ≤ (MF : p → domFType α) p0 := hle p0

/- ----------- equality ----------- -/

/- (*** left ***) -/

/-  csp law  -/

theorem cspF_fp_induct_mix_eq_left [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc p α} {Q : proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      eqF (f p0) MF MF Q →
        (∀ p, eqF ((Pf p) << f) MF MF (f p)) →
          eqF (proc.Proc_name p0 : proc p α) MF MF Q := by
  intro hPf hguard hmode hp hfix
  have e0 : semFf (f p0) MF = semFf Q MF := hp
  have hL : refF (proc.Proc_name p0 : proc p α) MF MF Q :=
    cspF_fp_induct_mix_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hmode (le_of_eq e0.symm) (fun q => le_of_eq (hfix q).symm)
  have hR : refF Q MF MF (proc.Proc_name p0 : proc p α) :=
    cspF_fp_induct_cpo_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf (Or.inr hmode) (le_of_eq e0) (fun q => le_of_eq (hfix q))
  exact le_antisymm hR hL

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

/- Isabelle-name aliases for the `_ALL` variants: their only difference is an
   object-level `ALL` induction hypothesis instead of the meta-level `!!`,
   which in Lean is the same `∀`, so they coincide with the plain laws. -/
alias cspF_fp_induct_cpo_ref_right_ALL := cspF_fp_induct_cpo_ref_right
alias cspF_fp_induct_mix_ref_left_ALL := cspF_fp_induct_mix_ref_left
alias cspF_fp_induct_mix_eq_left_ALL := cspF_fp_induct_mix_eq_left

end
