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

import LeanCspProver.CSP_T.CSP_T_law_ufp

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

theorem semT_hasLFP_cpo [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → hasLFP (semTfun Pf) := by
  intro hPf
  subst hPf
  exact Tarski_thm_EX (f := semTfun PNfun) continuous_semTfun

theorem semT_LFP_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      semT (proc.Proc_name p0 : proc p α) = LFP (semTfun Pf) p0 := by
  intro hPf hmode
  subst hPf
  rcases hmode with hmode | hmode
  · simp [semT_def, semTf_def, traces, MT_def, semTfix_def, hmode]
  · simp [semT_def, semTf_def, traces, MT_def, semTfix_def, hmode]

theorem semT_LFP_fun_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      (fun pn => semT (proc.Proc_name pn : proc p α)) = LFP (semTfun Pf) := by
  intro hPf hmode
  funext pn
  exact semT_LFP_cpo (Pf := Pf) (p0 := pn) hPf hmode

/- ---------*
 |    MT   |
 *--------- -/

theorem MT_fixed_point_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      semTfun Pf (MT : p → domTType α) = (MT : p → domTType α) := by
  intro hPf hmode
  subst hPf
  rw [MT_def]
  rcases hmode with hmode | hmode
  · simp [semTfix_def, hmode, LFP_fp (semT_hasLFP_cpo (Pf := PNfun) rfl)]
  · simp [semTfix_def, hmode, LFP_fp (semT_hasLFP_cpo (Pf := PNfun) rfl)]

/- ---------*
 | greatest |
 *--------- -/

theorem ALL_cspT_greatest_cpo [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} :
    Pf = PNfun → FPmode = CPOmode →
      (∀ pn, eqT ((Pf pn) << f) MT MT (f pn)) →
        ∀ pn, refT (f pn) MT MT (proc.Proc_name pn : proc p α) := by
  intro hPf hmode hgreat pn; subst hPf
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rw [hmode]; exact fun hc => fpmode.noConfusion hc
  have hMT : (MT : p → domTType α) = LFP (semTfun PNfun) := by
    rw [MT_def, semTfix_def, if_neg hne]
  have hg_fix : semTfun (PNfun : p → proc p α) (fun q => semT (f q)) = (fun q => semT (f q)) := by
    rw [← semT_subst_semTfun]; funext q; exact hgreat q
  have hle : LFP (semTfun (PNfun : p → proc p α)) ≤ (fun q => semT (f q)) :=
    LFP_least (semT_hasLFP_cpo rfl) hg_fix
  rw [refT_def]
  change (MT : p → domTType α) pn ≤ semTf (f pn) MT
  have hmt_le : (MT : p → domTType α) ≤ (fun q => semT (f q)) := hMT ▸ hle
  exact hmt_le pn

theorem cspT_greatest_cpo [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {p0 : p} :
    Pf = PNfun → FPmode = CPOmode →
      (∀ pn, eqT ((Pf pn) << f) MT MT (f pn)) →
        refT (f p0) MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hgreatest
  exact ALL_cspT_greatest_cpo (Pf := Pf) (f := f) hPf hmode hgreatest p0

/- ------------------------------------------------------*
 |                                                      |
 |          Fixpoint unwind (CSP-Prover rule)          |
 |                                                      |
 *------------------------------------------------------ -/

theorem ALL_cspT_unwind_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      ∀ pn, eqT (proc.Proc_name pn : proc p α) MT MT (Pf pn) := by
  intro hPf hmode pn; subst hPf
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rcases hmode with h | h <;> rw [h] <;> exact fun hc => fpmode.noConfusion hc
  have hMT : (MT : p → domTType α) = LFP (semTfun PNfun) := by
    rw [MT_def, semTfix_def, if_neg hne]
  have hfix : semTfun (PNfun : p → proc p α) MT = MT := by
    rw [hMT]; exact LFP_fp (semT_hasLFP_cpo rfl)
  rw [eqT_def]
  change (MT : p → domTType α) pn = semTf (PNfun pn) MT
  exact (congrFun hfix pn).symm

/-  csp law  -/

theorem cspT_unwind_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqT (proc.Proc_name p0 : proc p α) MT MT (Pf p0) := by
  intro hPf hmode
  exact ALL_cspT_unwind_cpo (Pf := Pf) hPf hmode p0

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

theorem cspT_fp_induct_cpo_ref_right [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      refT Q MT MT (f p0) →
        (∀ p, refT (f p) MT MT ((Pf p) << f)) →
          refT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hp hfix
  subst hPf
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rcases hmode with h | h <;> rw [h] <;> exact fun hc => fpmode.noConfusion hc
  have hMT : (MT : p → domTType α) = LFP (semTfun PNfun) := by
    rw [MT_def, semTfix_def, if_neg hne]
  have hcont : continuous (semTfun (PNfun : p → proc p α)) := continuous_semTfun
  set g : p → domTType α := fun q => semT (f q) with hg
  have hpre : semTfun (PNfun : p → proc p α) g ≤ g := by
    have hsub : semTfun (PNfun : p → proc p α) g = (fun q => semT ((PNfun q) << f)) := by
      rw [hg]; exact (semT_subst_semTfun).symm
    rw [hsub]; intro q
    simpa [refT_def, semT_def, hg] using hfix q
  have hle : LFP (semTfun (PNfun : p → proc p α)) ≤ g := cpo_fixpoint_induction_rev hcont hpre
  rw [refT_def]
  change (MT : p → domTType α) p0 ≤ semTf Q MT
  calc (MT : p → domTType α) p0
      = LFP (semTfun (PNfun : p → proc p α)) p0 := by rw [hMT]
    _ ≤ g p0 := hle p0
    _ = semTf (f p0) MT := rfl
    _ ≤ semTf Q MT := hp

/- The Isabelle theorem bundle `cspT_fp_induct_cpo_right` is represented by
   `cspT_fp_induct_cpo_ref_right`. -/

/- =======================================*
 |                                        |
 |              LFP <--> UFP              |
 |                                        |
 |                MIXmode                 |
 |                                        |
 *======================================= -/

theorem semT_guarded_LFP_UFP [HasPNfun p α]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf →
      LFP (semTfun Pf) = UFP (semTfun Pf) := by
  intro hPf hguard
  exact hasUFP_LFP_UFP (semT_hasUFP_cms (Pf := Pf) hPf hguard)

/- ----------- refinement ----------- -/

/- (*** left ***) -/

/-  csp law  -/

theorem cspT_fp_induct_mix_ref_left [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      refT (f p0) MT MT Q →
        (∀ p, refT ((Pf p) << f) MT MT (f p)) →
          refT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hguard hmode hp hfix
  subst hPf
  haveI : Nonempty p := ⟨p0⟩
  have hne : (FPmode : fpmode) ≠ fpmode.CMSmode := by
    rw [hmode]; exact fun hc => fpmode.noConfusion hc
  have hMT : (MT : p → domTType α) = LFP (semTfun PNfun) := by
    rw [MT_def, semTfix_def, if_neg hne]
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
  have hfixMT : (MT : p → domTType α) = semTfun (PNfun : p → proc p α) MT := by
    rw [hMT]; exact (LFP_fp (Tarski_thm_EX continuous_semTfun)).symm
  have hle : g ≤ (MT : p → domTType α) :=
    cms_fixpoint_induction_ref (β := p → domTType α) hdist hdist hconst hmono hpre hfixMT
  rw [refT_def]
  change semTf Q MT ≤ (MT : p → domTType α) p0
  calc semTf Q MT
      ≤ semTf (f p0) MT := hp
    _ = g p0 := rfl
    _ ≤ (MT : p → domTType α) p0 := hle p0

/- ----------- equality ----------- -/

/- (*** left ***) -/

/-  csp law  -/

theorem cspT_fp_induct_mix_eq_left [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      eqT (f p0) MT MT Q →
        (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
          eqT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hguard hmode hp hfix
  have e0 : semTf (f p0) MT = semTf Q MT := hp
  have hL : refT (proc.Proc_name p0 : proc p α) MT MT Q :=
    cspT_fp_induct_mix_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hmode (le_of_eq e0.symm) (fun q => le_of_eq (hfix q).symm)
  have hR : refT Q MT MT (proc.Proc_name p0 : proc p α) :=
    cspT_fp_induct_cpo_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf (Or.inr hmode) (le_of_eq e0) (fun q => le_of_eq (hfix q))
  exact le_antisymm hR hL

theorem cspT_fp_induct_mix_eq_right [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = MIXmode →
      eqT Q MT MT (f p0) →
        (∀ p, eqT (f p) MT MT ((Pf p) << f)) →
          eqT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hguard hmode hQ hfix
  apply cspT_sym
  apply cspT_fp_induct_mix_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
  · exact hPf
  · exact hguard
  · exact hmode
  · exact cspT_sym hQ
  · intro p
    exact cspT_sym (hfix p)

/- The Isabelle theorem bundle `cspT_fp_induct_mix_left` is represented by
   `cspT_fp_induct_mix_ref_left` and `cspT_fp_induct_mix_eq_left`. -/

/- The Isabelle theorem bundle `cspT_fp_induct_mix_right` is represented by
   `cspT_fp_induct_cpo_ref_right` and `cspT_fp_induct_mix_eq_right`. -/

/- =======================================*
 |                                        |
 |          mixing CPOmode and CMSmode    |
 |                                        |
 *======================================= -/

theorem cspT_unwind [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
        eqT (proc.Proc_name p0 : proc p α) MT MT (Pf p0) := by
  intro hPf hmode
  rcases hmode with hCPO | hrest
  · exact cspT_unwind_cpo (Pf := Pf) (p0 := p0) hPf (Or.inl hCPO)
  · rcases hrest with hCMS | hMIX
    · exact cspT_unwind_cms (Pf := Pf) (p0 := p0) hPf hCMS.2 hCMS.1
    · exact cspT_unwind_cpo (Pf := Pf) (p0 := p0) hPf (Or.inr hMIX)

theorem cspT_fp_induct_ref_right [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
        refT Q MT MT (f p0) →
          (∀ p, refT (f p) MT MT ((Pf p) << f)) →
            refT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hQ hfix
  rcases hmode with hCPO | hrest
  · exact cspT_fp_induct_cpo_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf (Or.inl hCPO) hQ hfix
  · rcases hrest with hCMS | hMIX
    · exact cspT_fp_induct_cms_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
        hPf hCMS.2 hCMS.1 hQ hfix
    · exact cspT_fp_induct_cpo_ref_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
        hPf (Or.inr hMIX) hQ hfix

theorem cspT_fp_induct_ref_left [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CMSmode ∨ FPmode = MIXmode) →
        guardedfun Pf →
          refT (f p0) MT MT Q →
            (∀ p, refT ((Pf p) << f) MT MT (f p)) →
              refT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hmode hguard hp hfix
  rcases hmode with hCMS | hMIX
  · exact cspT_fp_induct_cms_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hCMS hp hfix
  · exact cspT_fp_induct_mix_ref_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hMIX hp hfix

theorem cspT_fp_induct_eq_left [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CMSmode ∨ FPmode = MIXmode) →
        guardedfun Pf →
          eqT (f p0) MT MT Q →
            (∀ p, eqT ((Pf p) << f) MT MT (f p)) →
              eqT (proc.Proc_name p0 : proc p α) MT MT Q := by
  intro hPf hmode hguard hp hfix
  rcases hmode with hCMS | hMIX
  · exact cspT_fp_induct_cms_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hCMS hp hfix
  · exact cspT_fp_induct_mix_eq_left (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hMIX hp hfix

theorem cspT_fp_induct_eq_right [HasPNfun p α] [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {f : p → proc q α} {Q : proc q α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CMSmode ∨ FPmode = MIXmode) →
        guardedfun Pf →
          eqT Q MT MT (f p0) →
            (∀ p, eqT (f p) MT MT ((Pf p) << f)) →
              eqT Q MT MT (proc.Proc_name p0 : proc p α) := by
  intro hPf hmode hguard hQ hfix
  rcases hmode with hCMS | hMIX
  · exact cspT_fp_induct_cms_eq_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hCMS hQ hfix
  · exact cspT_fp_induct_mix_eq_right (Pf := Pf) (f := f) (Q := Q) (p0 := p0)
      hPf hguard hMIX hQ hfix

/- The Isabelle theorem bundle `cspT_fp_induct_right` is represented by
   `cspT_fp_induct_ref_right` and `cspT_fp_induct_eq_right`. -/

/- The Isabelle theorem bundle `cspT_fp_induct_left` is represented by
   `cspT_fp_induct_ref_left` and `cspT_fp_induct_eq_left`. -/

/- Isabelle-name aliases for the `_ALL` variants: their only difference is an
   object-level `ALL` induction hypothesis instead of the meta-level `!!`,
   which in Lean is the same `∀`, so they coincide with the plain laws. -/
alias cspT_fp_induct_cpo_ref_right_ALL := cspT_fp_induct_cpo_ref_right
alias cspT_fp_induct_mix_ref_left_ALL := cspT_fp_induct_mix_ref_left
alias cspT_fp_induct_mix_eq_left_ALL := cspT_fp_induct_mix_eq_left

end
