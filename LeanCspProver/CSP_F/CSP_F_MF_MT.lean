           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                 August 2007               |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_fp

open fpmode

noncomputable section

/-
(*********************************************************
            MT = fstF o MF if fixed points exist
 *********************************************************)
-/

/- --------------*
 |      cms     |
 *-------------- -/

/- (*** fixed point ***) -/

theorem fstF_MF_fixed_point_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      semTfun Pf (fstF ∘ (MF : p → domFType α)) = (fstF ∘ (MF : p → domFType α)) := by
  intro hPf hguard hmode
  funext p0
  calc
    semTfun Pf (fstF ∘ (MF : p → domFType α)) p0
        = fstF (semFf (Pf p0) (MF : p → domFType α)) := by
            simpa using
              (semTfun_fstF_semFf (Pf := Pf) (M := (MF : p → domFType α)) (p0 := p0))
    _ = fstF (semFf (proc.Proc_name p0 : proc p α) (MF : p → domFType α)) := by
          have hEq : eqF (proc.Proc_name p0 : proc p α) MF MF (Pf p0) :=
            cspF_unwind_cms (Pf := Pf) (p0 := p0) hPf hguard hmode
          have hEqSem :
              semFf (Pf p0) (MF : p → domFType α) =
                semFf (proc.Proc_name p0 : proc p α) (MF : p → domFType α) :=
            (eqF_def (Pf p0) MF MF (proc.Proc_name p0 : proc p α)).mp (cspF_sym hEq)
          exact congrArg fstF hEqSem
    _ = fstF ((MF : p → domFType α) p0) := by
          simp [semFf_Proc_name]
    _ = (fstF ∘ (MF : p → domFType α)) p0 := rfl

/- (*** fstF o MF = MT ***) -/

theorem fstF_MF_MT_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      (fstF ∘ (MF : p → domFType α)) = (MT : p → domTType α) := by
  intro hPf hguard hmode
  exact hasUFP_unique_solution
    (semT_hasUFP_cms (Pf := Pf) hPf hguard)
    (fstF_MF_fixed_point_cms (Pf := Pf) hPf hguard hmode)
    (MT_fixed_point_cms (Pf := Pf) hPf hguard hmode)

/- --------------*
 |    least     |
 *-------------- -/

/- (*** fixed point ***) -/

theorem fstF_MF_fixed_point_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      semTfun Pf (fstF ∘ (MF : p → domFType α)) = (fstF ∘ (MF : p → domFType α)) := by
  intro hPf hmode
  funext p0
  calc
    semTfun Pf (fstF ∘ (MF : p → domFType α)) p0
        = fstF (semFf (Pf p0) (MF : p → domFType α)) := by
            simpa using
              (semTfun_fstF_semFf (Pf := Pf) (M := (MF : p → domFType α)) (p0 := p0))
    _ = fstF (semFf (proc.Proc_name p0 : proc p α) (MF : p → domFType α)) := by
          have hEq : eqF (proc.Proc_name p0 : proc p α) MF MF (Pf p0) :=
            cspF_unwind_cpo (Pf := Pf) (p0 := p0) hPf hmode
          have hEqSem :
              semFf (Pf p0) (MF : p → domFType α) =
                semFf (proc.Proc_name p0 : proc p α) (MF : p → domFType α) :=
            (eqF_def (Pf p0) MF MF (proc.Proc_name p0 : proc p α)).mp (cspF_sym hEq)
          exact congrArg fstF hEqSem
    _ = fstF ((MF : p → domFType α) p0) := by
          simp [semFf_Proc_name]
    _ = (fstF ∘ (MF : p → domFType α)) p0 := rfl

/- (*** fstF o MF = MT ***) -/

axiom MT_LFP_UnionT_cpo_lm [HasPNfun p α]
    {y : domTType α} {p0 : p} :
    (∃ x, (∃ n, x = ((semTfun PNfun)^[n]) Bot) ∧ y = x p0) ↔
      ∃ n, y = ((semTfun PNfun)^[n]) Bot p0

axiom MT_LFP_UnionT_cpo [HasPNfun p α]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun →
      LFP (semTfun Pf) p0 = UnionT {y | ∃ n, y = ((semTfun Pf)^[n]) Bot p0}

axiom fstF_MF_LFP_UnionT_cpo_lm1 [HasPNfun p α]
    {Pf : p → proc p α} {y : domTType α} {p0 : p} :
    (∃ b x,
        (∃ xa, (∃ n, xa = ((semFfun Pf)^[n]) Bot) ∧ x = xa p0) ∧
          (y, b) = Rep_domF x) ↔
      ∃ n, y = fstF (((semFfun Pf)^[n]) Bot p0)

axiom fstF_MF_LFP_UnionT_cpo_lm2 [HasPNfun p α]
    {Pf : p → proc p α} {p0 : p} :
    LFP (semFfun Pf) p0 =
      LUB_domF ((fun x : p → domFType α => x p0) '' {x | ∃ n, x = ((semFfun Pf)^[n]) Bot})

axiom fstF_MF_LFP_UnionT_cpo [HasPNfun p α]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun →
      fstF (LFP (semFfun Pf) p0) =
        UnionT {y | ∃ n, y = fstF (((semFfun Pf)^[n]) Bot p0)}

theorem iterative_fstF_semFfun_semFfun [HasPNfun p α]
    {Pf : p → proc p α} :
    ∀ n p0, fstF (((semFfun Pf)^[n]) Bot p0) = ((semTfun Pf)^[n]) Bot p0 := by
  intro n
  induction n with
  | zero =>
      intro p0
      change fstF (Bot : domFType α) = (Bot : domTType α)
      rw [bottom_domF_def, bottom_domT_def]
      simpa using
        (pairF_fstF
          (S := Abs_domT ({<>} : Set (traceType α)))
          (F := ({}f : setFType α))
          BOT_in_domF)
  | succ n ih =>
      intro p0
      have hIH :
          fstF ∘ (((semFfun Pf)^[n]) Bot) = ((semTfun Pf)^[n]) Bot := by
        funext q
        exact ih q
      calc
        fstF (((semFfun Pf)^[n.succ]) Bot p0)
            = traces (Pf p0) (fstF ∘ (((semFfun Pf)^[n]) Bot)) := by
                simp [Function.iterate_succ_apply', semFfun_def, semFf_def]
        _ = traces (Pf p0) (((semTfun Pf)^[n]) Bot) := by
              simpa using congrArg (traces (Pf p0)) hIH
        _ = ((semTfun Pf)^[n.succ]) Bot p0 := by
              simp [Function.iterate_succ_apply', semTfun_def, semTf_def]

axiom fstF_MF_MT_cpo_lm [HasPNfun p α]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun →
      fstF (LFP (semFfun Pf) p0) = LFP (semTfun Pf) p0

theorem fstF_MF_MT_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      (fstF ∘ (MF : p → domFType α)) = (MT : p → domTType α) := by
  intro hPf hmode
  subst hPf
  funext p0
  rcases hmode with hmode | hmode
  · simpa [Function.comp, MF_def, MT_def, semFfix_def, semTfix_def, hmode] using
      (fstF_MF_MT_cpo_lm (Pf := PNfun) (p0 := p0) rfl)
  · simpa [Function.comp, MF_def, MT_def, semFfix_def, semTfix_def, hmode] using
      (fstF_MF_MT_cpo_lm (Pf := PNfun) (p0 := p0) rfl)

/- ===================================*
              conclusion
 *=================================== -/

theorem fstF_MF_MT [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    Pf = PNfun →
      (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
        (fstF ∘ (MF : p → domFType α)) = (MT : p → domTType α) := by
  intro hPf hmode
  rcases hmode with hCPO | hrest
  · exact fstF_MF_MT_cpo (Pf := Pf) hPf (Or.inl hCPO)
  · rcases hrest with hCMS | hMIX
    · exact fstF_MF_MT_cms (Pf := Pf) hPf hCMS.2 hCMS.1
    · exact fstF_MF_MT_cpo (Pf := Pf) hPf (Or.inr hMIX)
