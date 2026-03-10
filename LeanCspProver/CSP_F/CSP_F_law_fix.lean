           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  March 2007               |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_fp
import LeanCspProver.CSP_T.CSP_T_law_fix

open fpmode

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq` or         -/
/-  `Inf_image_eq`, so there is nothing to disable or re-enable here.   -/

/- -----------*
 |    Bot    |
 *----------- -/

theorem failures_prod_Bot {ι κ : Type _} {M : κ → domFType α} :
    (fun _ : ι => failures proc.DIV M) = (Bot : ι → setFType α) := by
  funext i
  apply le_antisymm
  · exact BOT_is_bottom_setF
  · intro f hf
    exact False.elim ((in_failures_DIV (f := f) (M := M)) hf)

theorem traces_failures_prod_Bot {ι κ : Type _} {M : κ → domFType α} :
    (fun _ : ι => traces proc.DIV (fstF ∘ M) ,, failures proc.DIV M) = (Bot : ι → domFType α) := by
  funext i
  have hT :=
    congrArg (fun F : Unit → domTType α => F ())
      (traces_prod_Bot (ι := Unit) (κ := κ) (M := fstF ∘ M))
  have hF :=
    congrArg (fun F : Unit → setFType α => F ())
      (failures_prod_Bot (ι := Unit) (κ := κ) (M := M))
  have hT' : traces proc.DIV (fstF ∘ M) = (Bot : domTType α) := by
    simpa using hT
  have hF' : failures proc.DIV M = (Bot : setFType α) := by
    simpa using hF
  change traces proc.DIV (fstF ∘ M) ,, failures proc.DIV M = (Bot : domFType α)
  rw [hT', hF']
  rw [bottom_domF_def, bottom_domT_def, bottom_setF_def]

theorem semF_prod_Bot [HasPNfun p α] [HasFPmode] :
    (fun _ : p => semF (proc.DIV : proc p α)) = (Bot : p → domFType α) := by
  simpa [semF_def, semFf_def] using (traces_failures_prod_Bot (ι := p) (κ := p) (M := MF))

/- -----------*
 |   FIX P   |
 *----------- -/

/- (*** iteration lemmas ***) -/

private theorem FIXn_succ {Pf : p → proc p α} {n : Nat} :
    FIXn (n.succ) Pf = Pf <<< FIXn n Pf := by
  funext p0
  simp [FIXn, Function.iterate_succ_apply', Subst_procfun_prod]

theorem semTfun_iteration_semFfun_Bot
    {Pf : p → proc p α} {n : Nat} :
    ∀ p0, ((semTfun Pf)^[n]) Bot p0 = fstF (((semFfun Pf)^[n]) Bot p0) := by
  induction n with
  | zero =>
      intro p0
      change (Bot : domTType α) = fstF (Bot : domFType α)
      rw [bottom_domF_def, bottom_domT_def]
      simpa using
        (pairF_fstF
          (S := Abs_domT ({<>} : Set (traceType α)))
          (F := ({}f : setFType α))
          BOT_in_domF).symm
  | succ n ih =>
      intro p0
      calc
        ((semTfun Pf)^[n.succ]) Bot p0
            = traces (Pf p0) (((semTfun Pf)^[n]) Bot) := by
                simp [Function.iterate_succ_apply', semTfun_def, semTf_def]
        _ = traces (Pf p0) (fstF ∘ (((semFfun Pf)^[n]) Bot)) := by
              congr
              funext q
              exact ih q
        _ = fstF (((semFfun Pf)^[n.succ]) Bot p0) := by
              simp [Function.iterate_succ_apply', semFfun_def, semFf_def]

theorem semF_iteration_semFfun_Bot [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {n : Nat} :
    ∀ p0, semF (FIXn n Pf p0) = ((semFfun Pf)^[n]) Bot p0 := by
  induction n with
  | zero =>
      intro p0
      have h :=
        congrArg (fun F : p → domFType α => F p0)
          (semF_prod_Bot (p := p) (α := α))
      simpa [FIXn, semF_def, semFf_def] using h
  | succ n ih =>
      intro p0
      have hfun : (fun q => semF (FIXn n Pf q)) = ((semFfun Pf)^[n]) Bot := by
        funext q
        exact ih q
      rw [FIXn_succ, Subst_procfun_prod_p, semF_subst, hfun]
      simp [Function.iterate_succ_apply', semFfun_def]

theorem semF_iteration_semFfun_Bot_sndF [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {n : Nat} {p0 : p} :
    failures (FIXn n Pf p0) MF = sndF (((semFfun Pf)^[n]) Bot p0) := by
  exact semF_decompo_sndF (semF_iteration_semFfun_Bot (Pf := Pf) (n := n) p0)

/- (*** FIX ***) -/

axiom semF_FIX_LUB_domF_T
    {Pf : p → proc p α} {p0 : p} :
    (fun y => Prod.fst (Rep_domF y)) '' {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0} =
      {t | ∃ n, t = fstF ((((semFfun Pf)^[n]) Bot) p0)}

axiom semF_FIX_LUB_domF_F
    {Pf : p → proc p α} {p0 : p} :
    Union ((fun y => Rep_setF (Prod.snd (Rep_domF y))) ''
      {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0}) =
      {f | ∃ n, f :f sndF ((((semFfun Pf)^[n]) Bot) p0)}

axiom semF_FIX [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    semF (FIX Pf p0) =
      LUB_domF {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0}

/- (*** FIX is LUB ***) -/

axiom semF_FIX_isLUB [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    isLUB (fun p0 => semF (FIX Pf p0)) {x | ∃ n, x = ((semFfun Pf)^[n]) Bot}

theorem semF_FIX_LUB [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    (fun p0 => semF (FIX Pf p0)) = LUB {x | ∃ n, x = ((semFfun Pf)^[n]) Bot} := by
  symm
  exact isLUB_LUB (semF_FIX_isLUB (Pf := Pf))

theorem semF_FIX_LFP [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    (fun p0 => semF (FIX Pf p0)) = LFP (semFfun Pf) := by
  rw [semF_FIX_LUB]
  symm
  exact Tarski_thm_LFP_LUB (f := semFfun Pf) continuous_semFfun

theorem semF_FIX_LFP_p [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    semF (FIX Pf p0) = LFP (semFfun Pf) p0 := by
  exact congrArg (fun F => F p0) (semF_FIX_LFP (Pf := Pf))

theorem semF_FIX_isLFP [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    isLFP (fun p0 => semF (FIX Pf p0)) (semFfun Pf) := by
  rw [semF_FIX_LFP]
  exact LFP_is (Tarski_thm_EX (f := semFfun Pf) continuous_semFfun)

theorem semF_FIX_LFP_fixed_point [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    semFfun Pf (fun p0 => semF (FIX Pf p0)) = (fun p0 => semF (FIX Pf p0)) := by
  exact (semF_FIX_isLFP (Pf := Pf)).1.symm

theorem semF_FIX_LFP_least [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    ∀ M, semFfun Pf M = M → (fun p0 => semF (FIX Pf p0)) <= M := by
  intro M hM
  exact (semF_FIX_isLFP (Pf := Pf)).2 M hM.symm

/- =======================================================*
 |                                                       |
 |                        CPO                            |
 |                                                       |
 *======================================================= -/

theorem cspF_FIX_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqF (proc.Proc_name p0 : proc p α) MF MF (FIX Pf p0) := by
  intro hPf hmode
  subst hPf
  change semF (proc.Proc_name p0 : proc p α) = semF (FIX PNfun p0)
  rw [semF_LFP_cpo (Pf := PNfun) (p0 := p0) rfl hmode]
  rw [semF_FIX_LFP_p (Pf := PNfun) (p0 := p0)]

theorem cspF_FIX_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    FPmode = CMSmode → Pf = PNfun → guardedfun Pf →
      eqF (proc.Proc_name p0 : proc p α) MF MF (FIX Pf p0) := by
  intro hmode hPf hguard
  subst hPf
  change semF (proc.Proc_name p0 : proc p α) = semF (FIX PNfun p0)
  rw [semF_UFP_cms (Pf := PNfun) (p0 := p0) rfl hguard hmode]
  rw [semF_FIX_LFP_p (Pf := PNfun) (p0 := p0)]
  symm
  simpa using congrArg (fun F => F p0) (semF_guarded_LFP_UFP (Pf := PNfun) rfl hguard)

theorem cspF_FIX [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
      Pf = PNfun →
        eqF (proc.Proc_name p0 : proc p α) MF MF (FIX Pf p0) := by
  intro hmode hPf
  rcases hmode with hCPO | hrest
  · exact cspF_FIX_cpo (Pf := Pf) (p0 := p0) hPf (Or.inl hCPO)
  · rcases hrest with hCMS | hMIX
    · exact cspF_FIX_cms (Pf := Pf) (p0 := p0) hCMS.1 hPf hCMS.2
    · exact cspF_FIX_cpo (Pf := Pf) (p0 := p0) hPf (Or.inr hMIX)

/- ==============================================================*
 |                                                              |
 | replace process names by infinite repcicated internal choice |
 |                         rmPN   (FIX)                         |
 |                                                              |
 *============================================================== -/

axiom cspF_rmPN_eqF [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨
      (FPmode = CMSmode ∧ guardedfun (PNfun : p → proc p α)) ∨
      FPmode = MIXmode) →
        eqF P MF MF (rmPN P)

/- -------------------------------------------------------*
 |                                                       |
 |         FIX expansion (CSP-Prover intro rule)         |
 |                                                       |
 *------------------------------------------------------- -/

axiom failures_FIXn_plus_sub_lm
    {Pf : p → proc p α} {M : p → domFType α} :
    ∀ n m p0, failures (FIXn n Pf p0) M <= failures (FIXn (n + m) Pf p0) M

theorem failures_FIXn_plus_sub
    {Pf : p → proc p α} {M : p → domFType α} {n m : Nat} {p0 : p} :
    failures (FIXn n Pf p0) M <= failures (FIXn (n + m) Pf p0) M :=
  failures_FIXn_plus_sub_lm (Pf := Pf) (M := M) n m p0

theorem semF_FIXn_plus_sub
    {Pf : p → proc p α} {M : p → domFType α} {n m : Nat} {p0 : p} :
    semFf (FIXn n Pf p0) M <= semFf (FIXn (n + m) Pf p0) M := by
  apply (subdomF_decompo
    (SF := semFf (FIXn n Pf p0) M)
    (SE := semFf (FIXn (n + m) Pf p0) M)).2
  constructor
  · simpa [semFf_def] using
      (traces_FIXn_plus_sub (Pf := Pf) (M := fstF ∘ M) (n := n) (m := m) (p0 := p0))
  · simpa [semFf_def] using
      (failures_FIXn_plus_sub (Pf := Pf) (M := M) (n := n) (m := m) (p0 := p0))

theorem in_failures_FIXn_plus_sub
    {Pf : p → proc p α} {M : p → domFType α} {n m : Nat} {p0 : p}
    {s : traceType α} {X : Set (event α)} :
    (s, X) :f failures (FIXn n Pf p0) M →
      (s, X) :f failures (FIXn (n + m) Pf p0) M := by
  intro hsX
  exact (failures_FIXn_plus_sub (Pf := Pf) (M := M) (n := n) (m := m) (p0 := p0)) hsX

/- -----------------------------------------------------*
 |  sometimes FIX[n + f n] is useful more than FIX[n]  |
 *----------------------------------------------------- -/

theorem cspF_FIX_plus_eq [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    ∀ f : Nat → Nat, ∀ p0,
      eqF (FIX Pf p0) MF MF
        (Rep_int_choice_nat Set.univ (fun n => FIXn (n + f n) Pf p0)) := by
  intro f p0
  refine (cspF_cspT_eqF_semantics
    (P := FIX Pf p0)
    (Q := Rep_int_choice_nat Set.univ (fun n => FIXn (n + f n) Pf p0))
    (M1 := MF)
    (M2 := MF)).2 ?_
  constructor
  · simpa using
      (cspT_FIX_plus_eq (Pf := Pf) (M := fstF ∘ MF) (f := f) (p0 := p0))
  · apply le_antisymm
    · apply subsetFI
      intro s X hs
      rw [FIX_def, in_failures_Rep_int_choice_nat] at hs
      rcases hs with ⟨n, -, hs⟩
      rw [in_failures_Rep_int_choice_nat]
      refine ⟨n, by simp, ?_⟩
      exact in_failures_FIXn_plus_sub (Pf := Pf) (M := MF) (n := n) (m := f n) (p0 := p0) hs
    · apply subsetFI
      intro s X hs
      rw [in_failures_Rep_int_choice_nat] at hs
      rcases hs with ⟨n, -, hs⟩
      rw [FIX_def, in_failures_Rep_int_choice_nat]
      exact ⟨n + f n, by simp, hs⟩

end
