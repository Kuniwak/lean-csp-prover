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

/- Lean note:
   as for `traces_iteration_semTfun_Bot`, the Isabelle originals write the raw
   iteration `((Pf <<<) ^^ n) (%q. DIV) p` and not `FIX[n] Pf p`.  `Pf <<<`
   leaves the target process-name type free, while the constant `FIX[n]` is
   homogeneous, so phrasing these with `FIXn` would weaken them.  `FIXn_def`
   specialises them to `FIXn` at the call sites. -/

theorem semF_iteration_semFfun_Bot [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {n : Nat} :
    ∀ p0, semF (((fun Qf : p → proc q α => Pf <<< Qf)^[n])
                  (fun _ => (proc.DIV : proc q α)) p0)
      = ((semFfun Pf)^[n]) Bot p0 := by
  induction n with
  | zero =>
      intro p0
      have hBot : (fun _ : p => semF (proc.DIV : proc q α)) = (Bot : p → domFType α) := by
        simpa [semF_def, semFf_def] using
          (traces_failures_prod_Bot (ι := p) (κ := q) (α := α) (M := (MF : q → domFType α)))
      simpa using congrArg (fun F : p → domFType α => F p0) hBot
  | succ n ih =>
      intro p0
      have hfun :
          (fun r => semF (((fun Qf : p → proc q α => Pf <<< Qf)^[n])
            (fun _ => (proc.DIV : proc q α)) r)) = ((semFfun Pf)^[n]) Bot := by
        funext r
        exact ih r
      rw [Function.iterate_succ_apply' (f := fun Qf : p → proc q α => Pf <<< Qf),
        Subst_procfun_prod_p, semF_subst, hfun]
      simp [Function.iterate_succ_apply', semFfun_def]

theorem semF_iteration_semFfun_Bot_sndF [HasPNfun q α] [HasFPmode]
    {Pf : p → proc p α} {n : Nat} {p0 : p} :
    failures (((fun Qf : p → proc q α => Pf <<< Qf)^[n])
                (fun _ => (proc.DIV : proc q α)) p0) MF
      = sndF (((semFfun Pf)^[n]) Bot p0) := by
  exact semF_decompo_sndF (semF_iteration_semFfun_Bot (Pf := Pf) (n := n) p0)

/- (*** FIX ***) -/

theorem semF_FIX_LUB_domF_T
    {Pf : p → proc p α} {p0 : p} :
    (fun y => Prod.fst (Rep_domF y)) '' {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0} =
      {t | ∃ n, t = fstF ((((semFfun Pf)^[n]) Bot) p0)} := by
  ext t
  constructor
  · rintro ⟨y, ⟨x, ⟨n, rfl⟩, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨((semFfun Pf)^[n]) Bot p0, ⟨((semFfun Pf)^[n]) Bot, ⟨n, rfl⟩, rfl⟩, rfl⟩

/- Lean note: the Isabelle original is
     `Union (Rep_setF ` snd ` Rep_domF ` {...}) = {f. EX n. f :f sndF (...)}`,
   where `Union` is the set-theoretic `⋃₀`.  A bare `Union` in Lean resolves
   to Mathlib's `Union` *type class* and would turn the proposition into an
   equality of types, so the transcription below spells it `⋃₀`. -/
theorem semF_FIX_LUB_domF_F
    {Pf : p → proc p α} {p0 : p} :
    ⋃₀ ((fun y => Rep_setF (Prod.snd (Rep_domF y))) ''
      {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0}) =
      {f | ∃ n, f :f sndF ((((semFfun Pf)^[n]) Bot) p0)} := by
  ext f
  constructor
  · rintro ⟨A, ⟨y, ⟨x, ⟨n, rfl⟩, rfl⟩, rfl⟩, hf⟩
    exact ⟨n, hf⟩
  · rintro ⟨n, hf⟩
    exact ⟨Rep_setF (Prod.snd (Rep_domF (((semFfun Pf)^[n]) Bot p0))),
      ⟨((semFfun Pf)^[n]) Bot p0, ⟨((semFfun Pf)^[n]) Bot, ⟨n, rfl⟩, rfl⟩, rfl⟩, hf⟩

private theorem semF_FIXn_le_FIX [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} {n : Nat} :
    semF (FIXn n Pf p0) ≤ semF (FIX Pf p0) := by
  rw [subdomF_decompo]
  constructor
  · rw [← semF_decompo_fstF (P := FIXn n Pf p0) rfl,
      ← semF_decompo_fstF (P := FIX Pf p0) rfl]
    refine subdomT_iff.mpr fun t ht => ?_
    rw [FIX_def, in_traces_Rep_int_choice_nat]
    exact Or.inr ⟨n, trivial, ht⟩
  · rw [← semF_decompo_sndF (P := FIXn n Pf p0) rfl,
      ← semF_decompo_sndF (P := FIX Pf p0) rfl]
    refine subsetF_iff.mpr fun s X hf => ?_
    rw [FIX_def, in_failures_Rep_int_choice_nat]
    exact ⟨n, trivial, hf⟩

private theorem semF_FIX_isLUB_p [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    isLUB (semF (FIX Pf p0)) {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0} := by
  constructor
  · rintro y ⟨x, ⟨n, rfl⟩, rfl⟩
    rw [← semF_iteration_semFfun_Bot (Pf := Pf) (q := p) (n := n) p0]
    exact semF_FIXn_le_FIX
  · intro T hT
    have hTn : ∀ n : Nat, semF (FIXn n Pf p0) ≤ T := by
      intro n
      rw [FIXn_def, semF_iteration_semFfun_Bot (Pf := Pf) (q := p) (n := n) p0]
      exact hT _ ⟨((semFfun Pf)^[n]) Bot, ⟨n, rfl⟩, rfl⟩
    rw [subdomF_decompo]
    constructor
    · rw [← semF_decompo_fstF (P := FIX Pf p0) rfl]
      refine subdomT_iff.mpr fun t ht => ?_
      rw [FIX_def, in_traces_Rep_int_choice_nat] at ht
      rcases ht with rfl | ⟨n, -, ht⟩
      · exact nilt_in_T
      · have hle := (subdomF_decompo.mp (hTn n)).1
        rw [← semF_decompo_fstF (P := FIXn n Pf p0) rfl] at hle
        exact subdomT_iff.mp hle t ht
    · rw [← semF_decompo_sndF (P := FIX Pf p0) rfl]
      refine subsetF_iff.mpr fun s X hf => ?_
      rw [FIX_def, in_failures_Rep_int_choice_nat] at hf
      obtain ⟨n, -, hf⟩ := hf
      have hle := (subdomF_decompo.mp (hTn n)).2
      rw [← semF_decompo_sndF (P := FIXn n Pf p0) rfl] at hle
      exact subsetF_iff.mp hle s X hf

private theorem FIX_index_set_ne [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    {y : domFType α | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0} ≠ ∅ := by
  intro hEq
  exact Set.eq_empty_iff_forall_notMem.mp hEq (((semFfun Pf)^[0]) Bot p0)
    ⟨((semFfun Pf)^[0]) Bot, ⟨0, rfl⟩, rfl⟩

theorem semF_FIX [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    semF (FIX Pf p0) =
      LUB_domF {y | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0} :=
  isLUB_LUB_domF_only_if FIX_index_set_ne semF_FIX_isLUB_p

/- (*** FIX is LUB ***) -/

theorem semF_FIX_isLUB [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    isLUB (fun p0 => semF (FIX Pf p0)) {x | ∃ n, x = ((semFfun Pf)^[n]) Bot} := by
  refine prod_LUB_decompo_if fun p0 => ?_
  have himg : proj_fun p0 '' {x : p → domFType α | ∃ n, x = ((semFfun Pf)^[n]) Bot} =
      {y : domFType α | ∃ x, (∃ n, x = ((semFfun Pf)^[n]) Bot) ∧ y = x p0} := by
    ext y
    constructor
    · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
      exact ⟨((semFfun Pf)^[n]) Bot, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
      exact ⟨((semFfun Pf)^[n]) Bot, ⟨n, rfl⟩, rfl⟩
  rw [himg]
  exact semF_FIX_isLUB_p

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

theorem cspF_rmPN_eqF [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨
      (FPmode = CMSmode ∧ guardedfun (PNfun : p → proc p α)) ∨
      FPmode = MIXmode) →
        eqF P MF MF (rmPN P) := by
  intro hmode
  induction P with
  | STOP => exact cspF_reflex_eq_P
  | SKIP => exact cspF_reflex_eq_P
  | DIV => exact cspF_reflex_eq_P
  | Act_prefix a P ih => exact cspF_Act_prefix_cong rfl ih
  | Ext_pre_choice X Qf ih => exact cspF_Ext_pre_choice_cong rfl fun a _ => ih a
  | Ext_choice P Q ihP ihQ => exact cspF_Ext_choice_cong ihP ihQ
  | Int_choice P Q ihP ihQ => exact cspF_Int_choice_cong ihP ihQ
  | Rep_int_choice C Qf ih => exact cspF_Rep_int_choice_cong_sum rfl fun c _ => ih c
  | «IF» b P Q ihP ihQ => exact cspF_IF_cong rfl ihP ihQ
  | Parallel P X Q ihP ihQ => exact cspF_Parallel_cong rfl ihP ihQ
  | Hiding P X ih => exact cspF_Hiding_cong rfl ih
  | Renaming P r ih => exact cspF_Renaming_cong rfl ih
  | Seq_compo P Q ihP ihQ => exact cspF_Seq_compo_cong ihP ihQ
  | Depth_rest P n ih => exact cspF_Depth_rest_cong rfl ih
  | Proc_name p0 => exact cspF_FIX hmode rfl

/- -------------------------------------------------------*
 |                                                       |
 |         FIX expansion (CSP-Prover intro rule)         |
 |                                                       |
 *------------------------------------------------------- -/

private theorem FIXn_succ' {Pf : p → proc p α} {n : Nat} :
    FIXn (n.succ) Pf = Pf <<< FIXn n Pf := by
  funext p0
  simp [FIXn, Function.iterate_succ_apply', Subst_procfun_prod]

private theorem semFf_iteration_semFfun_Bot
    {Pf : p → proc p α} {n : Nat} {M : p → domFType α} :
    ∀ p0, semFf (FIXn n Pf p0) M = ((semFfun Pf)^[n]) Bot p0 := by
  induction n with
  | zero =>
      intro p0
      have h :=
        congrArg (fun F : p → domFType α => F p0)
          (traces_failures_prod_Bot (ι := p) (κ := p) (α := α) (M := M))
      simpa [FIXn, semFf_def] using h
  | succ n ih =>
      intro p0
      have hfun : (fun q => semFf (FIXn n Pf q) M) = ((semFfun Pf)^[n]) Bot := by
        funext q
        exact ih q
      rw [FIXn_succ', Subst_procfun_prod_p, Function.iterate_succ_apply', ← hfun]
      simp only [semFfun_def]
      refine (eqF_decompo).mpr ⟨?_, ?_⟩
      · rw [fstF_semFf, fstF_semFf, traces_subst, fstF_semFf_comp]
      · rw [sndF_semFf, sndF_semFf, failrues_subst]

private theorem iterate_Bot_mono_F {Pf : p → proc p α} :
    ∀ n m : Nat, ((semFfun Pf)^[n]) Bot ≤ ((semFfun Pf)^[n + m]) Bot := by
  intro n
  induction n with
  | zero => intro m; exact bottom_bot _
  | succ n ih =>
      intro m
      rw [Function.iterate_succ_apply', show n + 1 + m = (n + m) + 1 by omega,
        Function.iterate_succ_apply']
      exact mono_semFfun (ih m)

theorem failures_FIXn_plus_sub_lm
    {Pf : p → proc p α} {M : p → domFType α} :
    ∀ n m p0, failures (FIXn n Pf p0) M <= failures (FIXn (n + m) Pf p0) M := by
  intro n m p0
  rw [← sndF_semFf (P := FIXn n Pf p0) (M := M),
    ← sndF_semFf (P := FIXn (n + m) Pf p0) (M := M),
    semFf_iteration_semFfun_Bot (Pf := Pf) (n := n) (M := M) p0,
    semFf_iteration_semFfun_Bot (Pf := Pf) (n := n + m) (M := M) p0]
  exact (subdomF_decompo.mp (iterate_Bot_mono_F n m p0)).2

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
