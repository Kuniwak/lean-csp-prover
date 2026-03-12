           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  March 2007               |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law_fp

open fpmode

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq` or         -/
/-  `Inf_image_eq`, so there is nothing to disable or re-enable here.   -/

def FIXn (n : Nat) (Pf : p → proc p α) : p → proc p α :=
  ((fun Qf => Pf <<< Qf)^[n]) (fun _ => proc.DIV)

theorem FIXn_def (n : Nat) (Pf : p → proc p α) :
    FIXn n Pf = ((fun Qf => Pf <<< Qf)^[n]) (fun _ => proc.DIV) :=
  rfl

def FIX (Pf : p → proc p α) : p → proc p α :=
  fun p0 => Rep_int_choice_nat Set.univ (fun n => FIXn n Pf p0)

theorem FIX_def (Pf : p → proc p α) :
    FIX Pf = fun p0 => Rep_int_choice_nat Set.univ (fun n => FIXn n Pf p0) :=
  rfl

/-
(*-----------*
 |   noPN    |
 *-----------*)
-/

axiom noPNfun_FIXn {n : Nat} {Pf : p → proc p α} :
    noPNfun (FIXn n Pf)

theorem noPN_FIXn {n : Nat} {Pf : p → proc p α} {p0 : p} :
    noPN (FIXn n Pf p0) :=
  noPNfun_FIXn (n := n) (Pf := Pf) p0

axiom noPN_FIX {Pf : p → proc p α} {p0 : p} :
    noPN (FIX Pf p0)

/-
(*-----------*
 |    Bot    |
 *-----------*)
-/

theorem traces_prod_Bot {ι κ : Type _} {M : κ → domTType α} :
    (fun _ : ι => traces (proc.DIV : proc κ α) M) = (Bot : ι → domTType α) := by
  funext i
  apply le_antisymm
  · intro t ht
    have hEq : t = <> := (in_traces_DIV (t := t) (M := M)).1 ht
    subst t
    exact nilt_in_T (T := (Bot : domTType α))
  · exact bottom_bot _

theorem semT_prod_Bot [HasPNfun p α] [HasFPmode] :
    (fun _ : p => semT (proc.DIV : proc p α)) = (Bot : p → domTType α) := by
  funext p0
  have h :=
    congrArg (fun F : p → domTType α => F p0)
      (traces_prod_Bot (ι := p) (κ := p) (α := α) (M := MT))
  simpa [semT_def, semTf_def] using h

/-
(*-----------*
 |   FIX P   |
 *-----------*)
-/

theorem traces_subst_Bot {P : proc p α} {M : q → domTType α} :
    traces (P << (fun _ : p => (proc.DIV : proc q α))) M = traces P Bot := by
  rw [traces_subst]
  have hBot :
      (fun _ : p => traces (proc.DIV : proc q α) M) = (Bot : p → domTType α) :=
    traces_prod_Bot (ι := p) (κ := q) (α := α) (M := M)
  rw [hBot]

private theorem FIXn_succ {Pf : p → proc p α} {n : Nat} :
    FIXn (n.succ) Pf = Pf <<< FIXn n Pf := by
  funext p0
  simp [FIXn, Function.iterate_succ_apply', Subst_procfun_prod]

theorem traces_iteration_semTfun_Bot
    {Pf : p → proc p α} {n : Nat} {M : p → domTType α} :
    ∀ p0, traces (FIXn n Pf p0) M = ((semTfun Pf)^[n]) Bot p0 := by
  induction n with
  | zero =>
      intro p0
      have h :=
        congrArg (fun F : p → domTType α => F p0)
          (traces_prod_Bot (ι := p) (κ := p) (α := α) (M := M))
      simpa [FIXn, semTfun_def, semTf_def] using h
  | succ n ih =>
      intro p0
      have hfun : (fun q => traces (FIXn n Pf q) M) = ((semTfun Pf)^[n]) Bot := by
        funext q
        exact ih q
      rw [FIXn_succ, Function.iterate_succ_apply', Subst_procfun_prod_p, traces_subst, hfun]
      simp [semTfun_def, semTf_def]

axiom traces_FIX
    {Pf : p → proc p α} {p0 : p} {M : p → domTType α} :
    traces (FIX Pf p0) M = UnionT {u | ∃ n, u = ((semTfun Pf)^[n]) Bot p0}

theorem semT_FIX [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    semT (FIX Pf p0) = UnionT {u | ∃ n, u = ((semTfun Pf)^[n]) Bot p0} := by
  simpa [semT_def, semTf_def] using (traces_FIX (Pf := Pf) (p0 := p0) (M := MT))

axiom semT_FIX_isLUB [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    isLUB (fun p0 => semT (FIX Pf p0)) {x | ∃ n, x = ((semTfun Pf)^[n]) Bot}

theorem semT_FIX_LUB [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    (fun p0 => semT (FIX Pf p0)) = LUB {x | ∃ n, x = ((semTfun Pf)^[n]) Bot} := by
  symm
  exact isLUB_LUB (semT_FIX_isLUB (Pf := Pf))

theorem semT_FIX_LFP [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    (fun p0 => semT (FIX Pf p0)) = LFP (semTfun Pf) := by
  rw [semT_FIX_LUB]
  symm
  exact Tarski_thm_LFP_LUB (f := semTfun Pf) continuous_semTfun

theorem semT_FIX_LFP_p [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    semT (FIX Pf p0) = LFP (semTfun Pf) p0 := by
  exact congrArg (fun F => F p0) (semT_FIX_LFP (Pf := Pf))

theorem semT_FIX_isLFP [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    isLFP (fun p0 => semT (FIX Pf p0)) (semTfun Pf) := by
  rw [semT_FIX_LFP]
  exact LFP_is (Tarski_thm_EX (f := semTfun Pf) continuous_semTfun)

theorem semT_FIX_LFP_fixed_point [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    semTfun Pf (fun p0 => semT (FIX Pf p0)) = (fun p0 => semT (FIX Pf p0)) := by
  exact (semT_FIX_isLFP (Pf := Pf)).1.symm

theorem semT_FIX_LFP_least [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} :
    ∀ Tf, semTfun Pf Tf = Tf → (fun p0 => semT (FIX Pf p0)) <= Tf := by
  intro Tf hTf
  exact (semT_FIX_isLFP (Pf := Pf)).2 Tf hTf.symm

/-
(*=======================================================*
 |                                                       |
 |                        CPO                            |
 |                                                       |
 *=======================================================*)
-/

theorem cspT_FIX_cpo [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqT (proc.Proc_name p0 : proc p α) MT MT (FIX Pf p0) := by
  intro hPf hmode
  subst hPf
  change semT (proc.Proc_name p0 : proc p α) = semT (FIX PNfun p0)
  rw [semT_LFP_cpo (Pf := PNfun) (p0 := p0) rfl hmode]
  rw [semT_FIX_LFP_p (Pf := PNfun) (p0 := p0)]

theorem cspT_FIX_cms [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun → guardedfun Pf → FPmode = CMSmode →
      eqT (proc.Proc_name p0 : proc p α) MT MT (FIX Pf p0) := by
  intro hPf hguard hmode
  subst hPf
  change semT (proc.Proc_name p0 : proc p α) = semT (FIX PNfun p0)
  rw [semT_UFP_cms (Pf := PNfun) (p0 := p0) rfl hguard hmode]
  rw [semT_FIX_LFP_p (Pf := PNfun) (p0 := p0)]
  symm
  simpa using congrArg (fun F => F p0) (semT_guarded_LFP_UFP (Pf := PNfun) rfl hguard)

theorem cspT_FIX [HasPNfun p α] [HasFPmode]
    {Pf : p → proc p α} {p0 : p} :
    Pf = PNfun →
      (FPmode = CPOmode ∨ (FPmode = CMSmode ∧ guardedfun Pf) ∨ FPmode = MIXmode) →
        eqT (proc.Proc_name p0 : proc p α) MT MT (FIX Pf p0) := by
  intro hPf hmode
  rcases hmode with hCPO | hrest
  · exact cspT_FIX_cpo (Pf := Pf) (p0 := p0) hPf (Or.inl hCPO)
  · rcases hrest with hCMS | hMIX
    · exact cspT_FIX_cms (Pf := Pf) (p0 := p0) hPf hCMS.2 hCMS.1
    · exact cspT_FIX_cpo (Pf := Pf) (p0 := p0) hPf (Or.inr hMIX)

/-
(*==============================================================*
 |                                                              |
 | replace process names by infinite repcicated internal choice |
 |                         rmPN   (FIX)                         |
 |                                                              |
 *==============================================================*)
-/

def rmPN [HasPNfun p α] : proc p α → proc p α
  | .STOP => .STOP
  | .SKIP => .SKIP
  | .DIV => .DIV
  | .Act_prefix a P => .Act_prefix a (rmPN P)
  | .Ext_pre_choice X Pf => .Ext_pre_choice X (fun a => rmPN (Pf a))
  | .Ext_choice P Q => .Ext_choice (rmPN P) (rmPN Q)
  | .Int_choice P Q => .Int_choice (rmPN P) (rmPN Q)
  | .Rep_int_choice C Pf => .Rep_int_choice C (fun c => rmPN (Pf c))
  | .IF b P Q => .IF b (rmPN P) (rmPN Q)
  | .Parallel P X Q => .Parallel (rmPN P) X (rmPN Q)
  | .Hiding P X => .Hiding (rmPN P) X
  | .Renaming P r => .Renaming (rmPN P) r
  | .Seq_compo P Q => .Seq_compo (rmPN P) (rmPN Q)
  | .Depth_rest P n => .Depth_rest (rmPN P) n
  | .Proc_name p0 => FIX PNfun p0

axiom noPN_rmPN [HasPNfun p α] {P : proc p α} :
    noPN (rmPN P)

axiom cspT_rmPN_eqT [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨
      (FPmode = CMSmode ∧ guardedfun (PNfun : p → proc p α)) ∨
      FPmode = MIXmode) →
        eqT P MT MT (rmPN P)

/-
(*-------------------------------------------------------*
 |                                                       |
 |         FIX expansion (CSP-Prover intro rule)         |
 |                                                       |
 *-------------------------------------------------------*)
-/

axiom traces_FIXn_plus_sub_lm
    {Pf : p → proc p α} {M : p → domTType α} :
    ∀ n m p0, traces (FIXn n Pf p0) M <= traces (FIXn (n + m) Pf p0) M

theorem traces_FIXn_plus_sub
    {Pf : p → proc p α} {M : p → domTType α} {n m : Nat} {p0 : p} :
    traces (FIXn n Pf p0) M <= traces (FIXn (n + m) Pf p0) M :=
  traces_FIXn_plus_sub_lm (Pf := Pf) (M := M) n m p0

theorem semT_FIXn_plus_sub
    {Pf : p → proc p α} {M : p → domTType α} {n m : Nat} {p0 : p} :
    semTf (FIXn n Pf p0) M <= semTf (FIXn (n + m) Pf p0) M := by
  simpa [semTf_def] using
    (traces_FIXn_plus_sub (Pf := Pf) (M := M) (n := n) (m := m) (p0 := p0))

theorem in_traces_FIXn_plus_sub
    {Pf : p → proc p α} {M : p → domTType α} {n m : Nat} {p0 : p} {t : traceType α} :
    t :t traces (FIXn n Pf p0) M → t :t traces (FIXn (n + m) Pf p0) M := by
  intro ht
  exact (traces_FIXn_plus_sub (Pf := Pf) (M := M) (n := n) (m := m) (p0 := p0)) ht

/-
(*-----------------------------------------------------*
 |  sometimes FIX[n + f n] is useful more than FIX[n]  |
 *-----------------------------------------------------*)
-/

axiom cspT_FIX_plus_eq
    {Pf : p → proc p α} {M : p → domTType α} :
    ∀ f : Nat → Nat, ∀ p0,
      eqT (FIX Pf p0) M M (Rep_int_choice_nat Set.univ (fun n => FIXn (n + f n) Pf p0))

end
