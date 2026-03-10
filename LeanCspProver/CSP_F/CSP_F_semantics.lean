           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_semantics
import LeanCspProver.CSP_F.Domain_F_cms

open Classical
open SumType

noncomputable section

/-
(*****************************************************************

         1. semantic clause
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(*********************************************************
                    semantic clause
 *********************************************************)
-/

def failures (P : proc p α) (M : p → domFType α) : setFType α :=
  match P with
  | .STOP =>
      CollectF fun f => ∃ X, f = (<>, X)
  | .SKIP =>
      CollectF fun f =>
        (∃ X, f = (<>, X) ∧ X ⊆ Evset) ∨
          ∃ X, f = ((Abs_trace [event.Tick] : traceType α), X)
  | .DIV =>
      {}f
  | .Act_prefix a P =>
      CollectF fun f =>
        (∃ X, f = (<>, X) ∧ event.Ev a ∉ X) ∨
          ∃ s X, f = (Abs_trace [event.Ev a] ^^^ s, X) ∧ (s, X) :f failures P M
  | proc.Ext_pre_choice X Pf =>
      CollectF fun f =>
        (∃ Y, f = (<>, Y) ∧ (event.Ev '' X) ∩ Y = ∅) ∨
          ∃ a s Y, f = (Abs_trace [event.Ev a] ^^^ s, Y) ∧
            (s, Y) :f failures (Pf a) M ∧ a ∈ X
  | .Ext_choice P Q =>
      CollectF fun f =>
        (∃ X, f = (<>, X) ∧ f :f (failures P M IntF failures Q M)) ∨
          (∃ s X, f = (s, X) ∧ f :f (failures P M UnF failures Q M) ∧ s ≠ <>) ∨
          ∃ X, f = (<>, X) ∧
            ((Abs_trace [event.Tick] : traceType α) :t
              (traces P (fstF ∘ M) UnT traces Q (fstF ∘ M))) ∧
            X ⊆ Evset
  | .Int_choice P Q =>
      failures P M UnF failures Q M
  | proc.Rep_int_choice C Pf =>
      CollectF fun f => ∃ c, c ∈ sumset C ∧ f :f failures (Pf c) M
  | proc.IF b P Q =>
      if b then failures P M else failures Q M
  | proc.Parallel P X Q =>
      CollectF fun f =>
        ∃ u Y Z, f = (u, Y ∪ Z) ∧
          Y \ ((event.Ev '' X) ∪ {event.Tick}) = Z \ ((event.Ev '' X) ∪ {event.Tick}) ∧
          ∃ s t, u ∈ par_tr s X t ∧ (s, Y) :f failures P M ∧ (t, Z) :f failures Q M
  | proc.Hiding P X =>
      CollectF fun f =>
        ∃ s Y, f = (hide_tr s X, Y) ∧ (s, (event.Ev '' X) ∪ Y) :f failures P M
  | proc.Renaming P r =>
      CollectF fun f =>
        ∃ s t X, f = (t, X) ∧ s [[r]]* t ∧ (s, [[r]]inv X) :f failures P M
  | proc.Seq_compo P Q =>
      CollectF fun f =>
        (∃ t X, f = (t, X) ∧ (t, X ∪ {event.Tick}) :f failures P M ∧ noTick t) ∨
          ∃ s t X, f = (s ^^^ t, X) ∧
            (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t traces P (fstF ∘ M) ∧
            (t, X) :f failures Q M ∧ noTick s
  | proc.Depth_rest P n =>
      failures P M .|. n
  | proc.Proc_name pn =>
      sndF (M pn)

/-
(*** for dealing with both !nat and !set ***)
-/

axiom failures_inv_inj [Inhabited β] {g : β → γ} (hg : Function.Injective g)
    {N : Set β} {Pf : β → proc p α} {f : failure α} {x : p → domFType α} :
    (∃ c : γ, (∃ n, c = g n ∧ n ∈ N) ∧ f :f failures (Pf (Function.invFun g c)) x) ↔
      ∃ z, z ∈ N ∧ f :f failures (Pf z) x

axiom Rep_int_choice_failures_nat (N : Set Nat) (Pf : Nat → proc p α) :
    failures (Rep_int_choice_nat N Pf) =
      fun M => CollectF fun f => ∃ n, n ∈ N ∧ f :f failures (Pf n) M

axiom Rep_int_choice_failures_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    failures (Rep_int_choice_set Xs Pf) =
      fun M => CollectF fun f => ∃ X, X ∈ Xs ∧ f :f failures (Pf X) M

axiom Rep_int_choice_failures_com_lm [Inhabited α] {X : Set α} {Pf : α → proc p α}
    {f : failure α} {M : p → domFType α} :
    (∃ z, (∃ a, z = ({a} : Set α) ∧ a ∈ X) ∧ f :f failures (Pf (the_elem z)) M) ↔
      ∃ a, a ∈ X ∧ f :f failures (Pf a) M

axiom Rep_int_choice_failures_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    failures (Rep_int_choice_com X Pf) =
      fun M => CollectF fun f => ∃ a, a ∈ X ∧ f :f failures (Pf a) M

axiom Rep_int_choice_failures_f [Inhabited α] [Inhabited β]
    {g : β → α} (hg : Function.Injective g) (X : Set β) (Pf : β → proc p α) :
    failures (Rep_int_choice_f (p := p) g X Pf) =
      fun M => CollectF fun f => ∃ a, a ∈ X ∧ f :f failures (Pf a) M

/- The Isabelle theorem bundle `Rep_int_choice_failures` is represented by
   `Rep_int_choice_failures_nat`, `Rep_int_choice_failures_set`,
   `Rep_int_choice_failures_com`, and `Rep_int_choice_failures_f`. -/

/- The Isabelle theorem bundle `failures_iff` is represented by the equations
   for `failures` together with the replicated-choice lemmas above. -/

/-
(*********************************************************
                     semantics
 *********************************************************)
-/

def semFf (P : proc p α) : (p → domFType α) → domFType α :=
  fun M => traces P (fstF ∘ M) ,, failures P M

theorem semFf_def (P : proc p α) :
    semFf P = fun M => traces P (fstF ∘ M) ,, failures P M :=
  rfl

def semFfun (Pf : p → proc p α) : (p → domFType α) → (p → domFType α) :=
  fun M p => semFf (Pf p) M

theorem semFfun_def (Pf : p → proc p α) :
    semFfun Pf = fun M p => semFf (Pf p) M :=
  rfl

theorem semFf_semFfun (Pf : p → proc p α) (M : p → domFType α) :
    (fun p => semFf (Pf p) M) = semFfun Pf M :=
  rfl

/-
*------------------------------------------------------------------*
        M such that [[p]]Ff M = [[PNfun(p)]]Ff M
   such M is the fixed point of the function [[PNfun(p)]]Ffun
 *------------------------------------------------------------------*
-/

def semFfix [HasFPmode] (Pf : p → proc p α) : p → domFType α :=
  if FPmode = fpmode.CMSmode then UFP (semFfun Pf) else LFP (semFfun Pf)

theorem semFfix_def [HasFPmode] (Pf : p → proc p α) :
    semFfix Pf = (if FPmode = fpmode.CMSmode then UFP (semFfun Pf) else LFP (semFfun Pf)) :=
  rfl

def MF [HasPNfun p α] [HasFPmode] : p → domFType α :=
  semFfix PNfun

theorem MF_def [HasPNfun p α] [HasFPmode] :
    (MF : p → domFType α) = semFfix PNfun :=
  rfl

/- (*** semantics ***) -/

def semF [HasPNfun p α] [HasFPmode] (P : proc p α) : domFType α :=
  semFf P MF

theorem semF_def [HasPNfun p α] [HasFPmode] (P : proc p α) :
    semF P = semFf P MF :=
  rfl

/-
(*********************************************************
              relations over processes
 *********************************************************)
-/

def refF (P1 : proc p α) (M1 : p → domFType α) (M2 : q → domFType α) (P2 : proc q α) : Prop :=
  semFf P2 M2 <= semFf P1 M1

theorem refF_def (P1 : proc p α) (M1 : p → domFType α) (M2 : q → domFType α) (P2 : proc q α) :
    refF P1 M1 M2 P2 ↔ semFf P2 M2 <= semFf P1 M1 :=
  Iff.rfl

def eqF (P1 : proc p α) (M1 : p → domFType α) (M2 : q → domFType α) (P2 : proc q α) : Prop :=
  semFf P1 M1 = semFf P2 M2

theorem eqF_def (P1 : proc p α) (M1 : p → domFType α) (M2 : q → domFType α) (P2 : proc q α) :
    eqF P1 M1 M2 P2 ↔ semFf P1 M1 = semFf P2 M2 :=
  Iff.rfl

/-
(*********************************************************
        relations over processes (fixed point)
 *********************************************************)
-/

abbrev refFfix [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) : Prop :=
  refF P1 MF MF P2

abbrev eqFfix [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) : Prop :=
  eqF P1 MF MF P2

theorem refF_semF [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) :
    refFfix P1 P2 ↔ semF P2 <= semF P1 :=
  Iff.rfl

theorem eqF_semF [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) :
    eqFfix P1 P2 ↔ semF P1 = semF P2 :=
  Iff.rfl

/-
(*------------------*
 |      csp law     |
 *------------------*)
-/

theorem cspF_eq_ref_iff {P1 : proc p α} {P2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P1 M1 M2 P2 ↔ (refF P1 M1 M2 P2 ∧ refF P2 M2 M1 P1) := by
  constructor
  · intro h
    change semFf P1 M1 = semFf P2 M2 at h
    constructor
    · exact show semFf P2 M2 <= semFf P1 M1 from le_of_eq h.symm
    · exact show semFf P1 M1 <= semFf P2 M2 from le_of_eq h
  · intro h
    show semFf P1 M1 = semFf P2 M2
    exact le_antisymm h.2 h.1

theorem cspF_eq_ref {P1 : proc p α} {P2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P1 M1 M2 P2 → refF P1 M1 M2 P2 := by
  intro h
  exact (cspF_eq_ref_iff (P1 := P1) (P2 := P2) (M1 := M1) (M2 := M2)).1 h |>.1

theorem cspF_ref_eq {P1 : proc p α} {P2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    refF P1 M1 M2 P2 → refF P2 M2 M1 P1 → eqF P1 M1 M2 P2 := by
  intro h12 h21
  exact (cspF_eq_ref_iff (P1 := P1) (P2 := P2) (M1 := M1) (M2 := M2)).2 ⟨h12, h21⟩

/- (*** reflexivity ***) -/

theorem cspF_reflex_eq_P {P : proc p α} {M : p → domFType α} :
    eqF P M M P := by
  rfl

theorem cspF_reflex_eq_STOP {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.STOP : proc p α) M1 M2 (proc.STOP : proc q α) := by
  simp [eqF, semFf, failures, traces]

theorem cspF_reflex_eq_SKIP {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.SKIP : proc p α) M1 M2 (proc.SKIP : proc q α) := by
  simp [eqF, semFf, failures, traces]

theorem cspF_reflex_eq_DIV {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.DIV : proc p α) M1 M2 (proc.DIV : proc q α) := by
  simp [eqF, semFf, failures, traces]

/- The Isabelle theorem bundle `cspF_reflex_eq` is represented by
   `cspF_reflex_eq_P`, `cspF_reflex_eq_STOP`, `cspF_reflex_eq_SKIP`,
   and `cspF_reflex_eq_DIV`. -/

theorem cspF_reflex_ref_P {P : proc p α} {M : p → domFType α} :
    refF P M M P := by
  exact le_rfl

theorem cspF_reflex_ref_STOP {M1 : p → domFType α} {M2 : q → domFType α} :
    refF (proc.STOP : proc p α) M1 M2 (proc.STOP : proc q α) := by
  simp [refF, semFf, failures, traces]

theorem cspF_reflex_ref_SKIP {M1 : p → domFType α} {M2 : q → domFType α} :
    refF (proc.SKIP : proc p α) M1 M2 (proc.SKIP : proc q α) := by
  simp [refF, semFf, failures, traces]

theorem cspF_reflex_ref_DIV {M1 : p → domFType α} {M2 : q → domFType α} :
    refF (proc.DIV : proc p α) M1 M2 (proc.DIV : proc q α) := by
  simp [refF, semFf, failures, traces]

/- The Isabelle theorem bundle `cspF_reflex_ref` is represented by
   `cspF_reflex_ref_P`, `cspF_reflex_ref_STOP`, `cspF_reflex_ref_SKIP`,
   and `cspF_reflex_ref_DIV`. -/

/- The Isabelle theorem bundle `cspF_reflex` is represented by
   `cspF_reflex_eq` and `cspF_reflex_ref`. -/

/- (*** symmetry ***) -/

theorem cspF_sym {P1 : proc p α} {P2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF P1 M1 M2 P2 → eqF P2 M2 M1 P1 := by
  intro h
  simpa [eqF] using h.symm

theorem cspF_symE {P1 : proc p α} {P2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    {Z : Prop} :
    eqF P1 M1 M2 P2 → (eqF P2 M2 M1 P1 → Z) → Z := by
  intro h hZ
  exact hZ (cspF_sym h)

/- (*** transitivity ***) -/

theorem cspF_trans_left_eq
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domFType α} {M2 : q → domFType α} {M3 : r → domFType α} :
    eqF P1 M1 M2 P2 → eqF P2 M2 M3 P3 → eqF P1 M1 M3 P3 := by
  intro h12 h23
  simpa [eqF] using Eq.trans h12 h23

theorem cspF_trans_left_ref
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domFType α} {M2 : q → domFType α} {M3 : r → domFType α} :
    refF P1 M1 M2 P2 → refF P2 M2 M3 P3 → refF P1 M1 M3 P3 := by
  intro h12 h23
  simpa [refF] using le_trans h23 h12

/- The Isabelle theorem bundles `cspF_trans_left` and `cspF_trans` are
   represented by `cspF_trans_left_eq` and `cspF_trans_left_ref`. -/

theorem cspF_trans_right_eq
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domFType α} {M2 : q → domFType α} {M3 : r → domFType α} :
    eqF P2 M2 M3 P3 → eqF P1 M1 M2 P2 → eqF P1 M1 M3 P3 := by
  intro h23 h12
  simpa [eqF] using Eq.trans h12 h23

theorem cspF_trans_right_ref
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domFType α} {M2 : q → domFType α} {M3 : r → domFType α} :
    refF P2 M2 M3 P3 → refF P1 M1 M2 P2 → refF P1 M1 M3 P3 := by
  intro h23 h12
  simpa [refF] using le_trans h23 h12

/- The Isabelle theorem bundle `cspF_trans_right` is represented by
   `cspF_trans_right_eq` and `cspF_trans_right_ref`. -/

/- (*** rewrite (eq) ***) -/

theorem cspF_rw_left_eq_MF [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqFfix P1 P2 → eqFfix P2 P3 → eqFfix P1 P3 := by
  intro h12 h23
  simpa [eqF] using Eq.trans h12 h23

theorem cspF_rw_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    eqF P1 M1 M1 P2 → eqF P2 M1 M3 P3 → eqF P1 M1 M3 P3 := by
  intro h12 h23
  simpa [eqF] using Eq.trans h12 h23

theorem cspF_rw_left_ref_MF [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqFfix P1 P2 → refFfix P2 P3 → refFfix P1 P3 := by
  intro h12 h23
  change semFf P1 MF = semFf P2 MF at h12
  change semFf P3 MF <= semFf P2 MF at h23
  change semFf P3 MF <= semFf P1 MF
  exact h12.symm ▸ h23

theorem cspF_rw_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    eqF P1 M1 M1 P2 → refF P2 M1 M3 P3 → refF P1 M1 M3 P3 := by
  intro h12 h23
  change semFf P1 M1 = semFf P2 M1 at h12
  change semFf P3 M3 <= semFf P2 M1 at h23
  change semFf P3 M3 <= semFf P1 M1
  exact h12.symm ▸ h23

/- The Isabelle theorem bundle `cspF_rw_left` is represented by
   `cspF_rw_left_eq_MF`, `cspF_rw_left_ref_MF`, `cspF_rw_left_eq`,
   and `cspF_rw_left_ref`. -/

theorem cspF_rw_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    eqF P3 M3 M3 P2 → eqF P1 M1 M3 P2 → eqF P1 M1 M3 P3 := by
  intro h32 h12
  change semFf P3 M3 = semFf P2 M3 at h32
  change semFf P1 M1 = semFf P2 M3 at h12
  change semFf P1 M1 = semFf P3 M3
  exact h32.symm ▸ h12

theorem cspF_rw_right_eq_MF [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqFfix P3 P2 → eqFfix P1 P2 → eqFfix P1 P3 := by
  intro h32 h12
  change semFf P3 MF = semFf P2 MF at h32
  change semFf P1 MF = semFf P2 MF at h12
  change semFf P1 MF = semFf P3 MF
  exact h32.symm ▸ h12

theorem cspF_rw_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    eqF P3 M3 M3 P2 → refF P1 M1 M3 P2 → refF P1 M1 M3 P3 := by
  intro h32 h12
  change semFf P3 M3 = semFf P2 M3 at h32
  change semFf P2 M3 <= semFf P1 M1 at h12
  change semFf P3 M3 <= semFf P1 M1
  exact h32.symm ▸ h12

theorem cspF_rw_right_ref_MF [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqFfix P3 P2 → refFfix P1 P2 → refFfix P1 P3 := by
  intro h32 h12
  change semFf P3 MF = semFf P2 MF at h32
  change semFf P2 MF <= semFf P1 MF at h12
  change semFf P3 MF <= semFf P1 MF
  exact h32.symm ▸ h12

/- The Isabelle theorem bundle `cspF_rw_right` is represented by
   `cspF_rw_right_eq_MF`, `cspF_rw_right_ref_MF`, `cspF_rw_right_eq`,
   and `cspF_rw_right_ref`. -/

/- (*** rewrite (ref) ***) -/

theorem cspF_tr_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    eqF P1 M1 M1 P2 → eqF P2 M1 M3 P3 → eqF P1 M1 M3 P3 := by
  exact cspF_rw_left_eq

theorem cspF_tr_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    refF P1 M1 M1 P2 → refF P2 M1 M3 P3 → refF P1 M1 M3 P3 := by
  intro h12 h23
  simpa [refF] using le_trans h23 h12

/- The Isabelle theorem bundle `cspF_tr_left` is represented by
   `cspF_tr_left_eq` and `cspF_tr_left_ref`. -/

theorem cspF_tr_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    eqF P2 M3 M3 P3 → eqF P1 M1 M3 P2 → eqF P1 M1 M3 P3 := by
  intro h23 h12
  simpa [eqF] using Eq.trans h12 h23

theorem cspF_tr_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} :
    refF P2 M3 M3 P3 → refF P1 M1 M3 P2 → refF P1 M1 M3 P3 := by
  intro h23 h12
  simpa [refF] using le_trans h23 h12

/- The Isabelle theorem bundle `cspF_tr_right` is represented by
   `cspF_tr_right_eq` and `cspF_tr_right_ref`. -/

/-
(*----------------------------------------*
 |   rewriting processes in assumptions   |
 *----------------------------------------*)
-/

/- (*** rewrite (eq) ***) -/

theorem cspF_rw_left_eqE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    eqFfix P1 P3 → eqFfix P1 P2 → (eqFfix P2 P3 → R) → R := by
  intro h13 h12 hR
  apply hR
  simpa [eqF] using Eq.trans h12.symm h13

theorem cspF_rw_left_eqE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop} :
    eqF P1 M1 M3 P3 → eqF P1 M1 M1 P2 → (eqF P2 M1 M3 P3 → R) → R := by
  intro h13 h12 hR
  apply hR
  simpa [eqF] using Eq.trans h12.symm h13

theorem cspF_rw_left_refE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    refFfix P1 P3 → eqFfix P1 P2 → (refFfix P2 P3 → R) → R := by
  intro h13 h12 hR
  apply hR
  change semFf P1 MF = semFf P2 MF at h12
  change semFf P3 MF <= semFf P1 MF at h13
  change semFf P3 MF <= semFf P2 MF
  exact h12 ▸ h13

theorem cspF_rw_left_refE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop} :
    refF P1 M1 M3 P3 → eqF P1 M1 M1 P2 → (refF P2 M1 M3 P3 → R) → R := by
  intro h13 h12 hR
  apply hR
  change semFf P1 M1 = semFf P2 M1 at h12
  change semFf P3 M3 <= semFf P1 M1 at h13
  change semFf P3 M3 <= semFf P2 M1
  exact h12 ▸ h13

/- The Isabelle theorem bundle `cspF_rw_leftE` is represented by
   `cspF_rw_left_eqE_MF`, `cspF_rw_left_refE_MF`, `cspF_rw_left_eqE`,
   and `cspF_rw_left_refE`. -/

theorem cspF_rw_right_eqE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    eqFfix P1 P3 → eqFfix P3 P2 → (eqFfix P1 P2 → R) → R := by
  intro h13 h32 hR
  apply hR
  change semFf P1 MF = semFf P3 MF at h13
  change semFf P3 MF = semFf P2 MF at h32
  change semFf P1 MF = semFf P2 MF
  exact h32 ▸ h13

theorem cspF_rw_right_eqE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop} :
    eqF P1 M1 M3 P3 → eqF P3 M3 M3 P2 → (eqF P1 M1 M3 P2 → R) → R := by
  intro h13 h32 hR
  apply hR
  change semFf P1 M1 = semFf P3 M3 at h13
  change semFf P3 M3 = semFf P2 M3 at h32
  change semFf P1 M1 = semFf P2 M3
  exact h32 ▸ h13

theorem cspF_rw_right_refE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    refFfix P1 P3 → eqFfix P3 P2 → (refFfix P1 P2 → R) → R := by
  intro h13 h32 hR
  apply hR
  change semFf P3 MF <= semFf P1 MF at h13
  change semFf P3 MF = semFf P2 MF at h32
  change semFf P2 MF <= semFf P1 MF
  exact h32 ▸ h13

theorem cspF_rw_right_refE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop} :
    refF P1 M1 M3 P3 → eqF P3 M3 M3 P2 → (refF P1 M1 M3 P2 → R) → R := by
  intro h13 h32 hR
  apply hR
  change semFf P3 M3 <= semFf P1 M1 at h13
  change semFf P3 M3 = semFf P2 M3 at h32
  change semFf P2 M3 <= semFf P1 M1
  exact h32 ▸ h13

/- The Isabelle theorem bundle `cspF_rw_rightE` is represented by
   `cspF_rw_right_eqE_MF`, `cspF_rw_right_refE_MF`, `cspF_rw_right_eqE`,
   and `cspF_rw_right_refE`. -/

/-
(*-----------------------------------------*
 |                   noPN                  |
 *-----------------------------------------*)
-/

axiom failures_noPN_Constant_lm_EC {X : Set α} {Pf : α → proc p α} :
    (∀ P ∈ Set.range Pf, ∃ F, failures P = fun _ => F) →
      ∃ F2, failures (proc.Ext_pre_choice X Pf) = fun _ => F2

axiom failures_noPN_Constant_lm_RIC {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ P ∈ Set.range Pf, ∃ F, failures P = fun _ => F) →
      ∃ F2, failures (proc.Rep_int_choice C Pf) = fun _ => F2

axiom failures_noPN_Constant_lm {P : proc p α} :
    noPN P → ∃ F, failures P = fun _ => F

theorem failures_noPN_Constant {P : proc p α} :
    noPN P → ∃ F, failures P = fun _ => F :=
  failures_noPN_Constant_lm

end
