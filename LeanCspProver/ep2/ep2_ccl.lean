           /- -------------------------------------------*
            |                 (a part of) ep2            |
            |                  September 2004            |
            |                   December 2004 (modified) |
            |                   November 2005 (modified) |
            |                      April 2006 (modified) |
            |                      March 2007 (modified) |
            |                                            |
            |        CSP-Prover on Isabelle2009          |
            |                       June 2009  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2016          |
            |                        May 2016  (modified)|
            |                                            |
            |  Markus Roggenbach (Univ of Wales Swansea, |
            |  UK)                                       |
            |  Yoshinao Isobe    (AIST, Japan)           |
            *------------------------------------------- -/

import LeanCspProver.ep2.ep2_acl

open fpmode
open ep2_acl

noncomputable section

namespace ep2_ccl

local notation:50 P " <=F " Q => refF P MF MF Q

private noncomputable def decideMem {α : Type _} (x : α) (X : Set α) : Bool := by
  classical
  exact decide (x ∈ X)

/- *********************************************************
                    functions
 ********************************************************* -/

/- pair -/
def state : TerminalState × Trigger → TerminalState
  | (s, _) => s

theorem state_def (p : TerminalState × Trigger) :
    state p = Prod.fst p := by
  cases p
  rfl

def trigger : TerminalState × Trigger → Trigger
  | (_, t) => t

theorem trigger_def (p : TerminalState × Trigger) :
    trigger p = Prod.snd p := by
  cases p
  rfl

/- Session start -/
/- Lean note:
   Isabelle's unspecified `consts` were ported as `axiom`s; they are now
   `noncomputable opaque` constants (the codomains are inhabited), the
   same abstraction without extending the axiom base. -/

noncomputable opaque sessionStart : Trigger → D_SI_Init_SessionStart

/- ConfigDataRequest -/
noncomputable opaque configDataResponse :
  D_SI_Init_ConfigDataRequest × TerminalState →
    D_SI_Init_ConfigDataResponse

/- ConfigDataNotification -/
noncomputable opaque configDataAcknowledge : D_SI_Init_ConfigDataAcknowledge
noncomputable opaque configData :
  D_SI_Init_ConfigDataNotification × TerminalState →
    TerminalState

/- ConfigDataRemove -/
noncomputable opaque removeDataAcknowledge : D_SI_Init_RemoveConfigDataAcknowledge
noncomputable opaque removeData :
  D_SI_Init_RemoveConfigDataNotification × TerminalState →
    TerminalState

/- ActivateConfigDataNotification -/
noncomputable opaque activateDataAcknowledge : D_SI_Init_ActivateConfigDataAcknowledge
noncomputable opaque activateData :
  D_SI_Init_ActivateConfigDataNotification × TerminalState →
    TerminalState

/- Message -/
noncomputable opaque AcqConnectionFailed : Message
noncomputable opaque InitialisationFinished : Message
noncomputable opaque InitialisationFailed : Message

/- *********************************************************
         concrete component description level
 ********************************************************* -/

inductive CCName where
  | CTInit : TerminalState × Trigger → CCName
  | CTConfigurationManagement : TerminalState × Trigger → CCName
  | CAcquirerInit
  | CConfigurationManagement

instance : Inhabited CCName where
  default := CCName.CTInit default

noncomputable instance : DecidableEq CCName := Classical.decEq _

def CCfun : CCName → proc CCName Event
  | CCName.CTInit p =>
      Event.C_SI_Init (D_SI_Init.SStart (sessionStart (trigger p))) ~>
        proc.Proc_name (CCName.CTConfigurationManagement p)
  | CCName.CTConfigurationManagement p =>
      Rec_prefix Event.C_SI_Init Set.univ fun x =>
        IF decideMem x (Set.range D_SI_Init.CDReq) THEN
          (Event.C_SI_Init
              (D_SI_Init.CDRes
                (configDataResponse (Function.invFun D_SI_Init.CDReq x, state p))) ~>
            proc.Proc_name (CCName.CTConfigurationManagement p))
        ELSE IF decideMem x (Set.range D_SI_Init.CDN) THEN
          (Event.C_SI_Init (D_SI_Init.CDA configDataAcknowledge) ~>
            proc.Proc_name
              (CCName.CTConfigurationManagement
                (configData (Function.invFun D_SI_Init.CDN x, state p), trigger p)))
        ELSE IF decideMem x (Set.range D_SI_Init.RCDN) THEN
          (Event.C_SI_Init (D_SI_Init.RCDA removeDataAcknowledge) ~>
            proc.Proc_name
              (CCName.CTConfigurationManagement
                (removeData (Function.invFun D_SI_Init.RCDN x, state p), trigger p)))
        ELSE IF decideMem x (Set.range D_SI_Init.ACDN) THEN
          (Event.C_SI_Init (D_SI_Init.ACDA activateDataAcknowledge) ~>
            proc.Proc_name
              (CCName.CTConfigurationManagement
                (activateData (Function.invFun D_SI_Init.ACDN x, state p), trigger p)))
        ELSE IF decideMem x (Set.range D_SI_Init.SEnd) THEN
          (Event.C_TerminalDisplay InitialisationFinished ~> proc.SKIP)
        ELSE
          proc.STOP
  | CCName.CAcquirerInit =>
      Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.SStart) fun _ =>
        proc.Proc_name CCName.CConfigurationManagement
  | CCName.CConfigurationManagement =>
      (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.SEnd) fun _ =>
        proc.SKIP) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDReq) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.CDRes) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.CDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.CDA) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.RCDA) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement) |~|
        (Nondet_send_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDN) fun _ =>
          Rec_prefix Event.C_SI_Init (Set.range D_SI_Init.ACDA) fun _ =>
            proc.Proc_name CCName.CConfigurationManagement)

instance Set_CCfun : HasPNfun CCName Event where
  PNfun := CCfun

@[simp]
theorem Set_CCfun_def (pn : CCName) :
    PNfun pn = CCfun pn :=
  rfl

def CC : (TerminalState × Trigger) → proc CCName Event :=
  fun p =>
    (proc.Hiding
      (proc.Proc_name (CCName.CTInit p))
      (Set.range Event.C_TerminalDisplay)) |[Set.range Event.C_SI_Init]|
      (proc.Proc_name CCName.CAcquirerInit)

theorem CC_def (p : TerminalState × Trigger) :
    CC p =
      (proc.Hiding
        (proc.Proc_name (CCName.CTInit p))
        (Set.range Event.C_TerminalDisplay)) |[Set.range Event.C_SI_Init]|
        (proc.Proc_name CCName.CAcquirerInit) :=
  rfl

/- *********************************************************
                gProc lemmas (routine work)
 ********************************************************* -/

@[simp] theorem guarded_CC :
    guardedfun CCfun := by
  intro pn
  cases pn <;>
    simp [CCfun, Rec_prefix, guarded, noHide]

/- *********************************************************
        relating function between AbsName and ACName
 ********************************************************* -/

/- Lean note:
   Isabelle's `!<f> :X .. Pf` (`CSP_syntax.thy:252`,
   `!<f> :X .. Pf == ! :(f ` X) .. (%x. Pf ((inv f) x))`) is a replicated
   *internal choice* indexed through `f`; it performs no event.  The port had
   `Nondet_send_prefix`, which is `!<f> :X -> Pf` and prefixes each branch
   with `f x`.  The source here writes `..`, so it is `Rep_int_choice_f`. -/

def AC_to_CC : ACName → proc CCName Event
  | ACName.TInit =>
      Rep_int_choice_f Event.PairTT Set.univ fun p =>
        proc.Hiding
          (proc.Proc_name (CCName.CTInit p))
          (Set.range Event.C_TerminalDisplay)
  | ACName.TConfigurationManagement =>
      Rep_int_choice_f Event.PairTT Set.univ fun p =>
        proc.Hiding
          (proc.Proc_name (CCName.CTConfigurationManagement p))
          (Set.range Event.C_TerminalDisplay)
  | ACName.AcquirerInit =>
      proc.Proc_name CCName.CAcquirerInit
  | ACName.ConfigurationManagement =>
      proc.Proc_name CCName.CConfigurationManagement

/- *********************************************************
           a theorem for verifying !!p. AC <=F CC p
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare inj_on_def [simp]` has no direct Lean analogue here. -/

private theorem inj_PairTT : Function.Injective Event.PairTT := by
  intro a b h
  cases h
  rfl

private theorem inj_C_SI_Init : Function.Injective Event.C_SI_Init := by
  intro a b h
  cases h
  rfl

private theorem unwCC (pn : CCName) :
    eqF (proc.Proc_name pn : proc CCName Event) MF MF (CCfun pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guarded_CC⟩))

/-- Hiding the terminal display leaves a `C_SI_Init` prefix untouched. -/
private theorem hide_C_SI_Init (x : D_SI_Init) (P : proc CCName Event) :
    eqF (proc.Hiding (Event.C_SI_Init x ~> P) (Set.range Event.C_TerminalDisplay)) MF MF
      (Event.C_SI_Init x ~> proc.Hiding P (Set.range Event.C_TerminalDisplay)) :=
  cspF_Hiding_Act_prefix_notin (by simp)

theorem ep2_ccl_terminal_step1 :
    (ACfun ACName.TInit) << AC_to_CC <=F AC_to_CC ACName.TInit := by
  simp only [AC_to_CC]
  refine cspF_Rep_int_choice_f_right inj_PairTT (fun q _ => ?_)
  refine cspF_rw_right_ref
    (cspF_trans_left_eq (cspF_Hiding_cong rfl (unwCC (CCName.CTInit q)))
      (hide_C_SI_Init _ _)) ?_
  simp only [ACfun, AC_to_CC, Subst_procfun_Nondet_send_prefix, Subst_procfun]
  refine cspF_Nondet_send_prefix_left_x
    (a := D_SI_Init.SStart (sessionStart (trigger q))) inj_C_SI_Init ⟨_, rfl⟩ ?_
  refine cspF_Act_prefix_mono rfl ?_
  exact cspF_Rep_int_choice_f_left_x (f := Event.PairTT) (X := Set.univ)
    (Pf := fun r => proc.Hiding (proc.Proc_name (CCName.CTConfigurationManagement r))
      (Set.range Event.C_TerminalDisplay))
    (a := q) inj_PairTT (Set.mem_univ q) cspF_reflex_ref_P

/-- A single acknowledgement branch of the loop: the abstract side picks the
    very value that the concrete side is about to send, and then the internal
    choice over terminal states picks the concrete successor state. -/
private theorem step2_branch {γ : Type} [Inhabited γ] (g : γ → D_SI_Init) (v : γ)
    (r : TerminalState × Trigger) :
    refF
      (Nondet_send_prefix Event.C_SI_Init (Set.range g) fun _ =>
        Rep_int_choice_f Event.PairTT Set.univ fun s =>
          proc.Hiding (proc.Proc_name (CCName.CTConfigurationManagement s))
            (Set.range Event.C_TerminalDisplay))
      MF MF
      (proc.Hiding
        (Event.C_SI_Init (g v) ~> proc.Proc_name (CCName.CTConfigurationManagement r))
        (Set.range Event.C_TerminalDisplay)) := by
  refine cspF_rw_right_ref (hide_C_SI_Init _ _) ?_
  refine cspF_Nondet_send_prefix_left_x (a := g v) inj_C_SI_Init ⟨v, rfl⟩ ?_
  refine cspF_Act_prefix_mono rfl ?_
  exact cspF_Rep_int_choice_f_left_x (f := Event.PairTT) (X := Set.univ)
    (Pf := fun s => proc.Hiding (proc.Proc_name (CCName.CTConfigurationManagement s))
      (Set.range Event.C_TerminalDisplay))
    (a := r) inj_PairTT (Set.mem_univ r) cspF_reflex_ref_P

/-- The session-end branch: the concrete side reports on the terminal display,
    which is hidden, and both sides terminate. -/
private theorem step2_SEnd :
    refF (proc.SKIP : proc CCName Event) MF MF
      (proc.Hiding
        (Event.C_TerminalDisplay InitialisationFinished ~> (proc.SKIP : proc CCName Event))
        (Set.range Event.C_TerminalDisplay)) :=
  cspF_rw_right_ref
    (cspF_trans_left_eq (cspF_Hiding_Act_prefix_in ⟨_, rfl⟩) cspF_SKIP_Hiding_Id)
    cspF_reflex_ref_P

theorem ep2_ccl_terminal_step2 :
    (ACfun ACName.TConfigurationManagement) << AC_to_CC <=F
      AC_to_CC ACName.TConfigurationManagement := by
  have hdisj :
      Event.C_SI_Init '' (Set.univ : Set D_SI_Init) ∩
        Set.range Event.C_TerminalDisplay = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨⟨x, -, rfl⟩, y, hy⟩
    exact absurd hy (by simp)
  simp only [AC_to_CC]
  refine cspF_Rep_int_choice_f_right inj_PairTT (fun q _ => ?_)
  refine cspF_rw_right_ref
    (cspF_Hiding_cong rfl (unwCC (CCName.CTConfigurationManagement q))) ?_
  simp only [CCfun, ACfun, AC_to_CC, Subst_procfun_Rec_prefix,
    Subst_procfun_Nondet_send_prefix, Subst_procfun]
  refine cspF_rw_right_ref (cspF_Hiding_Rec_prefix_notin hdisj) ?_
  refine cspF_Rec_prefix_mono inj_C_SI_Init rfl rfl (fun x _ => ?_)
  refine cspF_rw_right_ref cspF_Hiding_IF ?_
  refine cspF_IF_mono rfl
    (step2_branch D_SI_Init.CDRes
      (configDataResponse (Function.invFun D_SI_Init.CDReq x, state q)) q) ?_
  refine cspF_rw_right_ref cspF_Hiding_IF ?_
  refine cspF_IF_mono rfl
    (step2_branch D_SI_Init.CDA configDataAcknowledge
      (configData (Function.invFun D_SI_Init.CDN x, state q), trigger q)) ?_
  refine cspF_rw_right_ref cspF_Hiding_IF ?_
  refine cspF_IF_mono rfl
    (step2_branch D_SI_Init.RCDA removeDataAcknowledge
      (removeData (Function.invFun D_SI_Init.RCDN x, state q), trigger q)) ?_
  refine cspF_rw_right_ref cspF_Hiding_IF ?_
  refine cspF_IF_mono rfl
    (step2_branch D_SI_Init.ACDA activateDataAcknowledge
      (activateData (Function.invFun D_SI_Init.ACDN x, state q), trigger q)) ?_
  refine cspF_rw_right_ref cspF_Hiding_IF ?_
  refine cspF_IF_mono rfl step2_SEnd ?_
  exact cspF_rw_right_ref cspF_STOP_Hiding_Id cspF_reflex_ref_P

theorem ACDef_AC_to_CC (p : ACName) :
    (ACfun p) << AC_to_CC <=F AC_to_CC p := by
  cases p with
  | TInit => exact ep2_ccl_terminal_step1
  | TConfigurationManagement => exact ep2_ccl_terminal_step2
  | AcquirerInit =>
      exact cspF_rw_right_ref (unwCC CCName.CAcquirerInit) cspF_reflex_ref_P
  | ConfigurationManagement =>
      refine cspF_rw_right_ref (unwCC CCName.CConfigurationManagement) ?_
      simp only [ACfun, CCfun, Subst_procfun_Nondet_send_prefix, Subst_procfun]
      exact cspF_reflex_ref_P

/- ****************************
      !!p. AC p <=F CC p
 **************************** -/

theorem ep2_acl_ccl : ∀ p, AC <=F CC p := by
  intro p
  rw [AC_def, CC_def]
  refine cspF_Parallel_mono rfl ?_ ?_
  · refine cspF_fp_induct_ref_left (Pf := ACfun) (f := AC_to_CC) (p0 := ACName.TInit)
      rfl (Or.inl rfl) guarded_AC ?_ ACDef_AC_to_CC
    exact cspF_Rep_int_choice_f_left_x (f := Event.PairTT) (X := Set.univ)
      (Pf := fun q => proc.Hiding (proc.Proc_name (CCName.CTInit q))
        (Set.range Event.C_TerminalDisplay))
      (a := p) inj_PairTT (Set.mem_univ p) cspF_reflex_ref_P
  · refine cspF_fp_induct_ref_left (Pf := ACfun) (f := AC_to_CC) (p0 := ACName.AcquirerInit)
      rfl (Or.inl rfl) guarded_AC cspF_reflex_ref_P ACDef_AC_to_CC

/- ****************************
      !!p. Abs <=F CC p
 **************************** -/

theorem ep2_abs_ccl :
    ∀ p, Abs <=F CC p := by
  intro p
  exact cspF_trans_left_ref ep2_abs (ep2_acl_ccl p)

/- Lean note:
   Isabelle's `declare inj_on_def [simp del]` has no direct Lean analogue
   here. -/

end ep2_ccl
