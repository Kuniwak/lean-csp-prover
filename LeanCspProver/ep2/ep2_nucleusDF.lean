           /- -------------------------------------------*
            |                 (a part of) ep2            |
            |                  September 2004            |
            |                   December 2004 (modified) |
            |                   November 2005 (modified) |
            |                      April 2006 (modified) |
            |                      March 2007  (modified)|
            |                     August 2007  (modified)|
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

import LeanCspProver.DFP
import LeanCspProver.ep2.ep2_nucleus

open fpmode

noncomputable section

namespace ep2_nucleusDF

local notation:50 P " <=F " Q => refF P MF MF Q

abbrev NEvent := ep2_nucleus.Event
abbrev NACName := ep2_nucleus.ACName

/- *********************************************************
                     abstract level
 ********************************************************* -/

inductive AbsName where
  | Abstract
  | Loop

instance : Inhabited AbsName where
  default := AbsName.Abstract

noncomputable instance : DecidableEq AbsName := Classical.decEq _

/- Lean note:
   `Absfun Loop` is `c !? x -> (SKIP |~| c !? x -> $Loop)` in the source
   (`ep2_nucleusDF.thy:37`): the internal choice is the *continuation* of a
   prefix.  The port had `SKIP |~| (c !? x -> $Loop)`, which hoists the
   choice out of the prefix and is a different process -- it can terminate
   immediately, so `$AcConfigManagement |[range c]| $TerminalConfigManagement`
   does not refine it and `ep2_Abs_AC` is not provable as ported. -/

def Absfun : AbsName → proc AbsName NEvent
  | AbsName.Abstract =>
      Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ =>
        proc.Proc_name AbsName.Loop
  | AbsName.Loop =>
      Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ =>
        proc.SKIP |~|
          (Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ =>
            proc.Proc_name AbsName.Loop)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Absfun : HasPNfun AbsName NEvent where
  PNfun := Absfun

@[simp]
theorem Set_Absfun_def (pn : AbsName) :
    PNfun pn = Absfun pn :=
  rfl

def Abs : proc AbsName NEvent :=
  proc.Proc_name AbsName.Abstract

theorem Abs_def :
    Abs = proc.Proc_name AbsName.Abstract :=
  rfl

/- *********************************************************
               guard lemmas (routine work)
 ********************************************************* -/

@[simp]
theorem guardedfun_Abs :
    guardedfun Absfun := by
  intro pn
  cases pn <;> simp [Absfun, noHide]

/- *********************************************************
        relating function between ACName and AbsName
 ********************************************************* -/

def Abs_to_AC : AbsName → proc NACName NEvent
  | AbsName.Abstract =>
      (proc.Proc_name ep2_nucleus.ACName.Acquirer) |[Set.range ep2_nucleus.Event.c]|
        (proc.Proc_name ep2_nucleus.ACName.Terminal)
  | AbsName.Loop =>
      (proc.Proc_name ep2_nucleus.ACName.AcConfigManagement) |[Set.range ep2_nucleus.Event.c]|
        (proc.Proc_name ep2_nucleus.ACName.TerminalConfigManagement)

/- *********************************************************
           a theorem for verifying Abs <=F AC
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare simp_event_set [simp]` has no direct Lean analogue
   here. -/

private theorem inj_c : Function.Injective ep2_nucleus.Event.c := by
  intro a b h
  cases h
  rfl

private theorem unwAC (pn : NACName) :
    eqF (proc.Proc_name pn : proc NACName NEvent) MF MF (ep2_nucleus.ACfun pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, ep2_nucleus.guardedfun_AC_Seq.1⟩))

private theorem range_ne {γ : Type _} [Inhabited γ] (f : γ → ep2_nucleus.Data) :
    Set.range f ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp ⟨f default, default, rfl⟩

theorem ep2_Abs_AC :
    Abs <=F ep2_nucleus.AC := by
  rw [Abs_def, ep2_nucleus.AC_def]
  refine cspF_fp_induct_ref_left (Pf := Absfun) (f := Abs_to_AC)
    rfl (Or.inl rfl) guardedfun_Abs cspF_reflex_ref_P ?_
  intro pn
  cases pn with
  | Abstract =>
      refine cspF_rw_right_ref
        (cspF_Parallel_cong rfl (unwAC ep2_nucleus.ACName.Acquirer)
          (unwAC ep2_nucleus.ACName.Terminal)) ?_
      simp only [Absfun, Abs_to_AC, ep2_nucleus.ACfun,
        Subst_procfun_Nondet_send_prefix, Subst_procfun]
      refine cspF_rw_right_ref
        (cspF_Parallel_Rec_Nondet_send_prefix (f := ep2_nucleus.Event.c)
          (A := Set.range ep2_nucleus.Data.Init) (B := Set.range ep2_nucleus.Data.Init)
          (Pf := fun _ => proc.Proc_name ep2_nucleus.ACName.AcConfigManagement)
          (Qf := fun _ => proc.Proc_name ep2_nucleus.ACName.TerminalConfigManagement)
          (Set.image_subset_range _ _) (subset_refl _)
          (range_ne ep2_nucleus.Data.Init)) ?_
      exact cspF_Nondet_send_prefix_subset inj_c (Set.subset_univ _)
        (fun _ _ => cspF_reflex_ref_P)
  | Loop =>
      refine cspF_rw_right_ref
        (cspF_Parallel_cong rfl (unwAC ep2_nucleus.ACName.AcConfigManagement)
          (unwAC ep2_nucleus.ACName.TerminalConfigManagement)) ?_
      simp only [Absfun, Abs_to_AC, ep2_nucleus.ACfun,
        Subst_procfun_Nondet_send_prefix, Subst_procfun]
      refine cspF_rw_right_ref cspF_Parallel_dist_l ?_
      refine cspF_Int_choice_right ?_ ?_
      · -- the terminal exits: the abstract side then chooses `SKIP`
        refine cspF_rw_right_ref
          (cspF_Parallel_Nondet_send_Rec_prefix (f := ep2_nucleus.Event.c)
            (A := Set.univ) (B := Set.range ep2_nucleus.Data.Exit)
            (Set.image_subset_range _ _) (Set.subset_univ _)
            (range_ne ep2_nucleus.Data.Exit)) ?_
        refine cspF_Nondet_send_prefix_subset inj_c (Set.subset_univ _) (fun x hx => ?_)
        obtain ⟨e, rfl⟩ := hx
        refine cspF_Int_choice_left1 ?_
        exact cspF_rw_right_ref
          (cspF_trans_left_eq
            (cspF_Parallel_cong rfl cspF_reflex_eq_P (ep2_nucleus.TCM_body_Exit e))
            cspF_Parallel_term)
          cspF_reflex_ref_P
      · -- a request/response round trip: the abstract side keeps looping
        refine cspF_rw_right_ref
          (cspF_Parallel_Nondet_send_Rec_prefix (f := ep2_nucleus.Event.c)
            (A := Set.univ) (B := Set.range ep2_nucleus.Data.Request)
            (Set.image_subset_range _ _) (Set.subset_univ _)
            (range_ne ep2_nucleus.Data.Request)) ?_
        refine cspF_Nondet_send_prefix_subset inj_c (Set.subset_univ _) (fun x hx => ?_)
        obtain ⟨r, rfl⟩ := hx
        refine cspF_Int_choice_left2 ?_
        refine cspF_rw_right_ref
          (cspF_Parallel_cong rfl cspF_reflex_eq_P (ep2_nucleus.TCM_body_Request r)) ?_
        refine cspF_rw_right_ref
          (cspF_Parallel_Rec_Nondet_send_prefix (f := ep2_nucleus.Event.c)
            (A := Set.range ep2_nucleus.Data.Response)
            (B := Set.range ep2_nucleus.Data.Response)
            (Pf := fun _ => proc.Proc_name ep2_nucleus.ACName.AcConfigManagement)
            (Qf := fun _ => proc.Proc_name ep2_nucleus.ACName.TerminalConfigManagement)
            (Set.image_subset_range _ _) (subset_refl _)
            (range_ne ep2_nucleus.Data.Response)) ?_
        exact cspF_Nondet_send_prefix_subset inj_c (Set.subset_univ _)
          (fun _ _ => cspF_reflex_ref_P)

/- *********************************************************
        relating function between ACName and AbsName
 ********************************************************* -/

def Abs_to_DF : AbsName → proc DFtickName NEvent
  | AbsName.Abstract => proc.Proc_name DFtickName.DFtick
  | AbsName.Loop => proc.Proc_name DFtickName.DFtick

/- *********************************************************
           a theorem for verifying Abs <=F AC
 ********************************************************* -/

private theorem DFtick_unwound :
    eqF (proc.Proc_name DFtickName.DFtick : proc DFtickName NEvent) MF MF
      (Int_pre_choice Set.univ
          (fun _ : NEvent => proc.Proc_name DFtickName.DFtick) |~| proc.SKIP) :=
  «cspF_unwind» (Pf := DFtickfun) rfl (Or.inr (Or.inl ⟨rfl, guardedfun_DFtick⟩))

/-- `$DFtick <=F ! x:(c ` univ) -> Q` whenever `$DFtick <=F Q` — the reusable
    core step. -/
private theorem DF_ref_send_gen {Q : proc DFtickName NEvent}
    (hQ : refF (proc.Proc_name DFtickName.DFtick : proc DFtickName NEvent) MF MF Q) :
    refF (proc.Proc_name DFtickName.DFtick : proc DFtickName NEvent) MF MF
      (Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ => Q) := by
  refine cspF_rw_left_ref DFtick_unwound ?_
  refine cspF_Int_choice_left1 ?_
  rw [Nondet_send_prefix_def, Int_pre_choice, Int_pre_choice]
  refine cspF_Rep_int_choice_com_right (fun a _ => ?_)
  refine cspF_Rep_int_choice_com_left ⟨a, Set.mem_univ a, ?_⟩
  exact cspF_Act_prefix_mono rfl hQ

private theorem DF_ref_send :
    refF (proc.Proc_name DFtickName.DFtick : proc DFtickName NEvent) MF MF
      (Nondet_send_prefix ep2_nucleus.Event.c Set.univ fun _ =>
        proc.Proc_name DFtickName.DFtick) :=
  DF_ref_send_gen cspF_reflex_ref_P

theorem ep2_DF_Abs :
    (proc.Proc_name DFtickName.DFtick : proc DFtickName NEvent) <=F Abs := by
  rw [Abs_def]
  refine cspF_fp_induct_cms_ref_right (Pf := Absfun) (f := Abs_to_DF)
    rfl guardedfun_Abs rfl cspF_reflex_ref_P (fun pn => ?_)
  cases pn with
  | Abstract =>
      simp only [Absfun, Subst_procfun_Nondet_send_prefix]
      exact DF_ref_send
  | Loop =>
      simp only [Absfun, Subst_procfun, Subst_procfun_Nondet_send_prefix]
      refine DF_ref_send_gen ?_
      refine cspF_Int_choice_right ?_ ?_
      · refine cspF_rw_left_ref DFtick_unwound ?_
        exact cspF_Int_choice_left2 cspF_reflex_ref_P
      · exact DF_ref_send

/- -------------------------------------------------------*
 |                 AC is Deadlock-free.                  |
 *------------------------------------------------------- -/

theorem AC_isDeadlockFree :
    isDeadlockFree ep2_nucleus.AC := by
  exact (DeadlockFree_DFtick_ref (P := ep2_nucleus.AC)).2
    (cspF_trans_left_ref ep2_DF_Abs ep2_Abs_AC)

end ep2_nucleusDF
