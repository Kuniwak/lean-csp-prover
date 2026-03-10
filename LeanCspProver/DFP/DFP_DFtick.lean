           /- -------------------------------------------*
            |                  DFtick                   |
            |                                           |
            |                   June 2007               |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DFP.DFP_Deadlock

open event

noncomputable section

variable {α : Type _}

/- Lean note:
   Isabelle's local simp-set update `declare csp_prefix_ss_def[simp]` has no
   direct analogue here. -/

/- *****************************************************************

         1. The most abstract deadlockfree process DFtick

 *****************************************************************) -/

/- *********************************************************
                         event
 *********************************************************) -/

/- typedecl Event    any event -/

inductive DFtickName where
  | DFtick
deriving DecidableEq, Inhabited

/- (*** Spc ***) -/

def DFtickfun : DFtickName → proc DFtickName α
  | DFtickName.DFtick =>
      proc.Ext_pre_choice Set.univ (fun _ : α => proc.Proc_name DFtickName.DFtick) |~| proc.SKIP

instance Set_DFtickfun : HasPNfun DFtickName α where
  PNfun := DFtickfun

@[simp]
theorem Set_DFtickfun_def (pn : DFtickName) :
    PNfun (p := DFtickName) (α := α) pn = DFtickfun (α := α) pn :=
  rfl

/- ---------------------------------------------------*
 |                  n-replicted spec                 |
 *--------------------------------------------------- -/

inductive RDFtickName where
  | RDFtick
deriving DecidableEq, Inhabited

/- (*** Spc ***) -/

def NatDFtick : Nat → proc RDFtickName α → proc RDFtickName α
  | 0, P => P
  | Nat.succ n, P =>
      (proc.Ext_pre_choice Set.univ (fun _ : α => NatDFtick n P) |~| proc.SKIP) |~| P

def RDFtickfun : RDFtickName → proc RDFtickName α
  | RDFtickName.RDFtick =>
      proc.Ext_pre_choice Set.univ (fun _ : α =>
        Rep_int_choice_nat Set.univ
          (fun n => NatDFtick n (proc.Proc_name RDFtickName.RDFtick)) |~| proc.SKIP)

instance Set_RDFtickfun : HasPNfun RDFtickName α where
  PNfun := RDFtickfun

@[simp]
theorem Set_RDFtickfun_def (pn : RDFtickName) :
    PNfun (p := RDFtickName) (α := α) pn = RDFtickfun (α := α) pn :=
  rfl

/- *********************************************************
              DFtick lemma
 *********************************************************) -/

@[simp]
axiom guardedfun_DFtick :
    guardedfun (p := DFtickName) (q := DFtickName) (α := α) (DFtickfun (α := α))

@[simp]
axiom guardedfun_RDFtick :
    guardedfun (p := RDFtickName) (q := RDFtickName) (α := α) (RDFtickfun (α := α))

/- -------------------------------------------------*
 |                                                  |
 |  syntactical approach --> semantical approach    |
 |                                                  |
 * ------------------------------------------------- -/

/- (*** sub ***) -/

axiom DFtick_is_DeadlockFree [HasFPmode] :
    isDeadlockFree (proc.Proc_name DFtickName.DFtick : proc DFtickName α)

/- (*** main ***) -/

theorem DFtick_DeadlockFree
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α}
    (hRef : refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P) :
    isDeadlockFree P := by
  have hDF :
      DeadlockFree Set.univ (proc.Proc_name DFtickName.DFtick : proc DFtickName α) :=
    (isDeadlockFree_def _).mp DFtick_is_DeadlockFree
  have hFailSub :
      failures P MF <= failures (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF :=
    (cspF_refF_semantics
      (P := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
      (Q := P) (M1 := MF) (M2 := MF)).mp hRef |>.2
  rw [isDeadlockFree_def, DeadlockFree_def]
  intro s hsNoTick hsFail
  exact hDF s hsNoTick (hFailSub hsFail)

/- -------------------------------------------------*
 |                                                  |
 |  semantical approach --> syntactical approach    |
 |                                                  |
 * ------------------------------------------------- -/

axiom traces_included_in_DFtick [HasFPmode] {t : traceType α} :
    t :t traces ((FIX DFtickfun) DFtickName.DFtick) (fstF ∘ MF)

axiom failures_included_in_DFtick_lm [HasFPmode] {t : traceType α} {X : Set (event α)} :
    (X ≠ Set.univ ∨ Tick ∈ sett t) →
      (t, X) :f failures ((FIX DFtickfun) DFtickName.DFtick) MF

theorem failures_included_in_DFtick [HasFPmode] {t : traceType α} {X : Set (event α)}
    (hX : X ≠ Set.univ) (_hTick : Tick ∈ sett t) :
    (t, X) :f failures ((FIX DFtickfun) DFtickName.DFtick) MF := by
  exact failures_included_in_DFtick_lm (t := t) (X := X) (Or.inl hX)

axiom DeadlockFree_DFtick
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α} :
    isDeadlockFree P →
      refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P

/- -------------------------------------------------*
 |                                                  |
 |  syntactical approach <--> semantical approach   |
 |                                                  |
 * ------------------------------------------------- -/

theorem DeadlockFree_DFtick_ref
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α} :
    isDeadlockFree P ↔
      refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P := by
  constructor
  · exact DeadlockFree_DFtick
  · exact DFtick_DeadlockFree

/- ================================================================*
 |                                                                |
 |                   n-replicted DF specification                 |
 |                                                                |
 *================================================================ -/

/- *******************************************************************
        relating function between DFtickName and Rep...
 *******************************************************************) -/

/- (*** ref1 ***) -/

def RepDF_to_DF : RDFtickName → proc DFtickName α
  | RDFtickName.RDFtick => proc.Proc_name DFtickName.DFtick

axiom RDFtick_DFtick_ref1_induct_lm [HasFPmode] {n : Nat} :
    refF ((proc.Proc_name DFtickName.DFtick : proc DFtickName α)) MF MF
      ((NatDFtick n (proc.Proc_name RDFtickName.RDFtick)) << RepDF_to_DF)

axiom RDFtick_DFtick_ref1 [HasFPmode] :
    refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF
      (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α)

/- (*** ref2 ***) -/

def DF_to_RepDF : DFtickName → proc RDFtickName α
  | DFtickName.DFtick => proc.Proc_name RDFtickName.RDFtick

axiom RDFtick_DFtick_ref2 [HasFPmode] :
    refF (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) MF MF
      (proc.Proc_name DFtickName.DFtick : proc DFtickName α)

/- **************************** =F**************************** -/

theorem RDFtick_DFtick [HasFPmode] :
    eqF (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) MF MF
      (proc.Proc_name DFtickName.DFtick : proc DFtickName α) := by
  exact (cspF_eq_ref_iff
    (P1 := (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α))
    (P2 := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
    (M1 := MF) (M2 := MF)).2 ⟨RDFtick_DFtick_ref2, RDFtick_DFtick_ref1⟩

/- ---------------------------------------------------*
 |                                                    |
 |  syntactical approach 2 <--> semantical approach   |
 |                                                    |
 * --------------------------------------------------- -/

theorem DeadlockFree_RDFtick_ref
    {p : Type _} [HasPNfun p α] [HasFPmode] {P : proc p α} :
    isDeadlockFree P ↔
      refF (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α) MF MF P := by
  constructor
  · intro hDF
    have hDFtick :
        refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P :=
      (DeadlockFree_DFtick_ref (P := P)).1 hDF
    exact cspF_trans_left_ref
      (cspF_eq_ref
        (P1 := (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α))
        (P2 := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
        (M1 := MF) (M2 := MF) RDFtick_DFtick)
      hDFtick
  · intro hRDFtick
    have hDFtick :
        refF (proc.Proc_name DFtickName.DFtick : proc DFtickName α) MF MF P :=
      cspF_trans_left_ref
        (cspF_eq_ref
          (P1 := (proc.Proc_name DFtickName.DFtick : proc DFtickName α))
          (P2 := (proc.Proc_name RDFtickName.RDFtick : proc RDFtickName α))
          (M1 := MF) (M2 := MF) (cspF_sym RDFtick_DFtick))
        hRDFtick
    exact (DeadlockFree_DFtick_ref (P := P)).2 hDFtick

/- Lean note:
   Isabelle's local simp-set update `declare csp_prefix_ss_def[simp del]` has
   no direct analogue here. -/
