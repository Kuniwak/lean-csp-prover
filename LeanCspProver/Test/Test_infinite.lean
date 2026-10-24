           /- -------------------------------------------*
            |                   Test                    |
            |                                           |
            |        CSP-Prover on Isabelle2004         |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_Main

open fpmode

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Test_infinite

local notation:50 P " <=F " Q => refF P MF MF Q

/- *****************************************************************

         1. simple example for fixed point inductuction theorem
         2. Parallel, Hiding, Internal choice
         3. Refinement
         4.

 ***************************************************************** -/

/- *********************************************************
                         event
 ********************************************************* -/

inductive Event where
  | Num : Nat → Event
  | Read : Nat → Event
deriving DecidableEq, Inhabited

inductive SpcName where
  | SPC : Nat → SpcName
deriving DecidableEq, Inhabited

inductive ImpName where
  | UI
  | VAR : Nat → ImpName
deriving DecidableEq, Inhabited

/- *********************************************************
            specification SPC and system IMP
 ********************************************************* -/

def GTs : Nat → Set Nat
  | n => {m | n < m}

theorem GTs_def (n : Nat) :
    GTs n = {m | n < m} :=
  rfl

/- (*** Spc ***) -/

/- Lean note:
   Isabelle: `Spcfun (SPC n) = Num n -> (!nat m:(GTs n) .. $(SPC m))`.
   `!nat m:X .. P m` is the replicated *internal* choice
   (`Rep_int_choice_nat`); an earlier port spelled it
   `Rec_prefix Event.Read (GTs n) …`, i.e. the external prefix choice
   `Read ? m:X -> …`, which inserts visible `Read` events — but `Imp`
   hides all `Read` events, so `Spc <=F Imp` would not hold. Repaired. -/

def Spcfun : SpcName → proc SpcName Event
  | SpcName.SPC n =>
      Event.Num n ~> Rep_int_choice_nat (GTs n) fun m =>
        proc.Proc_name (SpcName.SPC m)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Spcfun : HasPNfun SpcName Event where
  PNfun := Spcfun

@[simp]
theorem Set_Spcfun_def (pn : SpcName) :
    PNfun pn = Spcfun pn :=
  rfl

def Spc : proc SpcName Event :=
  proc.Proc_name (SpcName.SPC 0)

theorem Spc_def :
    Spc = proc.Proc_name (SpcName.SPC 0) :=
  rfl

/- (*** Imp ***) -/

def Impfun : ImpName → proc ImpName Event
  | ImpName.UI =>
      Rec_prefix Event.Read Set.univ fun m =>
        Event.Num m ~> proc.Proc_name ImpName.UI
  | ImpName.VAR n =>
      Event.Read n ~> proc.Proc_name (ImpName.VAR (Nat.succ n))

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Impfun : HasPNfun ImpName Event where
  PNfun := Impfun

@[simp]
theorem Set_Impfun_def (pn : ImpName) :
    PNfun pn = Impfun pn :=
  rfl

theorem Set_Impfun_eq :
    (PNfun : ImpName → proc ImpName Event) = Impfun :=
  rfl

def Imp : proc ImpName Event :=
  proc.Hiding
    ((proc.Proc_name ImpName.UI) |[Set.range Event.Read]| (proc.Proc_name (ImpName.VAR 0)))
    (Set.range Event.Read)

theorem Imp_def :
    Imp =
      proc.Hiding
        ((proc.Proc_name ImpName.UI) |[Set.range Event.Read]| (proc.Proc_name (ImpName.VAR 0)))
        (Set.range Event.Read) :=
  rfl

/- *********************************************************
            relation between SPC and IMP
 ********************************************************* -/

def Spc_to_Imp : SpcName → proc ImpName Event
  | SpcName.SPC n =>
      proc.Hiding
        ((proc.Proc_name ImpName.UI) |[Set.range Event.Read]| (proc.Proc_name (ImpName.VAR n)))
        (Set.range Event.Read)

/- *********************************************************
                     small lemmas
 ********************************************************* -/

@[simp]
theorem set1 (n : Nat) :
    Set.range Event.Read ∩ ({Event.Read n} : Set Event) = ({Event.Read n} : Set Event) := by
  ext e
  constructor
  · intro h
    exact h.2
  · intro h
    constructor
    · rcases Set.mem_singleton_iff.mp h with rfl
      exact ⟨n, rfl⟩
    · exact h

@[simp]
theorem set2 (n : Nat) :
    (({Event.Read (Nat.succ n)} : Set Event) ∩
        (Set.range Event.Read ∩ ({Event.Num n} : Set Event))) ∪
      ((({Event.Num n} : Set Event) \ Set.range Event.Read)) =
        ({Event.Num n} : Set Event) := by
  ext e
  cases e <;> simp [Set.mem_range]

@[simp]
theorem set3 (n : Nat) :
    Event.Num n ∉ Set.range Event.Read := by
  simp [Set.mem_range]

theorem Read_inj : Function.Injective Event.Read := by
  intro a b h
  injection h

@[simp]
theorem invFun_Read (n : Nat) :
    Function.invFun Event.Read (Event.Read n) = n :=
  Function.leftInverse_invFun Read_inj n

/- index sets produced by `cspF_Parallel_step` in the proof below -/

theorem set4 (n : Nat) :
    ((Set.range Event.Read ∩ Set.range Event.Read ∩ {Event.Read n}) ∪
        (Set.range Event.Read \ Set.range Event.Read) ∪
        ({Event.Read n} \ Set.range Event.Read)) = {Event.Read n} := by
  ext e
  cases e <;> simp [Set.mem_range]

theorem set5 (n : Nat) :
    ((Set.range Event.Read ∩ {Event.Num n} ∩ {Event.Read (Nat.succ n)}) ∪
        ({Event.Num n} \ Set.range Event.Read) ∪
        ({Event.Read (Nat.succ n)} \ Set.range Event.Read)) = {Event.Num n} := by
  ext e
  cases e <;> simp [Set.mem_range]

theorem set6 (n : Nat) :
    ({Event.Read n} : Set Event) \ Set.range Event.Read = ∅ := by
  simp [Set.diff_eq_empty]

theorem set7 (n : Nat) :
    ({Event.Read n} : Set Event) ∩ Set.range Event.Read = {Event.Read n} := by
  simp

theorem set8 (n : Nat) :
    ({Event.Num n} : Set Event) ∩ Set.range Event.Read = ∅ := by
  ext e
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false,
    iff_false, not_and]
  rintro rfl
  exact set3 n

/- *********************************************************
               guardedfun (rutine work)
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare csp_prefix_ss_def[simp]` and `declare inj_on_def[simp]`
   have no direct Lean analogue here. -/

@[simp] theorem guardedfun_Spcfun :
    guardedfun Spcfun := by
  intro pn
  cases pn with
  | SPC n => simp [Spcfun, guarded, noHide, Rep_int_choice_nat]

@[simp] theorem guardedfun_Impfun :
    guardedfun Impfun := by
  intro pn
  cases pn <;> simp [Impfun, guarded, noHide, Rec_prefix]

/- *********************************************************
                   ? SPC <=F IMP ?
 ********************************************************* -/

/- Lean note:
   Isabelle's overloaded constant `FPmode` is represented by a typeclass
   instance. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def :
    FPmode = CMSmode :=
  rfl

/- it declares to use CMS approach.

   If you want to verify them by CPO approach,
   use the following mode:

defs FPmode_def [simp]: "FPmode == CPOmode"

   In this example, both modes are available,
   because Spcfun and Impfun are guarded.       -/

/- one step of the implementation:
   `Spc_to_Imp (SPC n) =F Num n -> Spc_to_Imp (SPC (Suc n))`,
   obtained by unwinding `$UI` and `$(VAR n)`, one synchronised (and then
   hidden) `Read n`, and one visible `Num n`. -/

private theorem Spc_to_Imp_step (n : Nat) :
    eqF (Spc_to_Imp (SpcName.SPC n)) MF MF
      (Event.Num n ~> Spc_to_Imp (SpcName.SPC (Nat.succ n))) := by
  -- unwind $UI into an external prefix choice over `range Read`
  have hUI : eqF (proc.Proc_name ImpName.UI : proc ImpName Event) MF MF
      (proc.Ext_pre_choice (Set.range Event.Read) fun x =>
        Event.Num (Function.invFun Event.Read x) ~> proc.Proc_name ImpName.UI) := by
    have h := «cspF_unwind» (Pf := Impfun) (p0 := ImpName.UI) rfl
      (Or.inr (Or.inl ⟨rfl, guardedfun_Impfun⟩))
    simpa [Impfun, Rec_prefix, Set.image_univ] using h
  -- unwind $(VAR k) into an external prefix choice over `{Read k}`
  have hVAR : ∀ k : Nat,
      eqF (proc.Proc_name (ImpName.VAR k) : proc ImpName Event) MF MF
        (proc.Ext_pre_choice ({Event.Read k} : Set Event) fun _ =>
          proc.Proc_name (ImpName.VAR (Nat.succ k))) := by
    intro k
    have h := «cspF_unwind» (Pf := Impfun) (p0 := ImpName.VAR k) rfl
      (Or.inr (Or.inl ⟨rfl, guardedfun_Impfun⟩))
    simp only [Impfun] at h
    exact cspF_trans_left_eq h cspF_Act_prefix_step
  -- $UI |[R]| $(VAR n)  =F  ? x:{Read n} -> ((Num n -> $UI) |[R]| $(VAR (Suc n)))
  have hParA :
      eqF ((proc.Proc_name ImpName.UI : proc ImpName Event)
            |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR n)) MF MF
        (proc.Ext_pre_choice ({Event.Read n} : Set Event) fun _ =>
          (Event.Num n ~> proc.Proc_name ImpName.UI)
            |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR (Nat.succ n))) := by
    have hstep := cspF_Parallel_step
      (X := Set.range Event.Read) (Y := Set.range Event.Read)
      (Z := ({Event.Read n} : Set Event))
      (Pf := fun x =>
        Event.Num (Function.invFun Event.Read x) ~> proc.Proc_name ImpName.UI)
      (Qf := fun _ => proc.Proc_name (ImpName.VAR (Nat.succ n)))
      (M := (MF : ImpName → domFType Event))
    rw [set4 n] at hstep
    refine cspF_trans_left_eq (cspF_Parallel_cong rfl hUI (hVAR n)) ?_
    refine cspF_trans_left_eq hstep ?_
    refine cspF_Ext_pre_choice_cong rfl ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [procIte_pos (Set.mem_range_self n)]
    simp only [invFun_Read]
    exact cspF_reflex_eq_P
  -- hide the synchronised Read:
  -- Spc_to_Imp (SPC n)  =F  ((Num n -> $UI) |[R]| $(VAR (Suc n))) -- R
  have hHideA :
      eqF (Spc_to_Imp (SpcName.SPC n)) MF MF
        (proc.Hiding
          ((Event.Num n ~> proc.Proc_name ImpName.UI)
            |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR (Nat.succ n)))
          (Set.range Event.Read)) := by
    have hne : ¬(({Event.Read n} : Set Event) ∩ Set.range Event.Read = ∅) := by
      intro h
      have hm : Event.Read n ∈ ({Event.Read n} : Set Event) ∩ Set.range Event.Read :=
        ⟨rfl, Set.mem_range_self n⟩
      rw [h] at hm
      exact hm
    have hstep := cspF_Hiding_step
      (X := Set.range Event.Read) (Y := ({Event.Read n} : Set Event))
      (Pf := fun _ =>
        (Event.Num n ~> proc.Proc_name ImpName.UI)
          |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR (Nat.succ n)))
      (M := (MF : ImpName → domFType Event))
    rw [procIte_neg hne, set6 n, set7 n] at hstep
    refine cspF_trans_left_eq (cspF_Hiding_cong rfl hParA) ?_
    refine cspF_trans_left_eq hstep ?_
    refine cspF_trans_left_eq
      (cspF_Timeout_cong (cspF_sym cspF_STOP_step)
        (cspF_Rep_int_choice_com_unit (by simp))) ?_
    exact cspF_STOP_Timeout
  -- (Num n -> $UI) |[R]| $(VAR (Suc n))  =F  ? x:{Num n} -> ($UI |[R]| $(VAR (Suc n)))
  have hParB :
      eqF ((Event.Num n ~> proc.Proc_name ImpName.UI)
            |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR (Nat.succ n))) MF MF
        (proc.Ext_pre_choice ({Event.Num n} : Set Event) fun _ =>
          (proc.Proc_name ImpName.UI : proc ImpName Event)
            |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR (Nat.succ n))) := by
    have hstep := cspF_Parallel_step
      (X := Set.range Event.Read) (Y := ({Event.Num n} : Set Event))
      (Z := ({Event.Read (Nat.succ n)} : Set Event))
      (Pf := fun _ => proc.Proc_name ImpName.UI)
      (Qf := fun _ => proc.Proc_name (ImpName.VAR (Nat.succ (Nat.succ n))))
      (M := (MF : ImpName → domFType Event))
    rw [set5 n] at hstep
    refine cspF_trans_left_eq
      (cspF_Parallel_cong rfl cspF_Act_prefix_step (hVAR (Nat.succ n))) ?_
    refine cspF_trans_left_eq hstep ?_
    refine cspF_Ext_pre_choice_cong rfl ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [procIte_neg (set3 n), procIte_neg (by simp),
      procIte_pos (show Event.Num n ∈ ({Event.Num n} : Set Event) from rfl)]
    exact cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym (hVAR (Nat.succ n)))
  -- hide nothing (Num n is not hidden) and fold everything together
  have hstep := cspF_Hiding_step
    (X := Set.range Event.Read) (Y := ({Event.Num n} : Set Event))
    (Pf := fun _ =>
      (proc.Proc_name ImpName.UI : proc ImpName Event)
        |[Set.range Event.Read]| proc.Proc_name (ImpName.VAR (Nat.succ n)))
    (M := (MF : ImpName → domFType Event))
  rw [procIte_pos (set8 n)] at hstep
  refine cspF_trans_left_eq hHideA ?_
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl hParB) ?_
  refine cspF_trans_left_eq hstep ?_
  exact cspF_sym cspF_Act_prefix_step

theorem Spc_ref_Imp :
    Spc <=F Imp := by
  rw [Spc_def]
  refine cspF_fp_induct_cms_ref_left (Pf := Spcfun) (f := Spc_to_Imp)
    rfl guardedfun_Spcfun rfl cspF_reflex_ref_P (fun pn => ?_)
  cases pn with
  | SPC n =>
      refine cspF_rw_right_ref (Spc_to_Imp_step n) ?_
      simp only [Spcfun, Subst_procfun, Subst_procfun_Rep_int_choice_nat]
      refine cspF_Act_prefix_mono rfl ?_
      exact cspF_Rep_int_choice_nat_left
        ⟨Nat.succ n, Nat.lt_succ_self n, cspF_reflex_ref_P⟩

end Test_infinite
