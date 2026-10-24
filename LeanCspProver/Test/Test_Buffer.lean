           /- -------------------------------------------*
            |                   Test                    |
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

open fpmode

noncomputable section

namespace Test_Buffer

local notation:50 P " <=F " Q => refF P MF MF Q

/- *****************************************************************

         1. test Buffer
         2. verification of deadlock-free.
         3.
         4.

 ***************************************************************** -/

inductive Event where
  | left : Real → Event
  | right : Real × Nat → Event
deriving DecidableEq, Inhabited

inductive Name where
  | Empty : Nat → Name
  | Full : Real → Nat → Name
deriving DecidableEq, Inhabited

inductive DFName where
  | DF
deriving DecidableEq, Inhabited

def Bufferfun : Name → proc Name Event
  | Name.Empty n =>
      Rec_prefix Event.left Set.univ fun r => proc.Proc_name (Name.Full r n)
  | Name.Full r n =>
      Event.right (r, n) ~> proc.Proc_name (Name.Empty (Nat.succ n))

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Bufferfun : HasPNfun Name Event where
  PNfun := Bufferfun

@[simp]
theorem Set_Bufferfun_def (pn : Name) :
    PNfun pn = Bufferfun pn :=
  rfl

def Buffer : proc Name Event :=
  proc.Proc_name (Name.Empty 0)

theorem Buffer_def :
    Buffer = proc.Proc_name (Name.Empty 0) :=
  rfl

/- (*** Spc ***) -/

def DFfun : DFName → proc DFName Event
  | DFName.DF =>
      Int_pre_choice Set.univ (fun _ : Event => proc.Proc_name DFName.DF)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_DFfun : HasPNfun DFName Event where
  PNfun := DFfun

@[simp]
theorem Set_DFfun_def (pn : DFName) :
    PNfun pn = DFfun pn :=
  rfl

/- Lean note:
   Isabelle's `declare csp_prefix_ss_def[simp]` and `declare inj_on_def[simp]`
   have no direct Lean analogue here. -/

/- *********************************************************
               guardedfun (rutine work)
 ********************************************************* -/

@[simp] theorem guardedfun_Bufferfun :
    guardedfun Bufferfun := by
  intro pn
  cases pn <;> simp [Bufferfun, guarded, noHide]

@[simp] theorem guardedfun_DFfun :
    guardedfun DFfun := by
  intro pn
  cases pn with
  | DF => simp [DFfun, noHide]

/- *********************************************************
            relation between Buffer and DF
 ********************************************************* -/

def Buffer_to_DF : Name → proc DFName Event
  | Name.Empty _ => proc.Proc_name DFName.DF
  | Name.Full _ _ => proc.Proc_name DFName.DF

/- *********************************************************
               Buffer is deadlock free.
 ********************************************************* -/

/- Lean note:
   Isabelle's overloaded constant `FPmode` is represented by a typeclass
   instance. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

/- (*** manual proof ***) -/

theorem manual_proof_Buffer :
    (proc.Proc_name DFName.DF : proc DFName Event) <=F Buffer := by
  rw [Buffer]
  refine cspF_fp_induct_cms_ref_right (Pf := Bufferfun) (f := Buffer_to_DF)
    rfl guardedfun_Bufferfun rfl cspF_reflex_ref_P (fun pn => ?_)
  have hunwind :
      eqF (proc.Proc_name DFName.DF : proc DFName Event) MF MF
        (DFfun DFName.DF) :=
    «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_DFfun⟩))
  cases pn with
  | Empty n =>
      -- $DF <=F (? r:(left ` UNIV) -> $DF)
      refine cspF_rw_left_ref hunwind ?_
      rw [DFfun]
      show refF (Int_pre_choice Set.univ fun _ => proc.Proc_name DFName.DF)
        MF MF
        (Rec_prefix Event.left Set.univ fun r =>
          Buffer_to_DF (Name.Full r n))
      rw [Rec_prefix]
      exact cspF_Int_Ext_pre_choice_subset
        (by simp [Set.image_univ])
        (Set.subset_univ _)
        (fun a _ => cspF_reflex_ref_P)
  | Full r n =>
      -- $DF <=F (right (r,n) -> $DF)
      refine cspF_rw_left_ref hunwind ?_
      show refF (DFfun DFName.DF) MF MF
        (Event.right (r, n) ~> proc.Proc_name DFName.DF)
      refine cspF_rw_right_ref cspF_Act_prefix_step ?_
      rw [DFfun]
      exact cspF_Int_Ext_pre_choice_subset
        (by simp)
        (Set.subset_univ _)
        (fun a _ => cspF_reflex_ref_P)

/- (*** semi-automatic proof ***) -/

theorem semi_auto_proof_Buffer :
    (proc.Proc_name DFName.DF : proc DFName Event) <=F Buffer :=
  manual_proof_Buffer

end Test_Buffer
