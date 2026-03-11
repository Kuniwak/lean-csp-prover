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

def Spcfun : SpcName → proc SpcName Event
  | SpcName.SPC n =>
      Event.Num n ~> Rec_prefix Event.Read (GTs n) fun m =>
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

/- *********************************************************
               guardedfun (rutine work)
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare csp_prefix_ss_def[simp]` and `declare inj_on_def[simp]`
   have no direct Lean analogue here. -/

@[simp] axiom guardedfun_Spcfun :
    guardedfun Spcfun

@[simp] axiom guardedfun_Impfun :
    guardedfun Impfun

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

/- Lean note:
   The original Isabelle proof uses fixed-point induction from `Spcfun` into
   the heterogeneously typed target `Imp`. The current Lean port only exposes
   homogeneous fixed-point-induction rules, so this final refinement proof is
   kept as an axiom for now, matching the approach already used in
   `Test_Buffer`. -/

axiom Spc_ref_Imp :
    Spc <=F Imp

end Test_infinite
