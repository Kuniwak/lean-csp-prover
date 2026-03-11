           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                  May 2016  (modified)     |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_hide
import LeanCspProver.FNF_F.FNF_F_sf_par
import LeanCspProver.FNF_F.FNF_F_sf_ren
import LeanCspProver.FNF_F.FNF_F_sf_seq
import LeanCspProver.FNF_F.FNF_F_sf_rest

open fpmode
open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {p : Type u} {α : Type v}

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion` and `Set.sInter`.     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`                 -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there is -/
/-  nothing to disable or re-enable here.                              -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`      -/
/- Isabelle 2017: `split_if --> if_split`                              -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is  -/
/-  nothing to disable or re-enable here.                              -/

/-
(*****************************************************************

         1. full sequentialisation
         2.
         3.

 *****************************************************************)
-/

/-
(*****************************************************************
                      small transformation
 *****************************************************************)
-/

def fsfF_Act_prefix
    (a : α) (P : proc p α) : proc p α :=
  (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) [+] proc.STOP

theorem fsfF_Act_prefix_def
    (a : α) (P : proc p α) :
    fsfF_Act_prefix (p := p) (α := α) a P =
      (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) [+] proc.STOP :=
  rfl

def fsfF_Ext_pre_choice
    (A : Set α) (Pf : α → proc p α) : proc p α :=
  (proc.Ext_pre_choice A Pf) [+] proc.STOP

theorem fsfF_Ext_pre_choice_def
    (A : Set α) (Pf : α → proc p α) :
    fsfF_Ext_pre_choice (p := p) (α := α) A Pf =
      (proc.Ext_pre_choice A Pf) [+] proc.STOP :=
  rfl

/- Lean note:
   Isabelle's syntax/translations for `? :A ->seq Pf` and `? a:A ->seq P`
   are represented directly by `fsfF_Ext_pre_choice A Pf`. -/

/- a -> P -/

theorem fsfF_Act_prefix_in
    {a : α} {P : proc p α} :
    fsfF_proc P →
      fsfF_proc (fsfF_Act_prefix a P) := by
  intro hP
  rw [fsfF_Act_prefix_def]
  refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
  intro x hx
  simpa using hP

theorem cspF_fsfF_Act_prefix_eqF
    [HasPNfun p α] [HasFPmode]
    {a : α} {P : proc p α} :
    eqFfix (a ~> P) (fsfF_Act_prefix a P) := by
  have hStep :
      eqFfix (a ~> P) (proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) := by
    simpa using (cspF_Act_prefix_step (a := a) (P := P) (M := MF))
  have hUnit :
      eqFfix (proc.Ext_pre_choice ({a} : Set α) (fun _ => P))
        ((proc.Ext_pre_choice ({a} : Set α) (fun _ => P)) [+] proc.STOP) := by
    exact cspF_sym
      (cspF_Ext_choice_unit_r
        (P := proc.Ext_pre_choice ({a} : Set α) (fun _ => P))
        (M := MF))
  simpa [fsfF_Act_prefix_def] using cspF_trans_left_eq hStep hUnit

/- ? :A -> Pf -/

theorem fsfF_Ext_pre_choice_in
    {A : Set α} {Pf : α → proc p α} :
    (∀ a, fsfF_proc (Pf a)) →
      fsfF_proc (fsfF_Ext_pre_choice A Pf) := by
  intro hPf
  rw [fsfF_Ext_pre_choice_def]
  refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
  intro a _ha
  exact hPf a

theorem cspF_fsfF_Ext_pre_choice_eqF
    [HasPNfun p α] [HasFPmode]
    {A : Set α} {Pf : α → proc p α} :
    eqFfix (proc.Ext_pre_choice A Pf) (fsfF_Ext_pre_choice A Pf) := by
  simpa [fsfF_Ext_pre_choice_def] using
    (cspF_sym (cspF_Ext_choice_unit_r (P := proc.Ext_pre_choice A Pf) (M := MF)))

/- IF b THEN P ELSE Q -/

theorem fsfF_IF_in
    {b : Bool} {P Q : proc p α} :
    fsfF_proc P →
      fsfF_proc Q →
        fsfF_proc (if b then P else Q) := by
  intro hP hQ
  cases b
  · simpa using hQ
  · simpa using hP

theorem cspF_fsfF_IF_eqF
    [HasPNfun p α] [HasFPmode]
    {b : Bool} {P Q : proc p α} :
    eqFfix (IF b THEN P ELSE Q) (if b then P else Q) := by
  simpa using (cspF_IF_split (b := b) (P := P) (Q := Q) (M := MF))

/- *===============================================================*
 |                                                               |
 |      definition of a function for full sequentialization      |
 |                     (no process name)                         |
 |                                                               |
 *===============================================================* -/

def prefsfF [Inhabited α] : proc p α → proc p α
  | proc.STOP => SSTOP
  | proc.SKIP => SSKIP
  | proc.DIV => SDIV
  | proc.Act_prefix a P => fsfF_Act_prefix a (prefsfF P)
  | proc.Ext_pre_choice A Pf => fsfF_Ext_pre_choice A (fun a => prefsfF (Pf a))
  | proc.Ext_choice P Q => (prefsfF P) [+]seq (prefsfF Q)
  | proc.Int_choice P Q => fsfF_Int_choice (prefsfF P) (prefsfF Q)
  | proc.Rep_int_choice C Pf => fsfF_Rep_int_choice C (fun c => prefsfF (Pf c))
  | proc.IF b P Q => if b then prefsfF P else prefsfF Q
  | proc.Parallel P X Q => fsfF_Parallel (prefsfF P) X (prefsfF Q)
  | proc.Hiding P X => fsfF_Hiding (prefsfF P) X
  | proc.Renaming P r => fsfF_Renaming (prefsfF P) r
  | proc.Seq_compo P Q => (prefsfF P) ;;seq (prefsfF Q)
  | proc.Depth_rest P n => fsfF_Depth_rest (prefsfF P) n
  | proc.Proc_name p0 => proc.Proc_name p0

/- *===============================================================*
            --- prefsfF P is fullly sequentialized ---
 *===============================================================* -/

axiom prefsfF_in_lm [Inhabited α]
    {P : proc p α} :
    noPN P →
      fsfF_proc (prefsfF P)

theorem prefsfF_in [Inhabited α]
    {P : proc p α} :
    noPN P →
      fsfF_proc (prefsfF P) := by
  intro hP
  exact prefsfF_in_lm hP

/- *===============================================================*
           --- prefsfF P is equal to P based on F ---
 *===============================================================* -/

axiom cspF_prefsfF_eqF_lm [Inhabited α]
    [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    noPN P →
      eqFfix P (prefsfF P)

theorem cspF_prefsfF_eqF [Inhabited α]
    [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    noPN P →
      eqFfix P (prefsfF P) := by
  intro hP
  exact cspF_prefsfF_eqF_lm hP

/- *===============================================================*
 |                                                               |
 |      definition of a function for full sequentialization      |
 |                                                               |
 *===============================================================* -/

def fsfF [Inhabited α] [HasPNfun p α]
    (P : proc p α) : proc p α :=
  prefsfF (rmPN P)

theorem fsfF_def [Inhabited α] [HasPNfun p α]
    (P : proc p α) :
    fsfF P = prefsfF (rmPN P) :=
  rfl

/- *===============================================================*
           theorem --- fsfF P is fullly sequentialized ---
 *===============================================================* -/

theorem fsfF_in [Inhabited α] [HasPNfun p α]
    {P : proc p α} :
    fsfF_proc (fsfF P) := by
  rw [fsfF_def]
  exact prefsfF_in noPN_rmPN

/- *===============================================================*
           theorem --- fsfF P is equal to P based on F ---
 *===============================================================* -/

theorem cspF_fsfF_eqF [Inhabited α]
    [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix P (fsfF P) := by
  intro hMode
  rw [fsfF_def]
  have hRm :
      eqFfix P (rmPN P) := by
    rcases hMode with hCPO | hMIX
    · exact cspF_rmPN_eqF (Or.inl hCPO)
    · exact cspF_rmPN_eqF (Or.inr <| Or.inr hMIX)
  exact cspF_trans_left_eq hRm (cspF_prefsfF_eqF noPN_rmPN)

end
