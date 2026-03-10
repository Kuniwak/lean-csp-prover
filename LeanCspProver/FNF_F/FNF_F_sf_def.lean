           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_Main

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

         1. definition of full sequential-formed process
         2.
         3.

 *****************************************************************)
-/

/-
*==========================================================*
 |                                                          |
 |                    Definition of fsfF                    |
 |                                                          |
 *==========================================================*
-/

inductive fsfF_proc : proc p α → Prop where
  | fsfF_proc_int
      {C : sets_nats α} {Rf : aset_anat α → proc p α}
      (hC : sumset C ≠ ∅)
      (hRf : ∀ c, c ∈ sumset C → fsfF_proc (Rf c)) :
      fsfF_proc (proc.Rep_int_choice C Rf)
  | fsfF_proc_ext
      {A : Set α} {Pf : α → proc p α} {Q : proc p α}
      (hPf : ∀ a, a ∈ A → fsfF_proc (Pf a))
      (hQ : Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) :
      fsfF_proc ((proc.Ext_pre_choice A Pf) [+] Q)

/- -------------------------------------------*
 |   sequential-formed SSKIP, SDIV, SSTOP    |
 *------------------------------------------- -/

def SSKIP : proc p α :=
  (proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.SKIP

theorem SSKIP_def :
    SSKIP (p := p) (α := α) =
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.SKIP :=
  rfl

def SDIV : proc p α :=
  (proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.DIV

theorem SDIV_def :
    SDIV (p := p) (α := α) =
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.DIV :=
  rfl

def SSTOP : proc p α :=
  (proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.STOP

theorem SSTOP_def :
    SSTOP (p := p) (α := α) =
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.STOP :=
  rfl

/- (*** small lemmas ***) -/

/- in -/

@[simp]
theorem fsfF_SSKIP_in : fsfF_proc (SSKIP (p := p) (α := α)) := by
  rw [SSKIP_def]
  refine fsfF_proc.fsfF_proc_ext ?_ (Or.inl rfl)
  intro a ha
  cases ha

@[simp]
theorem fsfF_SDIV_in : fsfF_proc (SDIV (p := p) (α := α)) := by
  rw [SDIV_def]
  refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inl rfl)
  intro a ha
  cases ha

@[simp]
theorem fsfF_SSTOP_in : fsfF_proc (SSTOP (p := p) (α := α)) := by
  rw [SSTOP_def]
  refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
  intro a ha
  cases ha

/- eqF -/

theorem cspF_SSKIP_eqF [HasPNfun p α] [HasFPmode] :
    eqFfix (proc.SKIP : proc p α) (SSKIP (p := p) (α := α)) := by
  simpa [SSKIP_def] using
    (cspF_sym
      (cspF_Ext_choice_unit_l_hsf
        (Qf := fun _ => (proc.DIV : proc p α))
        (P := (proc.SKIP : proc p α))
        (M := MF)))

theorem cspF_SDIV_eqF [HasPNfun p α] [HasFPmode] :
    eqFfix (proc.DIV : proc p α) (SDIV (p := p) (α := α)) := by
  simpa [SDIV_def] using
    (cspF_sym
      (cspF_Ext_choice_unit_l_hsf
        (Qf := fun _ => (proc.DIV : proc p α))
        (P := (proc.DIV : proc p α))
        (M := MF)))

theorem cspF_SSTOP_eqF [HasPNfun p α] [HasFPmode] :
    eqFfix (proc.STOP : proc p α) (SSTOP (p := p) (α := α)) := by
  simpa [SSTOP_def] using
    (cspF_sym
      (cspF_Ext_choice_unit_l_hsf
        (Qf := fun _ => (proc.DIV : proc p α))
        (P := (proc.STOP : proc p α))
        (M := MF)))

/-
*----------------------------------------------------------*
 |                          iff                             |
 *----------------------------------------------------------*
-/

/- proc -/

theorem fsfF_proc_iff {SP : proc p α} :
    fsfF_proc SP ↔
      (∃ C Rf,
        sumset C ≠ ∅ ∧
          SP = proc.Rep_int_choice C Rf ∧
          (∀ c, c ∈ sumset C → fsfF_proc (Rf c))) ∨
      (∃ A Pf Q,
        SP = (proc.Ext_pre_choice A Pf) [+] Q ∧
          (∀ a, a ∈ A → fsfF_proc (Pf a)) ∧
          (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP)) := by
  constructor
  · intro hSP
    cases hSP with
    | fsfF_proc_int hC hRf =>
        exact Or.inl ⟨_, _, hC, rfl, hRf⟩
    | fsfF_proc_ext hPf hQ =>
        exact Or.inr ⟨_, _, _, rfl, hPf, hQ⟩
  · intro hSP
    rcases hSP with hSP | hSP
    · rcases hSP with ⟨C, Rf, hC, rfl, hRf⟩
      exact fsfF_proc.fsfF_proc_int hC hRf
    · rcases hSP with ⟨A, Pf, Q, rfl, hPf, hQ⟩
      exact fsfF_proc.fsfF_proc_ext hPf hQ

theorem fsfF_procI {SP : proc p α} :
    ((∃ C Rf,
        sumset C ≠ ∅ ∧
          SP = proc.Rep_int_choice C Rf ∧
          (∀ c, c ∈ sumset C → fsfF_proc (Rf c))) ∨
      (∃ A Pf Q,
        SP = (proc.Ext_pre_choice A Pf) [+] Q ∧
          (∀ a, a ∈ A → fsfF_proc (Pf a)) ∧
          (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP))) →
      fsfF_proc SP := by
  intro hSP
  exact (fsfF_proc_iff (SP := SP)).2 hSP

theorem fsfF_procE {SP : proc p α} {S : Prop} :
    fsfF_proc SP →
      (((∃ C Rf,
          sumset C ≠ ∅ ∧
            SP = proc.Rep_int_choice C Rf ∧
            (∀ c, c ∈ sumset C → fsfF_proc (Rf c))) ∨
        (∃ A Pf Q,
          SP = (proc.Ext_pre_choice A Pf) [+] Q ∧
            (∀ a, a ∈ A → fsfF_proc (Pf a)) ∧
            (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP))) →
        S) →
      S := by
  intro hSP hS
  exact hS ((fsfF_proc_iff (SP := SP)).1 hSP)

/-
*----------------------------------------------------------*
 |                    subexpression                         |
 *----------------------------------------------------------*
-/

/- proc -/

theorem Rf_fsfF_proc {C : sets_nats α} {Rf : aset_anat α → proc p α} {c : aset_anat α} :
    fsfF_proc (proc.Rep_int_choice C Rf) →
      c ∈ sumset C →
      fsfF_proc (Rf c) := by
  intro hSP hc
  cases hSP with
  | fsfF_proc_int _ hRf =>
      exact hRf c hc

theorem Pf_fsfF_proc {A : Set α} {Pf : α → proc p α} {Q : proc p α} {a : α} :
    fsfF_proc ((proc.Ext_pre_choice A Pf) [+] Q) →
      a ∈ A →
      fsfF_proc (Pf a) := by
  intro hSP ha
  cases hSP with
  | fsfF_proc_ext hPf _ =>
      exact hPf a ha

theorem Qf_range {A : Set α} {Pf : α → proc p α} {Q : proc p α} :
    fsfF_proc ((proc.Ext_pre_choice A Pf) [+] Q) →
      Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP := by
  intro hSP
  cases hSP with
  | fsfF_proc_ext _ hQ =>
      exact hQ

/-
*======================================================*
 |                                                      |
 |    function to decompose : fsfF_decompo_int, ext     |
 |                                                      |
 *======================================================*
-/

def fsfF_C : proc p α → sets_nats α
  | proc.Rep_int_choice C _ => C
  | _ => type1 (∅ : Set (Set α))

def fsfF_Rf : proc p α → aset_anat α → proc p α
  | proc.Rep_int_choice _ Rf => Rf
  | _ => fun _ => proc.DIV

def fsfF_A : proc p α → Set α
  | (proc.Ext_pre_choice A _) [+] _ => A
  | _ => ∅

def fsfF_Pf : proc p α → α → proc p α
  | (proc.Ext_pre_choice _ Pf) [+] _ => Pf
  | _ => fun _ => proc.DIV

def fsfF_Q : proc p α → proc p α
  | (proc.Ext_pre_choice _ _) [+] Q => Q
  | _ => proc.DIV

/- they are partial functions -/

/-
*------------------------*
 |     decomposition      |
 *------------------------*
-/

theorem cspF_fsfF_proc_decompo {P : proc p α} :
    fsfF_proc P →
      (P = proc.Rep_int_choice (fsfF_C P) (fsfF_Rf P) ∨
        P = (proc.Ext_pre_choice (fsfF_A P) (fsfF_Pf P)) [+] fsfF_Q P) := by
  intro hP
  cases hP with
  | fsfF_proc_int =>
      left
      rfl
  | fsfF_proc_ext =>
      right
      rfl

/- (****************** to add them again ******************) -/

/- Lean has no direct analogue of Isabelle's local `declare if_split [split]`
   or `declare disj_not1 [simp]` commands. -/

end
