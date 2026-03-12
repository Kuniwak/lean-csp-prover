           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                  May 2016  (modified)     |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_Main

open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v w

variable {p : Type u} {α : Type v} {ι : Type w}

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion`.                     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`               -/
/-                                                                   -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there  -/
/-  is nothing to disable or re-enable here.                         -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`     -/
/- Isabelle 2017: `split_if --> if_split`                             -/
/-                                                                    -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is -/
/-  nothing to disable or re-enable here.                             -/

/-
(*****************************************************************

         1. definition of full normalisation
         2.
         3.

 *****************************************************************)
-/

/- (*----------------------------------------------------------------------*
 |                         full normal form                             |
 *----------------------------------------------------------------------*) -/

def fnfF_set_condition (A : Set α) (Ys : Set (Set α)) : Prop :=
  ∀ Y, ((∃ Y0 ∈ Ys, Y0 ⊆ Y) ∧ Y ⊆ (A ∪ Set.sUnion Ys)) → Y ∈ Ys

def fnfF_set_completion (A : Set α) (Ys : Set (Set α)) : Set (Set α) :=
  {Y | (∃ Y0 ∈ Ys, Y0 ⊆ Y) ∧ Y ⊆ (A ∪ Set.sUnion Ys)}

inductive fnfF_proc : proc p α → Prop where
  | fnfF_proc_rule
      {A : Set α} {Ys : Set (Set α)} {Pf : α → proc p α} {Q : proc p α}
      (hPf : ∀ a, a ∈ A → fnfF_proc (Pf a))
      (hPfDIV : ∀ a, a ∉ A → Pf a = proc.DIV)
      (hCond : fnfF_set_condition A Ys)
      (hUnion : Set.sUnion Ys ⊆ A)
      (hQ : Q = proc.SKIP ∨ Q = proc.DIV) :
      fnfF_proc
        ((((proc.Ext_pre_choice A Pf) [+] Q) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))

def XfnfF_proc [HasPNfun p α] [HasFPmode] : Set (proc p α) :=
  {P | ∃ Pf : Nat → proc p α,
    P = Rep_int_choice_nat Set.univ Pf ∧
      (∀ n, eqFfix (Pf n) ((Rep_int_choice_nat Set.univ Pf) |. n)) ∧
      (∀ n, fnfF_proc (Pf n))}

/- (*** convenient lemmas ***) -/

theorem fnfF_set_completion_sat_condition {A : Set α} {Ys : Set (Set α)} :
    fnfF_set_condition A (fnfF_set_completion A Ys) := by
  intro Y hY
  rcases hY with ⟨⟨Y0, hY0, hY0subY⟩, hYsub⟩
  rcases hY0 with ⟨⟨Y1, hY1, hY1sub⟩, hY0subAU⟩
  refine ⟨?_, ?_⟩
  · exact ⟨Y1, hY1, Set.Subset.trans hY1sub hY0subY⟩
  · intro x hx
    rcases hYsub hx with hxA | hxUnion
    · exact Or.inl hxA
    · rcases hxUnion with ⟨Z, hZ, hxZ⟩
      exact hZ.2 hxZ

theorem fnfF_set_completion_subset {A : Set α} {Ys : Set (Set α)} :
    Ys ⊆ fnfF_set_completion A Ys := by
  intro Y hY
  refine ⟨?_, ?_⟩
  · exact ⟨Y, hY, Set.Subset.rfl⟩
  · intro x hx
    exact Or.inr ⟨Y, hY, hx⟩

theorem fnfF_set_completion_Union_subset {A : Set α} {Ys : Set (Set α)}
    (hUnion : Set.sUnion Ys ⊆ A) :
    Set.sUnion (fnfF_set_completion A Ys) ⊆ A := by
  intro x hx
  rcases hx with ⟨Y, hY, hxY⟩
  rcases hY.2 hxY with hxA | hxUnionY
  · exact hxA
  · exact hUnion hxUnionY

/- (*----------------------------------------------------------*
 |                   intro, elim, simp                      |
 *----------------------------------------------------------*) -/

axiom fnfF_proc_iff {NP : proc p α} :
    fnfF_proc NP ↔
      ∃ A Ys Pf Q,
        (NP =
            ((((proc.Ext_pre_choice A Pf) [+] Q) |~|
              Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) ∧
          (∀ a, (if a ∈ A then fnfF_proc (Pf a) else Pf a = proc.DIV)) ∧
          fnfF_set_condition A Ys ∧
          Set.sUnion Ys ⊆ A ∧
          (Q = proc.SKIP ∨ Q = proc.DIV)

axiom fnfF_proc_EX_I {NP : proc p α} :
    (∃ A Ys Pf Q,
        (NP =
            ((((proc.Ext_pre_choice A Pf) [+] Q) |~|
              Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) ∧
          (∀ a, (if a ∈ A then fnfF_proc (Pf a) else Pf a = proc.DIV)) ∧
          fnfF_set_condition A Ys ∧
          Set.sUnion Ys ⊆ A ∧
          (Q = proc.SKIP ∨ Q = proc.DIV)) →
      fnfF_proc NP

axiom fnfF_proc_EX_E {NP : proc p α} {S : Prop} :
    fnfF_proc NP →
      ((∃ A Ys Pf Q,
          (NP =
              ((((proc.Ext_pre_choice A Pf) [+] Q) |~|
                Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) ∧
            (∀ a, (if a ∈ A then fnfF_proc (Pf a) else Pf a = proc.DIV)) ∧
            fnfF_set_condition A Ys ∧
            Set.sUnion Ys ⊆ A ∧
            (Q = proc.SKIP ∨ Q = proc.DIV)) →
        S) →
      S

/- (*----------------------------------------------------------*
 |                 ALL fnfF_proc_iff                   |
 *----------------------------------------------------------*) -/

private abbrev FnfFData (p : Type u) (α : Type v) :=
  Set α × Set (Set α) × (α → proc p α) × proc p α

private def FnfFData.A (d : FnfFData p α) : Set α := d.1
private def FnfFData.Ys (d : FnfFData p α) : Set (Set α) := d.2.1
private def FnfFData.Pf (d : FnfFData p α) : α → proc p α := d.2.2.1
private def FnfFData.Q (d : FnfFData p α) : proc p α := d.2.2.2

axiom ALL_fnfF_proc_only_if {X : Set ι} {NPf : ι → proc p α} :
    (∀ x ∈ X, fnfF_proc (NPf x)) →
      ∃ Af : ι → Set α, ∃ Ysf : ι → Set (Set α), ∃ Pff : ι → α → proc p α, ∃ Qf : ι → proc p α,
        (NPf =
            (fun x =>
              if x ∈ X then
                ((((proc.Ext_pre_choice (Af x) (Pff x)) [+] (Qf x)) |~|
                  Rep_int_choice_set (Ysf x) (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
              else
                NPf x)) ∧
          (∀ x ∈ X, ∀ a, (if a ∈ Af x then fnfF_proc (Pff x a) else Pff x a = proc.DIV)) ∧
          (∀ x ∈ X, fnfF_set_condition (Af x) (Ysf x)) ∧
          (∀ x ∈ X, Set.sUnion (Ysf x) ⊆ Af x) ∧
          (∀ x ∈ X, Qf x = proc.SKIP ∨ Qf x = proc.DIV)

axiom ALL_fnfF_proc_iff {X : Set ι} {NPf : ι → proc p α} :
    (∀ x ∈ X, fnfF_proc (NPf x)) ↔
      ∃ Af : ι → Set α, ∃ Ysf : ι → Set (Set α), ∃ Pff : ι → α → proc p α, ∃ Qf : ι → proc p α,
        (NPf =
            (fun x =>
              if x ∈ X then
                ((((proc.Ext_pre_choice (Af x) (Pff x)) [+] (Qf x)) |~|
                  Rep_int_choice_set (Ysf x) (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
              else
                NPf x)) ∧
          (∀ x ∈ X, ∀ a, (if a ∈ Af x then fnfF_proc (Pff x a) else Pff x a = proc.DIV)) ∧
          (∀ x ∈ X, fnfF_set_condition (Af x) (Ysf x)) ∧
          (∀ x ∈ X, Set.sUnion (Ysf x) ⊆ Af x) ∧
          (∀ x ∈ X, Qf x = proc.SKIP ∨ Qf x = proc.DIV)

axiom ALL_fnfF_procI {X : Set ι} {NPf : ι → proc p α} :
    (∃ Af : ι → Set α, ∃ Ysf : ι → Set (Set α), ∃ Pff : ι → α → proc p α, ∃ Qf : ι → proc p α,
        (NPf =
            (fun x =>
              if x ∈ X then
                ((((proc.Ext_pre_choice (Af x) (Pff x)) [+] (Qf x)) |~|
                  Rep_int_choice_set (Ysf x) (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
              else
                NPf x)) ∧
          (∀ x ∈ X, ∀ a, (if a ∈ Af x then fnfF_proc (Pff x a) else Pff x a = proc.DIV)) ∧
          (∀ x ∈ X, fnfF_set_condition (Af x) (Ysf x)) ∧
          (∀ x ∈ X, Set.sUnion (Ysf x) ⊆ Af x) ∧
          (∀ x ∈ X, Qf x = proc.SKIP ∨ Qf x = proc.DIV)) →
      ∀ x ∈ X, fnfF_proc (NPf x)

axiom ALL_fnfF_procE {X : Set ι} {NPf : ι → proc p α} {S : Prop} :
    (∀ x ∈ X, fnfF_proc (NPf x)) →
      ((∃ Af : ι → Set α, ∃ Ysf : ι → Set (Set α), ∃ Pff : ι → α → proc p α, ∃ Qf : ι → proc p α,
          (NPf =
              (fun x =>
                if x ∈ X then
                  ((((proc.Ext_pre_choice (Af x) (Pff x)) [+] (Qf x)) |~|
                    Rep_int_choice_set (Ysf x)
                      (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
                else
                  NPf x)) ∧
            (∀ x ∈ X, ∀ a, (if a ∈ Af x then fnfF_proc (Pff x a) else Pff x a = proc.DIV)) ∧
            (∀ x ∈ X, fnfF_set_condition (Af x) (Ysf x)) ∧
            (∀ x ∈ X, Set.sUnion (Ysf x) ⊆ Af x) ∧
            (∀ x ∈ X, Qf x = proc.SKIP ∨ Qf x = proc.DIV)) →
        S) →
      S

/- (*======================================================*
 |         function to decompose : fnfF_decompo         |
 *======================================================*) -/

/- they are partial functions -/

def fnfF_A : proc p α → Set α
  | (((proc.Ext_pre_choice A _) [+] _) |~| _) => A
  | _ => ∅

def fnfF_Ys : proc p α → Set (Set α)
  | (_ |~| proc.Rep_int_choice (type1 Ys) _) => Ys
  | _ => ∅

def fnfF_Pf : proc p α → (α → proc p α)
  | (((proc.Ext_pre_choice _ Pf) [+] _) |~| _) => Pf
  | _ => fun _ => proc.DIV

def fnfF_Q : proc p α → proc p α
  | (((proc.Ext_pre_choice _ _) [+] Q) |~| _) => Q
  | _ => proc.DIV

@[simp]
theorem fnfF_Ys_get {P : proc p α} {Ys : Set (Set α)} {Pf : Set α → proc p α} :
    fnfF_Ys (P |~| Rep_int_choice_set Ys Pf) = Ys := by
  simp [fnfF_Ys, Rep_int_choice_set_def]

/- (*------------------------*
 |     decomposition      |
 *------------------------*) -/

axiom cspF_fnfF_nat_decompo [HasPNfun p α] [HasFPmode] {P : proc p α} :
    fnfF_proc P →
      eqFfix P
        ((((proc.Ext_pre_choice (fnfF_A P) (fnfF_Pf P)) [+] (fnfF_Q P)) |~|
          Rep_int_choice_set (fnfF_Ys P) (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))

/- (*--------------------------------------*
 |   properties of fnfF decomposition   |
 *--------------------------------------*) -/

axiom fnfF_Pf_A {P : proc p α} {a : α} :
    fnfF_proc P →
      a ∈ fnfF_A P →
      fnfF_proc ((fnfF_Pf P) a)

axiom fnfF_Pf_DIV {P : proc p α} {a : α} :
    fnfF_proc P →
      a ∉ fnfF_A P →
      (fnfF_Pf P) a = proc.DIV

axiom fnfF_Q_range {P : proc p α} :
    fnfF_proc P →
      fnfF_Q P = proc.SKIP ∨ fnfF_Q P = proc.DIV

axiom fnfF_condition_A_Ys {P : proc p α} :
    fnfF_proc P →
      fnfF_set_condition (fnfF_A P) (fnfF_Ys P)

axiom fnfF_Union_Ys_A {P : proc p α} :
    fnfF_proc P →
      Set.sUnion (fnfF_Ys P) ⊆ fnfF_A P

/- (*-----------------------*
 |    DIV, SKIP, STOP    |
 *-----------------------*) -/

def NSKIP : proc p α :=
  ((((proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.SKIP) |~|
    Rep_int_choice_set (∅ : Set (Set α)) (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))

def NDIV : proc p α :=
  ((((proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.DIV) |~|
    Rep_int_choice_set (∅ : Set (Set α)) (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))

def NSTOP : proc p α :=
  ((((proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.DIV) |~|
    Rep_int_choice_set ({(∅ : Set α)} : Set (Set α))
      (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))

/- (*** in fnfF ***) -/

@[simp] axiom fnfF_NSKIP : fnfF_proc (NSKIP (p := p) (α := α))

@[simp] axiom fnfF_NDIV : fnfF_proc (NDIV (p := p) (α := α))

@[simp] axiom fnfF_NSTOP : fnfF_proc (NSTOP (p := p) (α := α))

/- (*** eqF ***) -/

axiom cspF_NSKIP_eqF [HasPNfun p α] [HasFPmode] :
    eqFfix (proc.SKIP : proc p α) (NSKIP (p := p) (α := α))

axiom cspF_NDIV_eqF [HasPNfun p α] [HasFPmode] :
    eqFfix (proc.DIV : proc p α) (NDIV (p := p) (α := α))

axiom cspF_NSTOP_eqF [HasPNfun p α] [HasFPmode] :
    eqFfix (proc.STOP : proc p α) (NSTOP (p := p) (α := α))

/- (*==============================================================*
 |               convenient rules for fnfF                      |
 *==============================================================*) -/

axiom cspF_fnfF_Depth_rest_dist [HasPNfun p α] [HasFPmode]
    {A : Set α} {Ys : Set (Set α)} {Pf : α → proc p α} {Q : proc p α} {n : Nat} :
    (Q = proc.SKIP ∨ Q = proc.DIV) →
      eqFfix
        (((((proc.Ext_pre_choice A Pf) [+] Q) |~|
            Rep_int_choice_set Ys
              (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))) |. Nat.succ n))
        ((((proc.Ext_pre_choice A (fun a => Pf a |. n)) [+] Q) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))

/- left DIV -/

axiom cspF_fsfF_left_DIV [HasPNfun p α] [HasFPmode] {P : proc p α} :
    eqFfix
      ((((proc.Ext_pre_choice (∅ : Set α) (fun _ => proc.DIV)) [+] proc.DIV) |~| P))
      P

axiom cspF_fsfF_right_DIV [HasPNfun p α] [HasFPmode]
    {P : proc p α} {Pf : Set α → proc p α} :
    eqFfix (P |~| Rep_int_choice_set (∅ : Set (Set α)) Pf) P

/- (****************** to add them again ******************) -/

/- Lean has no direct analogue of Isabelle's local `declare if_split [split]`
   or `declare disj_not1 [simp]` commands. -/
