           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                January 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_def

open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v w

variable {p : Type u} {α : Type v} {β : Type w}

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

         1. full sequentialization for Rep_int_choice_nat
         2. full sequentialization for Rep_int_choice_set
         3. full sequentialization for Int_choice
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                    Rep_int_choice_nat                      |
 |                                                            |
 *============================================================* -/

def fsfF_Rep_int_choice
    (C : sets_nats α) (SPf : aset_anat α → proc p α) : proc p α :=
  if sumset C = ∅ then SDIV else proc.Rep_int_choice C SPf

theorem fsfF_Rep_int_choice_def
    (C : sets_nats α) (SPf : aset_anat α → proc p α) :
    fsfF_Rep_int_choice C SPf =
      if sumset C = ∅ then SDIV else proc.Rep_int_choice C SPf :=
  rfl

/- Lean note:
   Isabelle's syntax/translations for `!! :C ..seq SPf` and
   `!! c:C ..seq SP` are represented directly by `fsfF_Rep_int_choice`. -/

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Rep_int_choice_in
    {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
      fsfF_proc (fsfF_Rep_int_choice C SPf) := by
  intro hSPf
  by_cases hC : sumset C = ∅
  · rw [fsfF_Rep_int_choice_def, if_pos hC]
    exact fsfF_SDIV_in
  · rw [fsfF_Rep_int_choice_def, if_neg hC]
    exact fsfF_proc.fsfF_proc_int hC hSPf

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fsfF_Rep_int_choice_eqF
    [HasPNfun p α] [HasFPmode]
    {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    eqFfix (proc.Rep_int_choice C SPf) (fsfF_Rep_int_choice C SPf) := by
  by_cases hC : sumset C = ∅
  · rw [fsfF_Rep_int_choice_def, if_pos hC]
    exact cspF_trans_left_eq (cspF_Rep_int_choice_sum_DIV hC) cspF_SDIV_eqF
  · rw [fsfF_Rep_int_choice_def, if_neg hC]
    exact cspF_reflex_eq_P

theorem cspF_fsfF_Rep_int_choice_eqF_sym
    [HasPNfun p α] [HasFPmode]
    {C : sets_nats α} {SPf : aset_anat α → proc p α} :
    eqFfix (fsfF_Rep_int_choice C SPf) (proc.Rep_int_choice C SPf) :=
  cspF_sym cspF_fsfF_Rep_int_choice_eqF

/- *============================================================*
 |                                                            |
 |                       for convenience                      |
 |                                                            |
 *============================================================* -/

def fsfF_Rep_int_choice_set
    (Xs : Set (Set α)) (Pf : Set α → proc p α) : proc p α :=
  fsfF_Rep_int_choice (type1 Xs) (fun c => Pf (Function.invFun type1 c))

theorem fsfF_Rep_int_choice_set_def
    (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    fsfF_Rep_int_choice_set (p := p) Xs Pf =
      fsfF_Rep_int_choice (type1 Xs) (fun c => Pf (Function.invFun type1 c)) :=
  rfl

def fsfF_Rep_int_choice_nat
    (N : Set Nat) (Pf : Nat → proc p α) : proc p α :=
  fsfF_Rep_int_choice (type2 N) (fun c => Pf (Function.invFun type2 c))

theorem fsfF_Rep_int_choice_nat_def
    (N : Set Nat) (Pf : Nat → proc p α) :
    fsfF_Rep_int_choice_nat (p := p) N Pf =
      fsfF_Rep_int_choice (type2 N) (fun c => Pf (Function.invFun type2 c)) :=
  rfl

/- Lean note:
   Isabelle's syntax/translations for `!set :Xs ..seq Pf`, `!nat :N ..seq Pf`,
   `!set X:Xs ..seq P`, and `!nat n:N ..seq P` are represented directly by
   `fsfF_Rep_int_choice_set` and `fsfF_Rep_int_choice_nat`. -/

/- com -/

def fsfF_Rep_int_choice_com [Inhabited α]
    (A : Set α) (Pf : α → proc p α) : proc p α :=
  fsfF_Rep_int_choice_set {X | ∃ a, a ∈ A ∧ X = ({a} : Set α)} fun X => Pf (the_elem X)

theorem fsfF_Rep_int_choice_com_def [Inhabited α]
    (A : Set α) (Pf : α → proc p α) :
    fsfF_Rep_int_choice_com (p := p) A Pf =
      fsfF_Rep_int_choice_set
        {X | ∃ a, a ∈ A ∧ X = ({a} : Set α)}
        (fun X => Pf (the_elem X)) :=
  rfl

/- Lean note:
   Isabelle's syntax/translations for `! :A ..seq Pf` and `! x:X ..seq P`
   are represented directly by `fsfF_Rep_int_choice_com`. -/

/- f -/

def fsfF_Rep_int_choice_f [Inhabited α] [Inhabited β]
    (f : β → α) (X : Set β) (Pf : β → proc p α) : proc p α :=
  fsfF_Rep_int_choice_com (f '' X) fun x => Pf (Function.invFun f x)

theorem fsfF_Rep_int_choice_f_def [Inhabited α] [Inhabited β]
    (f : β → α) (X : Set β) (Pf : β → proc p α) :
    fsfF_Rep_int_choice_f (p := p) f X Pf =
      fsfF_Rep_int_choice_com (f '' X) (fun x => Pf (Function.invFun f x)) :=
  rfl

/- Lean note:
   Isabelle's syntax/translations for `!<f> :X ..seq Pf` and
   `!<f> x:X ..seq P` are represented directly by `fsfF_Rep_int_choice_f`. -/

/- *============================================================*
 |                                                            |
 |                 convenient expressions                     |
 |                                                            |
 *============================================================* -/

/- *------------------------------------*
 |                 in                 |
 *------------------------------------* -/

theorem fsfF_Rep_int_choice_nat_in
    {N : Set Nat} {SPf : Nat → proc p α} :
    (∀ n, n ∈ N → fsfF_proc (SPf n)) →
      fsfF_proc (fsfF_Rep_int_choice_nat N SPf) := by
  intro hSPf
  apply fsfF_Rep_int_choice_in
  intro c hc
  exact P_inv_type2 (X := N) (P := fun n => fsfF_proc (SPf n)) hSPf hc

theorem fsfF_Rep_int_choice_set_in
    {Xs : Set (Set α)} {SPf : Set α → proc p α} :
    (∀ X, X ∈ Xs → fsfF_proc (SPf X)) →
      fsfF_proc (fsfF_Rep_int_choice_set Xs SPf) := by
  intro hSPf
  apply fsfF_Rep_int_choice_in
  intro c hc
  exact P_inv_type1 (X := Xs) (P := fun X => fsfF_proc (SPf X)) hSPf hc

theorem fsfF_Rep_int_choice_com_in [Inhabited α]
    {X : Set α} {SPf : α → proc p α} :
    (∀ x, x ∈ X → fsfF_proc (SPf x)) →
      fsfF_proc (fsfF_Rep_int_choice_com X SPf) := by
  intro hSPf
  apply fsfF_Rep_int_choice_set_in
  intro Y hY
  rcases hY with ⟨a, haX, rfl⟩
  simpa [the_elem_singleton] using hSPf a haX

theorem fsfF_Rep_int_choice_f_in [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {SPf : β → proc p α} :
    Injective f →
      (∀ x, x ∈ X → fsfF_proc (SPf x)) →
        fsfF_proc (fsfF_Rep_int_choice_f f X SPf) := by
  intro hf hSPf
  apply fsfF_Rep_int_choice_com_in
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  simpa [Function.leftInverse_invFun hf x] using hSPf x hx

/- *------------------------------------*
 |                 eqF                |
 *------------------------------------* -/

theorem cspF_fsfF_Rep_int_choice_nat_eqF
    [HasPNfun p α] [HasFPmode]
    {N : Set Nat} {SPf : Nat → proc p α} :
    eqFfix (Rep_int_choice_nat N SPf) (fsfF_Rep_int_choice_nat N SPf) := by
  simpa [fsfF_Rep_int_choice_nat_def, Rep_int_choice_nat_def] using
    (cspF_fsfF_Rep_int_choice_eqF
      (C := type2 N)
      (SPf := fun c => SPf (Function.invFun type2 c)))

theorem cspF_fsfF_Rep_int_choice_set_eqF
    [HasPNfun p α] [HasFPmode]
    {Xs : Set (Set α)} {SPf : Set α → proc p α} :
    eqFfix (Rep_int_choice_set Xs SPf) (fsfF_Rep_int_choice_set Xs SPf) := by
  simpa [fsfF_Rep_int_choice_set_def, Rep_int_choice_set_def] using
    (cspF_fsfF_Rep_int_choice_eqF
      (C := type1 Xs)
      (SPf := fun c => SPf (Function.invFun type1 c)))

theorem cspF_fsfF_Rep_int_choice_com_eqF [Inhabited α]
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {SPf : α → proc p α} :
    eqFfix (Rep_int_choice_com X SPf) (fsfF_Rep_int_choice_com X SPf) := by
  simpa [fsfF_Rep_int_choice_com_def, Rep_int_choice_com_def] using
    (cspF_fsfF_Rep_int_choice_set_eqF
      (Xs := {Y | ∃ a, a ∈ X ∧ Y = ({a} : Set α)})
      (SPf := fun Y => SPf (the_elem Y)))

theorem cspF_fsfF_Rep_int_choice_f_eqF [Inhabited α] [Inhabited β]
    [HasPNfun p α] [HasFPmode]
    {f : β → α} {X : Set β} {SPf : β → proc p α} :
    Injective f →
      eqFfix (Rep_int_choice_f f X SPf) (fsfF_Rep_int_choice_f f X SPf) := by
  intro _hf
  simpa [Rep_int_choice_f_def, fsfF_Rep_int_choice_f_def] using
    (cspF_fsfF_Rep_int_choice_com_eqF
      (X := f '' X)
      (SPf := fun x => SPf (Function.invFun f x)))

/- *============================================================*
 |                                                            |
 |                        Int_choice                          |
 |                                                            |
 *============================================================* -/

def fsfF_Int_choice
    (P Q : proc p α) : proc p α :=
  Rep_int_choice_nat ({0, 1} : Set Nat) fun x => if x = 0 then P else Q

theorem fsfF_Int_choice_def
    (P Q : proc p α) :
    fsfF_Int_choice P Q =
      Rep_int_choice_nat ({0, 1} : Set Nat) (fun x => if x = 0 then P else Q) :=
  rfl

/- Lean note:
   Isabelle's syntax for `P |~|seq Q` is represented directly by
   `fsfF_Int_choice P Q`. -/

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Int_choice_in
    {P Q : proc p α} :
    fsfF_proc P →
      fsfF_proc Q →
        fsfF_proc (fsfF_Int_choice P Q) := by
  intro hP hQ
  rw [fsfF_Int_choice_def, Rep_int_choice_nat_def]
  refine fsfF_proc.fsfF_proc_int ?_ ?_
  · intro hEmpty
    have hMem : (type2 0 : aset_anat α) ∈ sumset (type2 ({0, 1} : Set Nat)) := by
      simp [sumset]
    simp [hEmpty] at hMem
  · intro c hc
    have hc' : Function.invFun type2 c ∈ ({0, 1} : Set Nat) := by
      exact P_inv_type2
        (X := ({0, 1} : Set Nat))
        (P := fun n => n ∈ ({0, 1} : Set Nat))
        (by intro n hn; exact hn)
        hc
    have hc'' : Function.invFun type2 c = 0 ∨ Function.invFun type2 c = 1 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hc'
    rcases hc'' with h0 | h1
    · simpa [h0] using hP
    · simpa [h1] using hQ

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

private theorem cspF_Rep_int_choice_nat_branch_eqF
    [HasPNfun p α] [HasFPmode]
    {N : Set Nat} {Pf Qf : Nat → proc p α} :
    (∀ n, n ∈ N → eqFfix (Pf n) (Qf n)) →
      eqFfix (Rep_int_choice_nat N Pf) (Rep_int_choice_nat N Qf) := by
  intro hEq
  change eqF (Rep_int_choice_nat N Pf) MF MF (Rep_int_choice_nat N Qf)
  rw [cspF_cspT_eqF_semantics]
  constructor
  · rw [cspT_eqT_semantics]
    ext t
    constructor
    · intro ht
      have ht' :=
        (in_traces_Rep_int_choice_nat
          (t := t) (N := N) (Pf := Pf) (M := fstF ∘ MF)).1 ht
      rcases ht' with htNil | ⟨n, hn, ht'⟩
      · exact (in_traces_Rep_int_choice_nat
          (t := t) (N := N) (Pf := Qf) (M := fstF ∘ MF)).2 (Or.inl htNil)
      · refine (in_traces_Rep_int_choice_nat
          (t := t) (N := N) (Pf := Qf) (M := fstF ∘ MF)).2 ?_
        refine Or.inr ⟨n, hn, ?_⟩
        have hBranch :=
          (cspF_cspT_eqF_semantics
            (P := Pf n) (Q := Qf n) (M1 := MF) (M2 := MF)).mp (hEq n hn)
        have hTraceEq : traces (Pf n) (fstF ∘ MF) = traces (Qf n) (fstF ∘ MF) := by
          exact (cspT_eqT_semantics).mp hBranch.1
        simpa [hTraceEq] using ht'
    · intro ht
      have ht' :=
        (in_traces_Rep_int_choice_nat
          (t := t) (N := N) (Pf := Qf) (M := fstF ∘ MF)).1 ht
      rcases ht' with htNil | ⟨n, hn, ht'⟩
      · exact (in_traces_Rep_int_choice_nat
          (t := t) (N := N) (Pf := Pf) (M := fstF ∘ MF)).2 (Or.inl htNil)
      · refine (in_traces_Rep_int_choice_nat
          (t := t) (N := N) (Pf := Pf) (M := fstF ∘ MF)).2 ?_
        refine Or.inr ⟨n, hn, ?_⟩
        have hBranch :=
          (cspF_cspT_eqF_semantics
            (P := Pf n) (Q := Qf n) (M1 := MF) (M2 := MF)).mp (hEq n hn)
        have hTraceEq : traces (Pf n) (fstF ∘ MF) = traces (Qf n) (fstF ∘ MF) := by
          exact (cspT_eqT_semantics).mp hBranch.1
        simpa [hTraceEq] using ht'
  · ext f
    constructor
    · intro hf
      have hf' :=
        (in_failures_Rep_int_choice_nat
          (f := f) (N := N) (Pf := Pf) (M := MF)).1 hf
      rcases hf' with ⟨n, hn, hf'⟩
      refine (in_failures_Rep_int_choice_nat
        (f := f) (N := N) (Pf := Qf) (M := MF)).2 ?_
      refine ⟨n, hn, ?_⟩
      have hBranch :=
        (cspF_cspT_eqF_semantics
          (P := Pf n) (Q := Qf n) (M1 := MF) (M2 := MF)).mp (hEq n hn)
      simpa [hBranch.2] using hf'
    · intro hf
      have hf' :=
        (in_failures_Rep_int_choice_nat
          (f := f) (N := N) (Pf := Qf) (M := MF)).1 hf
      rcases hf' with ⟨n, hn, hf'⟩
      refine (in_failures_Rep_int_choice_nat
        (f := f) (N := N) (Pf := Pf) (M := MF)).2 ?_
      refine ⟨n, hn, ?_⟩
      have hBranch :=
        (cspF_cspT_eqF_semantics
          (P := Pf n) (Q := Qf n) (M1 := MF) (M2 := MF)).mp (hEq n hn)
      simpa [hBranch.2] using hf'

theorem cspF_fsfF_Int_choice_eqF
    [HasPNfun p α] [HasFPmode]
    {P Q : proc p α} :
    eqFfix (P |~| Q) (fsfF_Int_choice P Q) := by
  apply cspF_trans_left_eq cspF_Int_choice_to_Rep
  simpa [fsfF_Int_choice_def] using
    (cspF_Rep_int_choice_nat_branch_eqF
      (N := ({0, 1} : Set Nat))
      (Pf := fun n => IF n = 0 THEN P ELSE Q)
      (Qf := fun n => if n = 0 then P else Q)
      (by
        intro n hn
        simpa using (cspF_IF_split (b := (n = 0)) (P := P) (Q := Q) (M := MF))))

end
