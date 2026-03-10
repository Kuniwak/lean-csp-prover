           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |              Februaru 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_ext

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

         1. full sequentialization for Parallel (P1 |[X]| DIV)
         2. full sequentialization for Parallel (P1 |[X]| SKIP)
         3. full sequentialization for Parallel (P1 |[X]| P2)

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                Parallel (P |[X]| DIV)                      |
 |                                                            |
 *============================================================* -/

def Pfun_Parallel_DIV (X : Set α) : proc p α → proc p α :=
  fun P1 => P1 |[X]| (proc.DIV : proc p α)

theorem Pfun_Parallel_DIV_def
    (X : Set α) :
    Pfun_Parallel_DIV (p := p) (α := α) X =
      (fun P1 => P1 |[X]| (proc.DIV : proc p α)) :=
  rfl

def SP_step_Parallel_DIV
    (X : Set α) :
    Set α → (α → proc p α) → proc p α → (α → proc p α) → proc p α :=
  fun A1 _Pf1 _Q1 SPf =>
    (proc.Ext_pre_choice (A1 \ X) SPf) [+] (proc.DIV : proc p α)

theorem SP_step_Parallel_DIV_def
    (X : Set α) :
    SP_step_Parallel_DIV (p := p) (α := α) X =
      (fun A1 _Pf1 _Q1 SPf =>
        (proc.Ext_pre_choice (A1 \ X) SPf) [+] (proc.DIV : proc p α)) :=
  rfl

def fsfF_Parallel_DIV
    (X : Set α) (P1 : proc p α) : proc p α :=
  fsfF_induct1 (Pfun_Parallel_DIV X) (SP_step_Parallel_DIV X) P1

theorem fsfF_Parallel_DIV_def
    (X : Set α) (P1 : proc p α) :
    fsfF_Parallel_DIV (p := p) (α := α) X P1 =
      fsfF_induct1 (Pfun_Parallel_DIV X) (SP_step_Parallel_DIV X) P1 :=
  rfl

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Parallel_DIV_in
    {X : Set α} {P1 : proc p α} :
    fsfF_proc P1 →
      fsfF_proc (fsfF_Parallel_DIV X P1) := by
  intro hP1
  rw [fsfF_Parallel_DIV_def]
  refine fsfF_induct1_in hP1 ?_
  intro A1 Pf1 Q1 SPf _hPf1 hSPf _hQ1
  refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inl rfl)
  intro a ha
  exact hSPf a ha.1

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fsfF_Parallel_DIV_eqF
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {P1 : proc p α} :
    eqFfix (P1 |[X]| (proc.DIV : proc p α)) (fsfF_Parallel_DIV X P1)

/- *============================================================*
 |                                                            |
 |                Parallel (P |[X]| SKIP)                     |
 |                                                            |
 *============================================================* -/

def Pfun_Parallel_SKIP (X : Set α) : proc p α → proc p α :=
  fun P1 => P1 |[X]| (proc.SKIP : proc p α)

theorem Pfun_Parallel_SKIP_def
    (X : Set α) :
    Pfun_Parallel_SKIP (p := p) (α := α) X =
      (fun P1 => P1 |[X]| (proc.SKIP : proc p α)) :=
  rfl

def SP_step_Parallel_SKIP
    (X : Set α) :
    Set α → (α → proc p α) → proc p α → (α → proc p α) → proc p α :=
  fun A1 _Pf1 Q1 SPf =>
    (proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1

theorem SP_step_Parallel_SKIP_def
    (X : Set α) :
    SP_step_Parallel_SKIP (p := p) (α := α) X =
      (fun A1 _Pf1 Q1 SPf =>
        (proc.Ext_pre_choice (A1 \ X) SPf) [+] Q1) :=
  rfl

def fsfF_Parallel_SKIP
    (X : Set α) (P1 : proc p α) : proc p α :=
  fsfF_induct1 (Pfun_Parallel_SKIP X) (SP_step_Parallel_SKIP X) P1

theorem fsfF_Parallel_SKIP_def
    (X : Set α) (P1 : proc p α) :
    fsfF_Parallel_SKIP (p := p) (α := α) X P1 =
      fsfF_induct1 (Pfun_Parallel_SKIP X) (SP_step_Parallel_SKIP X) P1 :=
  rfl

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Parallel_SKIP_in
    {X : Set α} {P1 : proc p α} :
    fsfF_proc P1 →
      fsfF_proc (fsfF_Parallel_SKIP X P1) := by
  intro hP1
  rw [fsfF_Parallel_SKIP_def]
  refine fsfF_induct1_in hP1 ?_
  intro A1 Pf1 Q1 SPf _hPf1 hSPf hQ1
  exact fsfF_proc.fsfF_proc_ext (fun a ha => hSPf a ha.1) hQ1

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fsfF_Parallel_SKIP_eqF
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {P1 : proc p α} :
    eqFfix (P1 |[X]| (proc.SKIP : proc p α)) (fsfF_Parallel_SKIP X P1)

/- *============================================================*
 |                                                            |
 |              Parallel (P |[X]| SKIP or DIV)                |
 |                                                            |
 *============================================================* -/

def fsfF_Parallel_SKIP_DIV
    (X : Set α) (P1 P2 : proc p α) : proc p α :=
  if P2 = proc.SKIP then fsfF_Parallel_SKIP X P1
  else if P2 = proc.DIV then fsfF_Parallel_DIV X P1
  else P1 |[X]| P2

theorem fsfF_Parallel_SKIP_DIV_def
    (X : Set α) (P1 P2 : proc p α) :
    fsfF_Parallel_SKIP_DIV (p := p) (α := α) X P1 P2 =
      if P2 = proc.SKIP then fsfF_Parallel_SKIP X P1
      else if P2 = proc.DIV then fsfF_Parallel_DIV X P1
      else P1 |[X]| P2 :=
  rfl

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fsfF_Parallel_SKIP_DIV_in
    {X : Set α} {P1 P2 : proc p α} :
    fsfF_proc P1 →
      (P2 = proc.SKIP ∨ P2 = proc.DIV) →
        fsfF_proc (fsfF_Parallel_SKIP_DIV X P1 P2) := by
  intro hP1 hP2
  rw [fsfF_Parallel_SKIP_DIV_def]
  rcases hP2 with rfl | rfl
  · simp [fsfF_Parallel_SKIP_in, hP1]
  · simp [fsfF_Parallel_DIV_in, hP1]

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fsfF_Parallel_SKIP_DIV_eqF
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {P1 P2 : proc p α} :
    eqFfix (P1 |[X]| P2) (fsfF_Parallel_SKIP_DIV X P1 P2) := by
  rw [fsfF_Parallel_SKIP_DIV_def]
  by_cases hSkip : P2 = proc.SKIP
  · simp [hSkip, cspF_fsfF_Parallel_SKIP_eqF]
  · by_cases hDiv : P2 = proc.DIV
    · simp [hDiv, cspF_fsfF_Parallel_DIV_eqF]
    · simp [hSkip, hDiv]
      simpa using (cspF_reflex_eq_P (P := P1 |[X]| P2) (M := MF))

theorem cspF_fsfF_Parallel_SKIP_DIV_eqF_sym
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {P1 P2 : proc p α} :
    eqFfix (fsfF_Parallel_SKIP_DIV X P1 P2) (P1 |[X]| P2) :=
  cspF_sym cspF_fsfF_Parallel_SKIP_DIV_eqF

/- *============================================================*
 |                                                            |
 |            Genaralized Parallel (P |[X]| Q)                |
 |                                                            |
 *============================================================* -/

def Pfun_Parallel
    (X : Set α) : proc p α → proc p α → proc p α :=
  fun P1 P2 => P1 |[X]| P2

theorem Pfun_Parallel_def
    (X : Set α) :
    Pfun_Parallel (p := p) (α := α) X =
      (fun P1 P2 => P1 |[X]| P2) :=
  rfl

def SP_step_Parallel
    (X : Set α) :
    Set α → (α → proc p α) → proc p α →
      Set α → (α → proc p α) → proc p α →
      (α → proc p α) → (α → proc p α) → (α → proc p α) →
      proc p α :=
  fun A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 =>
    let Y := (X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)
    let R :=
      proc.Ext_pre_choice Y fun a =>
        if a ∈ X then SPf a
        else if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (SPf1 a) (SPf2 a)
        else if a ∈ A1 then SPf1 a
        else SPf2 a
    if Q1 = proc.STOP ∧ Q2 = proc.STOP then
      R [+] (proc.STOP : proc p α)
    else if Q1 = proc.STOP then
      (R [+] (proc.STOP : proc p α)) [>seq
        (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A1 Pf1) [+] Q1)) Q2)
    else if Q2 = proc.STOP then
      (R [+] (proc.STOP : proc p α)) [>seq
        (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A2 Pf2) [+] Q2)) Q1)
    else
      (R [+] (proc.STOP : proc p α)) [>seq
        (fsfF_Int_choice
          (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A2 Pf2) [+] Q2)) Q1)
          (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A1 Pf1) [+] Q1)) Q2))

theorem SP_step_Parallel_def
    (X : Set α) :
    SP_step_Parallel (p := p) (α := α) X =
      (fun A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 =>
        let Y := (X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)
        let R :=
          proc.Ext_pre_choice Y fun a =>
            if a ∈ X then SPf a
            else if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (SPf1 a) (SPf2 a)
            else if a ∈ A1 then SPf1 a
            else SPf2 a
        if Q1 = proc.STOP ∧ Q2 = proc.STOP then
          R [+] (proc.STOP : proc p α)
        else if Q1 = proc.STOP then
          (R [+] (proc.STOP : proc p α)) [>seq
            (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A1 Pf1) [+] Q1)) Q2)
        else if Q2 = proc.STOP then
          (R [+] (proc.STOP : proc p α)) [>seq
            (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A2 Pf2) [+] Q2)) Q1)
        else
          (R [+] (proc.STOP : proc p α)) [>seq
            (fsfF_Int_choice
              (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A2 Pf2) [+] Q2)) Q1)
              (fsfF_Parallel_SKIP_DIV X (((proc.Ext_pre_choice A1 Pf1) [+] Q1)) Q2))) :=
  rfl

def fsfF_Parallel
    (P1 : proc p α) (X : Set α) (P2 : proc p α) : proc p α :=
  fsfF_induct2 (Pfun_Parallel X) (SP_step_Parallel X) P1 P2

theorem fsfF_Parallel_def
    (P1 : proc p α) (X : Set α) (P2 : proc p α) :
    fsfF_Parallel (p := p) (α := α) P1 X P2 =
      fsfF_induct2 (Pfun_Parallel X) (SP_step_Parallel X) P1 P2 :=
  rfl

notation:76 P " |[" X "]|seq " Q => fsfF_Parallel P X Q

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

axiom fsfF_Parallel_in_lm
    {X A1 A2 : Set α}
    {Pf1 Pf2 SPf SPf1 SPf2 : α → proc p α}
    {Q1 Q2 : proc p α} :
    (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
      (∀ a, a ∈ A2 → fsfF_proc (Pf2 a)) →
        (∀ a, a ∈ A1 ∩ A2 → fsfF_proc (SPf a)) →
          (∀ a, a ∈ A1 → fsfF_proc (SPf1 a)) →
            (∀ a, a ∈ A2 → fsfF_proc (SPf2 a)) →
              (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
                (Q2 = proc.SKIP ∨ Q2 = proc.DIV ∨ Q2 = proc.STOP) →
                  fsfF_proc (SP_step_Parallel X A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2)

theorem fsfF_Parallel_in
    {P1 P2 : proc p α} {X : Set α} :
    fsfF_proc P1 →
      fsfF_proc P2 →
        fsfF_proc (P1 |[X]|seq P2) := by
  intro hP1 hP2
  rw [fsfF_Parallel_def]
  refine fsfF_induct2_in hP1 hP2 ?_
  intro A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2 hPf1 hPf2 hSPf hSPf1 hSPf2 hQ1 hQ2
  exact fsfF_Parallel_in_lm hPf1 hPf2 hSPf hSPf1 hSPf2 hQ1 hQ2

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

axiom cspF_fsfF_Parallel_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} {X : Set α} :
    eqFfix (P1 |[X]| P2) (P1 |[X]|seq P2)

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
