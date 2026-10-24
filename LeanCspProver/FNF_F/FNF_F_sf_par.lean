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

theorem cspF_fsfF_Parallel_DIV_eqF
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {P1 : proc p α} :
    eqFfix (P1 |[X]| (proc.DIV : proc p α)) (fsfF_Parallel_DIV X P1) := by
  rw [fsfF_Parallel_DIV_def]
  refine cspF_fsfF_induct1_eqF
    (Pfun := Pfun_Parallel_DIV X) (SP_step := SP_step_Parallel_DIV X) ?_ ?_ ?_
  · intro C1 Rf1 hC
    exact cspF_Parallel_Dist_sum_l_nonempty hC
  · intro A1 Pf1 Q1 hQ1
    change eqFfix (((proc.Ext_pre_choice A1 Pf1) [+] Q1) |[X]| (proc.DIV : proc p α))
      (SP_step_Parallel_DIV X A1 Pf1 Q1 (fun a => Pf1 a |[X]| (proc.DIV : proc p α)))
    simp only [SP_step_Parallel_DIV_def]
    refine cspF_trans_left_eq
      (cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l hQ1) ?_
    exact cspF_DIV_Parallel_step_r
  · intro A1 Pf1 Q1 SPf SQf hSPf
    simp only [SP_step_Parallel_DIV_def]
    exact cspF_Ext_choice_cong
      (cspF_Ext_pre_choice_cong rfl (fun a ha => hSPf a ha.1)) cspF_reflex_eq_P

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

theorem cspF_fsfF_Parallel_SKIP_eqF
    [HasPNfun p α] [HasFPmode]
    {X : Set α} {P1 : proc p α} :
    eqFfix (P1 |[X]| (proc.SKIP : proc p α)) (fsfF_Parallel_SKIP X P1) := by
  rw [fsfF_Parallel_SKIP_def]
  refine cspF_fsfF_induct1_eqF
    (Pfun := Pfun_Parallel_SKIP X) (SP_step := SP_step_Parallel_SKIP X) ?_ ?_ ?_
  · intro C1 Rf1 hC
    exact cspF_Parallel_Dist_sum_l_nonempty hC
  · intro A1 Pf1 Q1 hQ1
    change eqFfix (((proc.Ext_pre_choice A1 Pf1) [+] Q1) |[X]| (proc.SKIP : proc p α))
      (SP_step_Parallel_SKIP X A1 Pf1 Q1 (fun a => Pf1 a |[X]| (proc.SKIP : proc p α)))
    simp only [SP_step_Parallel_SKIP_def]
    exact cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l hQ1
  · intro A1 Pf1 Q1 SPf SQf hSPf
    simp only [SP_step_Parallel_SKIP_def]
    exact cspF_Ext_choice_cong
      (cspF_Ext_pre_choice_cong rfl (fun a ha => hSPf a ha.1)) cspF_reflex_eq_P

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

theorem fsfF_Parallel_in_lm
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
                  fsfF_proc (SP_step_Parallel X A1 Pf1 Q1 A2 Pf2 Q2 SPf SPf1 SPf2) := by
  intro hPf1 hPf2 hSPf hSPf1 hSPf2 hQ1 hQ2
  -- the common prefix part
  have hR : fsfF_proc
      ((proc.Ext_pre_choice ((X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) fun a =>
          if a ∈ X then SPf a
          else if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (SPf1 a) (SPf2 a)
          else if a ∈ A1 then SPf1 a
          else SPf2 a) [+] (proc.STOP : proc p α)) := by
    refine fsfF_proc.fsfF_proc_ext ?_ (Or.inr <| Or.inr rfl)
    intro a ha
    by_cases haX : a ∈ X
    · rw [if_pos haX]
      refine hSPf a ?_
      rcases ha with (hIn | hIn) | hIn
      · exact ⟨hIn.1.2, hIn.2⟩
      · exact absurd haX hIn.2
      · exact absurd haX hIn.2
    · rw [if_neg haX]
      by_cases hBoth : a ∈ A1 ∧ a ∈ A2
      · rw [if_pos hBoth]
        exact fsfF_Int_choice_in (hSPf1 a hBoth.1) (hSPf2 a hBoth.2)
      · rw [if_neg hBoth]
        by_cases hA1 : a ∈ A1
        · rw [if_pos hA1]
          exact hSPf1 a hA1
        · rw [if_neg hA1]
          refine hSPf2 a ?_
          rcases ha with (hIn | hIn) | hIn
          · exact absurd hIn.1.1 haX
          · exact absurd hIn.1 hA1
          · exact hIn.1
  -- the two step bodies whose terminal parts may be SKIP or DIV
  have hP1ext : fsfF_proc ((proc.Ext_pre_choice A1 Pf1) [+] Q1) :=
    fsfF_proc.fsfF_proc_ext hPf1 hQ1
  have hP2ext : fsfF_proc ((proc.Ext_pre_choice A2 Pf2) [+] Q2) :=
    fsfF_proc.fsfF_proc_ext hPf2 hQ2
  simp only [SP_step_Parallel_def]
  by_cases hBothStop : Q1 = (proc.STOP : proc p α) ∧ Q2 = (proc.STOP : proc p α)
  · simp only [if_pos hBothStop]
    exact hR
  · simp only [if_neg hBothStop]
    by_cases hQ1Stop : Q1 = (proc.STOP : proc p α)
    · have hQ2SD : Q2 = (proc.SKIP : proc p α) ∨ Q2 = proc.DIV := by
        rcases hQ2 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd ⟨hQ1Stop, h⟩ hBothStop
      simp only [if_pos hQ1Stop]
      exact fsfF_Timeout_in hR (fsfF_Parallel_SKIP_DIV_in hP1ext hQ2SD)
    · simp only [if_neg hQ1Stop]
      have hQ1SD : Q1 = (proc.SKIP : proc p α) ∨ Q1 = proc.DIV := by
        rcases hQ1 with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h hQ1Stop
      by_cases hQ2Stop : Q2 = (proc.STOP : proc p α)
      · simp only [if_pos hQ2Stop]
        exact fsfF_Timeout_in hR (fsfF_Parallel_SKIP_DIV_in hP2ext hQ1SD)
      · simp only [if_neg hQ2Stop]
        have hQ2SD : Q2 = (proc.SKIP : proc p α) ∨ Q2 = proc.DIV := by
          rcases hQ2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hQ2Stop
        exact fsfF_Timeout_in hR
          (fsfF_Int_choice_in
            (fsfF_Parallel_SKIP_DIV_in hP2ext hQ1SD)
            (fsfF_Parallel_SKIP_DIV_in hP1ext hQ2SD))

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

/-- Congruence of the sequentialised timeout in its left argument. -/
private theorem Timeout_seq_cong_left
    [HasPNfun p α] [HasFPmode] {P1 P1' P2 : proc p α}
    (h : eqFfix P1 P1') :
    eqFfix (P1 [>seq P2) (P1' [>seq P2) := by
  refine cspF_trans_left_eq (cspF_sym cspF_fsfF_Timeout_eqF) ?_
  refine cspF_trans_left_eq (cspF_Timeout_cong h cspF_reflex_eq_P) ?_
  exact cspF_fsfF_Timeout_eqF

/-- Congruence of the sequentialised internal choice. -/
private theorem Int_choice_seq_cong
    [HasPNfun p α] [HasFPmode] {P1 P1' P2 P2' : proc p α}
    (h1 : eqFfix P1 P1') (h2 : eqFfix P2 P2') :
    eqFfix (fsfF_Int_choice P1 P2) (fsfF_Int_choice P1' P2') := by
  refine cspF_trans_left_eq (cspF_sym cspF_fsfF_Int_choice_eqF) ?_
  refine cspF_trans_left_eq (cspF_Int_choice_cong h1 h2) ?_
  exact cspF_fsfF_Int_choice_eqF

/-- Inside the index set of a parallel expansion, an event of `X` can only come
    from the synchronised summand, so it lies in both alphabets. -/
private theorem par_index_mem_X {X A1 A2 : Set α} {a : α}
    (ha : a ∈ (X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) (haX : a ∈ X) :
    a ∈ A1 ∧ a ∈ A2 := by
  rcases ha with (hIn | hIn) | hIn
  · exact ⟨hIn.1.2, hIn.2⟩
  · exact absurd haX hIn.2
  · exact absurd haX hIn.2

private theorem par_index_mem_A2 {X A1 A2 : Set α} {a : α}
    (ha : a ∈ (X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) (haX : a ∉ X) (haA1 : a ∉ A1) :
    a ∈ A2 := by
  rcases ha with (hIn | hIn) | hIn
  · exact absurd hIn.1.1 haX
  · exact absurd hIn.1 haA1
  · exact hIn.1

set_option maxHeartbeats 1000000 in
-- The step obligation splits four ways on the two terminal components and each
-- limb carries the whole indexed branch function through a Timeout law.
theorem cspF_fsfF_Parallel_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} {X : Set α} :
    eqFfix (P1 |[X]| P2) (P1 |[X]|seq P2) := by
  rw [fsfF_Parallel_def]
  refine cspF_fsfF_induct2_eqF
    (Pfun := Pfun_Parallel X) (SP_step := SP_step_Parallel X) ?_ ?_ ?_ ?_
  · intro C1 Rf1 Q hC
    exact cspF_Parallel_Dist_sum_l_nonempty hC
  · intro Q C2 Rf2 hC
    exact cspF_Parallel_Dist_sum_r_nonempty hC
  · intro A1 Pf1 Q1 A2 Pf2 Q2 hQ1 hQ2
    change eqFfix
      (((proc.Ext_pre_choice A1 Pf1) [+] Q1) |[X]| ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
      (SP_step_Parallel X A1 Pf1 Q1 A2 Pf2 Q2
        (fun a => Pf1 a |[X]| Pf2 a)
        (fun a => Pf1 a |[X]| ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
        (fun a => ((proc.Ext_pre_choice A1 Pf1) [+] Q1) |[X]| Pf2 a))
    simp only [SP_step_Parallel_def]
    -- the visible part is the same in every limb, up to how each side was resolved
    have hvis : ∀ B1 B2 : proc p α,
        eqFfix B1 ((proc.Ext_pre_choice A1 Pf1) [+] Q1) →
          eqFfix B2 ((proc.Ext_pre_choice A2 Pf2) [+] Q2) →
            eqFfix
              (proc.Ext_pre_choice ((X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) fun a =>
                procIte (a ∈ X) (Pf1 a |[X]| Pf2 a)
                  (procIte (a ∈ A1 ∧ a ∈ A2)
                    ((Pf1 a |[X]| B2) |~| (B1 |[X]| Pf2 a))
                    (procIte (a ∈ A1) (Pf1 a |[X]| B2) (B1 |[X]| Pf2 a))))
              ((proc.Ext_pre_choice ((X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) fun a =>
                  if a ∈ X then Pf1 a |[X]| Pf2 a
                  else if a ∈ A1 ∧ a ∈ A2 then
                    fsfF_Int_choice (Pf1 a |[X]| ((proc.Ext_pre_choice A2 Pf2) [+] Q2))
                      (((proc.Ext_pre_choice A1 Pf1) [+] Q1) |[X]| Pf2 a)
                  else if a ∈ A1 then Pf1 a |[X]| ((proc.Ext_pre_choice A2 Pf2) [+] Q2)
                  else ((proc.Ext_pre_choice A1 Pf1) [+] Q1) |[X]| Pf2 a)
                [+] (proc.STOP : proc p α)) := by
      intro B1 B2 h1 h2
      refine cspF_trans_left_eq ?_ (cspF_sym cspF_Ext_choice_unit_r)
      refine cspF_Ext_pre_choice_cong rfl (fun a ha => ?_)
      by_cases haX : a ∈ X
      · rw [procIte_pos haX, if_pos haX]
        exact cspF_reflex_eq_P
      · rw [procIte_neg haX, if_neg haX]
        by_cases hBoth : a ∈ A1 ∧ a ∈ A2
        · rw [procIte_pos hBoth, if_pos hBoth]
          refine cspF_trans_left_eq ?_ cspF_fsfF_Int_choice_eqF
          exact cspF_Int_choice_cong
            (cspF_Parallel_cong rfl cspF_reflex_eq_P h2)
            (cspF_Parallel_cong rfl h1 cspF_reflex_eq_P)
        · rw [procIte_neg hBoth, if_neg hBoth]
          by_cases hA1 : a ∈ A1
          · rw [procIte_pos hA1, if_pos hA1]
            exact cspF_Parallel_cong rfl cspF_reflex_eq_P h2
          · rw [procIte_neg hA1, if_neg hA1]
            exact cspF_Parallel_cong rfl h1 cspF_reflex_eq_P
    by_cases hBothStop : Q1 = (proc.STOP : proc p α) ∧ Q2 = (proc.STOP : proc p α)
    · simp only [if_pos hBothStop]
      obtain ⟨hQ1s, hQ2s⟩ := hBothStop
      subst hQ1s
      subst hQ2s
      refine cspF_trans_left_eq
        (cspF_Parallel_cong rfl cspF_Ext_choice_unit_r cspF_Ext_choice_unit_r) ?_
      refine cspF_trans_left_eq cspF_Parallel_step ?_
      exact hvis _ _ (cspF_sym cspF_Ext_choice_unit_r) (cspF_sym cspF_Ext_choice_unit_r)
    · simp only [if_neg hBothStop]
      by_cases hQ1Stop : Q1 = (proc.STOP : proc p α)
      · -- only the right component can time out
        have hQ2SD : Q2 = (proc.SKIP : proc p α) ∨ Q2 = proc.DIV := by
          rcases hQ2 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd ⟨hQ1Stop, h⟩ hBothStop
        simp only [if_pos hQ1Stop]
        subst hQ1Stop
        refine cspF_trans_left_eq
          (cspF_Parallel_cong rfl cspF_Ext_choice_unit_r
            (cspF_Ext_choice_SKIP_or_DIV_resolve hQ2SD)) ?_
        refine cspF_trans_left_eq cspF_Parallel_Timeout_input_r ?_
        refine cspF_trans_left_eq ?_ cspF_fsfF_Timeout_eqF
        refine cspF_Timeout_cong
          (hvis _ _ (cspF_sym cspF_Ext_choice_unit_r)
            (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ2SD))) ?_
        -- the internal transition
        rw [fsfF_Parallel_SKIP_DIV_def]
        rcases hQ2SD with rfl | rfl
        · rw [if_pos rfl]
          refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_SKIP_eqF
          exact cspF_Parallel_cong rfl (cspF_sym cspF_Ext_choice_unit_r) cspF_reflex_eq_P
        · rw [if_neg (show ¬ ((proc.DIV : proc p α) = proc.SKIP) by intro h; cases h),
            if_pos rfl]
          refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_DIV_eqF
          exact cspF_Parallel_cong rfl (cspF_sym cspF_Ext_choice_unit_r) cspF_reflex_eq_P
      · have hQ1SD : Q1 = (proc.SKIP : proc p α) ∨ Q1 = proc.DIV := by
          rcases hQ1 with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hQ1Stop
        simp only [if_neg hQ1Stop]
        by_cases hQ2Stop : Q2 = (proc.STOP : proc p α)
        · -- only the left component can time out
          simp only [if_pos hQ2Stop]
          subst hQ2Stop
          refine cspF_trans_left_eq
            (cspF_Parallel_cong rfl (cspF_Ext_choice_SKIP_or_DIV_resolve hQ1SD)
              cspF_Ext_choice_unit_r) ?_
          refine cspF_trans_left_eq cspF_Parallel_Timeout_input_l ?_
          refine cspF_trans_left_eq ?_ cspF_fsfF_Timeout_eqF
          refine cspF_Timeout_cong
            (hvis _ _ (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ1SD))
              (cspF_sym cspF_Ext_choice_unit_r)) ?_
          rw [fsfF_Parallel_SKIP_DIV_def]
          rcases hQ1SD with rfl | rfl
          · rw [if_pos rfl]
            refine cspF_trans_left_eq cspF_Parallel_commut ?_
            refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_SKIP_eqF
            exact cspF_Parallel_cong rfl (cspF_sym cspF_Ext_choice_unit_r) cspF_reflex_eq_P
          · rw [if_neg (show ¬ ((proc.DIV : proc p α) = proc.SKIP) by intro h; cases h),
              if_pos rfl]
            refine cspF_trans_left_eq cspF_Parallel_commut ?_
            refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_DIV_eqF
            exact cspF_Parallel_cong rfl (cspF_sym cspF_Ext_choice_unit_r) cspF_reflex_eq_P
        · -- both components can time out
          have hQ2SD : Q2 = (proc.SKIP : proc p α) ∨ Q2 = proc.DIV := by
            rcases hQ2 with h | h | h
            · exact Or.inl h
            · exact Or.inr h
            · exact absurd h hQ2Stop
          simp only [if_neg hQ2Stop]
          refine cspF_trans_left_eq
            (cspF_Parallel_cong rfl (cspF_Ext_choice_SKIP_or_DIV_resolve hQ1SD)
              (cspF_Ext_choice_SKIP_or_DIV_resolve hQ2SD)) ?_
          refine cspF_trans_left_eq cspF_Parallel_Timeout_split ?_
          refine cspF_trans_left_eq ?_ cspF_fsfF_Timeout_eqF
          refine cspF_Timeout_cong
            (hvis _ _ (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ1SD))
              (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ2SD))) ?_
          refine cspF_trans_left_eq ?_ cspF_fsfF_Int_choice_eqF
          refine cspF_Int_choice_cong ?_ ?_
          · rw [fsfF_Parallel_SKIP_DIV_def]
            refine cspF_trans_left_eq cspF_Parallel_commut ?_
            rcases hQ1SD with rfl | rfl
            · rw [if_pos rfl]
              refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_SKIP_eqF
              exact cspF_Parallel_cong rfl
                (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ2SD)) cspF_reflex_eq_P
            · rw [if_neg (show ¬ ((proc.DIV : proc p α) = proc.SKIP) by intro h; cases h),
                if_pos rfl]
              refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_DIV_eqF
              exact cspF_Parallel_cong rfl
                (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ2SD)) cspF_reflex_eq_P
          · rw [fsfF_Parallel_SKIP_DIV_def]
            rcases hQ2SD with rfl | rfl
            · rw [if_pos rfl]
              refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_SKIP_eqF
              exact cspF_Parallel_cong rfl
                (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ1SD)) cspF_reflex_eq_P
            · rw [if_neg (show ¬ ((proc.DIV : proc p α) = proc.SKIP) by intro h; cases h),
                if_pos rfl]
              refine cspF_trans_left_eq ?_ cspF_fsfF_Parallel_DIV_eqF
              exact cspF_Parallel_cong rfl
                (cspF_sym (cspF_Ext_choice_SKIP_or_DIV_resolve hQ1SD)) cspF_reflex_eq_P
  · intro A1 Pf1 Q1 A2 Pf2 Q2 SPf SQf SPf1 SQf1 SPf2 SQf2 hSPf hSPf1 hSPf2
    simp only [SP_step_Parallel_def]
    have hR : eqFfix
        ((proc.Ext_pre_choice ((X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) fun a =>
            if a ∈ X then SPf a
            else if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (SPf1 a) (SPf2 a)
            else if a ∈ A1 then SPf1 a else SPf2 a) [+] (proc.STOP : proc p α))
        ((proc.Ext_pre_choice ((X ∩ A1 ∩ A2) ∪ (A1 \ X) ∪ (A2 \ X)) fun a =>
            if a ∈ X then SQf a
            else if a ∈ A1 ∧ a ∈ A2 then fsfF_Int_choice (SQf1 a) (SQf2 a)
            else if a ∈ A1 then SQf1 a else SQf2 a) [+] (proc.STOP : proc p α)) := by
      refine cspF_Ext_choice_cong (cspF_Ext_pre_choice_cong rfl (fun a ha => ?_))
        cspF_reflex_eq_P
      by_cases haX : a ∈ X
      · rw [if_pos haX, if_pos haX]
        exact hSPf a (par_index_mem_X ha haX)
      · rw [if_neg haX, if_neg haX]
        by_cases hBoth : a ∈ A1 ∧ a ∈ A2
        · rw [if_pos hBoth, if_pos hBoth]
          exact Int_choice_seq_cong (hSPf1 a hBoth.1) (hSPf2 a hBoth.2)
        · rw [if_neg hBoth, if_neg hBoth]
          by_cases hA1 : a ∈ A1
          · rw [if_pos hA1, if_pos hA1]
            exact hSPf1 a hA1
          · rw [if_neg hA1, if_neg hA1]
            exact hSPf2 a (par_index_mem_A2 ha haX hA1)
    by_cases hBothStop : Q1 = (proc.STOP : proc p α) ∧ Q2 = (proc.STOP : proc p α)
    · simp only [if_pos hBothStop]
      exact hR
    · simp only [if_neg hBothStop]
      by_cases hQ1Stop : Q1 = (proc.STOP : proc p α)
      · simp only [if_pos hQ1Stop]
        exact Timeout_seq_cong_left hR
      · simp only [if_neg hQ1Stop]
        by_cases hQ2Stop : Q2 = (proc.STOP : proc p α)
        · simp only [if_pos hQ2Stop]
          exact Timeout_seq_cong_left hR
        · simp only [if_neg hQ2Stop]
          exact Timeout_seq_cong_left hR

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
