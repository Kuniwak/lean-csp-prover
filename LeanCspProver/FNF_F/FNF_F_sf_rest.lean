           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |              Februaru 2006                |
            |                 March 2007  (modified)    |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_sf_def

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

         1. full sequentialization for Depth-restriction (P |. n)
         2.
         3.

 *****************************************************************)
-/

/- *============================================================*
 |                                                            |
 |                       Depth_rest                           |
 |                                                            |
 *============================================================* -/

/- *============================================================*
 |                         Pfun P1 P2                         |
 *============================================================* -/

/- relation -/

/- Lean note:
   Isabelle defines `fsfF_Depth_rest_rel` as an `inductive_set`; an earlier
   port axiomatized the predicate, its introduction rules, and the
   uniqueness / inversion / existence facts. It is now a real `inductive`,
   and all of those become theorems. The `int` and `step` introduction
   rules keep their Isabelle statements (with an `if _ then _ else _`
   premise); since a recursive occurrence under `ite` is not strictly
   positive for Lean's kernel, the constructors themselves
   (`int_split` / `step_split`) take the two implications separately, and
   the original rules are derived. -/

inductive fsfF_Depth_rest_rel : proc p α → Nat → proc p α → Prop where
  | zero
      {P1 : proc p α} :
      fsfF_Depth_rest_rel P1 0 SDIV
  | etc
      {P1 : proc p α}
      {n : Nat} :
      ¬ fsfF_proc P1 →
        fsfF_Depth_rest_rel P1 (Nat.succ n) (P1 |. Nat.succ n)
  | int_split
      {C1 : sets_nats α}
      {Rf1 SRf : aset_anat α → proc p α}
      {m : Nat} :
      (∀ c, c ∈ sumset C1 →
        fsfF_Depth_rest_rel (Rf1 c) (Nat.succ m) (SRf c)) →
        (∀ c, c ∉ sumset C1 → SRf c = proc.DIV) →
          sumset C1 ≠ ∅ →
            (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
              fsfF_Depth_rest_rel
                (proc.Rep_int_choice C1 Rf1)
                (Nat.succ m)
                (proc.Rep_int_choice C1 SRf)
  | step_split
      {A1 : Set α}
      {Pf1 SPf : α → proc p α}
      {Q1 : proc p α}
      {n : Nat} :
      (∀ a, a ∈ A1 → fsfF_Depth_rest_rel (Pf1 a) n (SPf a)) →
        (∀ a, a ∉ A1 → SPf a = proc.DIV) →
          (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
            (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
              fsfF_Depth_rest_rel
                ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
                (Nat.succ n)
                ((proc.Ext_pre_choice A1 SPf) [+] Q1)

namespace fsfF_Depth_rest_rel

theorem int
    {C1 : sets_nats α}
    {Rf1 SRf : aset_anat α → proc p α}
    {m : Nat} :
    (∀ c, if c ∈ sumset C1
      then fsfF_Depth_rest_rel (Rf1 c) (Nat.succ m) (SRf c)
      else SRf c = proc.DIV) →
      sumset C1 ≠ ∅ →
        (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
          fsfF_Depth_rest_rel
            (proc.Rep_int_choice C1 Rf1)
            (Nat.succ m)
            (proc.Rep_int_choice C1 SRf) := by
  intro h hC hRf
  refine int_split ?_ ?_ hC hRf
  · intro c hc
    have hc' := h c
    rwa [if_pos hc] at hc'
  · intro c hc
    have hc' := h c
    rwa [if_neg hc] at hc'

theorem step
    {A1 : Set α}
    {Pf1 SPf : α → proc p α}
    {Q1 : proc p α}
    {n : Nat} :
    (∀ a, if a ∈ A1
      then fsfF_Depth_rest_rel (Pf1 a) n (SPf a)
      else SPf a = proc.DIV) →
      (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
        (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
          fsfF_Depth_rest_rel
            ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
            (Nat.succ n)
            ((proc.Ext_pre_choice A1 SPf) [+] Q1) := by
  intro h hPf hQ
  refine step_split ?_ ?_ hPf hQ
  · intro a ha
    have ha' := h a
    rwa [if_pos ha] at ha'
  · intro a ha
    have ha' := h a
    rwa [if_neg ha] at ha'

end fsfF_Depth_rest_rel

/- function -/

private theorem fsfF_Depth_rest_rel_exists_in'
    {P1 : proc p α} (hP1 : fsfF_proc P1) :
    ∀ n, ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  induction hP1 with
  | @fsfF_proc_int C Rf hC hRf ih =>
      intro n
      cases n with
      | zero => exact ⟨SDIV, fsfF_Depth_rest_rel.zero⟩
      | succ m =>
          refine ⟨proc.Rep_int_choice C (fun c =>
            if hc : c ∈ sumset C
            then Classical.choose (ih c hc (Nat.succ m))
            else proc.DIV), ?_⟩
          refine fsfF_Depth_rest_rel.int_split ?_ ?_ hC hRf
          · intro c hc
            rw [dif_pos hc]
            exact Classical.choose_spec (ih c hc (Nat.succ m))
          · intro c hc
            rw [dif_neg hc]
  | @fsfF_proc_ext A Pf Q hPf hQ ih =>
      intro n
      cases n with
      | zero => exact ⟨SDIV, fsfF_Depth_rest_rel.zero⟩
      | succ m =>
          refine ⟨(proc.Ext_pre_choice A (fun a =>
            if ha : a ∈ A
            then Classical.choose (ih a ha m)
            else proc.DIV)) [+] Q, ?_⟩
          refine fsfF_Depth_rest_rel.step_split ?_ ?_ hPf hQ
          · intro a ha
            rw [dif_pos ha]
            exact Classical.choose_spec (ih a ha m)
          · intro a ha
            rw [dif_neg ha]

private theorem fsfF_Depth_rest_rel_exists_ax
    (P1 : proc p α)
    (n : Nat) :
    ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  cases n with
  | zero => exact ⟨SDIV, fsfF_Depth_rest_rel.zero⟩
  | succ m =>
      by_cases hP1 : fsfF_proc P1
      · exact fsfF_Depth_rest_rel_exists_in' hP1 (Nat.succ m)
      · exact ⟨P1 |. Nat.succ m, fsfF_Depth_rest_rel.etc hP1⟩

def fsfF_Depth_rest
    (P1 : proc p α) (n : Nat) : proc p α :=
  Classical.choose (fsfF_Depth_rest_rel_exists_ax P1 n)

theorem fsfF_Depth_rest_def
    (P1 : proc p α) (n : Nat) :
    fsfF_Depth_rest P1 n =
      Classical.choose (fsfF_Depth_rest_rel_exists_ax P1 n) :=
  rfl

/- Lean note:
   Isabelle's syntax/translation for `P |.seq n` is represented directly by
   `fsfF_Depth_rest P n`. -/

/-
(****************************************************************
 |                      uniquness                               |
 ****************************************************************)
-/

theorem fsfF_Depth_rest_rel_unique
    {P1 : proc p α}
    {n : Nat}
    {SP1 SP2 : proc p α} :
    fsfF_Depth_rest_rel P1 n SP1 →
      fsfF_Depth_rest_rel P1 n SP2 →
        SP1 = SP2 := by
  intro h1
  induction h1 generalizing SP2 with
  | zero =>
      intro h2
      cases h2
      rfl
  | etc hnot =>
      intro h2
      cases h2 with
      | etc _ => rfl
      | int_split _ _ hC hRf =>
          exact absurd (fsfF_proc.fsfF_proc_int hC hRf) hnot
      | step_split _ _ hPf hQ =>
          exact absurd (fsfF_proc.fsfF_proc_ext hPf hQ) hnot
  | @int_split C1 Rf1 SRf m hin hout hC hRf ih =>
      intro h2
      cases h2 with
      | etc hnot =>
          exact absurd (fsfF_proc.fsfF_proc_int hC hRf) hnot
      | int_split hin' hout' _ _ =>
          congr 1
          funext c
          by_cases hc : c ∈ sumset C1
          · exact ih c hc (hin' c hc)
          · rw [hout c hc, hout' c hc]
  | @step_split A1 Pf1 SPf Q1 m hin hout hPf hQ ih =>
      intro h2
      cases h2 with
      | etc hnot =>
          exact absurd (fsfF_proc.fsfF_proc_ext hPf hQ) hnot
      | step_split hin' hout' _ _ =>
          congr 1
          congr 1
          funext a
          by_cases ha : a ∈ A1
          · exact ih a ha (hin' a ha)
          · rw [hout a ha, hout' a ha]

lemma fsfF_Depth_rest_rel_unique_in_lm
    {P1 : proc p α}
    {n : Nat}
    {SP1 : proc p α} :
    fsfF_Depth_rest_rel P1 n SP1 →
      ∀ SP2 : proc p α, fsfF_Depth_rest_rel P1 n SP2 → SP1 = SP2 := by
  intro hSP1 SP2 hSP2
  exact fsfF_Depth_rest_rel_unique (P1 := P1) (n := n) hSP1 hSP2

/- *-----------------------*
 |        unique         |
 *-----------------------* -/

lemma fsfF_Depth_rest_rel_EX1
    (P1 : proc p α)
    (n : Nat) :
    (∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP) ↔
      ∃! SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  constructor
  · intro h
    rcases h with ⟨SP, hSP⟩
    exact ⟨SP, hSP, fun SP2 hSP2 =>
      fsfF_Depth_rest_rel_unique
        (P1 := P1)
        (n := n)
        (SP1 := SP2)
        (SP2 := SP)
        hSP2
        hSP⟩
  · intro h
    exact h.exists

/- *------------------------------------------------------------*
 |                   fsfF_Depth_rest_rel (iff)                |
 *------------------------------------------------------------* -/

/- zero -/

theorem fsfF_Depth_rest_rel_zero_iff
    {P1 SP : proc p α} :
    fsfF_Depth_rest_rel P1 0 SP ↔ SP = SDIV := by
  constructor
  · intro h
    exact fsfF_Depth_rest_rel_unique h fsfF_Depth_rest_rel.zero
  · rintro rfl
    exact fsfF_Depth_rest_rel.zero

/- etc -/

theorem fsfF_Depth_rest_rel_etc_iff
    {P1 SP : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      (fsfF_Depth_rest_rel P1 (Nat.succ n) SP ↔ SP = P1 |. Nat.succ n) := by
  intro hnot
  constructor
  · intro h
    exact fsfF_Depth_rest_rel_unique h (fsfF_Depth_rest_rel.etc hnot)
  · rintro rfl
    exact fsfF_Depth_rest_rel.etc hnot

/- int nat -/

theorem fsfF_Depth_rest_rel_int_iff
    {C1 : sets_nats α}
    {Rf1 SRf : aset_anat α → proc p α}
    {m : Nat}
    {SP : proc p α} :
    (∀ c, if c ∈ sumset C1
      then fsfF_Depth_rest_rel (Rf1 c) (Nat.succ m) (SRf c)
      else SRf c = proc.DIV) →
      sumset C1 ≠ ∅ →
        (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
          (fsfF_Depth_rest_rel
              (proc.Rep_int_choice C1 Rf1)
              (Nat.succ m)
              SP ↔
            SP = proc.Rep_int_choice C1 SRf) := by
  intro h hC hRf
  constructor
  · intro hSP
    exact fsfF_Depth_rest_rel_unique hSP (fsfF_Depth_rest_rel.int h hC hRf)
  · rintro rfl
    exact fsfF_Depth_rest_rel.int h hC hRf

/- step -/

theorem fsfF_Depth_rest_rel_step_iff
    {A1 : Set α}
    {Pf1 SPf : α → proc p α}
    {Q1 SP : proc p α}
    {n : Nat} :
    (∀ a, if a ∈ A1
      then fsfF_Depth_rest_rel (Pf1 a) n (SPf a)
      else SPf a = proc.DIV) →
      (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
        (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
          (fsfF_Depth_rest_rel
              ((proc.Ext_pre_choice A1 Pf1) [+] Q1)
              (Nat.succ n)
              SP ↔
            SP = ((proc.Ext_pre_choice A1 SPf) [+] Q1)) := by
  intro h hPf hQ
  constructor
  · intro hSP
    exact fsfF_Depth_rest_rel_unique hSP (fsfF_Depth_rest_rel.step h hPf hQ)
  · rintro rfl
    exact fsfF_Depth_rest_rel.step h hPf hQ

/-
(****************************************************************
 |                      existency                               |
 ****************************************************************)
-/

/- exists -/

lemma fsfF_Depth_rest_rel_exists_zero
    (P1 : proc p α) :
    ∃ SP : proc p α, fsfF_Depth_rest_rel P1 0 SP := by
  exact ⟨SDIV, fsfF_Depth_rest_rel.zero⟩

lemma fsfF_Depth_rest_rel_exists_notin
    {P1 : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  intro hP1
  cases n with
  | zero =>
      exact fsfF_Depth_rest_rel_exists_zero P1
  | succ m =>
      exact ⟨P1 |. Nat.succ m, fsfF_Depth_rest_rel.etc hP1⟩

/- in fsfF_proc -/

lemma fsfF_Depth_rest_rel_exists_in
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ n, ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP := by
  intro _hP1 n
  exact fsfF_Depth_rest_rel_exists_ax P1 n

/- *-----------------------*
 |        exists         |
 *-----------------------* -/

lemma fsfF_Depth_rest_rel_exists
    (P1 : proc p α)
    (n : Nat) :
    ∃ SP : proc p α, fsfF_Depth_rest_rel P1 n SP :=
  fsfF_Depth_rest_rel_exists_ax P1 n

/- *-----------------------*
 |    uniquely exists    |
 *-----------------------* -/

lemma fsfF_Depth_rest_rel_unique_exists
    (P1 : proc p α)
    (n : Nat) :
    ∃! SP : proc p α, fsfF_Depth_rest_rel P1 n SP :=
  (fsfF_Depth_rest_rel_EX1 P1 n).1 (fsfF_Depth_rest_rel_exists P1 n)

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

lemma fsfF_Depth_rest_rel_zero_in
    {P1 SP : proc p α} :
    fsfF_Depth_rest_rel P1 0 SP →
      fsfF_proc SP := by
  intro hSP
  have hEq : SP = SDIV :=
    (fsfF_Depth_rest_rel_zero_iff (P1 := P1) (SP := SP)).1 hSP
  subst SP
  exact fsfF_SDIV_in (p := p) (α := α)

theorem fsfF_Depth_rest_rel_in
    {P1 SP : proc p α}
    {n : Nat}
    (hP1 : fsfF_proc P1)
    (h : fsfF_Depth_rest_rel P1 n SP) :
    fsfF_proc SP := by
  induction h with
  | zero => exact fsfF_SDIV_in
  | etc hnot => exact absurd hP1 hnot
  | int_split hin hout hC hRf ih =>
      refine fsfF_proc.fsfF_proc_int hC (fun c hc => ?_)
      exact ih c hc (hRf c hc)
  | step_split hin hout hPf hQ ih =>
      refine fsfF_proc.fsfF_proc_ext (fun a ha => ?_) hQ
      exact ih a ha (hPf a ha)

lemma fsfF_Depth_rest_rel_in_lm
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ n SP, fsfF_Depth_rest_rel P1 n SP → fsfF_proc SP := by
  intro hP1 n SP hSP
  exact fsfF_Depth_rest_rel_in (P1 := P1) (n := n) hP1 hSP

/- *------------------------------------*
 |                 in                 |
 *------------------------------------* -/

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fsfF_Depth_rest_rel_eqF_zero
    [HasPNfun p α] [HasFPmode]
    {P1 SP : proc p α} :
    fsfF_Depth_rest_rel P1 0 SP →
      eqFfix (P1 |. 0) SP := by
  intro h
  rw [fsfF_Depth_rest_rel_zero_iff.1 h]
  exact cspF_trans_left_eq cspF_Depth_rest_Zero cspF_SDIV_eqF

theorem cspF_fsfF_Depth_rest_rel_eqF_notin
    [HasPNfun p α] [HasFPmode]
    {P1 SP : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      fsfF_Depth_rest_rel P1 n SP →
        eqFfix (P1 |. n) SP := by
  intro hnot h
  cases n with
  | zero => exact cspF_fsfF_Depth_rest_rel_eqF_zero h
  | succ m =>
      rw [(fsfF_Depth_rest_rel_etc_iff hnot).1 h]
      exact cspF_reflex_eq_P

theorem cspF_fsfF_Depth_rest_rel_eqF_in
    [HasPNfun p α] [HasFPmode]
    {P1 : proc p α} :
    fsfF_proc P1 →
      ∀ n SP, fsfF_Depth_rest_rel P1 n SP → eqFfix (P1 |. n) SP := by
  intro hP1
  induction hP1 with
  | fsfF_proc_int hC hRf ih =>
      intro n SP hrel
      cases n with
      | zero =>
          exact cspF_fsfF_Depth_rest_rel_eqF_zero hrel
      | succ m =>
          cases hrel with
          | etc hnot =>
              exact absurd (fsfF_proc.fsfF_proc_int hC hRf) hnot
          | int_split hin hout _ _ =>
              refine cspF_trans_left_eq cspF_Depth_rest_Dist_sum ?_
              refine cspF_Rep_int_choice_cong_sum rfl (fun c hc => ?_)
              exact ih c hc (Nat.succ m) _ (hin c hc)
  | fsfF_proc_ext hPf hQ ih =>
      intro n SP hrel
      cases n with
      | zero =>
          exact cspF_fsfF_Depth_rest_rel_eqF_zero hrel
      | succ m =>
          cases hrel with
          | etc hnot =>
              exact absurd (fsfF_proc.fsfF_proc_ext hPf hQ) hnot
          | step_split hin hout _ hQ' =>
              refine cspF_trans_left_eq cspF_Depth_rest_Ext_dist ?_
              refine cspF_Ext_choice_cong ?_ ?_
              · refine cspF_trans_left_eq cspF_Depth_rest_step ?_
                refine cspF_Ext_pre_choice_cong rfl (fun a ha => ?_)
                exact ih a ha m _ (hin a ha)
              · rcases hQ with rfl | rfl | rfl
                · exact cspF_SKIP_Depth_rest
                · exact cspF_DIV_Depth_rest
                · exact cspF_STOP_Depth_rest

lemma cspF_fsfF_Depth_rest_rel_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_Depth_rest_rel P1 n SP →
      eqFfix (P1 |. n) SP := by
  intro hSP
  by_cases hP1 : fsfF_proc P1
  · exact cspF_fsfF_Depth_rest_rel_eqF_in hP1 n SP hSP
  · exact cspF_fsfF_Depth_rest_rel_eqF_notin hP1 hSP

/-
(*************************************************************
                  relation --> function
 *************************************************************)
-/

lemma fsfF_Depth_rest_in_rel
    {P1 : proc p α}
    {n : Nat} :
    fsfF_Depth_rest_rel P1 n (fsfF_Depth_rest P1 n) :=
  Classical.choose_spec (fsfF_Depth_rest_rel_exists_ax P1 n)

lemma fsfF_Depth_rest_from_rel
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_Depth_rest_rel P1 n SP ↔ fsfF_Depth_rest P1 n = SP := by
  constructor
  · intro hSP
    exact fsfF_Depth_rest_rel_unique
      (P1 := P1)
      (n := n)
      fsfF_Depth_rest_in_rel
      hSP
  · intro hSP
    subst hSP
    exact fsfF_Depth_rest_in_rel

lemma fsfF_Depth_rest_to_rel
    {P1 SP : proc p α}
    {n : Nat} :
    fsfF_Depth_rest P1 n = SP ↔ fsfF_Depth_rest_rel P1 n SP := by
  constructor
  · intro hSP
    subst hSP
    exact fsfF_Depth_rest_in_rel
  · intro hSP
    exact (fsfF_Depth_rest_from_rel (P1 := P1) (n := n) (SP := SP)).1 hSP

/-
(*************************************************************
                          function
 *************************************************************)
-/

lemma fsfF_Depth_rest_zero
    (P1 : proc p α) :
    fsfF_Depth_rest P1 0 = SDIV := by
  exact (fsfF_Depth_rest_from_rel (P1 := P1) (n := 0) (SP := SDIV)).1
    fsfF_Depth_rest_rel.zero

lemma fsfF_Depth_rest_etc
    {P1 : proc p α}
    {n : Nat} :
    ¬ fsfF_proc P1 →
      fsfF_Depth_rest P1 (Nat.succ n) = P1 |. Nat.succ n := by
  intro hP1
  exact (fsfF_Depth_rest_from_rel
      (P1 := P1)
      (n := Nat.succ n)
      (SP := P1 |. Nat.succ n)).1
    (fsfF_Depth_rest_rel.etc hP1)

lemma fsfF_Depth_rest_int
    {C1 : sets_nats α}
    {Rf1 : aset_anat α → proc p α}
    {m : Nat} :
    sumset C1 ≠ ∅ →
      (∀ c, c ∈ sumset C1 → fsfF_proc (Rf1 c)) →
        fsfF_Depth_rest (proc.Rep_int_choice C1 Rf1) (Nat.succ m) =
          proc.Rep_int_choice C1
            (fun c =>
              if c ∈ sumset C1
              then fsfF_Depth_rest (Rf1 c) (Nat.succ m)
              else proc.DIV) := by
  intro hC1 hRf1
  apply (fsfF_Depth_rest_from_rel
      (P1 := proc.Rep_int_choice C1 Rf1)
      (n := Nat.succ m)
      (SP := proc.Rep_int_choice C1
        (fun c =>
          if c ∈ sumset C1
          then fsfF_Depth_rest (Rf1 c) (Nat.succ m)
          else proc.DIV))).1
  apply fsfF_Depth_rest_rel.int
  · intro c
    by_cases hc : c ∈ sumset C1
    · simp [hc, fsfF_Depth_rest_in_rel]
    · simp [hc]
  · exact hC1
  · exact hRf1

lemma fsfF_Depth_rest_step
    {A1 : Set α}
    {Pf1 : α → proc p α}
    {Q1 : proc p α}
    {n : Nat} :
    (∀ a, a ∈ A1 → fsfF_proc (Pf1 a)) →
      (Q1 = proc.SKIP ∨ Q1 = proc.DIV ∨ Q1 = proc.STOP) →
        fsfF_Depth_rest ((proc.Ext_pre_choice A1 Pf1) [+] Q1) (Nat.succ n) =
          ((proc.Ext_pre_choice A1
            (fun a =>
              if a ∈ A1
              then fsfF_Depth_rest (Pf1 a) n
              else proc.DIV)) [+] Q1) := by
  intro hPf1 hQ1
  apply (fsfF_Depth_rest_from_rel
      (P1 := ((proc.Ext_pre_choice A1 Pf1) [+] Q1))
      (n := Nat.succ n)
      (SP := ((proc.Ext_pre_choice A1
        (fun a =>
          if a ∈ A1
          then fsfF_Depth_rest (Pf1 a) n
          else proc.DIV)) [+] Q1))).1
  apply fsfF_Depth_rest_rel.step
  · intro a
    by_cases ha : a ∈ A1
    · simp [ha, fsfF_Depth_rest_in_rel]
    · simp [ha]
  · exact hPf1
  · exact hQ1

/- The Isabelle theorem bundle `fsfF_Depth_rest` is represented by
   `fsfF_Depth_rest_etc`, `fsfF_Depth_rest_int`, and
   `fsfF_Depth_rest_step`. -/

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

lemma fsfF_Depth_rest_in
    {P1 : proc p α}
    {n : Nat} :
    fsfF_proc P1 →
      fsfF_proc (fsfF_Depth_rest P1 n) := by
  intro hP1
  exact fsfF_Depth_rest_rel_in (P1 := P1) (n := n) hP1 fsfF_Depth_rest_in_rel

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

lemma cspF_fsfF_Depth_rest_eqF
    [HasPNfun p α] [HasFPmode]
    {P1 : proc p α}
    {n : Nat} :
    eqFfix (P1 |. n) (fsfF_Depth_rest P1 n) :=
  cspF_fsfF_Depth_rest_rel_eqF fsfF_Depth_rest_in_rel

/- ****************** to add them again ****************** -/

/- Lean has no direct analogue of Isabelle's local `declare` commands. -/

end
