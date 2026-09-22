           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_nf_int
import LeanCspProver.FNF_F.FNF_F_sf

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

         1. full normalizing
         2.
         3.

 *****************************************************************)
-/

/- (*==================================================================*
 |                          fsfF --> fnfF                           |
 *==================================================================*) -/

/- Lean note:
   Isabelle declares `fnfF_fsfF_rel` with `inductive_set` (`FNF_F_nf.thy:39`);
   the port had the relation and its four introduction rules as axioms, which
   constrains nothing and leaves the uniqueness / existence facts about it
   unprovable.  It is now a real `inductive`.  The `int` and `step`
   introduction rules keep their Isabelle statements (with an
   `if _ then _ else _` premise); since a recursive occurrence under `ite` is
   not strictly positive for Lean's kernel, the constructors themselves
   (`int_split` / `step_split`) take the two implications separately, and the
   original rules are derived -- the same shape as
   `FNF_F_sf_rest.fsfF_Depth_rest_rel`. -/

inductive fnfF_fsfF_rel : Nat → proc p α → proc p α → Prop where
  | zero
      {P : proc p α} :
      fnfF_fsfF_rel 0 P NDIV
  | etc
      {n : Nat} {P : proc p α} :
      ¬ fsfF_proc P →
        fnfF_fsfF_rel (Nat.succ n) P (P |. Nat.succ n)
  | int_split
      {n : Nat}
      {C : sets_nats α}
      {SPf NPf : aset_anat α → proc p α} :
      (∀ c, c ∈ sumset C → fnfF_fsfF_rel (Nat.succ n) (SPf c) (NPf c)) →
        (∀ c, c ∉ sumset C → NPf c = proc.DIV) →
          sumset C ≠ ∅ →
            (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
              fnfF_fsfF_rel
                (Nat.succ n)
                (proc.Rep_int_choice C SPf)
                (fnfF_Rep_int_choice (Nat.succ n) C NPf)
  | step_split
      {n : Nat}
      {A : Set α}
      {SPf NPf : α → proc p α}
      {Q : proc p α} :
      (∀ a, a ∈ A → fnfF_fsfF_rel n (SPf a) (NPf a)) →
        (∀ a, a ∉ A → NPf a = proc.DIV) →
          (∀ a, a ∈ A → fsfF_proc (SPf a)) →
            (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
              fnfF_fsfF_rel
                (Nat.succ n)
                ((proc.Ext_pre_choice A SPf) [+] Q)
                (((proc.Ext_pre_choice A NPf) [+]
                    (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
                  Rep_int_choice_set
                    (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
                    (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))

namespace fnfF_fsfF_rel

theorem int
    {n : Nat}
    {C : sets_nats α}
    {SPf NPf : aset_anat α → proc p α} :
    (∀ c, if c ∈ sumset C
      then fnfF_fsfF_rel (Nat.succ n) (SPf c) (NPf c)
      else NPf c = proc.DIV) →
        sumset C ≠ ∅ →
          (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
            fnfF_fsfF_rel
              (Nat.succ n)
              (proc.Rep_int_choice C SPf)
              (fnfF_Rep_int_choice (Nat.succ n) C NPf) := by
  intro h hC hSPf
  refine int_split ?_ ?_ hC hSPf
  · intro c hc
    have hc' := h c
    rwa [if_pos hc] at hc'
  · intro c hc
    have hc' := h c
    rwa [if_neg hc] at hc'

theorem step
    {n : Nat}
    {A : Set α}
    {SPf NPf : α → proc p α}
    {Q : proc p α} :
    (∀ a, if a ∈ A
      then fnfF_fsfF_rel n (SPf a) (NPf a)
      else NPf a = proc.DIV) →
        (∀ a, a ∈ A → fsfF_proc (SPf a)) →
          (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
            fnfF_fsfF_rel
              (Nat.succ n)
              ((proc.Ext_pre_choice A SPf) [+] Q)
              (((proc.Ext_pre_choice A NPf) [+]
                  (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
                Rep_int_choice_set
                  (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
                  (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))) := by
  intro h hSPf hQ
  refine step_split ?_ ?_ hSPf hQ
  · intro a ha
    have ha' := h a
    rwa [if_pos ha] at ha'
  · intro a ha
    have ha' := h a
    rwa [if_neg ha] at ha'

end fnfF_fsfF_rel

/- (*** exists ***) -/

theorem fnfF_fsfF_rel_exists_zero
    (SP : proc p α) :
    ∃ NP : proc p α, fnfF_fsfF_rel 0 SP NP :=
  ⟨NDIV, fnfF_fsfF_rel.zero⟩

theorem fnfF_fsfF_rel_exists_notin
    {n : Nat} {P : proc p α} :
    ¬ fsfF_proc P →
      ∃ NP : proc p α, fnfF_fsfF_rel n P NP := by
  intro hP
  cases n with
  | zero =>
      exact fnfF_fsfF_rel_exists_zero P
  | succ m =>
      exact ⟨P |. Nat.succ m, fnfF_fsfF_rel.etc hP⟩

private theorem fnfF_fsfF_rel_exists_in_ind {SP : proc p α} (hSP : fsfF_proc SP) :
    ∀ n : Nat, ∃ NP : proc p α, fnfF_fsfF_rel n SP NP := by
  induction hSP with
  | @fsfF_proc_int C Rf hC hRf ih =>
      intro n
      cases n with
      | zero => exact ⟨NDIV, fnfF_fsfF_rel.zero⟩
      | succ m =>
          have hall : ∀ c, ∃ NP : proc p α,
              (c ∈ sumset C → fnfF_fsfF_rel (Nat.succ m) (Rf c) NP) ∧
                (c ∉ sumset C → NP = proc.DIV) := by
            intro c
            by_cases hc : c ∈ sumset C
            · obtain ⟨NP, hNP⟩ := ih c hc (Nat.succ m)
              exact ⟨NP, fun _ => hNP, fun h => absurd hc h⟩
            · exact ⟨proc.DIV, fun h => absurd h hc, fun _ => rfl⟩
          choose NPf h1 h2 using hall
          refine ⟨fnfF_Rep_int_choice (Nat.succ m) C NPf,
            fnfF_fsfF_rel.int (fun c => ?_) hC hRf⟩
          by_cases hc : c ∈ sumset C
          · rw [if_pos hc]; exact h1 c hc
          · rw [if_neg hc]; exact h2 c hc
  | @fsfF_proc_ext A Pf Q hPf hQ ih =>
      intro n
      cases n with
      | zero => exact ⟨NDIV, fnfF_fsfF_rel.zero⟩
      | succ m =>
          have hall : ∀ a, ∃ NP : proc p α,
              (a ∈ A → fnfF_fsfF_rel m (Pf a) NP) ∧ (a ∉ A → NP = proc.DIV) := by
            intro a
            by_cases ha : a ∈ A
            · obtain ⟨NP, hNP⟩ := ih a ha m
              exact ⟨NP, fun _ => hNP, fun h => absurd ha h⟩
            · exact ⟨proc.DIV, fun h => absurd h ha, fun _ => rfl⟩
          choose NPf h1 h2 using hall
          refine ⟨_, fnfF_fsfF_rel.step (NPf := NPf) (fun a => ?_) hPf hQ⟩
          by_cases ha : a ∈ A
          · rw [if_pos ha]; exact h1 a ha
          · rw [if_neg ha]; exact h2 a ha

theorem fnfF_fsfF_rel_exists_in
    {SP : proc p α} :
    fsfF_proc SP → ∀ n : Nat, ∃ NP : proc p α, fnfF_fsfF_rel n SP NP :=
  fnfF_fsfF_rel_exists_in_ind

/- *-----------------------*
 |        exists         |
 *-----------------------* -/

theorem fnfF_fsfF_rel_exists
    (n : Nat) (SP : proc p α) :
    ∃ NP : proc p α, fnfF_fsfF_rel n SP NP := by
  by_cases hSP : fsfF_proc SP
  · exact fnfF_fsfF_rel_exists_in hSP n
  · exact fnfF_fsfF_rel_exists_notin hSP

/- *-----------------------*
 |    uniquely exists    |
 *-----------------------* -/


/- (*** function ***) -/

def fnfF_fsfF
    (n : Nat) (SP : proc p α) : proc p α :=
  Classical.choose (fnfF_fsfF_rel_exists n SP)

def fnfF [HasPNfun p α] :
    Nat → proc p α → proc p α :=
  fun n P => fnfF_fsfF n (fsfF P)

theorem fnfF_def [HasPNfun p α] :
    fnfF (p := p) (α := α) =
      (fun n P => fnfF_fsfF n (fsfF P)) :=
  rfl

def XfnfF [HasPNfun p α] :
    proc p α → proc p α :=
  fun P => Rep_int_choice_nat Set.univ (fun n => fnfF n P)

theorem XfnfF_def [HasPNfun p α] :
    XfnfF (p := p) (α := α) =
      (fun P => Rep_int_choice_nat Set.univ (fun n => fnfF n P)) :=
  rfl

/- Lean note:
   Isabelle's syntax/translation for `!nat n .. (fnfF n P)` is represented
   directly by `Rep_int_choice_nat Set.univ (fun n => fnfF n P)`. -/

/-
(****************************************************************
 |                      uniquness                               |
 ****************************************************************)
-/

private theorem fnfF_fsfF_rel_unique_ind {n : Nat} {SP NP1 : proc p α}
    (h1 : fnfF_fsfF_rel n SP NP1) :
    ∀ NP2 : proc p α, fnfF_fsfF_rel n SP NP2 → NP1 = NP2 := by
  induction h1 with
  | zero =>
      intro NP2 h2
      cases h2
      rfl
  | etc hP =>
      intro NP2 h2
      cases h2 with
      | etc _ => rfl
      | int_split hrel2 hdiv2 hC2 hfsf2 =>
          exact absurd (fsfF_procI (Or.inl ⟨_, _, hC2, rfl, hfsf2⟩)) hP
      | step_split hrel2 hdiv2 hfsf2 hQ2 =>
          exact absurd (fsfF_procI (Or.inr ⟨_, _, _, rfl, hfsf2, hQ2⟩)) hP
  | @int_split m C SPf NPf hrel hdiv hC hfsf ih =>
      intro NP2 h2
      cases h2 with
      | etc hP => exact absurd (fsfF_procI (Or.inl ⟨_, _, hC, rfl, hfsf⟩)) hP
      | @int_split _ _ _ NPf2 hrel2 hdiv2 hC2 hfsf2 =>
          have hNPf : NPf = NPf2 := by
            funext c
            by_cases hc : c ∈ sumset C
            · exact ih c hc _ (hrel2 c hc)
            · rw [hdiv c hc, hdiv2 c hc]
          rw [hNPf]
  | @step_split m A SPf NPf Q hrel hdiv hfsf hQ ih =>
      intro NP2 h2
      cases h2 with
      | etc hP => exact absurd (fsfF_procI (Or.inr ⟨_, _, _, rfl, hfsf, hQ⟩)) hP
      | @step_split _ _ _ NPf2 _ hrel2 hdiv2 hfsf2 hQ2 =>
          have hNPf : NPf = NPf2 := by
            funext a
            by_cases ha : a ∈ A
            · exact ih a ha _ (hrel2 a ha)
            · rw [hdiv a ha, hdiv2 a ha]
          rw [hNPf]

theorem fnfF_fsfF_rel_unique {n : Nat} {SP NP1 NP2 : proc p α} :
    fnfF_fsfF_rel n SP NP1 → fnfF_fsfF_rel n SP NP2 → NP1 = NP2 :=
  fun h1 h2 => fnfF_fsfF_rel_unique_ind h1 NP2 h2

lemma fnfF_fsfF_rel_unique_in_lm
    {n : Nat} {SP NP1 : proc p α} :
    fnfF_fsfF_rel n SP NP1 →
      ∀ NP2 : proc p α, fnfF_fsfF_rel n SP NP2 → NP1 = NP2 := by
  intro hNP1 NP2 hNP2
  exact fnfF_fsfF_rel_unique (n := n) (SP := SP) hNP1 hNP2

/- *-----------------------*
 |        unique         |
 *-----------------------* -/

theorem fnfF_fsfF_rel_EX1
    (n : Nat) (SP : proc p α) :
    (∃ NP : proc p α, fnfF_fsfF_rel n SP NP) ↔
      ∃! NP : proc p α, fnfF_fsfF_rel n SP NP := by
  constructor
  · intro h
    rcases h with ⟨NP, hNP⟩
    exact ⟨NP, hNP, fun NP2 hNP2 =>
      (fnfF_fsfF_rel_unique (n := n) (SP := SP) (NP1 := NP) (NP2 := NP2) hNP hNP2).symm⟩
  · intro h
    exact h.exists

/- *------------------------------------------------------------*
 |                      fnfF_fsfF_rel (iff)                   |
 *------------------------------------------------------------* -/

/- zero -/

theorem fnfF_fsfF_rel_zero_iff {SP NP : proc p α} :
    fnfF_fsfF_rel 0 SP NP ↔ NP = NDIV := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact fnfF_fsfF_rel.zero

/- etc -/

theorem fnfF_fsfF_rel_etc_iff {n : Nat} {P NP : proc p α} :
    ¬ fsfF_proc P →
      (fnfF_fsfF_rel (Nat.succ n) P NP ↔ NP = P |. Nat.succ n) := by
  intro hP
  constructor
  · intro h
    cases h with
    | etc _ => rfl
    | int_split hrel hdiv hC hfsf =>
        exact absurd (fsfF_procI (Or.inl ⟨_, _, hC, rfl, hfsf⟩)) hP
    | step_split hrel hdiv hfsf hQ =>
        exact absurd (fsfF_procI (Or.inr ⟨_, _, _, rfl, hfsf, hQ⟩)) hP
  · rintro rfl
    exact fnfF_fsfF_rel.etc hP

/- int -/

theorem fnfF_fsfF_rel_int_iff
    {n : Nat}
    {C : sets_nats α}
    {SPf NPf : aset_anat α → proc p α}
    {NP : proc p α} :
    (∀ c, if c ∈ sumset C
      then fnfF_fsfF_rel (Nat.succ n) (SPf c) (NPf c)
      else NPf c = proc.DIV) →
        sumset C ≠ ∅ →
          (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
            (fnfF_fsfF_rel (Nat.succ n) (proc.Rep_int_choice C SPf) NP ↔
              NP = fnfF_Rep_int_choice (Nat.succ n) C NPf) := by
  intro h hC hfsf
  have hrel := fnfF_fsfF_rel.int h hC hfsf
  constructor
  · intro h2
    exact fnfF_fsfF_rel_unique h2 hrel
  · rintro rfl
    exact hrel

/- step -/

theorem fnfF_fsfF_rel_step_iff
    {n : Nat}
    {A : Set α}
    {SPf NPf : α → proc p α}
    {Q NP : proc p α} :
    (∀ a, if a ∈ A
      then fnfF_fsfF_rel n (SPf a) (NPf a)
      else NPf a = proc.DIV) →
        (∀ a, a ∈ A → fsfF_proc (SPf a)) →
          (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
            (fnfF_fsfF_rel (Nat.succ n) ((proc.Ext_pre_choice A SPf) [+] Q) NP ↔
              NP =
                ((((proc.Ext_pre_choice A NPf) [+]
                    (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
                  Rep_int_choice_set
                    (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
                    (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) := by
  intro h hfsf hQ
  have hrel := fnfF_fsfF_rel.step h hfsf hQ
  constructor
  · intro h2
    exact fnfF_fsfF_rel_unique h2 hrel
  · rintro rfl
    exact hrel

/-
(****************************************************************
 |                      existency                               |
 ****************************************************************)
-/

theorem fnfF_fsfF_rel_unique_exists
    (n : Nat) (SP : proc p α) :
    ∃! NP : proc p α, fnfF_fsfF_rel n SP NP :=
  (fnfF_fsfF_rel_EX1 n SP).1 (fnfF_fsfF_rel_exists n SP)

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fnfF_fsfF_rel_zero_in {SP NP : proc p α} :
    fnfF_fsfF_rel 0 SP NP → fnfF_proc NP := by
  intro h
  rw [fnfF_fsfF_rel_zero_iff.mp h]
  exact fnfF_NDIV

private theorem cond_step (A : Set α) (Q : proc p α) :
    fnfF_set_condition A (if Q = proc.STOP then ({A} : Set (Set α)) else ∅) := by
  by_cases hs : Q = proc.STOP
  · rw [if_pos hs]
    intro Y ⟨⟨Y0, hY0, hsub⟩, hYA⟩
    rw [Set.mem_singleton_iff] at hY0 ⊢
    subst hY0
    refine Set.Subset.antisymm ?_ hsub
    intro a ha
    rcases hYA ha with h | ⟨Z, hZ, hZa⟩
    · exact h
    · rw [Set.mem_singleton_iff] at hZ
      exact hZ ▸ hZa
  · rw [if_neg hs]
    rintro Y ⟨⟨Y0, hY0, -⟩, -⟩
    exact absurd hY0 (by simp)

private theorem union_step (A : Set α) (Q : proc p α) :
    Set.sUnion (if Q = proc.STOP then ({A} : Set (Set α)) else ∅) ⊆ A := by
  by_cases hs : Q = proc.STOP
  · rw [if_pos hs]
    rintro a ⟨Z, hZ, hZa⟩
    rw [Set.mem_singleton_iff] at hZ
    exact hZ ▸ hZa
  · rw [if_neg hs]
    simp

private theorem Q_step (Q : proc p α) :
    (if Q = proc.SKIP then (proc.SKIP : proc p α) else proc.DIV) = proc.SKIP ∨
      (if Q = proc.SKIP then (proc.SKIP : proc p α) else proc.DIV) = proc.DIV := by
  by_cases hs : Q = proc.SKIP
  · rw [if_pos hs]; exact Or.inl rfl
  · rw [if_neg hs]; exact Or.inr rfl

private theorem fnfF_fsfF_rel_in_ind {SP : proc p α} (hSP : fsfF_proc SP) :
    ∀ (n : Nat) (NP : proc p α), fnfF_fsfF_rel n SP NP → fnfF_proc NP := by
  induction hSP with
  | @fsfF_proc_int C Rf hC hRf ih =>
      intro n NP h
      cases n with
      | zero => exact fnfF_fsfF_rel_zero_in h
      | succ m =>
          cases h with
          | @etc _ _ hP => exact absurd (fsfF_proc.fsfF_proc_int hC hRf) hP
          | @int_split _ _ _ NPf hrel hdiv hC2 hfsf =>
              exact fnfF_Rep_int_choice_in (fun c hc => ih c hc _ _ (hrel c hc))
  | @fsfF_proc_ext A Pf Q hPf hQ ih =>
      intro n NP h
      cases n with
      | zero => exact fnfF_fsfF_rel_zero_in h
      | succ m =>
          cases h with
          | @etc _ _ hP => exact absurd (fsfF_proc.fsfF_proc_ext hPf hQ) hP
          | @step_split _ _ _ NPf _ hrel hdiv hfsf hQ2 =>
              exact fnfF_proc.fnfF_proc_rule
                (fun a ha => ih a ha _ _ (hrel a ha)) hdiv
                (cond_step A Q) (union_step A Q) (Q_step Q)

theorem fnfF_fsfF_rel_in
    {SP NP : proc p α} {n : Nat} :
    fsfF_proc SP → fnfF_fsfF_rel n SP NP → fnfF_proc NP :=
  fun hSP h => fnfF_fsfF_rel_in_ind hSP n NP h

lemma fnfF_fsfF_rel_in_lm
    {SP : proc p α} :
    fsfF_proc SP →
      ∀ n : Nat, ∀ NP : proc p α, fnfF_fsfF_rel n SP NP → fnfF_proc NP := by
  intro hSP n NP hNP
  exact fnfF_fsfF_rel_in (n := n) (SP := SP) (NP := NP) hSP hNP

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fnfF_fsfF_rel_eqF_zero
    [HasPNfun p α] [HasFPmode]
    {P NP : proc p α} :
    fnfF_fsfF_rel 0 P NP → eqFfix (P |. 0) NP := by
  intro h
  rw [fnfF_fsfF_rel_zero_iff.mp h]
  exact cspF_trans_left_eq cspF_Depth_rest_Zero cspF_NDIV_eqF

theorem cspF_fnfF_fsfF_rel_eqF_notin
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {P NP : proc p α} :
    ¬ fsfF_proc P → fnfF_fsfF_rel n P NP → eqFfix (P |. n) NP := by
  intro hP h
  cases n with
  | zero => exact cspF_fnfF_fsfF_rel_eqF_zero h
  | succ m =>
      rw [(fnfF_fsfF_rel_etc_iff hP).mp h]
      exact cspF_reflex_eq_P

axiom cspF_fnfF_fsfF_rel_eqF_in
    [HasPNfun p α] [HasFPmode]
    {SP : proc p α} :
    fsfF_proc SP →
      ∀ n : Nat, ∀ NP : proc p α, fnfF_fsfF_rel n SP NP → eqFfix (SP |. n) NP

theorem cspF_fnfF_fsfF_rel_eqF
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {SP NP : proc p α} :
    fnfF_fsfF_rel n SP NP →
      eqFfix (SP |. n) NP := by
  intro hNP
  by_cases hSP : fsfF_proc SP
  · exact cspF_fnfF_fsfF_rel_eqF_in (SP := SP) hSP n NP hNP
  · exact cspF_fnfF_fsfF_rel_eqF_notin (n := n) (P := SP) (NP := NP) hSP hNP

/-
(*************************************************************
                  relation --> function
 *************************************************************)
-/

theorem fnfF_fsfF_in_rel
    {n : Nat} {SP : proc p α} :
    fnfF_fsfF_rel n SP (fnfF_fsfF n SP) :=
  Classical.choose_spec (fnfF_fsfF_rel_exists n SP)

theorem fnfF_fsfF_from_rel
    {n : Nat} {SP NP : proc p α} :
    fnfF_fsfF_rel n SP NP ↔ fnfF_fsfF n SP = NP := by
  constructor
  · intro hNP
    exact fnfF_fsfF_rel_unique (n := n) (SP := SP)
      (NP1 := fnfF_fsfF n SP) (NP2 := NP) fnfF_fsfF_in_rel hNP
  · intro hNP
    subst hNP
    exact fnfF_fsfF_in_rel

theorem fnfF_fsfF_to_rel
    {n : Nat} {SP NP : proc p α} :
    fnfF_fsfF n SP = NP ↔ fnfF_fsfF_rel n SP NP := by
  constructor
  · intro hNP
    subst hNP
    exact fnfF_fsfF_in_rel (n := n) (SP := SP)
  · intro hNP
    exact (fnfF_fsfF_from_rel (n := n) (SP := SP) (NP := NP)).1 hNP

/-
(*************************************************************
                          function
 *************************************************************)
-/

theorem fnfF_fsfF_zero
    (SP : proc p α) :
    fnfF_fsfF 0 SP = NDIV :=
  (fnfF_fsfF_from_rel (n := 0) (SP := SP) (NP := NDIV)).1 fnfF_fsfF_rel.zero

theorem fnfF_fsfF_etc
    {n : Nat} {P : proc p α} :
    ¬ fsfF_proc P →
      fnfF_fsfF (Nat.succ n) P = P |. Nat.succ n := by
  intro hP
  exact (fnfF_fsfF_from_rel
      (n := Nat.succ n)
      (SP := P)
      (NP := P |. Nat.succ n)).1
    (fnfF_fsfF_rel.etc hP)

theorem fnfF_fsfF_int
    {n : Nat}
    {C : sets_nats α}
    {SPf : aset_anat α → proc p α} :
    sumset C ≠ ∅ →
      (∀ c, c ∈ sumset C → fsfF_proc (SPf c)) →
        fnfF_fsfF (Nat.succ n) (proc.Rep_int_choice C SPf) =
          fnfF_Rep_int_choice (Nat.succ n) C
            (fun c =>
              if c ∈ sumset C
              then fnfF_fsfF (Nat.succ n) (SPf c)
              else proc.DIV) := by
  intro hC hfsf
  refine fnfF_fsfF_from_rel.1 (fnfF_fsfF_rel.int (fun c => ?_) hC hfsf)
  by_cases hc : c ∈ sumset C
  · rw [if_pos hc, if_pos hc]
    exact fnfF_fsfF_in_rel
  · rw [if_neg hc, if_neg hc]

theorem fnfF_fsfF_step
    {n : Nat}
    {A : Set α}
    {SPf : α → proc p α}
    {Q : proc p α} :
    (∀ a, a ∈ A → fsfF_proc (SPf a)) →
      (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
        fnfF_fsfF (Nat.succ n) ((proc.Ext_pre_choice A SPf) [+] Q) =
          (((proc.Ext_pre_choice A
              (fun a =>
                if a ∈ A then fnfF_fsfF n (SPf a) else proc.DIV)) [+]
            (if Q = proc.SKIP then proc.SKIP else proc.DIV)) |~|
            Rep_int_choice_set
              (if Q = proc.STOP then ({A} : Set (Set α)) else ∅)
              (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))) := by
  intro hfsf hQ
  refine fnfF_fsfF_from_rel.1 (fnfF_fsfF_rel.step (fun a => ?_) hfsf hQ)
  by_cases ha : a ∈ A
  · rw [if_pos ha, if_pos ha]
    exact fnfF_fsfF_in_rel
  · rw [if_neg ha, if_neg ha]

/- The Isabelle theorem bundle `fnfF_fsfF` is represented by
   `fnfF_fsfF_etc`, `fnfF_fsfF_int`, and `fnfF_fsfF_step`. -/

/- *------------------------------------------------------------*
 |                        in fsfF_proc                        |
 *------------------------------------------------------------* -/

theorem fnfF_fsfF_in
    {n : Nat} {SP : proc p α} :
    fsfF_proc SP →
      fnfF_proc (fnfF_fsfF n SP) := by
  intro hSP
  exact fnfF_fsfF_rel_in (n := n) (SP := SP) (NP := fnfF_fsfF n SP)
    hSP (fnfF_fsfF_in_rel (n := n) (SP := SP))

/- *------------------------------------------------------------*
 |             syntactical transformation to fsfF             |
 *------------------------------------------------------------* -/

theorem cspF_fnfF_fsfF_eqF
    [HasPNfun p α] [HasFPmode]
    {n : Nat} {SP : proc p α} :
    eqFfix (SP |. n) (fnfF_fsfF n SP) :=
  cspF_fnfF_fsfF_rel_eqF (n := n) (SP := SP) (NP := fnfF_fsfF n SP)
    (fnfF_fsfF_in_rel (n := n) (SP := SP))

/- *===============================================================*
   theorem --- fnfF P is a (restricted) full normal form ---
 *===============================================================* -/

theorem fnfF_in [HasPNfun p α]
    {n : Nat} {P : proc p α} :
    fnfF_proc (fnfF n P) := by
  rw [fnfF_def]
  exact fnfF_fsfF_in (n := n) (SP := fsfF P) (fsfF_in (P := P))

/- *===============================================================*
        theorem --- fnfF P is equal to P based on F ---
 *===============================================================* -/

axiom cspF_fnfF_eqF [HasPNfun p α] [HasFPmode]
    {n : Nat} {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix (P |. n) (fnfF n P)

/- *------------------------*
 |     auxiliary laws     |
 *------------------------* -/

axiom cspF_fnfF_eqF_Depth_rest [HasPNfun p α] [HasFPmode]
    {n : Nat} {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix ((fnfF n P) |. n) (fnfF n P)

/- *===============================================================*
          theorem --- XfnfF P is a full normal form ---
 *===============================================================* -/

axiom XfnfF_in [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      XfnfF P ∈ XfnfF_proc (p := p) (α := α)

/- *===============================================================*
          theorem --- XfnfF P is equal to P based on F ---
 *===============================================================* -/

axiom cspF_XfnfF_eqF [HasPNfun p α] [HasFPmode]
    {P : proc p α} :
    (FPmode = CPOmode ∨ FPmode = MIXmode) →
      eqFfix P (XfnfF P)

/- (****************** to add them again ******************) -/

/- Lean has no direct analogue of Isabelle's local `declare if_split [split]`
   or `declare disj_not1 [simp]` commands. -/

end
