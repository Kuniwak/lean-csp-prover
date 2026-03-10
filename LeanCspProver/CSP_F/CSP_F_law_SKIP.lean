           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_T.CSP_T_law_SKIP

open Function
open SumType
open event

noncomputable section

/-
(*****************************************************************

         1. SKIP |[X]| SKIP
         2. SKIP |[X]| P
         3. P |[X]| SKIP
         4. SKIP -- X
         5. SKIP [[r]]
         6. SKIP ;; P
         7. P ;; SKIP
         8. SKIP |. n

 *****************************************************************)
-/

/-
(*********************************************************
                    SKIP |[X]| SKIP
 *********************************************************)
-/

axiom cspF_Parallel_term
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| proc.SKIP)) M1 M2 (proc.SKIP : proc q α)

/-
(*********************************************************
                      SKIP |[X]| P
 *********************************************************)
-/

theorem cspF_Parallel_preterm_l_set1
    {X Y : Set α} {Ya Z : Set (event α)}
    (hEq : Ya \ insert Tick (Ev '' X) = Z \ insert Tick (Ev '' X))
    (hDisj : Ev '' Y ∩ Z = ∅) :
    Ev '' (Y \ X) ∩ (Ya ∪ Z) = ∅ := by
  ext e
  constructor
  · intro he
    exfalso
    rcases he with ⟨heYX, heUnion⟩
    rcases heYX with ⟨a, haYX, rfl⟩
    rcases haYX with ⟨haY, haNotX⟩
    have hNotMem : Ev a ∉ insert Tick (Ev '' X) := by
      intro hMem
      rcases hMem with hTick | hEvX
      · cases hTick
      · rcases hEvX with ⟨b, hbX, hbEq⟩
        cases hbEq
        exact haNotX hbX
    have hNotDisj : Ev a ∉ Z := by
      intro haZ
      have hInter : Ev a ∈ Ev '' Y ∩ Z := ⟨⟨a, haY, rfl⟩, haZ⟩
      simpa [hDisj] using hInter
    rcases heUnion with haYa | haZ
    · have hDiff : Ev a ∈ Ya \ insert Tick (Ev '' X) := ⟨haYa, hNotMem⟩
      exact hNotDisj ((hEq ▸ hDiff).1)
    · exact hNotDisj haZ
  · intro he
    cases he

axiom cspF_Parallel_preterm_l
    {X Y : Set α} {Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Qf)) M M
      (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Qf x)))

theorem cspF_Parallel_preterm_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
      (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) := by
  have h₁ :
      eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
        (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) :=
    cspF_Parallel_commut
  have h₂ :
      eqF (((proc.SKIP : proc p α) |[X]| proc.Ext_pre_choice Y Pf)) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) :=
    cspF_Parallel_preterm_l
  have h₃ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_Parallel_preterm` is represented by
   `cspF_Parallel_preterm_l` and `cspF_Parallel_preterm_r`. -/

/-
(*********************************************************
                      SKIP and Parallel
 *********************************************************)
-/

/- p.288 -/

axiom cspF_SKIP_Parallel_Ext_choice_SKIP_l
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
        proc.SKIP))

theorem cspF_SKIP_Parallel_Ext_choice_SKIP_r
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.SKIP))) M M
      (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+]
        proc.SKIP)) := by
  have h₁ :
      eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] proc.SKIP))) M M
        ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF ((((proc.Ext_pre_choice Y Pf) [+] proc.SKIP) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
          proc.SKIP)) :=
    cspF_SKIP_Parallel_Ext_choice_SKIP_l
  have h₃₁ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  have h₃ :
      eqF
        (((proc.Ext_pre_choice (Y \ X) (fun x => (Pf x |[X]| (proc.SKIP : proc p α)))) [+]
          proc.SKIP))
        M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => ((proc.SKIP : proc p α) |[X]| Pf x))) [+]
          proc.SKIP)) := by
    exact cspF_Ext_choice_cong h₃₁ cspF_reflex_eq_SKIP
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_SKIP_Parallel_Ext_choice_SKIP` is
   represented by `cspF_SKIP_Parallel_Ext_choice_SKIP_l` and
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`. -/

/-
(*********************************************************
                      SKIP -- X
 *********************************************************)
-/

theorem cspF_SKIP_Hiding_Id
    {X : Set α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.Hiding (proc.SKIP : proc p α) X) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_SKIP_Hiding_Id, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_Hiding] at hs
    rcases hs with ⟨t, Z, hEq, htZ⟩
    rw [in_failures_SKIP] at htZ
    rw [in_failures_SKIP]
    rcases htZ with ⟨W, hPair, hSub⟩ | ⟨W, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨htEq, hWEq⟩
      subst t
      subst W
      rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      refine Or.inl ⟨Z, by simp, ?_⟩
      intro e he
      exact hSub (Or.inr he)
    · rcases Prod.mk.inj hPair with ⟨htEq, hWEq⟩
      subst t
      subst W
      rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      exact Or.inr ⟨Z, by simp⟩
  · rw [subsetF_iff]
    intro s Y hs
    rw [in_failures_SKIP] at hs
    rw [in_failures_Hiding]
    rcases hs with ⟨Z, hPair, hSub⟩ | ⟨Z, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      refine ⟨<>, Z, by simp, ?_⟩
      rw [in_failures_SKIP]
      refine Or.inl ⟨Ev '' X ∪ Z, rfl, ?_⟩
      intro e he
      rcases he with he | he
      · rcases he with ⟨a, haX, rfl⟩
        simp [Evset]
      · exact hSub he
    · rcases Prod.mk.inj hPair with ⟨hsEq, hYEq⟩
      subst s
      subst Y
      refine ⟨Abs_trace [Tick], Z, by simp, ?_⟩
      rw [in_failures_SKIP]
      exact Or.inr ⟨Ev '' X ∪ Z, rfl⟩

/-
(*********************************************************
                      SKIP and Hiding
 *********************************************************)
-/

/- p.288 version
  "((? :Y -> Pf) [+] SKIP) -- X =F[M,M]
       IF (Y Int X = {}) THEN ((? x:Y -> (Pf x -- X)) [+] SKIP)
                         ELSE (((? x:(Y-X) -> (Pf x -- X)) [+] SKIP)
                               |~| (! x:(Y Int X) .. (Pf x -- X)))"
-/

axiom cspF_SKIP_Hiding_step [Inhabited α]
    {X Y : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Hiding ((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) X) M M
      ((((proc.Ext_pre_choice (Y \ X) (fun x => proc.Hiding (Pf x) X)) [+] proc.SKIP) |~|
        Rep_int_choice_com (Y ∩ X) (fun x => proc.Hiding (Pf x) X)))

/-
(*********************************************************
                      SKIP [[r]]
 *********************************************************)
-/

theorem cspF_SKIP_Renaming_Id
    {r : Set (α × α)} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α)[[r]])) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_SKIP_Renaming_Id, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Renaming] at hs
    rcases hs with ⟨t, u, Y, hEq, hRen, htY⟩
    rw [in_failures_SKIP] at htY
    rw [in_failures_SKIP]
    rcases htY with ⟨Z, hPair, hSub⟩ | ⟨Z, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨htEq, hZEq⟩
      subst t
      subst Z
      have huNil : u = <> := (ren_tr_nil1 (r := r) (s := u)).1 hRen
      rcases Prod.mk.inj hEq with ⟨hsEq, hXEq⟩
      subst s
      subst X
      subst u
      refine Or.inl ⟨Y, rfl, ?_⟩
      exact (ren_inv_no_Tick (r := r) (X := Y)).1 hSub
    · rcases Prod.mk.inj hPair with ⟨htEq, hZEq⟩
      subst t
      subst Z
      have huTick : u = Abs_trace [Tick] := (ren_tr_Tick1 (r := r) (s := u)).1 hRen
      rcases Prod.mk.inj hEq with ⟨hsEq, hXEq⟩
      subst s
      subst X
      subst u
      exact Or.inr ⟨Y, rfl⟩
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_SKIP] at hs
    rw [in_failures_Renaming]
    rcases hs with ⟨Y, hPair, hSub⟩ | ⟨Y, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨<>, <>, Y, rfl, ren_tr_nil, ?_⟩
      rw [in_failures_SKIP]
      refine Or.inl ⟨[[r]]inv Y, rfl, ?_⟩
      exact Set.Subset.trans (ren_inv_sub hSub) (ren_inv_sub_Evset (r := r))
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨Abs_trace [Tick], Abs_trace [Tick], Y, rfl, ren_tr_Tick, ?_⟩
      rw [in_failures_SKIP]
      exact Or.inr ⟨[[r]]inv Y, rfl⟩

/-
(*********************************************************
                       SKIP ;; P
 *********************************************************)
-/

axiom cspF_Seq_compo_unit_l
    {P : proc p α} {M : p → domFType α} :
    eqF (((proc.SKIP : proc p α) ;; P)) M M P

/-
(*********************************************************
                       P ;; SKIP
 *********************************************************)
-/

axiom cspF_Seq_compo_unit_r
    {P : proc p α} {M : p → domFType α} :
    eqF ((P ;; (proc.SKIP : proc p α))) M M P

/- The Isabelle theorem bundle `cspF_Seq_compo_unit` is represented by
   `cspF_Seq_compo_unit_l` and `cspF_Seq_compo_unit_r`. -/

/-
(*********************************************************
               SKIP and Sequential composition
 *********************************************************)
-/

/- p.141 -/

axiom cspF_SKIP_Seq_compo_step
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice X Pf) [> (proc.SKIP : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> Q))

/-
(*********************************************************
                      SKIP |. n
 *********************************************************)
-/

theorem cspF_SKIP_Depth_rest
    {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.SKIP : proc p α) |. Nat.succ n)) M1 M2 (proc.SKIP : proc q α) := by
  rw [cspF_cspT_eqF_semantics]
  refine ⟨cspT_SKIP_Depth_rest, ?_⟩
  apply le_antisymm
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_Depth_rest] at hs
    rcases hs with ⟨t, Y, hEq, htY, hRest⟩
    simpa [hEq] using htY
  · rw [subsetF_iff]
    intro s X hs
    rw [in_failures_SKIP] at hs
    rw [in_failures_Depth_rest]
    rcases hs with ⟨Y, hPair, hSub⟩ | ⟨Y, hPair⟩
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨<>, Y, rfl, ?_, Or.inl (by simp)⟩
      exact (in_failures_SKIP (f := ((<>, Y) : failure α)) (M := M1)).2 (Or.inl ⟨Y, rfl, hSub⟩)
    · rcases Prod.mk.inj hPair with ⟨hsEq, hXEq⟩
      subst s
      subst X
      refine ⟨Abs_trace [Tick], Y, rfl, ?_, ?_⟩
      · exact (in_failures_SKIP (f := ((Abs_trace [Tick], Y) : failure α)) (M := M1)).2
          (Or.inr ⟨Y, rfl⟩)
      · by_cases hPos : 0 < n
        · exact Or.inl (by simpa using Nat.succ_lt_succ hPos)
        · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hPos
          subst n
          refine Or.inr ?_
          refine ⟨by simp, ?_⟩
          refine ⟨<>, by simp [tickTrace, noTick]⟩

/- The Isabelle theorem bundle `cspF_SKIP` is represented by
   `cspF_Parallel_term`, `cspF_Parallel_preterm_l`,
   `cspF_Parallel_preterm_r`, `cspF_SKIP_Parallel_Ext_choice_SKIP_l`,
   `cspF_SKIP_Parallel_Ext_choice_SKIP_r`, `cspF_SKIP_Hiding_Id`,
   `cspF_SKIP_Hiding_step`, `cspF_SKIP_Renaming_Id`,
   `cspF_Seq_compo_unit_l`, `cspF_Seq_compo_unit_r`,
   `cspF_SKIP_Seq_compo_step`, and `cspF_SKIP_Depth_rest`. -/

end
