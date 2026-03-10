           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_op_alpha_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `(notick \/ t = <>)`.          -/
/-                                                                     -/
/-                  Isabelle's `disj_not1` has no Lean analogue here. -/

private theorem ev_mem_insert_image {a : α} {X : Set α} :
    Ev a ∈ Set.insert Tick (Ev '' X) → a ∈ X := by
  intro h
  change Ev a = Tick ∨ Ev a ∈ Ev '' X at h
  rcases h with hTick | hImg
  · cases hTick
  · rcases hImg with ⟨b, hbX, hbEq⟩
    cases hbEq
    exact hbX

/-
(*********************************************************
             Alphabetized Parallel eval
 *********************************************************)
-/

theorem in_failures_Parallel_SKIP_lm1
    {X : Set α} {Y Z : Set (event α)} :
    Y \ Set.insert Tick (Ev '' X) = Z \ Set.insert Tick (Ev '' X) →
      (Tick ∉ Z ∨ Z ⊆ Evset) →
        Z \ Y ⊆ Ev '' X := by
  intro hEq hZ e he
  rcases he with ⟨heZ, heY⟩
  have heInsert : e ∈ Set.insert Tick (Ev '' X) := by
    by_contra heNot
    have heDiffZ : e ∈ Z \ Set.insert Tick (Ev '' X) := ⟨heZ, heNot⟩
    have heDiffY : e ∈ Y \ Set.insert Tick (Ev '' X) := by
      rw [hEq]
      exact heDiffZ
    exact heY heDiffY.1
  have heNeTick : e ≠ Tick := by
    rcases hZ with hTick | hSubset
    · exact fun h => hTick (h ▸ heZ)
    · have hEvset : e ∈ Evset := hSubset heZ
      simpa [Evset] using hEvset
  rcases not_Tick_to_Ev.mp heNeTick with ⟨a, rfl⟩
  exact ⟨a, ev_mem_insert_image (X := X) heInsert, rfl⟩

theorem in_failures_Parallel_SKIP_lm2
    {X : Set α} {Y Z : Set (event α)} :
    Y \ Set.insert Tick (Ev '' X) = Z \ Set.insert Tick (Ev '' X) →
      Z \ Set.insert Tick Y ⊆ Ev '' X := by
  intro hEq e he
  rcases he with ⟨heZ, heNotY⟩
  have hNotMemY : e ∉ Y := by
    intro heY
    exact heNotY (Or.inr heY)
  have heNeTick : e ≠ Tick := by
    intro h
    exact heNotY (Or.inl h)
  have heInsert : e ∈ Set.insert Tick (Ev '' X) := by
    by_contra heNot
    have heDiffZ : e ∈ Z \ Set.insert Tick (Ev '' X) := ⟨heZ, heNot⟩
    have heDiffY : e ∈ Y \ Set.insert Tick (Ev '' X) := by
      rw [hEq]
      exact heDiffZ
    exact hNotMemY heDiffY.1
  rcases not_Tick_to_Ev.mp heNeTick with ⟨a, rfl⟩
  exact ⟨a, ev_mem_insert_image (X := X) heInsert, rfl⟩

/- (*** Para SKIP ***) -/

axiom in_failures_Parallel_SKIP
    {f : failure α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    (f :f failures (P |[X]| proc.SKIP) M) ↔
      ∃ u Y Z, f = (u, Y ∪ Z) ∧
        (u, Y) :f failures P M ∧
        sett u ∩ Ev '' X = ∅ ∧
        Z ⊆ Ev '' X

/- (*** complement ***) -/

axiom in_failures_Parallel_SKIP_comp
    {f : failure α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    (f :f failures (P |[Xᶜ]| proc.SKIP) M) ↔
      ∃ u Y Z, f = (u, Y ∪ Z) ∧
        (u, Y) :f failures P M ∧
        sett u ⊆ Set.insert Tick (Ev '' X) ∧
        Z ∩ Set.insert Tick (Ev '' X) = ∅

/- (*** Alpha_parallel_evalF ***) -/

axiom in_failures_Alpha_parallel_lm1
    {X1 X2 : Set α} {Ya Yb Za Zb : Set (event α)} :
    Tick ∉ Za →
      Za ∩ Ev '' X1 = ∅ →
      Tick ∉ Zb →
      Zb ∩ Ev '' X2 = ∅ →
      (Ya ∪ Za) \ Set.insert Tick (Ev '' (X1 ∩ X2)) =
        (Yb ∪ Zb) \ Set.insert Tick (Ev '' (X1 ∩ X2)) →
        (Ya ∪ Za ∪ (Yb ∪ Zb)) ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) =
          (Ya ∩ Set.insert Tick (Ev '' X1)) ∪
            (Yb ∩ Set.insert Tick (Ev '' X2))

axiom in_failures_Alpha_parallel_lm2
    {X : Set (event α)} {Y Z : Set (event α)} {X1 X2 : Set α} :
    X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) ⊆ Y ∪ Z →
      X =
        (X ∩ Ev '' (X1 \ X2)) ∪
          (X ∩ Y ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
            (X \ Set.insert Tick (Ev '' X1)) ∪
              ((X ∩ Ev '' (X2 \ X1)) ∪
                (X ∩ Z ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
                (X \ Set.insert Tick (Ev '' X2)))

axiom in_failures_Alpha_parallel_lm3
    {X : Set (event α)} {Y Z : Set (event α)} {X1 X2 : Set α} :
    ((X ∩ Ev '' (X1 \ X2)) ∪
      (X ∩ Y ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
      (X \ Set.insert Tick (Ev '' X1))) \
        Set.insert Tick (Ev '' (X1 ∩ X2)) =
      ((X ∩ Ev '' (X2 \ X1)) ∪
        (X ∩ Z ∩ Set.insert Tick (Ev '' (X1 ∩ X2))) ∪
        (X \ Set.insert Tick (Ev '' X2))) \
          Set.insert Tick (Ev '' (X1 ∩ X2))

/- (*** F ***) -/

axiom in_failures_Alpha_parallel
    {f : failure α} {P Q : proc p α} {X1 X2 : Set α} {M : p → domFType α} :
    (f :f failures (P |[X1,X2]| Q) M) ↔
      ∃ u X,
        f = (u, X) ∧
          ∃ Y Z,
            X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) =
              (Y ∩ Set.insert Tick (Ev '' X1)) ∪
                (Z ∩ Set.insert Tick (Ev '' X2)) ∧
            (u rest-tr X1, Y) :f failures P M ∧
            (u rest-tr X2, Z) :f failures Q M ∧
            sett u ⊆ Set.insert Tick (Ev '' (X1 ∪ X2))

/- (*** Semantics for alphabetized parallel on F ***) -/

theorem failures_Alpha_parallel
    {P Q : proc p α} {X1 X2 : Set α} {M : p → domFType α} :
    failures (P |[X1,X2]| Q) M =
      CollectF (fun f : failure α =>
        ∃ u X,
          f = (u, X) ∧
            ∃ Y Z,
              X ∩ Set.insert Tick (Ev '' (X1 ∪ X2)) =
                (Y ∩ Set.insert Tick (Ev '' X1)) ∪
                  (Z ∩ Set.insert Tick (Ev '' X2)) ∧
              (u rest-tr X1, Y) :f failures P M ∧
              (u rest-tr X2, Z) :f failures Q M ∧
              sett u ⊆ Set.insert Tick (Ev '' (X1 ∪ X2))) := by
  rw [← CollectF_open (F := failures (P |[X1,X2]| Q) M)]
  apply CollectF_eq
  intro f
  exact propext
    (in_failures_Alpha_parallel (f := f) (P := P) (Q := Q) (X1 := X1) (X2 := X2) (M := M))

end
