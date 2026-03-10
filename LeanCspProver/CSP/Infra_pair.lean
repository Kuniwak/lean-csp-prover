           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_order

/-
(*****************************************************
                         Pair
 *****************************************************)
-/

def pair_fun (f : α → β) (g : α → γ) : α → (β × γ) :=
  fun x => (f x, g x)

infixr:52 " ** " => pair_fun

/- *** lemmas *** -/

@[simp]
theorem fst_pair_fun {f : α → β} {g : α → γ} : Prod.fst ∘ (f ** g) = f := by
  funext x
  rfl

@[simp]
theorem snd_pair_fun {f : α → β} {g : α → γ} : Prod.snd ∘ (f ** g) = g := by
  funext x
  rfl

theorem pair_eq_decompo {xc yc : α × β} :
    xc = yc ↔ (Prod.fst xc = Prod.fst yc ∧ Prod.snd xc = Prod.snd yc) := by
  cases xc
  cases yc
  simp

theorem pair_neq_decompo {xc yc : α × β} :
    xc ≠ yc ↔ (Prod.fst xc ≠ Prod.fst yc ∨ Prod.snd xc ≠ Prod.snd yc) := by
  constructor
  · intro hneq
    by_contra h
    apply hneq
    apply pair_eq_decompo.mpr
    push_neg at h
    exact h
  · intro hneq hEq
    rcases pair_eq_decompo.mp hEq with ⟨hfst, hsnd⟩
    rcases hneq with hfst' | hsnd'
    · exact hfst' hfst
    · exact hsnd' hsnd

/-
(*******************************
         <= in pair
 *******************************)

Lean already provides the pointwise order on products, so we only record the
corresponding decomposition lemmas here.
-/

theorem order_pair_def {xc yc : α × β} [LE α] [LE β] :
    xc <= yc ↔ (Prod.fst xc <= Prod.fst yc ∧ Prod.snd xc <= Prod.snd yc) :=
  Iff.rfl

theorem order_less_pair_def {xc yc : α × β} [PartialOrder α] [PartialOrder β] :
    xc < yc ↔
      (Prod.fst xc <= Prod.fst yc ∧ Prod.snd xc <= Prod.snd yc ∧
        (Prod.fst xc ≠ Prod.fst yc ∨ Prod.snd xc ≠ Prod.snd yc)) := by
  constructor
  · intro h
    rcases Prod.lt_iff.mp h with hxy | hxy
    · exact ⟨hxy.1.le, hxy.2, Or.inl (ne_of_lt hxy.1)⟩
    · exact ⟨hxy.1, hxy.2.le, Or.inr (ne_of_lt hxy.2)⟩
  · rintro ⟨hfst, hsnd, hneq⟩
    rcases hneq with hneq | hneq
    · exact Prod.lt_iff.mpr (Or.inl ⟨lt_of_le_of_ne hfst hneq, hsnd⟩)
    · exact Prod.lt_iff.mpr (Or.inr ⟨hfst, lt_of_le_of_ne hsnd hneq⟩)

/-
(*** LUB is decomposed for * ***)

(* only if *)
-/

theorem pair_LUB_decompo_fst_only_if {xc : α × β} {Xc : Set (α × β)}
    [PartialOrder α] [PartialOrder β] :
    isLUB xc Xc → isLUB (Prod.fst xc) (Prod.fst '' Xc) := by
  intro hxc
  constructor
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (order_pair_def.mp (hxc.1 z hz)).1
  · intro y hy
    have hy' : isUB (y, Prod.snd xc) Xc := by
      intro z hz
      have hzxc := order_pair_def.mp (hxc.1 z hz)
      exact order_pair_def.mpr ⟨hy _ ⟨z, hz, rfl⟩, hzxc.2⟩
    exact (order_pair_def.mp (hxc.2 (y, Prod.snd xc) hy')).1

theorem pair_LUB_decompo_snd_only_if {xc : α × β} {Xc : Set (α × β)}
    [PartialOrder α] [PartialOrder β] :
    isLUB xc Xc → isLUB (Prod.snd xc) (Prod.snd '' Xc) := by
  intro hxc
  constructor
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact (order_pair_def.mp (hxc.1 z hz)).2
  · intro y hy
    have hy' : isUB (Prod.fst xc, y) Xc := by
      intro z hz
      have hzxc := order_pair_def.mp (hxc.1 z hz)
      exact order_pair_def.mpr ⟨hzxc.1, hy _ ⟨z, hz, rfl⟩⟩
    exact (order_pair_def.mp (hxc.2 (Prod.fst xc, y) hy')).2

/- if -/

theorem pair_LUB_decompo_if {xc : α × β} {Xc : Set (α × β)}
    [PartialOrder α] [PartialOrder β] :
    isLUB (Prod.fst xc) (Prod.fst '' Xc) ∧ isLUB (Prod.snd xc) (Prod.snd '' Xc) →
      isLUB xc Xc := by
  rintro ⟨hfst, hsnd⟩
  constructor
  · intro z hz
    exact order_pair_def.mpr ⟨hfst.1 _ ⟨z, hz, rfl⟩, hsnd.1 _ ⟨z, hz, rfl⟩⟩
  · intro y hy
    have hyfst : isUB (Prod.fst y) (Prod.fst '' Xc) := by
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      exact (order_pair_def.mp (hy z hz)).1
    have hysnd : isUB (Prod.snd y) (Prod.snd '' Xc) := by
      intro b hb
      rcases hb with ⟨z, hz, rfl⟩
      exact (order_pair_def.mp (hy z hz)).2
    exact order_pair_def.mpr ⟨hfst.2 _ hyfst, hsnd.2 _ hysnd⟩

/- iff -/

theorem pair_LUB_decompo {xc : α × β} {Xc : Set (α × β)}
    [PartialOrder α] [PartialOrder β] :
    isLUB xc Xc ↔
      (isLUB (Prod.fst xc) (Prod.fst '' Xc) ∧ isLUB (Prod.snd xc) (Prod.snd '' Xc)) := by
  constructor
  · intro hxc
    exact ⟨pair_LUB_decompo_fst_only_if hxc, pair_LUB_decompo_snd_only_if hxc⟩
  · exact pair_LUB_decompo_if
