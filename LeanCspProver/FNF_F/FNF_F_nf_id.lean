           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  April 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F_nf_def

open Function
open SumType

attribute [local instance] Classical.propDecidable

noncomputable section

universe u v

variable {p : Type u} {α : Type v}

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion`.                     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`               -/
/-                                                                   -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there  -/
/-  is nothing to disable or re-enable here.                         -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`     -/
/- Isabelle 2017                                                      -/
/-                                                                    -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is -/
/-  nothing to disable or re-enable here.                             -/

/-
(*****************************************************************

         1. =F --> =
         2.
         3.

 *****************************************************************)
-/

/- (*---------------------------------------------------------*
 |              syntactically identical ?                  |
 *---------------------------------------------------------*) -/

/- (*===========================================================*
 |                      fnfF_nat_proc                        |
 *===========================================================*) -/

/- (*** Q ***) -/

theorem fnfF_syntactical_equality_Q_lm
    {A1 A2 : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    refF
      ((((proc.Ext_pre_choice A1 Pf1) [+] proc.DIV) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
      M1 M2
      ((((proc.Ext_pre_choice A2 Pf2) [+] proc.SKIP) |~|
        Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
      False := by
  intro h
  have hT := (cspF_cspT_refF_semantics.mp h).1
  rw [cspT_refT_semantics] at hT
  have hTick : (Abs_trace [event.Tick] : traceType α) :t
      traces ((((proc.Ext_pre_choice A2 Pf2) [+] proc.SKIP) |~|
        Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        (fstF ∘ M2) := by
    rw [in_traces_Int_choice, in_traces_Ext_choice, in_traces_SKIP]
    exact Or.inl (Or.inr (Or.inr rfl))
  have hin : (Abs_trace [event.Tick] : traceType α) :t
      traces ((((proc.Ext_pre_choice A1 Pf1) [+] proc.DIV) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        (fstF ∘ M1) := hT hTick
  rw [in_traces_Int_choice, in_traces_Ext_choice, in_traces_DIV,
    in_traces_Rep_int_choice_set] at hin
  rcases hin with (hin | hin) | (hin | ⟨Y, -, hin⟩)
  · exact Tick_notin_traces_Ext_pre_choice hin
  · exact one_neq_nil hin
  · exact one_neq_nil hin
  · exact Tick_notin_traces_Ext_pre_choice hin

theorem fnfF_syntactical_equality_Q
    {Q1 Q2 : proc p α} {A1 A2 : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    (Q1 = proc.SKIP ∨ Q1 = proc.DIV) →
      (Q2 = proc.SKIP ∨ Q2 = proc.DIV) →
        eqF
          ((((proc.Ext_pre_choice A1 Pf1) [+] Q1) |~|
            Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
          M1 M2
          ((((proc.Ext_pre_choice A2 Pf2) [+] Q2) |~|
            Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
          Q1 = Q2 := by
  intro hQ1 hQ2 h
  rcases cspF_eq_ref_iff.mp h with ⟨h12, h21⟩
  rcases hQ1 with rfl | rfl <;> rcases hQ2 with rfl | rfl
  · rfl
  · exact absurd (fnfF_syntactical_equality_Q_lm h21) id
  · exact absurd (fnfF_syntactical_equality_Q_lm h12) id
  · rfl

/- (*** A ***) -/

/- a one-event trace of `(? :A1 -> Pf1 [+] Q) |~| !set Y:Ys1 .. ? a:Y -> DIV`
   is offered either by `A1` itself or by one of the `Y ∈ Ys1`. -/

private theorem Union_head
    {x : α} {A1 : Set α} {Pf1 : α → proc p α} {Ys1 : Set (Set α)} {Q : proc p α}
    {M : p → domTType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV)
    (hY1 : Set.sUnion Ys1 ⊆ A1)
    (h : (Abs_trace [event.Ev x] : traceType α) :t
      traces ((((proc.Ext_pre_choice A1 Pf1) [+] Q) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M) :
    x ∈ A1 := by
  have hcancel : ∀ (b : α) (s : traceType α),
      (Abs_trace [event.Ev x] : traceType α) = Abs_trace [event.Ev b] ^^^ s → b = x := by
    intro b s heq
    have heq' : (Abs_trace [event.Ev x] : traceType α) ^^^ (<> : traceType α)
        = Abs_trace [event.Ev b] ^^^ s := by
      rw [appt_nil_right]
      exact heq
    exact (appt_same_head_only_if heq').1.symm
  rw [in_traces_Int_choice, in_traces_Ext_choice, in_traces_Rep_int_choice_set] at h
  rcases h with (h | h) | (h | ⟨Y, hYs, h⟩)
  · rw [in_traces_Ext_pre_choice] at h
    rcases h with h | ⟨b, s, heq, -, hb⟩
    · exact absurd h (by simp)
    · rw [hcancel b s heq] at hb
      exact hb
  · rcases hQ with rfl | rfl
    · rw [in_traces_SKIP] at h
      rcases h with h | h
      · exact absurd h (by simp)
      · exact absurd h.symm (by simp)
    · rw [in_traces_DIV] at h
      exact absurd h (by simp)
  · exact absurd h (by simp)
  · rw [in_traces_Ext_pre_choice] at h
    rcases h with h | ⟨b, s, heq, -, hb⟩
    · exact absurd h (by simp)
    · rw [hcancel b s heq] at hb
      exact hY1 ⟨Y, hYs, hb⟩

theorem fnfF_syntactical_equality_Union_lm
    {A1 A2 : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A1 →
      Set.sUnion Ys2 ⊆ A2 →
        (Q = proc.SKIP ∨ Q = proc.DIV) →
          refF
            ((((proc.Ext_pre_choice A1 Pf1) [+] Q) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A2 Pf2) [+] Q) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            A2 ⊆ A1 := by
  intro hY1 _ hQ h x hx
  have hT := (cspF_cspT_refF_semantics.mp h).1
  rw [cspT_refT_semantics] at hT
  have hR : (Abs_trace [event.Ev x] : traceType α) :t
      traces ((((proc.Ext_pre_choice A2 Pf2) [+] Q) |~|
        Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        (fstF ∘ M2) := by
    rw [in_traces_Int_choice, in_traces_Ext_choice, in_traces_Ext_pre_choice]
    refine Or.inl (Or.inl (Or.inr ⟨x, <>, ?_, nilt_in_T, hx⟩))
    rw [appt_nil_right]
  have hL : (Abs_trace [event.Ev x] : traceType α) :t
      traces ((((proc.Ext_pre_choice A1 Pf1) [+] Q) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        (fstF ∘ M1) := hT hR
  exact Union_head hQ hY1 hL

theorem fnfF_syntactical_equality_Union
    {A1 A2 : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A1 →
      Set.sUnion Ys2 ⊆ A2 →
        (Q = proc.SKIP ∨ Q = proc.DIV) →
          eqF
            ((((proc.Ext_pre_choice A1 Pf1) [+] Q) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A2 Pf2) [+] Q) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            A1 = A2 := by
  intro hY1 hY2 hQ h
  rcases cspF_eq_ref_iff.mp h with ⟨h12, h21⟩
  exact Set.Subset.antisymm
    (fnfF_syntactical_equality_Union_lm hY2 hY1 hQ h21)
    (fnfF_syntactical_equality_Union_lm hY1 hY2 hQ h12)

/- (*** Yf ***) -/

/- the refusal set `Evset ∪ {Tick} \ Ev '' x` used to probe `Ys1`: it refuses
   everything except the events of `x`, and in particular it refuses `Tick`,
   which is what rules out the `SKIP` summand. -/

private theorem Yf_head
    {A : Set α} {Pf1 : α → proc p α} {Ys1 : Set (Set α)} {Q : proc p α} {x : Set α}
    {M : p → domFType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV)
    (h : ((<> : traceType α), (Set.univ \ event.Ev '' x)) :f
      failures ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M) :
    ∃ X, X ∈ Ys1 ∧ X ⊆ x := by
  have hTick : (event.Tick : event α) ∈ (Set.univ \ event.Ev '' x) := by
    refine ⟨trivial, ?_⟩
    rintro ⟨b, -, hb⟩
    exact absurd hb (by simp)
  have hnotEvset : ¬ ((Set.univ \ event.Ev '' x) ⊆ (Evset : Set (event α))) := by
    intro hsub
    exact (hsub hTick) rfl
  rw [in_failures_Int_choice, in_failures_Ext_choice,
    in_failures_Rep_int_choice_set] at h
  rcases h with (⟨-, -, hQf⟩ | ⟨u, ⟨Z, hZ⟩, -, hne⟩ | ⟨Z, hZ, -, hEv⟩) | ⟨Y, hYs, hY⟩
  · rcases hQ with rfl | rfl
    · rw [in_failures_SKIP] at hQf
      rcases hQf with ⟨Z, hZ, hsub⟩ | ⟨Z, hZ⟩
      · obtain ⟨-, rfl⟩ := Prod.mk.inj hZ
        exact absurd hsub hnotEvset
      · exact absurd (Prod.mk.inj hZ).1.symm (by simp)
    · exact absurd hQf in_failures_DIV
  · exact absurd (Prod.mk.inj hZ).1.symm hne
  · obtain ⟨-, rfl⟩ := Prod.mk.inj hZ
    exact absurd hEv hnotEvset
  · rw [in_failures_Ext_pre_choice] at hY
    rcases hY with ⟨Z, hZ, hint⟩ | ⟨b, s, Z, hZ, -, -⟩
    · obtain ⟨-, rfl⟩ := Prod.mk.inj hZ
      refine ⟨Y, hYs, fun a ha => ?_⟩
      by_contra hax
      have : event.Ev a ∈ (event.Ev '' Y) ∩ (Set.univ \ event.Ev '' x) :=
        ⟨⟨a, ha, rfl⟩, trivial, fun hc => by
          rcases hc with ⟨b, hb, hb'⟩
          injection hb' with hba
          exact hax (hba ▸ hb)⟩
      rw [hint] at this
      exact this
    · exact absurd (Prod.mk.inj hZ).1.symm (by simp)

private theorem Yf_lm
    {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)} {Q : proc p α}
    {M1 M2 : p → domFType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV)
    (_hY1 : Set.sUnion Ys1 ⊆ A) (hY2 : Set.sUnion Ys2 ⊆ A)
    (hc1 : fnfF_set_condition A Ys1)
    (h : refF
      ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
      M1 M2
      ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
        Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) :
    Ys2 ⊆ Ys1 := by
  intro x hx
  have hF := (cspF_cspT_refF_semantics.mp h).2
  have hR : ((<> : traceType α), (Set.univ \ event.Ev '' x)) :f
      failures ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
        Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M2 := by
    rw [in_failures_Int_choice, in_failures_Rep_int_choice_set]
    refine Or.inr ⟨x, hx, ?_⟩
    rw [in_failures_Ext_pre_choice]
    refine Or.inl ⟨_, rfl, ?_⟩
    rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨he, -, hne⟩
    exact hne he
  exact hc1 x ⟨Yf_head hQ (hF hR), fun a ha => Or.inl (hY2 ⟨x, hx, ha⟩)⟩

theorem fnfF_syntactical_equality_Yf_DIV_lm
    {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)} {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A →
      Set.sUnion Ys2 ⊆ A →
        fnfF_set_condition A Ys1 →
          refF
            ((((proc.Ext_pre_choice A Pf1) [+] proc.DIV) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A Pf2) [+] proc.DIV) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            Ys2 ⊆ Ys1 :=
  fun hY1 hY2 hc1 h => Yf_lm (Or.inr rfl) hY1 hY2 hc1 h

theorem fnfF_syntactical_equality_Yf_SKIP_lm
    {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)} {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A →
      Set.sUnion Ys2 ⊆ A →
        fnfF_set_condition A Ys1 →
          refF
            ((((proc.Ext_pre_choice A Pf1) [+] proc.SKIP) |~|
              Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
            M1 M2
            ((((proc.Ext_pre_choice A Pf2) [+] proc.SKIP) |~|
              Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
            Ys2 ⊆ Ys1 :=
  fun hY1 hY2 hc1 h => Yf_lm (Or.inl rfl) hY1 hY2 hc1 h

theorem fnfF_syntactical_equality_Yf
    {A : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys1 Ys2 : Set (Set α)}
    {M1 M2 : p → domFType α} :
    Set.sUnion Ys1 ⊆ A →
      Set.sUnion Ys2 ⊆ A →
        fnfF_set_condition A Ys1 →
          fnfF_set_condition A Ys2 →
            (Q = proc.SKIP ∨ Q = proc.DIV) →
              eqF
                ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
                  Rep_int_choice_set Ys1 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
                M1 M2
                ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
                  Rep_int_choice_set Ys2 (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
                Ys1 = Ys2 := by
  intro hY1 hY2 hc1 hc2 hQ h
  rcases cspF_eq_ref_iff.mp h with ⟨h12, h21⟩
  rcases hQ with rfl | rfl
  · exact Set.Subset.antisymm
      (fnfF_syntactical_equality_Yf_SKIP_lm hY2 hY1 hc2 h21)
      (fnfF_syntactical_equality_Yf_SKIP_lm hY1 hY2 hc1 h12)
  · exact Set.Subset.antisymm
      (fnfF_syntactical_equality_Yf_DIV_lm hY2 hY1 hc2 h21)
      (fnfF_syntactical_equality_Yf_DIV_lm hY1 hY2 hc1 h12)

/- (*** Pf ***) -/

/- the trace argument shared by the two `Pf_T_*_lm` lemmas: an `Ev a`-headed
   trace of the left-hand side can only come from the `? :A -> Pf1` summand
   (whose tail is a trace of `Pf1 a`) or from a `? a:Y -> DIV` summand (whose
   tail is `<>`). -/

private theorem Pf_T_head
    {a : α} {A : Set α} {Pf1 : α → proc p α} {Ys : Set (Set α)} {Q : proc p α}
    {t : traceType α} {M : p → domTType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV)
    (h : (Abs_trace [event.Ev a] ^^^ t) :t
      traces ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M) :
    t :t traces (Pf1 a) M := by
  rw [in_traces_Int_choice, in_traces_Ext_choice, in_traces_Rep_int_choice_set] at h
  rcases h with (h | h) | (h | ⟨Y, -, h⟩)
  · rw [in_traces_Ext_pre_choice] at h
    rcases h with h | ⟨b, s, heq, hs, -⟩
    · exact absurd h.symm (by simp)
    · obtain ⟨rfl, rfl⟩ := appt_same_head_only_if heq
      exact hs
  · rcases hQ with rfl | rfl
    · rw [in_traces_SKIP] at h
      rcases h with h | h
      · exact absurd h.symm (by simp)
      · exact absurd h Ev_appt_neq_Tick
    · rw [in_traces_DIV] at h
      exact absurd h.symm (by simp)
  · exact absurd h.symm (by simp)
  · rw [in_traces_Ext_pre_choice] at h
    rcases h with h | ⟨b, s, heq, hs, -⟩
    · exact absurd h.symm (by simp)
    · obtain ⟨-, rfl⟩ := appt_same_head_only_if heq
      rw [in_traces_DIV] at hs
      rw [hs]
      exact nilt_in_T

private theorem Pf_T_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {Q : proc p α}
    {M1 M2 : p → domTType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV) (ha : a ∈ A)
    (h : refT
      ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
      M1 M2
      ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) :
    refT (Pf1 a) M1 M2 (Pf2 a) := by
  rw [cspT_refT_semantics] at h ⊢
  refine subdomTI (fun t ht => ?_)
  have hR : (Abs_trace [event.Ev a] ^^^ t) :t
      traces ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M2 := by
    rw [in_traces_Int_choice, in_traces_Ext_choice, in_traces_Ext_pre_choice]
    exact Or.inl (Or.inl (Or.inr ⟨a, t, rfl, ht, ha⟩))
  have hL : (Abs_trace [event.Ev a] ^^^ t) :t
      traces ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M1 := h hR
  exact Pf_T_head hQ hL

/- the failures counterpart: an `Ev a`-headed failure of the left-hand side can
   only come from the `? :A -> Pf1` summand.  `DIV` has no failures at all and
   `SKIP` only has `<>`- and `<Tick>`-failures, and the `? a:Y -> DIV` summands
   have no `Ev`-headed failure either. -/

private theorem Pf_F_head
    {a : α} {A : Set α} {Pf1 : α → proc p α} {Ys : Set (Set α)} {Q : proc p α}
    {s : traceType α} {X : Set (event α)} {M : p → domFType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV)
    (h : ((Abs_trace [event.Ev a] ^^^ s), X) :f
      failures ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M) :
    (s, X) :f failures (Pf1 a) M := by
  have hne : (Abs_trace [event.Ev a] ^^^ s) ≠ <> := by simp
  rw [in_failures_Int_choice, in_failures_Ext_choice,
    in_failures_Rep_int_choice_set] at h
  rcases h with (⟨⟨Z, hZ⟩, -, -⟩ | ⟨u, -, hor, -⟩ | ⟨Z, hZ, -, -⟩) | ⟨Y, -, hY⟩
  · exact absurd (Prod.mk.inj hZ).1 hne
  · rcases hor with hor | hor
    · rw [in_failures_Ext_pre_choice] at hor
      rcases hor with ⟨Z, hZ, -⟩ | ⟨b, s', Z, hZ, hF, -⟩
      · exact absurd (Prod.mk.inj hZ).1 hne
      · obtain ⟨heq, rfl⟩ := Prod.mk.inj hZ
        obtain ⟨rfl, rfl⟩ := appt_same_head_only_if heq
        exact hF
    · rcases hQ with rfl | rfl
      · rw [in_failures_SKIP] at hor
        rcases hor with ⟨Z, hZ, -⟩ | ⟨Z, hZ⟩
        · exact absurd (Prod.mk.inj hZ).1 hne
        · exact absurd (Prod.mk.inj hZ).1 Ev_appt_neq_Tick
      · exact absurd hor in_failures_DIV
  · exact absurd (Prod.mk.inj hZ).1 hne
  · rw [in_failures_Ext_pre_choice] at hY
    rcases hY with ⟨Z, hZ, -⟩ | ⟨b, s', Z, hZ, hF, -⟩
    · exact absurd (Prod.mk.inj hZ).1 hne
    · exact absurd hF in_failures_DIV

private theorem Pf_F_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {Q : proc p α}
    {M1 M2 : p → domFType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV) (ha : a ∈ A)
    (h : refF
      ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
      M1 M2
      ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))) :
    refF (Pf1 a) M1 M2 (Pf2 a) := by
  rcases cspF_cspT_refF_semantics.mp h with ⟨hT, hF⟩
  refine cspF_cspT_refF_semantics.mpr ⟨Pf_T_lm hQ ha hT, ?_⟩
  rw [subsetF_iff]
  intro s X hs
  have hR : ((Abs_trace [event.Ev a] ^^^ s), X) :f
      failures ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
        Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) M2 := by
    rw [in_failures_Int_choice, in_failures_Ext_choice]
    refine Or.inl (Or.inr (Or.inl ⟨_, ⟨X, rfl⟩, Or.inl ?_, by simp⟩))
    rw [in_failures_Ext_pre_choice]
    exact Or.inr ⟨a, s, X, rfl, hs, ha⟩
  exact Pf_F_head hQ (hF hR)

/- T DIV -/

theorem fnfF_syntactical_equality_Pf_T_DIV_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domTType α} :
    a ∈ A →
      refT
        ((((proc.Ext_pre_choice A Pf1) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refT (Pf1 a) M1 M2 (Pf2 a) :=
  fun ha h => Pf_T_lm (Or.inr rfl) ha h

/- T SKIP -/

theorem fnfF_syntactical_equality_Pf_T_SKIP_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domTType α} :
    a ∈ A →
      refT
        ((((proc.Ext_pre_choice A Pf1) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refT (Pf1 a) M1 M2 (Pf2 a) :=
  fun ha h => Pf_T_lm (Or.inl rfl) ha h

/- F DIV -/

theorem fnfF_syntactical_equality_Pf_F_DIV_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domFType α} :
    a ∈ A →
      refF
        ((((proc.Ext_pre_choice A Pf1) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.DIV) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refF (Pf1 a) M1 M2 (Pf2 a) :=
  fun ha h => Pf_F_lm (Or.inr rfl) ha h

/- F SKIP -/

theorem fnfF_syntactical_equality_Pf_F_SKIP_lm
    {a : α} {A : Set α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)} {M1 M2 : p → domFType α} :
    a ∈ A →
      refF
        ((((proc.Ext_pre_choice A Pf1) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
        M1 M2
        ((((proc.Ext_pre_choice A Pf2) [+] proc.SKIP) |~|
          Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
        refF (Pf1 a) M1 M2 (Pf2 a) :=
  fun ha h => Pf_F_lm (Or.inl rfl) ha h

theorem fnfF_syntactical_equality_Pf
    {a : α} {A : Set α} {Q : proc p α} {Pf1 Pf2 : α → proc p α} {Ys : Set (Set α)}
    {M1 M2 : p → domFType α} :
    a ∈ A →
      (Q = proc.SKIP ∨ Q = proc.DIV) →
        eqF
          ((((proc.Ext_pre_choice A Pf1) [+] Q) |~|
            Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV))))
          M1 M2
          ((((proc.Ext_pre_choice A Pf2) [+] Q) |~|
            Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) →
          eqF (Pf1 a) M1 M2 (Pf2 a) := by
  intro ha hQ h
  rcases cspF_eq_ref_iff.mp h with ⟨h12, h21⟩
  rcases hQ with rfl | rfl
  · exact cspF_eq_ref_iff.mpr
      ⟨fnfF_syntactical_equality_Pf_F_SKIP_lm ha h12,
        fnfF_syntactical_equality_Pf_F_SKIP_lm ha h21⟩
  · exact cspF_eq_ref_iff.mpr
      ⟨fnfF_syntactical_equality_Pf_F_DIV_lm ha h12,
        fnfF_syntactical_equality_Pf_F_DIV_lm ha h21⟩

/- (*------------------------------------------------------------------*
 |                fnfF_proc ---> syntactical equality               |
 *------------------------------------------------------------------*) -/

axiom fnfF_syntactical_equality_only_if_lm
    {P1 : proc p α} {M1 M2 : p → domFType α} :
    fnfF_proc P1 →
      ∀ P2 : proc p α, (fnfF_proc P2 ∧ eqF P1 M1 M2 P2) → P1 = P2

theorem fnfF_syntactical_equality_only_if
    {P1 P2 : proc p α} {M1 M2 : p → domFType α} :
    fnfF_proc P1 →
      fnfF_proc P2 →
        eqF P1 M1 M2 P2 →
          P1 = P2 := by
  intro hP1 hP2 hEq
  exact fnfF_syntactical_equality_only_if_lm hP1 P2 ⟨hP2, hEq⟩

/- (*--------------------------*
 |         theorem          |
 *--------------------------*) -/

theorem fnfF_syntactical_equality [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    fnfF_proc P1 →
      fnfF_proc P2 →
        (eqFfix P1 P2 ↔ P1 = P2) := by
  intro hP1 hP2
  constructor
  · intro hEq
    exact fnfF_syntactical_equality_only_if hP1 hP2 hEq
  · intro hEq
    subst P2
    simpa [eqFfix] using (cspF_reflex_eq_P (P := P1) (M := MF))

/- (*===========================================================*
 |                        XfnfF_proc                         |
 *===========================================================*) -/

axiom XfnfF_syntactical_equality [HasPNfun p α] [HasFPmode]
    {P1 P2 : proc p α} :
    P1 ∈ XfnfF_proc (p := p) (α := α) →
      P2 ∈ XfnfF_proc (p := p) (α := α) →
        (eqFfix P1 P2 ↔ P1 = P2)

/- (****************** to add them again ******************) -/

/- Lean has no direct analogue of Isabelle's local `declare if_split [split]`
   or `declare disj_not1 [simp]` commands. -/
