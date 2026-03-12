           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |              September 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_F.Domain_F_cpo
import LeanCspProver.CSP_F.CSP_F_mono

open Function
open SumType

noncomputable section

/-
(*****************************************************************

         1. continuous failuresfun
         2. continuous failuresFun
         3. continuous [[ ]]Ffun
         4. continuous [[ ]]FFun

 *****************************************************************)
-/

private theorem image_ne_empty_of_directed {δ : Type _} {γ : Type _}
    [Preorder δ] {f : δ → γ} {X : Set δ} (hX : directed X) :
    f '' X ≠ ∅ := by
  rcases hX.1 with ⟨x, hx⟩
  exact Set.nonempty_iff_ne_empty.mp ⟨f x, ⟨x, hx, rfl⟩⟩

private theorem continuous_lub_image {δ : Type _} {γ : Type _}
    [cpo δ] [cpo γ] {f : δ → γ} {X : Set δ}
    (hf : continuous f) (hX : directed X) :
    isLUB (f (LUB X)) (f '' X) := by
  have hLUBX : isLUB (LUB X) X := LUB_is (complete_cpo X hX)
  rcases (continuous_iff.mp hf) X hX with ⟨x, hfx, hx⟩
  have hxEq : x = LUB X := LUB_unique hx hLUBX
  simpa [hxEq] using hfx

/- =============================================================*
 |                     traces fstF                             |
 *============================================================= -/

theorem continuous_traces_fstF
    {P : proc p α} :
    continuous (fun M : p → domFType α => traces P (fstF ∘ M)) := by
  simpa [Function.comp] using
    (compo_continuous
      (f := fun M : p → domFType α => fstF ∘ M)
      (g := traces P)
      continuous_op_fstF
      (continuous_traces (P := P)))

/-
(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)
-/

theorem continuous_failures_STOP :
    continuous (failures (proc.STOP : proc p α)) := by
  simpa [failures] using
    (continuous_Constant
      (C := CollectF fun f : failure α => ∃ X, f = (<>, X)))

theorem continuous_failures_SKIP :
    continuous (failures (proc.SKIP : proc p α)) := by
  simpa [failures] using
    (continuous_Constant
      (C := CollectF fun f : failure α =>
        (∃ X, f = (<>, X) ∧ X ⊆ Evset) ∨
          ∃ X, f = ((Abs_trace [event.Tick] : traceType α), X)))

theorem continuous_failures_DIV :
    continuous (failures (proc.DIV : proc p α)) := by
  simpa [failures] using
    (continuous_Constant (C := ({}f : setFType α)))

/-
(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)
-/

theorem continuous_failures_Act_prefix
    {a : α} {P : proc p α} :
    continuous (failures P) →
      continuous (failures (a ~> P)) := by
  intro hP
  apply continuous_if_cpo
  intro X hX
  have hPx : isLUB (failures P (LUB X)) (failures P '' X) :=
    continuous_lub_image hP hX
  have hPxEq : failures P (LUB X) = UnionF (failures P '' X) :=
    (isLUB_UnionF).mp hPx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Act_prefix] at hs
    rw [memF_UnionF]
    rcases hX.1 with ⟨x, hx⟩
    rcases hs with hs | hs
    · exact ⟨failures (a ~> P) x, ⟨x, hx, rfl⟩, (in_failures_Act_prefix).mpr (Or.inl hs)⟩
    · rcases hs with ⟨t, Z, hEq, htZ⟩
      have htUnion : (t, Z) :f UnionF (failures P '' X) := by
        simpa [hPxEq] using htZ
      rcases (memF_UnionF).mp htUnion with ⟨F, hF, htF⟩
      rcases hF with ⟨x, hx, rfl⟩
      exact
        ⟨failures (a ~> P) x, ⟨x, hx, rfl⟩,
          (in_failures_Act_prefix).mpr (Or.inr ⟨t, Z, hEq, htF⟩)⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Act_prefix] at hsF ⊢
    rcases hsF with hsF | hsF
    · exact Or.inl hsF
    · rcases hsF with ⟨t, Z, hEq, htZ⟩
      exact Or.inr ⟨t, Z, hEq, hPx.1 _ ⟨x, hx, rfl⟩ htZ⟩

/-
(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)
-/

theorem continuous_failures_Ext_pre_choice
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, continuous (failures (Pf a))) →
      continuous (failures (proc.Ext_pre_choice X Pf)) := by
  intro hPf
  apply continuous_if_cpo
  intro Xa hXa
  have hPfLUB : ∀ a, isLUB (failures (Pf a) (LUB Xa)) (failures (Pf a) '' Xa) := by
    intro a
    exact continuous_lub_image (hPf a) hXa
  have hPfEq : ∀ a, failures (Pf a) (LUB Xa) = UnionF (failures (Pf a) '' Xa) := by
    intro a
    exact (isLUB_UnionF).mp (hPfLUB a)
  refine ⟨LUB Xa, ?_, LUB_is (complete_cpo Xa hXa)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Ext_pre_choice] at hs
    rw [memF_UnionF]
    rcases hXa.1 with ⟨x, hx⟩
    rcases hs with hs | hs
    · exact
        ⟨failures (proc.Ext_pre_choice X Pf) x, ⟨x, hx, rfl⟩,
          (in_failures_Ext_pre_choice).mpr (Or.inl hs)⟩
    · rcases hs with ⟨a, t, Z, hEq, htZ, haX⟩
      have htUnion : (t, Z) :f UnionF (failures (Pf a) '' Xa) := by
        simpa [hPfEq a] using htZ
      rcases (memF_UnionF).mp htUnion with ⟨F, hF, htF⟩
      rcases hF with ⟨x, hx, rfl⟩
      exact
        ⟨failures (proc.Ext_pre_choice X Pf) x, ⟨x, hx, rfl⟩,
          (in_failures_Ext_pre_choice).mpr (Or.inr ⟨a, t, Z, hEq, htF, haX⟩)⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Ext_pre_choice] at hsF ⊢
    rcases hsF with hsF | hsF
    · exact Or.inl hsF
    · rcases hsF with ⟨a, t, Z, hEq, htZ, haX⟩
      exact Or.inr ⟨a, t, Z, hEq, hPfLUB a |>.1 _ ⟨x, hx, rfl⟩ htZ, haX⟩

/-
(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)
-/

theorem continuous_failures_Ext_choice
    {P Q : proc p α} :
    continuous (failures P) → continuous (failures Q) →
      continuous (failures (P [+] Q)) := by
  intro hP hQ
  have hmonoP : mono (failures P) := continuous_mono hP
  have hmonoQ : mono (failures Q) := continuous_mono hQ
  have hTP : continuous (fun M : p → domFType α => traces P (fstF ∘ M)) :=
    continuous_traces_fstF (P := P)
  have hTQ : continuous (fun M : p → domFType α => traces Q (fstF ∘ M)) :=
    continuous_traces_fstF (P := Q)
  apply continuous_if_cpo
  intro X hX
  have hImgTP : (fun M : p → domFType α => traces P (fstF ∘ M)) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := fun M : p → domFType α => traces P (fstF ∘ M)) hX
  have hImgTQ : (fun M : p → domFType α => traces Q (fstF ∘ M)) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := fun M : p → domFType α => traces Q (fstF ∘ M)) hX
  have hPx : isLUB (failures P (LUB X)) (failures P '' X) := continuous_lub_image hP hX
  have hQx : isLUB (failures Q (LUB X)) (failures Q '' X) := continuous_lub_image hQ hX
  have hTx : isLUB (traces P (fstF ∘ LUB X))
      ((fun M : p → domFType α => traces P (fstF ∘ M)) '' X) :=
    continuous_lub_image hTP hX
  have hUx : isLUB (traces Q (fstF ∘ LUB X))
      ((fun M : p → domFType α => traces Q (fstF ∘ M)) '' X) :=
    continuous_lub_image hTQ hX
  have hPxEq : failures P (LUB X) = UnionF (failures P '' X) :=
    (isLUB_UnionF).mp hPx
  have hQxEq : failures Q (LUB X) = UnionF (failures Q '' X) :=
    (isLUB_UnionF).mp hQx
  have hTxEq : traces P (fstF ∘ LUB X) =
      UnionT ((fun M : p → domFType α => traces P (fstF ∘ M)) '' X) :=
    (isLUB_UnionT
      (T := traces P (fstF ∘ LUB X))
      (Ts := (fun M : p → domFType α => traces P (fstF ∘ M)) '' X)
      hImgTP).mp hTx
  have hUxEq : traces Q (fstF ∘ LUB X) =
      UnionT ((fun M : p → domFType α => traces Q (fstF ∘ M)) '' X) :=
    (isLUB_UnionT
      (T := traces Q (fstF ∘ LUB X))
      (Ts := (fun M : p → domFType α => traces Q (fstF ∘ M)) '' X)
      hImgTQ).mp hUx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Ext_choice] at hs
    rw [memF_UnionF]
    rcases hs with hs | hs | hs
    · rcases hs with ⟨hNil, hsP, hsQ⟩
      have hsPUnion : (s, Y) :f UnionF (failures P '' X) := by
        simpa [hPxEq] using hsP
      have hsQUnion : (s, Y) :f UnionF (failures Q '' X) := by
        simpa [hQxEq] using hsQ
      rcases (memF_UnionF).mp hsPUnion with ⟨FP, hFP, hsFP⟩
      rcases (memF_UnionF).mp hsQUnion with ⟨FQ, hFQ, hsFQ⟩
      rcases hFP with ⟨xP, hxP, rfl⟩
      rcases hFQ with ⟨xQ, hxQ, rfl⟩
      rcases hX.2 xP xQ hxP hxQ with ⟨z, hz, hxPz, hxQz⟩
      exact
        ⟨failures (P [+] Q) z, ⟨z, hz, rfl⟩,
          (in_failures_Ext_choice).mpr
            (Or.inl
              ⟨hNil,
                (subsetF_iff.mp (hmonoP hxPz)) _ _ hsFP,
                (subsetF_iff.mp (hmonoQ hxQz)) _ _ hsFQ⟩)⟩
    · rcases hs with ⟨u, hu, hsPQ, huNe⟩
      rcases hsPQ with hsP | hsQ
      · have hsPUnion : (s, Y) :f UnionF (failures P '' X) := by
          simpa [hPxEq] using hsP
        rcases (memF_UnionF).mp hsPUnion with ⟨FP, hFP, hsFP⟩
        rcases hFP with ⟨x, hx, rfl⟩
        exact
          ⟨failures (P [+] Q) x, ⟨x, hx, rfl⟩,
            (in_failures_Ext_choice).mpr (Or.inr <| Or.inl ⟨u, hu, Or.inl hsFP, huNe⟩)⟩
      · have hsQUnion : (s, Y) :f UnionF (failures Q '' X) := by
          simpa [hQxEq] using hsQ
        rcases (memF_UnionF).mp hsQUnion with ⟨FQ, hFQ, hsFQ⟩
        rcases hFQ with ⟨x, hx, rfl⟩
        exact
          ⟨failures (P [+] Q) x, ⟨x, hx, rfl⟩,
            (in_failures_Ext_choice).mpr (Or.inr <| Or.inl ⟨u, hu, Or.inr hsFQ, huNe⟩)⟩
    · rcases hs with ⟨Z, hEq, hTick, hSub⟩
      rcases hTick with hTickP | hTickQ
      · have hTickUnion :
            (Abs_trace [event.Tick] : traceType α) :t
              UnionT ((fun M : p → domFType α => traces P (fstF ∘ M)) '' X) := by
          simpa [hTxEq] using hTickP
        rcases (memT_UnionT hImgTP).mp hTickUnion with ⟨T, hT, hTickT⟩
        rcases hT with ⟨x, hx, rfl⟩
        exact
          ⟨failures (P [+] Q) x, ⟨x, hx, rfl⟩,
            (in_failures_Ext_choice).mpr (Or.inr <| Or.inr ⟨Z, hEq, Or.inl hTickT, hSub⟩)⟩
      · have hTickUnion :
            (Abs_trace [event.Tick] : traceType α) :t
              UnionT ((fun M : p → domFType α => traces Q (fstF ∘ M)) '' X) := by
          simpa [hUxEq] using hTickQ
        rcases (memT_UnionT hImgTQ).mp hTickUnion with ⟨T, hT, hTickT⟩
        rcases hT with ⟨x, hx, rfl⟩
        exact
          ⟨failures (P [+] Q) x, ⟨x, hx, rfl⟩,
            (in_failures_Ext_choice).mpr (Or.inr <| Or.inr ⟨Z, hEq, Or.inr hTickT, hSub⟩)⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Ext_choice] at hsF ⊢
    rcases hsF with hsF | hsF | hsF
    · rcases hsF with ⟨hNil, hsP, hsQ⟩
      exact Or.inl ⟨hNil, hPx.1 _ ⟨x, hx, rfl⟩ hsP, hQx.1 _ ⟨x, hx, rfl⟩ hsQ⟩
    · rcases hsF with ⟨u, hu, hsPQ, huNe⟩
      exact Or.inr <| Or.inl
        ⟨u, hu, hsPQ.elim
          (fun hsP => Or.inl (hPx.1 _ ⟨x, hx, rfl⟩ hsP))
          (fun hsQ => Or.inr (hQx.1 _ ⟨x, hx, rfl⟩ hsQ)), huNe⟩
    · rcases hsF with ⟨Z, hEq, hTick, hSub⟩
      exact Or.inr <| Or.inr
        ⟨Z, hEq, hTick.elim
          (fun hsP => Or.inl (hTx.1 _ ⟨x, hx, rfl⟩ hsP))
          (fun hsQ => Or.inr (hUx.1 _ ⟨x, hx, rfl⟩ hsQ)), hSub⟩

/-
(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)
-/

theorem continuous_failures_Int_choice
    {P Q : proc p α} :
    continuous (failures P) → continuous (failures Q) →
      continuous (failures (P |~| Q)) := by
  intro hP hQ
  apply continuous_if_cpo
  intro X hX
  have hPx : isLUB (failures P (LUB X)) (failures P '' X) :=
    continuous_lub_image hP hX
  have hQx : isLUB (failures Q (LUB X)) (failures Q '' X) :=
    continuous_lub_image hQ hX
  have hPxEq : failures P (LUB X) = UnionF (failures P '' X) :=
    (isLUB_UnionF).mp hPx
  have hQxEq : failures Q (LUB X) = UnionF (failures Q '' X) :=
    (isLUB_UnionF).mp hQx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Int_choice] at hs
    rw [memF_UnionF]
    rcases hs with hs | hs
    · have hsUnion : (s, Y) :f UnionF (failures P '' X) := by
        simpa [hPxEq] using hs
      rcases (memF_UnionF).mp hsUnion with ⟨F, hF, hsF⟩
      rcases hF with ⟨x, hx, rfl⟩
      exact
        ⟨failures (P |~| Q) x, ⟨x, hx, rfl⟩,
          (in_failures_Int_choice).mpr (Or.inl hsF)⟩
    · have hsUnion : (s, Y) :f UnionF (failures Q '' X) := by
        simpa [hQxEq] using hs
      rcases (memF_UnionF).mp hsUnion with ⟨F, hF, hsF⟩
      rcases hF with ⟨x, hx, rfl⟩
      exact
        ⟨failures (P |~| Q) x, ⟨x, hx, rfl⟩,
          (in_failures_Int_choice).mpr (Or.inr hsF)⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Int_choice] at hsF ⊢
    exact hsF.elim
      (fun hsP => Or.inl (hPx.1 _ ⟨x, hx, rfl⟩ hsP))
      (fun hsQ => Or.inr (hQx.1 _ ⟨x, hx, rfl⟩ hsQ))

/-
(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)
-/

theorem continuous_failures_Rep_int_choice
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, continuous (failures (Pf c))) →
      continuous (failures (proc.Rep_int_choice C Pf)) := by
  intro hPf
  apply continuous_if_cpo
  intro X hX
  have hPfLUB : ∀ c, isLUB (failures (Pf c) (LUB X)) (failures (Pf c) '' X) := by
    intro c
    exact continuous_lub_image (hPf c) hX
  have hPfEq : ∀ c, failures (Pf c) (LUB X) = UnionF (failures (Pf c) '' X) := by
    intro c
    exact (isLUB_UnionF).mp (hPfLUB c)
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Rep_int_choice_sum] at hs
    rw [memF_UnionF]
    rcases hs with ⟨c, hc, hsC⟩
    have hsUnion : (s, Y) :f UnionF (failures (Pf c) '' X) := by
      simpa [hPfEq c] using hsC
    rcases (memF_UnionF).mp hsUnion with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    exact
      ⟨failures (proc.Rep_int_choice C Pf) x, ⟨x, hx, rfl⟩,
        (in_failures_Rep_int_choice_sum).mpr ⟨c, hc, hsF⟩⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Rep_int_choice_sum] at hsF ⊢
    rcases hsF with ⟨c, hc, hsC⟩
    exact ⟨c, hc, hPfLUB c |>.1 _ ⟨x, hx, rfl⟩ hsC⟩

/-
(*--------------------------------*
 |              IF                |
 *--------------------------------*)
-/

theorem continuous_failures_IF
    {b : Bool} {P Q : proc p α} :
    continuous (failures P) → continuous (failures Q) →
      continuous (failures (IF b THEN P ELSE Q)) := by
  intro hP hQ
  by_cases hb : b
  · simpa [failures, hb] using hP
  · simpa [failures, hb] using hQ

/-
(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)
-/

theorem continuous_failures_Parallel
    {P Q : proc p α} {X : Set α} :
    continuous (failures P) → continuous (failures Q) →
      continuous (failures (P |[X]| Q)) := by
  intro hP hQ
  have hmonoP : mono (failures P) := continuous_mono hP
  have hmonoQ : mono (failures Q) := continuous_mono hQ
  apply continuous_if_cpo
  intro Xa hXa
  have hPx : isLUB (failures P (LUB Xa)) (failures P '' Xa) :=
    continuous_lub_image hP hXa
  have hQx : isLUB (failures Q (LUB Xa)) (failures Q '' Xa) :=
    continuous_lub_image hQ hXa
  have hPxEq : failures P (LUB Xa) = UnionF (failures P '' Xa) :=
    (isLUB_UnionF).mp hPx
  have hQxEq : failures Q (LUB Xa) = UnionF (failures Q '' Xa) :=
    (isLUB_UnionF).mp hQx
  refine ⟨LUB Xa, ?_, LUB_is (complete_cpo Xa hXa)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro u Y hs
    rw [in_failures_Parallel] at hs
    rw [memF_UnionF]
    rcases hs with ⟨t, Y1, Z1, hEq, hYZ, s, v, ht, hsY, hvZ⟩
    have hsUnion : (s, Y1) :f UnionF (failures P '' Xa) := by
      simpa [hPxEq] using hsY
    have hvUnion : (v, Z1) :f UnionF (failures Q '' Xa) := by
      simpa [hQxEq] using hvZ
    rcases (memF_UnionF).mp hsUnion with ⟨FP, hFP, hsFP⟩
    rcases (memF_UnionF).mp hvUnion with ⟨FQ, hFQ, hvFQ⟩
    rcases hFP with ⟨xP, hxP, rfl⟩
    rcases hFQ with ⟨xQ, hxQ, rfl⟩
    rcases hXa.2 xP xQ hxP hxQ with ⟨z, hz, hxPz, hxQz⟩
    exact
      ⟨failures (P |[X]| Q) z, ⟨z, hz, rfl⟩,
        (in_failures_Parallel).mpr
          ⟨t, Y1, Z1, hEq, hYZ, s, v, ht,
            (subsetF_iff.mp (hmonoP hxPz)) _ _ hsFP,
            (subsetF_iff.mp (hmonoQ hxQz)) _ _ hvFQ⟩⟩
  · apply subsetFI
    intro u Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Parallel] at hsF ⊢
    rcases hsF with ⟨t, Y1, Z1, hEq, hYZ, s, v, ht, hsY, hvZ⟩
    exact ⟨t, Y1, Z1, hEq, hYZ, s, v, ht,
      hPx.1 _ ⟨x, hx, rfl⟩ hsY,
      hQx.1 _ ⟨x, hx, rfl⟩ hvZ⟩

/-
(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)
-/

theorem continuous_failures_Hiding
    {P : proc p α} {X : Set α} :
    continuous (failures P) →
      continuous (failures (proc.Hiding P X)) := by
  intro hP
  apply continuous_if_cpo
  intro Xa hXa
  have hPx : isLUB (failures P (LUB Xa)) (failures P '' Xa) :=
    continuous_lub_image hP hXa
  have hPxEq : failures P (LUB Xa) = UnionF (failures P '' Xa) :=
    (isLUB_UnionF).mp hPx
  refine ⟨LUB Xa, ?_, LUB_is (complete_cpo Xa hXa)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Hiding] at hs
    rw [memF_UnionF]
    rcases hs with ⟨t, Z, hEq, htZ⟩
    have htUnion : (t, event.Ev '' X ∪ Z) :f UnionF (failures P '' Xa) := by
      simpa [hPxEq] using htZ
    rcases (memF_UnionF).mp htUnion with ⟨F, hF, htF⟩
    rcases hF with ⟨x, hx, rfl⟩
    exact
      ⟨failures (proc.Hiding P X) x, ⟨x, hx, rfl⟩,
        (in_failures_Hiding).mpr ⟨t, Z, hEq, htF⟩⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Hiding] at hsF ⊢
    rcases hsF with ⟨t, Z, hEq, htZ⟩
    exact ⟨t, Z, hEq, hPx.1 _ ⟨x, hx, rfl⟩ htZ⟩

/-
(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)
-/

theorem continuous_failures_Renaming
    {P : proc p α} {r : Set (α × α)} :
    continuous (failures P) →
      continuous (failures (P [[r]])) := by
  intro hP
  apply continuous_if_cpo
  intro X hX
  have hPx : isLUB (failures P (LUB X)) (failures P '' X) :=
    continuous_lub_image hP hX
  have hPxEq : failures P (LUB X) = UnionF (failures P '' X) :=
    (isLUB_UnionF).mp hPx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro s Y hs
    rw [in_failures_Renaming] at hs
    rw [memF_UnionF]
    rcases hs with ⟨t, u, Z, hEq, hRen, htZ⟩
    have htUnion : (t, [[r]]inv Z) :f UnionF (failures P '' X) := by
      simpa [hPxEq] using htZ
    rcases (memF_UnionF).mp htUnion with ⟨F, hF, htF⟩
    rcases hF with ⟨x, hx, rfl⟩
    exact
      ⟨failures (P [[r]]) x, ⟨x, hx, rfl⟩,
        (in_failures_Renaming).mpr ⟨t, u, Z, hEq, hRen, htF⟩⟩
  · apply subsetFI
    intro s Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Renaming] at hsF ⊢
    rcases hsF with ⟨t, u, Z, hEq, hRen, htZ⟩
    exact ⟨t, u, Z, hEq, hRen, hPx.1 _ ⟨x, hx, rfl⟩ htZ⟩

/-
(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)
-/

theorem continuous_failures_Seq_compo
    {P Q : proc p α} :
    continuous (failures P) → continuous (failures Q) →
      continuous (failures (P ;; Q)) := by
  intro hP hQ
  have hTP : continuous (fun M : p → domFType α => traces P (fstF ∘ M)) :=
    continuous_traces_fstF (P := P)
  have hmonoTP : mono (fun M : p → domFType α => traces P (fstF ∘ M)) :=
    continuous_mono hTP
  have hmonoQ : mono (failures Q) := continuous_mono hQ
  apply continuous_if_cpo
  intro X hX
  have hImgTP : (fun M : p → domFType α => traces P (fstF ∘ M)) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := fun M : p → domFType α => traces P (fstF ∘ M)) hX
  have hPx : isLUB (failures P (LUB X)) (failures P '' X) := continuous_lub_image hP hX
  have hQx : isLUB (failures Q (LUB X)) (failures Q '' X) := continuous_lub_image hQ hX
  have hTx : isLUB (traces P (fstF ∘ LUB X))
      ((fun M : p → domFType α => traces P (fstF ∘ M)) '' X) :=
    continuous_lub_image hTP hX
  have hPxEq : failures P (LUB X) = UnionF (failures P '' X) :=
    (isLUB_UnionF).mp hPx
  have hQxEq : failures Q (LUB X) = UnionF (failures Q '' X) :=
    (isLUB_UnionF).mp hQx
  have hTxEq : traces P (fstF ∘ LUB X) =
      UnionT ((fun M : p → domFType α => traces P (fstF ∘ M)) '' X) :=
    (isLUB_UnionT
      (T := traces P (fstF ∘ LUB X))
      (Ts := (fun M : p → domFType α => traces P (fstF ∘ M)) '' X)
      hImgTP).mp hTx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro u Y hs
    rw [in_failures_Seq_compo] at hs
    rw [memF_UnionF]
    rcases hs with hs | hs
    · rcases hs with ⟨t, Z, hEq, htZ, hNo⟩
      have htUnion : (t, Z ∪ {event.Tick}) :f UnionF (failures P '' X) := by
        simpa [hPxEq] using htZ
      rcases (memF_UnionF).mp htUnion with ⟨F, hF, htF⟩
      rcases hF with ⟨x, hx, rfl⟩
      exact
        ⟨failures (P ;; Q) x, ⟨x, hx, rfl⟩,
          (in_failures_Seq_compo).mpr (Or.inl ⟨t, Z, hEq, htF, hNo⟩)⟩
    · rcases hs with ⟨s, t, Z, hEq, hTick, htZ, hNo⟩
      have hTickUnion :
          (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t
            UnionT ((fun M : p → domFType α => traces P (fstF ∘ M)) '' X) := by
        simpa [hTxEq] using hTick
      have htUnion : (t, Z) :f UnionF (failures Q '' X) := by
        simpa [hQxEq] using htZ
      rcases (memT_UnionT hImgTP).mp hTickUnion with ⟨T, hT, hTickT⟩
      rcases (memF_UnionF).mp htUnion with ⟨F, hF, htF⟩
      rcases hT with ⟨xP, hxP, rfl⟩
      rcases hF with ⟨xQ, hxQ, rfl⟩
      rcases hX.2 xP xQ hxP hxQ with ⟨z, hz, hxPz, hxQz⟩
      exact
        ⟨failures (P ;; Q) z, ⟨z, hz, rfl⟩,
          (in_failures_Seq_compo).mpr (Or.inr
            ⟨s, t, Z, hEq,
              hmonoTP hxPz hTickT,
              (subsetF_iff.mp (hmonoQ hxQz)) _ _ htF, hNo⟩)⟩
  · apply subsetFI
    intro u Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Seq_compo] at hsF ⊢
    rcases hsF with hsF | hsF
    · rcases hsF with ⟨t, Z, hEq, htZ, hNo⟩
      exact Or.inl ⟨t, Z, hEq, hPx.1 _ ⟨x, hx, rfl⟩ htZ, hNo⟩
    · rcases hsF with ⟨s, t, Z, hEq, hTick, htZ, hNo⟩
      exact Or.inr
        ⟨s, t, Z, hEq, hTx.1 _ ⟨x, hx, rfl⟩ hTick, hQx.1 _ ⟨x, hx, rfl⟩ htZ, hNo⟩

/-
(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)
-/

theorem continuous_failures_Depth_rest
    {P : proc p α} {n : Nat} :
    continuous (failures P) →
      continuous (failures (P |. n)) := by
  intro hP
  apply continuous_if_cpo
  intro X hX
  have hPx : isLUB (failures P (LUB X)) (failures P '' X) :=
    continuous_lub_image hP hX
  have hPxEq : failures P (LUB X) = UnionF (failures P '' X) :=
    (isLUB_UnionF).mp hPx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionF).mpr
  apply le_antisymm
  · apply subsetFI
    intro t Y hs
    rw [in_failures_Depth_rest] at hs
    rw [memF_UnionF]
    rcases hs with ⟨u, Z, hEq, huZ, hRest⟩
    have huUnion : (u, Z) :f UnionF (failures P '' X) := by
      simpa [hPxEq] using huZ
    rcases (memF_UnionF).mp huUnion with ⟨F, hF, huF⟩
    rcases hF with ⟨x, hx, rfl⟩
    exact
      ⟨failures (P |. n) x, ⟨x, hx, rfl⟩,
        (in_failures_Depth_rest).mpr ⟨u, Z, hEq, huF, hRest⟩⟩
  · apply subsetFI
    intro t Y hs
    rw [memF_UnionF] at hs
    rcases hs with ⟨F, hF, hsF⟩
    rcases hF with ⟨x, hx, rfl⟩
    rw [in_failures_Depth_rest] at hsF ⊢
    rcases hsF with ⟨u, Z, hEq, huZ, hRest⟩
    exact ⟨u, Z, hEq, hPx.1 _ ⟨x, hx, rfl⟩ huZ, hRest⟩

/-
(*--------------------------------*
 |            variable            |
 *--------------------------------*)
-/

theorem continuous_failures_variable_lm
    {p0 : p} :
    continuous (fun M : p → domFType α => sndF (M p0)) := by
  simpa [Function.comp] using
    (compo_continuous
      (f := fun M : p → domFType α => M p0)
      (g := sndF)
      (continuous_prod_variable (pn := p0))
      sndF_continuous)

theorem continuous_failures_variable
    {p0 : p} :
    continuous (failures (proc.Proc_name p0 : proc p α)) := by
  simpa [failures] using (continuous_failures_variable_lm (p0 := p0))

/-
(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)
-/

theorem continuous_failures
    {P : proc p α} :
    continuous (failures P) := by
  induction P with
  | STOP =>
      exact continuous_failures_STOP
  | SKIP =>
      exact continuous_failures_SKIP
  | DIV =>
      exact continuous_failures_DIV
  | Act_prefix a P ih =>
      exact continuous_failures_Act_prefix ih
  | Ext_pre_choice X Pf ih =>
      exact continuous_failures_Ext_pre_choice (fun a => ih a)
  | Ext_choice P Q ihP ihQ =>
      exact continuous_failures_Ext_choice ihP ihQ
  | Int_choice P Q ihP ihQ =>
      exact continuous_failures_Int_choice ihP ihQ
  | Rep_int_choice C Pf ih =>
      exact continuous_failures_Rep_int_choice (fun c => ih c)
  | «IF» b P Q ihP ihQ =>
      exact continuous_failures_IF ihP ihQ
  | Parallel P X Q ihP ihQ =>
      exact continuous_failures_Parallel ihP ihQ
  | Hiding P X ih =>
      exact continuous_failures_Hiding ih
  | Renaming P r ih =>
      exact continuous_failures_Renaming ih
  | Seq_compo P Q ihP ihQ =>
      exact continuous_failures_Seq_compo ihP ihQ
  | Depth_rest P n ih =>
      exact continuous_failures_Depth_rest ih
  | Proc_name p0 =>
      exact continuous_failures_variable

/- =============================================================*
 |                          [[P]]Ff                            |
 *============================================================= -/

theorem continuous_semFf
    {P : proc p α} :
    continuous (semFf P) := by
  apply continuous_domF
  · intro M
    change (traces P (fstF ∘ M), failures P M) ∈ domF (α := α)
    simpa [semFf_def] using (proc_domF (P := P) (M := M))
  · simpa [Function.comp] using (continuous_traces_fstF (P := P))
  · simpa using (continuous_failures (P := P))

/- =============================================================*
 |                         [[P]]Ffun                           |
 *============================================================= -/

theorem continuous_semFfun
    {Pf : p → proc p α} :
    continuous (semFfun Pf) := by
  apply prod_continuous_if
  intro p0
  simpa [semFfun_def, semFf_def, proj_fun, Function.comp] using
    (continuous_semFf (P := Pf p0))

end
