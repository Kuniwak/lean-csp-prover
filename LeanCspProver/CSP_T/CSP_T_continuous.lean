           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_traces
import LeanCspProver.CSP_T.Domain_T_cpo
import LeanCspProver.CSP.CPO_prod

noncomputable section

/-
(*****************************************************************

         1. continuous traces
         2. continuous [[ ]]Tfun

 *****************************************************************)
-/

private theorem image_ne_empty_of_directed {δ : Type _} {γ : Type _}
    [Preorder δ]
    {f : δ → γ} {X : Set δ} (hX : directed X) :
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

/- --------------------------------*
 |        STOP,SKIP,DIV           |
 *-------------------------------- -/

/- (*** Constant_continuous ***) -/

theorem continuous_Constant {δ : Type _} {γ : Type _} [cpo δ] [cpo γ] {C : γ} :
    continuous (fun _ : δ => C) := by
  apply continuous_if_cpo
  intro X hX
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  constructor
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact le_rfl
  · intro y hy
    rcases hX.1 with ⟨x, hx⟩
    exact hy C ⟨x, hx, rfl⟩

theorem continuous_traces_STOP :
    continuous (traces (proc.STOP : proc p α)) := by
  simpa [traces] using
    (continuous_Constant (C := Abs_domT ({<>} : Set (traceType α))))

theorem continuous_traces_SKIP :
    continuous (traces (proc.SKIP : proc p α)) := by
  simpa [traces] using
    (continuous_Constant
      (C := Abs_domT
        ((({<>} : Set (traceType α)) ∪
          ({Abs_trace [event.Tick]} : Set (traceType α))))))

theorem continuous_traces_DIV :
    continuous (traces (proc.DIV : proc p α)) := by
  simpa [traces] using
    (continuous_Constant (C := Abs_domT ({<>} : Set (traceType α))))

/- --------------------------------*
 |          Act_prefix            |
 *-------------------------------- -/

theorem continuous_traces_Act_prefix
    {a : α} {P : proc p α} :
    continuous (traces P) → continuous (traces (a ~> P)) := by
  intro hP
  apply continuous_if_cpo
  intro X hX
  have hImgP : traces P '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces P) hX
  have hImgAct : traces (a ~> P) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (a ~> P)) hX
  have hPx : isLUB (traces P (LUB X)) (traces P '' X) :=
    continuous_lub_image hP hX
  have hPxEq : traces P (LUB X) = UnionT (traces P '' X) :=
    (isLUB_UnionT (T := traces P (LUB X)) (Ts := traces P '' X) hImgP).mp hPx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionT (T := traces (a ~> P) (LUB X)) (Ts := traces (a ~> P) '' X) hImgAct).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (a ~> P) (LUB X) at ht
    change t :t UnionT (traces (a ~> P) '' X)
    rw [in_traces_Act_prefix] at ht
    rw [memT_UnionT hImgAct]
    rcases hX.1 with ⟨x, hx⟩
    rcases ht with rfl | ⟨s, rfl, hs⟩
    · exact ⟨traces (a ~> P) x, ⟨x, hx, rfl⟩, nilt_in_T⟩
    · have hsUnion : s :t UnionT (traces P '' X) := by
        simpa [hPxEq] using hs
      rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact ⟨traces (a ~> P) x, ⟨x, hx, rfl⟩, (in_traces_Act_prefix).mpr (Or.inr ⟨s, rfl, hsT⟩)⟩
  · intro t ht
    change t :t UnionT (traces (a ~> P) '' X) at ht
    change t :t traces (a ~> P) (LUB X)
    rw [memT_UnionT hImgAct] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Act_prefix] at htT ⊢
    rcases htT with rfl | ⟨s, rfl, hs⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨s, rfl, hPx.1 _ ⟨x, hx, rfl⟩ hs⟩

/- --------------------------------*
 |        Ext_pre_choice          |
 *-------------------------------- -/

theorem continuous_traces_Ext_pre_choice
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, continuous (traces (Pf a))) →
      continuous (traces (proc.Ext_pre_choice X Pf)) := by
  intro hPf
  apply continuous_if_cpo
  intro Xa hXa
  have hImgExt : traces (proc.Ext_pre_choice X Pf) '' Xa ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (proc.Ext_pre_choice X Pf)) hXa
  have hPfLUB : ∀ a, isLUB (traces (Pf a) (LUB Xa)) (traces (Pf a) '' Xa) := by
    intro a
    exact continuous_lub_image (hPf a) hXa
  have hPfImg : ∀ a, traces (Pf a) '' Xa ≠ ∅ := by
    intro a
    exact image_ne_empty_of_directed (f := traces (Pf a)) hXa
  have hPfEq : ∀ a, traces (Pf a) (LUB Xa) = UnionT (traces (Pf a) '' Xa) := by
    intro a
    exact (isLUB_UnionT (T := traces (Pf a) (LUB Xa)) (Ts := traces (Pf a) '' Xa) (hPfImg a)).mp
      (hPfLUB a)
  refine ⟨LUB Xa, ?_, LUB_is (complete_cpo Xa hXa)⟩
  apply
    (isLUB_UnionT
      (T := traces (proc.Ext_pre_choice X Pf) (LUB Xa))
      (Ts := traces (proc.Ext_pre_choice X Pf) '' Xa) hImgExt).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (proc.Ext_pre_choice X Pf) (LUB Xa) at ht
    change t :t UnionT (traces (proc.Ext_pre_choice X Pf) '' Xa)
    rw [in_traces_Ext_pre_choice] at ht
    rw [memT_UnionT hImgExt]
    rcases hXa.1 with ⟨x, hx⟩
    rcases ht with rfl | ⟨a, s, rfl, hs, haX⟩
    · exact ⟨traces (proc.Ext_pre_choice X Pf) x, ⟨x, hx, rfl⟩, nilt_in_T⟩
    · have hsUnion : s :t UnionT (traces (Pf a) '' Xa) := by
        simpa [hPfEq a] using hs
      rcases (memT_UnionT (hPfImg a)).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact
        ⟨traces (proc.Ext_pre_choice X Pf) x, ⟨x, hx, rfl⟩,
          (in_traces_Ext_pre_choice).mpr (Or.inr ⟨a, s, rfl, hsT, haX⟩)⟩
  · intro t ht
    change t :t UnionT (traces (proc.Ext_pre_choice X Pf) '' Xa) at ht
    change t :t traces (proc.Ext_pre_choice X Pf) (LUB Xa)
    rw [memT_UnionT hImgExt] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Ext_pre_choice] at htT ⊢
    rcases htT with rfl | ⟨a, s, rfl, hs, haX⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨a, s, rfl, (hPfLUB a).1 _ ⟨x, hx, rfl⟩ hs, haX⟩

/- --------------------------------*
 |          Ext_choice            |
 *-------------------------------- -/

theorem continuous_traces_Ext_choice
    {P Q : proc p α} :
    continuous (traces P) → continuous (traces Q) →
      continuous (traces (P [+] Q)) := by
  intro hP hQ
  apply continuous_if_cpo
  intro X hX
  have hImgP : traces P '' X ≠ ∅ := image_ne_empty_of_directed (f := traces P) hX
  have hImgQ : traces Q '' X ≠ ∅ := image_ne_empty_of_directed (f := traces Q) hX
  have hImgOut : traces (P [+] Q) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (P [+] Q)) hX
  have hPx : isLUB (traces P (LUB X)) (traces P '' X) := continuous_lub_image hP hX
  have hQx : isLUB (traces Q (LUB X)) (traces Q '' X) := continuous_lub_image hQ hX
  have hPxEq : traces P (LUB X) = UnionT (traces P '' X) :=
    (isLUB_UnionT (T := traces P (LUB X)) (Ts := traces P '' X) hImgP).mp hPx
  have hQxEq : traces Q (LUB X) = UnionT (traces Q '' X) :=
    (isLUB_UnionT (T := traces Q (LUB X)) (Ts := traces Q '' X) hImgQ).mp hQx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionT (T := traces (P [+] Q) (LUB X)) (Ts := traces (P [+] Q) '' X) hImgOut).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (P [+] Q) (LUB X) at ht
    change t :t UnionT (traces (P [+] Q) '' X)
    rw [in_traces_Ext_choice] at ht
    rw [memT_UnionT hImgOut]
    rcases ht with hs | hs
    · have hsUnion : t :t UnionT (traces P '' X) := by
        simpa [hPxEq] using hs
      rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact ⟨traces (P [+] Q) x, ⟨x, hx, rfl⟩, (in_traces_Ext_choice).mpr (Or.inl hsT)⟩
    · have hsUnion : t :t UnionT (traces Q '' X) := by
        simpa [hQxEq] using hs
      rcases (memT_UnionT hImgQ).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact ⟨traces (P [+] Q) x, ⟨x, hx, rfl⟩, (in_traces_Ext_choice).mpr (Or.inr hsT)⟩
  · intro t ht
    change t :t UnionT (traces (P [+] Q) '' X) at ht
    change t :t traces (P [+] Q) (LUB X)
    rw [memT_UnionT hImgOut] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Ext_choice] at htT ⊢
    rcases htT with hs | hs
    · exact Or.inl (hPx.1 _ ⟨x, hx, rfl⟩ hs)
    · exact Or.inr (hQx.1 _ ⟨x, hx, rfl⟩ hs)

/- --------------------------------*
 |          Int_choice            |
 *-------------------------------- -/

theorem continuous_traces_Int_choice
    {P Q : proc p α} :
    continuous (traces P) → continuous (traces Q) →
      continuous (traces (P |~| Q)) := by
  intro hP hQ
  apply continuous_if_cpo
  intro X hX
  have hImgP : traces P '' X ≠ ∅ := image_ne_empty_of_directed (f := traces P) hX
  have hImgQ : traces Q '' X ≠ ∅ := image_ne_empty_of_directed (f := traces Q) hX
  have hImgOut : traces (P |~| Q) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (P |~| Q)) hX
  have hPx : isLUB (traces P (LUB X)) (traces P '' X) := continuous_lub_image hP hX
  have hQx : isLUB (traces Q (LUB X)) (traces Q '' X) := continuous_lub_image hQ hX
  have hPxEq : traces P (LUB X) = UnionT (traces P '' X) :=
    (isLUB_UnionT (T := traces P (LUB X)) (Ts := traces P '' X) hImgP).mp hPx
  have hQxEq : traces Q (LUB X) = UnionT (traces Q '' X) :=
    (isLUB_UnionT (T := traces Q (LUB X)) (Ts := traces Q '' X) hImgQ).mp hQx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionT (T := traces (P |~| Q) (LUB X)) (Ts := traces (P |~| Q) '' X) hImgOut).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (P |~| Q) (LUB X) at ht
    change t :t UnionT (traces (P |~| Q) '' X)
    rw [in_traces_Int_choice] at ht
    rw [memT_UnionT hImgOut]
    rcases ht with hs | hs
    · have hsUnion : t :t UnionT (traces P '' X) := by
        simpa [hPxEq] using hs
      rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact ⟨traces (P |~| Q) x, ⟨x, hx, rfl⟩, (in_traces_Int_choice).mpr (Or.inl hsT)⟩
    · have hsUnion : t :t UnionT (traces Q '' X) := by
        simpa [hQxEq] using hs
      rcases (memT_UnionT hImgQ).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact ⟨traces (P |~| Q) x, ⟨x, hx, rfl⟩, (in_traces_Int_choice).mpr (Or.inr hsT)⟩
  · intro t ht
    change t :t UnionT (traces (P |~| Q) '' X) at ht
    change t :t traces (P |~| Q) (LUB X)
    rw [memT_UnionT hImgOut] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Int_choice] at htT ⊢
    rcases htT with hs | hs
    · exact Or.inl (hPx.1 _ ⟨x, hx, rfl⟩ hs)
    · exact Or.inr (hQx.1 _ ⟨x, hx, rfl⟩ hs)

/- --------------------------------*
 |        Rep_int_choice          |
 *-------------------------------- -/

theorem continuous_traces_Rep_int_choice
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, continuous (traces (Pf c))) →
      continuous (traces (proc.Rep_int_choice C Pf)) := by
  intro hPf
  apply continuous_if_cpo
  intro X hX
  have hImgRep : traces (proc.Rep_int_choice C Pf) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (proc.Rep_int_choice C Pf)) hX
  have hPfLUB : ∀ c, isLUB (traces (Pf c) (LUB X)) (traces (Pf c) '' X) := by
    intro c
    exact continuous_lub_image (hPf c) hX
  have hPfImg : ∀ c, traces (Pf c) '' X ≠ ∅ := by
    intro c
    exact image_ne_empty_of_directed (f := traces (Pf c)) hX
  have hPfEq : ∀ c, traces (Pf c) (LUB X) = UnionT (traces (Pf c) '' X) := by
    intro c
    exact (isLUB_UnionT (T := traces (Pf c) (LUB X)) (Ts := traces (Pf c) '' X) (hPfImg c)).mp
      (hPfLUB c)
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply
    (isLUB_UnionT
      (T := traces (proc.Rep_int_choice C Pf) (LUB X))
      (Ts := traces (proc.Rep_int_choice C Pf) '' X) hImgRep).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (proc.Rep_int_choice C Pf) (LUB X) at ht
    change t :t UnionT (traces (proc.Rep_int_choice C Pf) '' X)
    rw [in_traces_Rep_int_choice_sum] at ht
    rw [memT_UnionT hImgRep]
    rcases hX.1 with ⟨x, hx⟩
    rcases ht with rfl | ⟨c, hc, hs⟩
    · exact ⟨traces (proc.Rep_int_choice C Pf) x, ⟨x, hx, rfl⟩, nilt_in_T⟩
    · have hsUnion : t :t UnionT (traces (Pf c) '' X) := by
        simpa [hPfEq c] using hs
      rcases (memT_UnionT (hPfImg c)).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact
        ⟨traces (proc.Rep_int_choice C Pf) x, ⟨x, hx, rfl⟩,
          (in_traces_Rep_int_choice_sum).mpr (Or.inr ⟨c, hc, hsT⟩)⟩
  · intro t ht
    change t :t UnionT (traces (proc.Rep_int_choice C Pf) '' X) at ht
    change t :t traces (proc.Rep_int_choice C Pf) (LUB X)
    rw [memT_UnionT hImgRep] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Rep_int_choice_sum] at htT ⊢
    rcases htT with rfl | ⟨c, hc, hs⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨c, hc, (hPfLUB c).1 _ ⟨x, hx, rfl⟩ hs⟩

/- --------------------------------*
 |                IF              |
 *-------------------------------- -/

theorem continuous_traces_IF
    {b : Bool} {P Q : proc p α} :
    continuous (traces P) → continuous (traces Q) →
      continuous (traces (IF b THEN P ELSE Q)) := by
  intro hP hQ
  by_cases hb : b
  · simpa [traces, hb] using hP
  · simpa [traces, hb] using hQ

/- --------------------------------*
 |           Parallel             |
 *-------------------------------- -/

theorem continuous_traces_Parallel
    {P Q : proc p α} {X : Set α} :
    continuous (traces P) → continuous (traces Q) →
      continuous (traces (P |[X]| Q)) := by
  intro hP hQ
  have hmonoP : mono (traces P) := continuous_mono hP
  have hmonoQ : mono (traces Q) := continuous_mono hQ
  apply continuous_if_cpo
  intro Xa hXa
  have hImgP : traces P '' Xa ≠ ∅ := image_ne_empty_of_directed (f := traces P) hXa
  have hImgQ : traces Q '' Xa ≠ ∅ := image_ne_empty_of_directed (f := traces Q) hXa
  have hImgOut : traces (P |[X]| Q) '' Xa ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (P |[X]| Q)) hXa
  have hPx : isLUB (traces P (LUB Xa)) (traces P '' Xa) := continuous_lub_image hP hXa
  have hQx : isLUB (traces Q (LUB Xa)) (traces Q '' Xa) := continuous_lub_image hQ hXa
  have hPxEq : traces P (LUB Xa) = UnionT (traces P '' Xa) :=
    (isLUB_UnionT (T := traces P (LUB Xa)) (Ts := traces P '' Xa) hImgP).mp hPx
  have hQxEq : traces Q (LUB Xa) = UnionT (traces Q '' Xa) :=
    (isLUB_UnionT (T := traces Q (LUB Xa)) (Ts := traces Q '' Xa) hImgQ).mp hQx
  refine ⟨LUB Xa, ?_, LUB_is (complete_cpo Xa hXa)⟩
  apply
    (isLUB_UnionT
      (T := traces (P |[X]| Q) (LUB Xa))
      (Ts := traces (P |[X]| Q) '' Xa) hImgOut).mpr
  apply le_antisymm
  · intro u hu
    change u :t traces (P |[X]| Q) (LUB Xa) at hu
    change u :t UnionT (traces (P |[X]| Q) '' Xa)
    rw [in_traces_Parallel] at hu
    rcases hu with ⟨s, t, hup, hs, ht⟩
    have hsUnion : s :t UnionT (traces P '' Xa) := by
      simpa [hPxEq] using hs
    have htUnion : t :t UnionT (traces Q '' Xa) := by
      simpa [hQxEq] using ht
    rcases (memT_UnionT hImgP).mp hsUnion with ⟨T1, hT1, hsT1⟩
    rcases (memT_UnionT hImgQ).mp htUnion with ⟨T2, hT2, htT2⟩
    rcases hT1 with ⟨xb, hxb, rfl⟩
    rcases hT2 with ⟨xc, hxc, rfl⟩
    rcases hXa.2 xb xc hxb hxc with ⟨z, hz, hxbz, hxcz⟩
    rw [memT_UnionT hImgOut]
    refine ⟨traces (P |[X]| Q) z, ⟨z, hz, rfl⟩, ?_⟩
    rw [in_traces_Parallel]
    exact ⟨s, t, hup, hmonoP hxbz hsT1, hmonoQ hxcz htT2⟩
  · intro u hu
    change u :t UnionT (traces (P |[X]| Q) '' Xa) at hu
    change u :t traces (P |[X]| Q) (LUB Xa)
    rw [memT_UnionT hImgOut] at hu
    rcases hu with ⟨T, hT, huT⟩
    rcases hT with ⟨z, hz, rfl⟩
    rw [in_traces_Parallel] at huT ⊢
    rcases huT with ⟨s, t, hup, hs, ht⟩
    exact ⟨s, t, hup, hPx.1 _ ⟨z, hz, rfl⟩ hs, hQx.1 _ ⟨z, hz, rfl⟩ ht⟩

/- --------------------------------*
 |            Hiding              |
 *-------------------------------- -/

theorem continuous_traces_Hiding
    {P : proc p α} {X : Set α} :
    continuous (traces P) →
      continuous (traces (proc.Hiding P X)) := by
  intro hP
  apply continuous_if_cpo
  intro Xa hXa
  have hImgP : traces P '' Xa ≠ ∅ := image_ne_empty_of_directed (f := traces P) hXa
  have hImgOut : traces (proc.Hiding P X) '' Xa ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (proc.Hiding P X)) hXa
  have hPx : isLUB (traces P (LUB Xa)) (traces P '' Xa) := continuous_lub_image hP hXa
  have hPxEq : traces P (LUB Xa) = UnionT (traces P '' Xa) :=
    (isLUB_UnionT (T := traces P (LUB Xa)) (Ts := traces P '' Xa) hImgP).mp hPx
  refine ⟨LUB Xa, ?_, LUB_is (complete_cpo Xa hXa)⟩
  apply
    (isLUB_UnionT
      (T := traces (proc.Hiding P X) (LUB Xa))
      (Ts := traces (proc.Hiding P X) '' Xa) hImgOut).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (proc.Hiding P X) (LUB Xa) at ht
    change t :t UnionT (traces (proc.Hiding P X) '' Xa)
    rw [in_traces_Hiding] at ht
    rw [memT_UnionT hImgOut]
    rcases ht with ⟨s, rfl, hs⟩
    have hsUnion : s :t UnionT (traces P '' Xa) := by
      simpa [hPxEq] using hs
    rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
    rcases hT with ⟨x, hx, rfl⟩
    exact ⟨traces (proc.Hiding P X) x, ⟨x, hx, rfl⟩, (in_traces_Hiding).mpr ⟨s, rfl, hsT⟩⟩
  · intro t ht
    change t :t UnionT (traces (proc.Hiding P X) '' Xa) at ht
    change t :t traces (proc.Hiding P X) (LUB Xa)
    rw [memT_UnionT hImgOut] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Hiding] at htT ⊢
    rcases htT with ⟨s, rfl, hs⟩
    exact ⟨s, rfl, hPx.1 _ ⟨x, hx, rfl⟩ hs⟩

/- --------------------------------*
 |           Renaming             |
 *-------------------------------- -/

theorem continuous_traces_Renaming
    {P : proc p α} {r : Set (α × α)} :
    continuous (traces P) →
      continuous (traces (P [[r]])) := by
  intro hP
  apply continuous_if_cpo
  intro X hX
  have hImgP : traces P '' X ≠ ∅ := image_ne_empty_of_directed (f := traces P) hX
  have hImgOut : traces (P [[r]]) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (P [[r]])) hX
  have hPx : isLUB (traces P (LUB X)) (traces P '' X) := continuous_lub_image hP hX
  have hPxEq : traces P (LUB X) = UnionT (traces P '' X) :=
    (isLUB_UnionT (T := traces P (LUB X)) (Ts := traces P '' X) hImgP).mp hPx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionT (T := traces (P [[r]]) (LUB X)) (Ts := traces (P [[r]]) '' X) hImgOut).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (P [[r]]) (LUB X) at ht
    change t :t UnionT (traces (P [[r]]) '' X)
    rw [in_traces_Renaming] at ht
    rw [memT_UnionT hImgOut]
    rcases ht with ⟨s, hs, htP⟩
    have hsUnion : s :t UnionT (traces P '' X) := by
      simpa [hPxEq] using htP
    rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
    rcases hT with ⟨x, hx, rfl⟩
    exact ⟨traces (P [[r]]) x, ⟨x, hx, rfl⟩, (in_traces_Renaming).mpr ⟨s, hs, hsT⟩⟩
  · intro t ht
    change t :t UnionT (traces (P [[r]]) '' X) at ht
    change t :t traces (P [[r]]) (LUB X)
    rw [memT_UnionT hImgOut] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Renaming] at htT ⊢
    rcases htT with ⟨s, hs, htP⟩
    exact ⟨s, hs, hPx.1 _ ⟨x, hx, rfl⟩ htP⟩

/- --------------------------------*
 |           Seq_compo            |
 *-------------------------------- -/

theorem continuous_traces_Seq_compo
    {P Q : proc p α} :
    continuous (traces P) → continuous (traces Q) →
      continuous (traces (P ;; Q)) := by
  intro hP hQ
  have hmonoP : mono (traces P) := continuous_mono hP
  have hmonoQ : mono (traces Q) := continuous_mono hQ
  apply continuous_if_cpo
  intro X hX
  have hImgP : traces P '' X ≠ ∅ := image_ne_empty_of_directed (f := traces P) hX
  have hImgQ : traces Q '' X ≠ ∅ := image_ne_empty_of_directed (f := traces Q) hX
  have hImgOut : traces (P ;; Q) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (P ;; Q)) hX
  have hPx : isLUB (traces P (LUB X)) (traces P '' X) := continuous_lub_image hP hX
  have hQx : isLUB (traces Q (LUB X)) (traces Q '' X) := continuous_lub_image hQ hX
  have hPxEq : traces P (LUB X) = UnionT (traces P '' X) :=
    (isLUB_UnionT (T := traces P (LUB X)) (Ts := traces P '' X) hImgP).mp hPx
  have hQxEq : traces Q (LUB X) = UnionT (traces Q '' X) :=
    (isLUB_UnionT (T := traces Q (LUB X)) (Ts := traces Q '' X) hImgQ).mp hQx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionT (T := traces (P ;; Q) (LUB X)) (Ts := traces (P ;; Q) '' X) hImgOut).mpr
  apply le_antisymm
  · intro u hu
    change u :t traces (P ;; Q) (LUB X) at hu
    change u :t UnionT (traces (P ;; Q) '' X)
    rw [in_traces_Seq_compo] at hu
    rw [memT_UnionT hImgOut]
    rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hs, ht, hnt⟩
    · have hsUnion : s :t UnionT (traces P '' X) := by
        simpa [hPxEq] using hs
      rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
      rcases hT with ⟨x, hx, rfl⟩
      exact ⟨traces (P ;; Q) x, ⟨x, hx, rfl⟩, (in_traces_Seq_compo).mpr (Or.inl ⟨s, rfl, hsT⟩)⟩
    · have hsUnion : (s ^^^ (Abs_trace [event.Tick] : traceType α)) :t UnionT (traces P '' X) := by
        simpa [hPxEq] using hs
      have htUnion : t :t UnionT (traces Q '' X) := by
        simpa [hQxEq] using ht
      rcases (memT_UnionT hImgP).mp hsUnion with ⟨T1, hT1, hsT1⟩
      rcases (memT_UnionT hImgQ).mp htUnion with ⟨T2, hT2, htT2⟩
      rcases hT1 with ⟨xb, hxb, rfl⟩
      rcases hT2 with ⟨xc, hxc, rfl⟩
      rcases hX.2 xb xc hxb hxc with ⟨z, hz, hxbz, hxcz⟩
      exact
        ⟨traces (P ;; Q) z, ⟨z, hz, rfl⟩,
          (in_traces_Seq_compo).mpr (Or.inr
            ⟨s, t, rfl, hmonoP hxbz hsT1, hmonoQ hxcz htT2, hnt⟩)⟩
  · intro u hu
    change u :t UnionT (traces (P ;; Q) '' X) at hu
    change u :t traces (P ;; Q) (LUB X)
    rw [memT_UnionT hImgOut] at hu
    rcases hu with ⟨T, hT, huT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Seq_compo] at huT ⊢
    rcases huT with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hs, ht, hnt⟩
    · exact Or.inl ⟨s, rfl, hPx.1 _ ⟨x, hx, rfl⟩ hs⟩
    · exact Or.inr ⟨s, t, rfl, hPx.1 _ ⟨x, hx, rfl⟩ hs, hQx.1 _ ⟨x, hx, rfl⟩ ht, hnt⟩

/- --------------------------------*
 |          Depth_rest            |
 *-------------------------------- -/

theorem continuous_traces_Depth_rest
    {P : proc p α} {n : Nat} :
    continuous (traces P) →
      continuous (traces (P |. n)) := by
  intro hP
  apply continuous_if_cpo
  intro X hX
  have hImgP : traces P '' X ≠ ∅ := image_ne_empty_of_directed (f := traces P) hX
  have hImgOut : traces (P |. n) '' X ≠ ∅ :=
    image_ne_empty_of_directed (f := traces (P |. n)) hX
  have hPx : isLUB (traces P (LUB X)) (traces P '' X) := continuous_lub_image hP hX
  have hPxEq : traces P (LUB X) = UnionT (traces P '' X) :=
    (isLUB_UnionT (T := traces P (LUB X)) (Ts := traces P '' X) hImgP).mp hPx
  refine ⟨LUB X, ?_, LUB_is (complete_cpo X hX)⟩
  apply (isLUB_UnionT (T := traces (P |. n) (LUB X)) (Ts := traces (P |. n) '' X) hImgOut).mpr
  apply le_antisymm
  · intro t ht
    change t :t traces (P |. n) (LUB X) at ht
    change t :t UnionT (traces (P |. n) '' X)
    rw [in_traces_Depth_rest] at ht
    rw [memT_UnionT hImgOut]
    have hsUnion : t :t UnionT (traces P '' X) := by
      simpa [hPxEq] using ht.1
    rcases (memT_UnionT hImgP).mp hsUnion with ⟨T, hT, hsT⟩
    rcases hT with ⟨x, hx, rfl⟩
    exact ⟨traces (P |. n) x, ⟨x, hx, rfl⟩, (in_traces_Depth_rest).mpr ⟨hsT, ht.2⟩⟩
  · intro t ht
    change t :t UnionT (traces (P |. n) '' X) at ht
    change t :t traces (P |. n) (LUB X)
    rw [memT_UnionT hImgOut] at ht
    rcases ht with ⟨T, hT, htT⟩
    rcases hT with ⟨x, hx, rfl⟩
    rw [in_traces_Depth_rest] at htT ⊢
    exact ⟨hPx.1 _ ⟨x, hx, rfl⟩ htT.1, htT.2⟩

/- --------------------------------*
 |            variable            |
 *-------------------------------- -/

theorem continuous_traces_variable
    {p0 : p} :
    continuous (traces (proc.Proc_name p0 : proc p α)) := by
  simpa [traces] using
    (continuous_prod_variable (pn := p0) : continuous (fun M : p → domTType α => M p0))

/- --------------------------------*
 |            Procfun             |
 *-------------------------------- -/

theorem continuous_traces
    {P : proc p α} :
    continuous (traces P) := by
  induction P with
  | STOP =>
      exact continuous_traces_STOP
  | SKIP =>
      exact continuous_traces_SKIP
  | DIV =>
      exact continuous_traces_DIV
  | Act_prefix a P ih =>
      exact continuous_traces_Act_prefix ih
  | Ext_pre_choice X Pf ih =>
      exact continuous_traces_Ext_pre_choice (fun a => ih a)
  | Ext_choice P Q ihP ihQ =>
      exact continuous_traces_Ext_choice ihP ihQ
  | Int_choice P Q ihP ihQ =>
      exact continuous_traces_Int_choice ihP ihQ
  | Rep_int_choice C Pf ih =>
      exact continuous_traces_Rep_int_choice (fun c => ih c)
  | «IF» b P Q ihP ihQ =>
      exact continuous_traces_IF ihP ihQ
  | Parallel P X Q ihP ihQ =>
      exact continuous_traces_Parallel ihP ihQ
  | Hiding P X ih =>
      exact continuous_traces_Hiding ih
  | Renaming P r ih =>
      exact continuous_traces_Renaming ih
  | Seq_compo P Q ihP ihQ =>
      exact continuous_traces_Seq_compo ihP ihQ
  | Depth_rest P n ih =>
      exact continuous_traces_Depth_rest ih
  | Proc_name p0 =>
      exact continuous_traces_variable

/- =============================================================*
 |                          [[P]]Tf                            |
 *============================================================= -/

theorem continuous_semTf
    {P : proc p α} :
    continuous (semTf P) := by
  simpa [semTf_def] using (continuous_traces (P := P))

/- =============================================================*
 |                         [[P]]Tfun                           |
 *============================================================= -/

theorem continuous_semTfun
    {Pf : p → proc p α} :
    continuous (semTfun Pf) := by
  apply (prod_continuous).mpr
  intro p0
  simpa [semTfun_def, semTf_def, proj_fun, Function.comp] using
    (continuous_semTf (P := Pf p0))

end
