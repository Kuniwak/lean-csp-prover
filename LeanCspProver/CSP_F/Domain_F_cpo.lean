           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                 August 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009-2       |
            |                October 2010  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.Domain_F
import LeanCspProver.CSP_T.Domain_T_cpo
import LeanCspProver.CSP_F.Set_F_cpo
import LeanCspProver.CSP.CPO_pair
import LeanCspProver.CSP.CPO_prod
import LeanCspProver.CSP_T.CSP_T_continuous

open Classical
open Function

noncomputable section

/-
(*****************************************************************

         1.
         2.
         3.
         4.

 *****************************************************************)
-/

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectedly rewrite `UnionT` and `InterT`.        -/
/-                  `Union (B \` A) = (UN x:A. B x)`                -/
/-                  `Inter (B \` A) = (INT x:A. B x)`               -/
/- no simp rules in Isabelle 2017 -/

private abbrev Tickt : traceType α := (Abs_trace [event.Tick] : traceType α)

private theorem image_ne_empty_of_ne_empty {β : Type _} {γ : Type _}
    {f : β → γ} {X : Set β} :
    X ≠ ∅ → f '' X ≠ ∅ := by
  intro hX
  rcases Set.nonempty_iff_ne_empty.mpr hX with ⟨x, hx⟩
  intro hImg
  have : f x ∈ f '' X := ⟨x, hx, rfl⟩
  simpa [hImg] using this

/-
(*********************************************************
                      Bottom in Dom_F
 *********************************************************)
-/

instance instBot0DomF {α : Type _} : bot0 (domFType α) where
  toPartialOrder := inferInstance
  bot := (Abs_domT ({<>} : Set (traceType α))) ,, ({}f : setFType α)

@[simp]
theorem bottom_domF_def {α : Type _} :
    (Bot : domFType α) =
      ((Abs_domT ({<>} : Set (traceType α))) ,, ({}f : setFType α)) :=
  rfl

theorem bottom_domF {α : Type _} :
    ∀ F : domFType α, Bot <= F := by
  intro F
  rw [bottom_domF_def]
  exact BOT_is_bottom_domF

instance instBotDomF {α : Type _} : bot (domFType α) where
  bottom_bot := bottom_domF

/- (*** fstF and sndF ***) -/

@[simp]
theorem fstF_bottom_domF {ι : Type _} {α : Type _} :
    fstF ∘ (Bot : ι → domFType α) = (Bot : ι → domTType α) := by
  funext i
  change fstF (Bot : domFType α) = (Bot : domTType α)
  rw [bottom_domF_def, bottom_domT_def]
  simpa using
    (pairF_fstF
      (S := Abs_domT ({<>} : Set (traceType α)))
      (F := ({}f : setFType α))
      BOT_in_domF)

@[simp]
theorem sndF_bottom_domF {ι : Type _} {α : Type _} :
    sndF ∘ (Bot : ι → domFType α) = (Bot : ι → setFType α) := by
  funext i
  change sndF (Bot : domFType α) = (Bot : setFType α)
  rw [bottom_domF_def, bottom_setF_def]
  simpa using
    (pairF_sndF
      (S := Abs_domT ({<>} : Set (traceType α)))
      (F := ({}f : setFType α))
      BOT_in_domF)

/-
(**********************************************************
      lemmas used in a proof that domain_F is a cpo.
 **********************************************************)
-/

/- LUB_TF TFs is an upper bound of TFs -/

def LUB_TF (TFs : Set (domTsetF α)) : domTsetF α :=
  (UnionT (Prod.fst '' TFs), UnionF (Prod.snd '' TFs))

@[simp]
theorem LUB_TF_def {TFs : Set (domTsetF α)} :
    LUB_TF TFs = (UnionT (Prod.fst '' TFs), UnionF (Prod.snd '' TFs)) :=
  rfl

def LUB_domF (Fs : Set (domFType α)) : domFType α :=
  Abs_domF (LUB_TF (Rep_domF '' Fs))

@[simp]
theorem LUB_domF_def {Fs : Set (domFType α)} :
    LUB_domF Fs = Abs_domF (LUB_TF (Rep_domF '' Fs)) :=
  rfl

/- (************* LUB_TF *************) -/

/- (*** LUB_TF --> LUB ***) -/

theorem LUB_TF_isLUB {TFs : Set (domTsetF α)} :
    TFs ≠ ∅ → isLUB (LUB_TF TFs) TFs := by
  intro hTFs
  apply pair_LUB_decompo.mpr
  constructor
  · simpa [LUB_TF_def] using
      (UnionT_isLUB (Ts := Prod.fst '' TFs)
        (image_ne_empty_of_ne_empty (f := Prod.fst) hTFs))
  · simpa [LUB_TF_def] using (UnionF_isLUB (Fs := Prod.snd '' TFs))

/- (*** LUB --> LUB_TF ***) -/

theorem isLUB_LUB_TF_only_if {TFs : Set (domTsetF α)} {TF : domTsetF α} :
    TFs ≠ ∅ → isLUB TF TFs → TF = LUB_TF TFs := by
  intro hTFs hTF
  exact LUB_unique hTF (LUB_TF_isLUB (TFs := TFs) hTFs)

/- iff -/

theorem isLUB_LUB_TF {TFs : Set (domTsetF α)} {TF : domTsetF α} :
    TFs ≠ ∅ → (isLUB TF TFs ↔ TF = LUB_TF TFs) := by
  intro hTFs
  constructor
  · exact isLUB_LUB_TF_only_if (TFs := TFs) hTFs
  · intro hTF
    simpa [hTF] using (LUB_TF_isLUB (TFs := TFs) hTFs)

/- (*** LUB TF = LUB_TF ***) -/

theorem LUB_LUB_TF {TFs : Set (domTsetF α)} :
    TFs ≠ ∅ → LUB TFs = LUB_TF TFs := by
  intro hTFs
  exact isLUB_LUB (LUB_TF_isLUB (TFs := TFs) hTFs)

/- (****** LUB_TF TFs in domF ******) -/

/- T3_F4 -/

theorem LUB_TF_in_T3_F4 {TFs : Set (domTsetF α)} :
    TFs ≠ ∅ →
      (∀ TF ∈ TFs, TF ∈ domF (α := α)) →
        HC_T3_F4 (LUB_TF TFs) := by
  intro hTFs hTFsIn
  intro s hs
  rcases (memT_UnionT
    (Ts := Prod.fst '' TFs)
    (t := s ^^^ Tickt (α := α))
    (image_ne_empty_of_ne_empty (f := Prod.fst) hTFs)).mp (by
      simpa [LUB_TF_def] using hs.1) with ⟨T, hT, hsT⟩
  rcases hT with ⟨TF, hTF, hEq⟩
  cases hEq
  rcases domTsetF_T3_F4 (TF := TF) (hTFsIn TF hTF) hsT hs.2 with ⟨hF4, hT3⟩
  constructor
  · simpa [LUB_TF_def] using
      (memF_UnionF_if (Fs := Prod.snd '' TFs) ⟨TF, hTF, rfl⟩ hF4)
  · intro X
    simpa [LUB_TF_def] using
      (memF_UnionF_if (Fs := Prod.snd '' TFs) ⟨TF, hTF, rfl⟩ (hT3 X))

/- F3 -/

theorem LUB_TF_in_F3 {TFs : Set (domTsetF α)} :
    TFs ≠ ∅ →
      (∀ TF ∈ TFs, TF ∈ domF (α := α)) →
        HC_F3 (LUB_TF TFs) := by
  intro hTFs hTFsIn
  intro s X Y hsX hNo hY
  change (s, X) :f UnionF (Prod.snd '' TFs) at hsX
  rcases memF_UnionF_only_if hsX with ⟨F, hF, hsXF⟩
  rcases hF with ⟨TF, hTF, hEq⟩
  cases hEq
  have hYTF : ∀ a, a ∈ Y → ¬ memT (s ^^^ (Abs_trace [a] : traceType α)) TF.1 := by
    intro a ha hsa
    apply hY a ha
    simpa [LUB_TF_def] using
      (memT_UnionT_if
        (Ts := Prod.fst '' TFs)
        (T := TF.1)
        ⟨TF, hTF, rfl⟩ hsa)
  simpa [LUB_TF_def] using
    (memF_UnionF_if
      (Fs := Prod.snd '' TFs)
      ⟨TF, hTF, rfl⟩
      (domTsetF_F3 (TF := TF) (hTFsIn TF hTF) hsXF hNo hYTF))

/- T2 -/

theorem LUB_TF_in_T2 {TFs : Set (domTsetF α)} :
    TFs ≠ ∅ →
      (∀ TF ∈ TFs, TF ∈ domF (α := α)) →
        HC_T2 (LUB_TF TFs) := by
  intro hTFs hTFsIn
  intro s X hsX
  change (s, X) :f UnionF (Prod.snd '' TFs) at hsX
  rcases memF_UnionF_only_if hsX with ⟨F, hF, hsXF⟩
  rcases hF with ⟨TF, hTF, hEq⟩
  cases hEq
  simpa [LUB_TF_def] using
    (memT_UnionT_if
      (Ts := Prod.fst '' TFs)
      (T := TF.1)
      ⟨TF, hTF, rfl⟩
      (domTsetF_T2 (TF := TF) (hTFsIn TF hTF) hsXF))

/- (*** LUB_TF TFs in domF ***) -/

theorem LUB_TF_in {TFs : Set (domTsetF α)} :
    TFs ≠ ∅ →
      (∀ TF ∈ TFs, TF ∈ domF (α := α)) →
        LUB_TF TFs ∈ domF (α := α) := by
  intro hTFs hTFsIn
  rw [domF_iff]
  exact ⟨
    LUB_TF_in_T2 (TFs := TFs) hTFs hTFsIn,
    LUB_TF_in_F3 (TFs := TFs) hTFs hTFsIn,
    LUB_TF_in_T3_F4 (TFs := TFs) hTFs hTFsIn⟩

theorem LUB_TF_in_Rep {Fs : Set (domFType α)} :
    Fs ≠ ∅ → LUB_TF (Rep_domF '' Fs) ∈ domF (α := α) := by
  intro hFs
  apply LUB_TF_in (TFs := Rep_domF '' Fs)
  · exact image_ne_empty_of_ne_empty (f := Rep_domF) hFs
  · intro TF hTF
    rcases hTF with ⟨F, hF, rfl⟩
    exact F.2

/- (************* LUB_domF *************) -/

/- isLUB lemma -/

theorem TF_isLUB_domFs {TF : domTsetF α} {Fs : Set (domFType α)} :
    TF ∈ domF (α := α) →
      isLUB TF (Rep_domF '' Fs) →
        isLUB (Abs_domF TF) Fs := by
  intro hTF hLUB
  constructor
  · intro F hF
    rw [subdomF_def]
    simpa [Abs_domF_inverse hTF] using hLUB.1 _ ⟨F, hF, rfl⟩
  · intro F hF
    rw [subdomF_def]
    have hRepUB : isUB (Rep_domF F) (Rep_domF '' Fs) := by
      intro T hT
      rcases hT with ⟨E, hE, rfl⟩
      exact subdomF_def.mp (hF E hE)
    simpa [Abs_domF_inverse hTF] using hLUB.2 _ hRepUB

/- (*** LUB_domF --> LUB ***) -/

theorem LUB_domF_isLUB {Fs : Set (domFType α)} :
    Fs ≠ ∅ → isLUB (LUB_domF Fs) Fs := by
  intro hFs
  apply TF_isLUB_domFs (Fs := Fs)
  · exact LUB_TF_in_Rep (Fs := Fs) hFs
  · simpa [LUB_domF_def, Abs_domF_inverse (LUB_TF_in_Rep (Fs := Fs) hFs)] using
      (LUB_TF_isLUB (TFs := Rep_domF '' Fs)
        (image_ne_empty_of_ne_empty (f := Rep_domF) hFs))

theorem LUB_domF_isLUB_I {Fs : Set (domFType α)} {F : domFType α} :
    Fs ≠ ∅ → F = LUB_domF Fs → isLUB F Fs := by
  intro hFs hF
  simpa [hF] using (LUB_domF_isLUB (Fs := Fs) hFs)

/- (*** LUB --> LUB_domF ***) -/

theorem isLUB_LUB_domF_only_if {Fs : Set (domFType α)} {F : domFType α} :
    Fs ≠ ∅ → isLUB F Fs → F = LUB_domF Fs := by
  intro hFs hF
  exact LUB_unique hF (LUB_domF_isLUB (Fs := Fs) hFs)

/- iff -/

theorem isLUB_LUB_domF {Fs : Set (domFType α)} {F : domFType α} :
    Fs ≠ ∅ → (isLUB F Fs ↔ F = LUB_domF Fs) := by
  intro hFs
  constructor
  · exact isLUB_LUB_domF_only_if (Fs := Fs) hFs
  · intro hF
    simpa [hF] using (LUB_domF_isLUB (Fs := Fs) hFs)

/-
(**********************************************************
                ( domF, <= ) is a CPO
 **********************************************************)
-/

instance instCpoDomF {α : Type _} : cpo (domFType α) where
  toPartialOrder := inferInstance
  toInhabited := inferInstance
  complete_cpo := by
    intro X hX
    exact ⟨LUB_domF X, LUB_domF_isLUB (Fs := X) (Set.nonempty_iff_ne_empty.mp hX.1)⟩

/-
(**********************************************************
             ( domF, <= ) is a pointed CPO
 **********************************************************)
-/

instance instCpoBotDomF {α : Type _} : cpo_bot (domFType α) where
  complete_cpo := by
    intro X hX
    exact ⟨LUB_domF X, LUB_domF_isLUB (Fs := X) (Set.nonempty_iff_ne_empty.mp hX.1)⟩
  bottom_bot := bottom_domF

/-
(**********************************************************
                 continuity of Abs_domF
 **********************************************************)
-/

/- (*** Abs_domF ***) -/

theorem continuous_Abs_domF {δ : Type _} [cpo δ] {f : δ → domTsetF α} :
    (∀ x, f x ∈ domF (α := α)) →
      continuous f →
        continuous (Abs_domF ∘ f) := by
  intro hfIn hf
  apply continuous_if_cpo
  intro X hX
  rcases (continuous_iff.mp hf) X hX with ⟨x, hfx, hx⟩
  refine ⟨x, ?_, hx⟩
  constructor
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    rw [subdomF_def]
    simpa [Function.comp, Abs_domF_inverse (hfIn z), Abs_domF_inverse (hfIn x)] using
      hfx.1 _ ⟨z, hz, rfl⟩
  · intro y hy
    rw [subdomF_def]
    have hUpper : isUB (Rep_domF y) (f '' X) := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      simpa [subdomF_def, Function.comp, Abs_domF_inverse (hfIn w)] using
        (hy _ ⟨w, hw, rfl⟩)
    simpa [Function.comp, Abs_domF_inverse (hfIn x)] using hfx.2 _ hUpper

/- (*** Rep_domF ***) -/

theorem cont_Rep_domF {α : Type _} :
    continuous (Rep_domF : domFType α → domTsetF α) := by
  apply continuous_if_cpo
  intro X hX
  have hXne : X ≠ ∅ := Set.nonempty_iff_ne_empty.mp hX.1
  refine ⟨LUB_domF X, ?_, LUB_domF_isLUB (Fs := X) hXne⟩
  rw [LUB_domF_def, Abs_domF_inverse (LUB_TF_in_Rep (Fs := X) hXne)]
  exact LUB_TF_isLUB (TFs := Rep_domF '' X)
    (image_ne_empty_of_ne_empty (f := Rep_domF) hXne)

/- (*** fstF and sndF ***) -/

theorem fstF_continuous {α : Type _} :
    continuous (fstF : domFType α → domTType α) := by
  simpa [fstF] using
    (compo_continuous
      (f := (Rep_domF : domFType α → domTsetF α))
      (g := Prod.fst)
      cont_Rep_domF fst_continuous)

theorem sndF_continuous {α : Type _} :
    continuous (sndF : domFType α → setFType α) := by
  simpa [sndF] using
    (compo_continuous
      (f := (Rep_domF : domFType α → domTsetF α))
      (g := Prod.snd)
      cont_Rep_domF snd_continuous)

/-
(**********************************************************
                continuity decomposition
 **********************************************************)
-/

/- (*** if ***) -/

theorem continuous_domF {δ : Type _} [cpo δ]
    {f : δ → domTType α} {g : δ → setFType α} :
    (∀ x, (f x, g x) ∈ domF (α := α)) →
      continuous f →
        continuous g →
          continuous (fun x => f x ,, g x) := by
  intro hfg hf hg
  have hpair : continuous (fun x => (f x, g x)) := by
    exact (pair_continuous (h := fun x => (f x, g x))).2 <| by
      constructor
      · simpa [Function.comp] using hf
      · simpa [Function.comp] using hg
  simpa [pairF, Function.comp] using
    (continuous_Abs_domF (f := fun x => (f x, g x)) hfg hpair)

theorem continuous_domF_decompo_if {δ : Type _} [cpo δ]
    {f : δ → domTType α} {g : δ → setFType α} :
    (∀ x, (f x, g x) ∈ domF (α := α)) →
      continuous f →
        continuous g →
          continuous (fun x => f x ,, g x) :=
  continuous_domF

/- (*** only if ***) -/

private theorem continuous_domF_decompo_only_if_lm {δ : Type _} [cpo δ]
    {f : δ → domTType α} {g : δ → setFType α} :
    continuous (fun x => (f x, g x)) →
      continuous f ∧ continuous g := by
  intro hfg
  simpa [Function.comp] using
    (pair_continuous (h := fun x => (f x, g x))).1 hfg

theorem continuous_domF_decompo_only_if {δ : Type _} [cpo δ]
    {f : δ → domTType α} {g : δ → setFType α} :
    (∀ x, (f x, g x) ∈ domF (α := α)) →
      continuous (fun x => f x ,, g x) →
        continuous f ∧ continuous g := by
  intro hfg hpair
  have hrep : continuous (Rep_domF ∘ fun x => f x ,, g x) :=
    compo_continuous hpair cont_Rep_domF
  have hEq : (Rep_domF ∘ fun x => f x ,, g x) = fun x => (f x, g x) := by
    funext x
    simp [Function.comp, pairF, hfg x, Abs_domF_inverse]
  exact continuous_domF_decompo_only_if_lm (hEq ▸ hrep)

theorem continuous_domF_decompo {δ : Type _} [cpo δ]
    {f : δ → domTType α} {g : δ → setFType α} :
    (∀ x, (f x, g x) ∈ domF (α := α)) →
      (continuous (fun x => f x ,, g x) ↔ continuous f ∧ continuous g) := by
  intro hfg
  constructor
  · exact continuous_domF_decompo_only_if (f := f) (g := g) hfg
  · intro h
    exact continuous_domF (f := f) (g := g) hfg h.1 h.2

/-
(**********************************************************
                continuity of (op o fstF)
 **********************************************************)
-/

private theorem fstF_isLUB_image {Fs : Set (domFType α)} {F : domFType α} :
    isLUB F Fs → isLUB (fstF F) (fstF '' Fs) := by
  intro hF
  constructor
  · intro T hT
    rcases hT with ⟨SF, hSF, rfl⟩
    exact (mono_fstF (α := α)) (hF.1 SF hSF)
  · intro T hT
    have hPairDom : (T, maxFof T) ∈ domF (α := α) := maxFof_domF (T := T)
    have hUpper : isUB (T ,, maxFof T) Fs := by
      intro SF hSF
      have hfst : fstF SF <= T := hT _ ⟨SF, hSF, rfl⟩
      have hsnd : sndF SF <= maxFof T := by
        apply subsetFI
        intro s X hsX
        exact maxFof_max (T := T) (X := X) (hfst (pairF_domF_T2 (SF := SF) hsX))
      apply (subdomF_decompo (SF := SF) (SE := T ,, maxFof T)).2
      constructor
      · simpa [pairF_fstF (hSF := hPairDom)] using hfst
      · simpa [pairF_sndF (hSF := hPairDom)] using hsnd
    have hfst : fstF F <= fstF (T ,, maxFof T) :=
      (subdomF_decompo (SF := F) (SE := T ,, maxFof T)).1 (hF.2 _ hUpper) |>.1
    simpa [pairF_fstF (hSF := hPairDom)] using hfst

theorem continuous_op_fstF {ι : Type _} {α : Type _} :
    continuous (fun y : ι → domFType α => fstF ∘ y) := by
  apply prod_continuous_if
  intro i
  simpa [Function.comp] using
    (compo_continuous
      (f := fun y : ι → domFType α => y i)
      (g := fstF)
      (continuous_prod_variable (α := domFType α) i)
      fstF_continuous)

/-
(**********************************************************
              fstF-distribution over LUB
 **********************************************************)
-/

private theorem hasLUB_fun_domF_of_nonempty {ι : Type _} {X : Set (ι → domFType α)} :
    X ≠ ∅ → hasLUB X := by
  intro hX
  refine ⟨fun i => LUB_domF (proj_fun i '' X), ?_⟩
  apply prod_LUB_decompo.mpr
  intro i
  exact LUB_domF_isLUB (Fs := proj_fun i '' X)
    (image_ne_empty_of_ne_empty (f := proj_fun i) hX)

private theorem hasLUB_fun_domT_of_nonempty {ι : Type _} {X : Set (ι → domTType α)} :
    X ≠ ∅ → hasLUB X := by
  intro hX
  refine ⟨fun i => UnionT (proj_fun i '' X), ?_⟩
  apply prod_LUB_decompo.mpr
  intro i
  exact UnionT_isLUB (Ts := proj_fun i '' X)
    (image_ne_empty_of_ne_empty (f := proj_fun i) hX)

theorem dist_fstF_LUB {ι : Type _} {α : Type _} {X : Set (ι → domFType α)} :
    X ≠ ∅ → fstF ∘ LUB X = LUB ((fun y : ι → domFType α => fstF ∘ y) '' X) := by
  intro hX
  let Y : Set (ι → domTType α) := (fun y : ι → domFType α => fstF ∘ y) '' X
  have hLUBX : hasLUB X := hasLUB_fun_domF_of_nonempty (X := X) hX
  have hLUBY : hasLUB Y := by
    apply hasLUB_fun_domT_of_nonempty (X := Y)
    simpa [Y] using image_ne_empty_of_ne_empty
      (f := fun y : ι → domFType α => fstF ∘ y) hX
  apply (isLUB_to_LUB (X := Y) (x := fstF ∘ LUB X) hLUBY).mp
  apply prod_LUB_decompo.mpr
  intro i
  have hXi : isLUB ((LUB X) i) (proj_fun i '' X) := by
    exact (prod_LUB_decompo.mp (LUB_is hLUBX)) i
  simpa [Y, Function.comp, Set.image_image, proj_fun] using
    (fstF_isLUB_image (Fs := proj_fun i '' X) (F := (LUB X) i) hXi)

/-(****************** to add them again ******************)
declare Union_image_eq [simp]
declare Inter_image_eq [simp]
-/
/-
declare Sup_image_eq [simp]
declare Inf_image_eq [simp]
-/

end
