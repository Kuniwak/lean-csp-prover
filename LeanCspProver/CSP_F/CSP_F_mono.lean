           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005 (modified)    |
            |                 August 2005 (modified)    |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_domain
import LeanCspProver.CSP_T.CSP_T_mono

open Function
open SumType

noncomputable section

/-
(*****************************************************************

         1. mono check of failuresfun
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(*--------------------------------*
 |        STOP,SKIP,DIV           |
 *--------------------------------*)
-/

theorem mono_failures_STOP : mono (failures (proc.STOP : proc p α)) := by
  intro x y hxy
  simp [failures]

theorem mono_failures_SKIP : mono (failures (proc.SKIP : proc p α)) := by
  intro x y hxy
  simp [failures]

theorem mono_failures_DIV : mono (failures (proc.DIV : proc p α)) := by
  intro x y hxy
  simp [failures]

/-
(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)
-/

theorem mono_failures_Act_prefix
    {a : α} {P : proc p α} :
    mono (failures P) → mono (failures (a ~> P)) := by
  intro hP x y hxy
  apply subsetFI
  intro s X hs
  rw [in_failures_Act_prefix] at hs ⊢
  rcases hs with hs | hs
  · exact Or.inl hs
  · rcases hs with ⟨t, Y, hEq, htY⟩
    exact Or.inr ⟨t, Y, hEq, (subsetF_iff.mp (hP hxy)) t Y htY⟩

/-
(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)
-/

theorem mono_failures_Ext_pre_choice
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, mono (failures (Pf a))) →
      mono (failures (proc.Ext_pre_choice X Pf)) := by
  intro hPf x y hxy
  apply subsetFI
  intro s Y hs
  rw [in_failures_Ext_pre_choice] at hs ⊢
  rcases hs with hs | hs
  · exact Or.inl hs
  · rcases hs with ⟨a, t, Z, hEq, htZ, haX⟩
    exact Or.inr ⟨a, t, Z, hEq, (subsetF_iff.mp (hPf a hxy)) t Z htZ, haX⟩

/-
(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)
-/

theorem mono_failures_Ext_choice
    {P Q : proc p α} :
    mono (traces P) → mono (traces Q) →
      mono (failures P) → mono (failures Q) →
        mono (failures (P [+] Q)) := by
  intro hTP hTQ hFP hFQ x y hxy
  have hfstxy : (fstF ∘ x) <= (fstF ∘ y) := by
    intro p0
    exact mono_fstF (hxy p0)
  apply subsetFI
  intro s X hs
  rw [in_failures_Ext_choice] at hs ⊢
  rcases hs with hs | hs | hs
  · rcases hs with ⟨hsNil, hsP, hsQ⟩
    exact Or.inl ⟨hsNil, (subsetF_iff.mp (hFP hxy)) _ _ hsP, (subsetF_iff.mp (hFQ hxy)) _ _ hsQ⟩
  · rcases hs with ⟨t, htEq, htPQ, htNe⟩
    exact Or.inr <| Or.inl ⟨t, htEq, htPQ.elim
      (fun htP => Or.inl ((subsetF_iff.mp (hFP hxy)) _ _ htP))
      (fun htQ => Or.inr ((subsetF_iff.mp (hFQ hxy)) _ _ htQ)), htNe⟩
  · rcases hs with ⟨Y, hEq, hTick, hSub⟩
    refine Or.inr <| Or.inr ⟨Y, hEq, ?_, hSub⟩
    exact hTick.elim
      (fun htP => Or.inl ((subdomT_iff.mp (hTP hfstxy)) _ htP))
      (fun htQ => Or.inr ((subdomT_iff.mp (hTQ hfstxy)) _ htQ))

/-
(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)
-/

theorem mono_failures_Int_choice
    {P Q : proc p α} :
    mono (failures P) → mono (failures Q) →
      mono (failures (P |~| Q)) := by
  intro hP hQ x y hxy
  apply subsetFI
  intro s X hs
  rw [in_failures_Int_choice] at hs ⊢
  exact hs.elim
    (fun hsP => Or.inl ((subsetF_iff.mp (hP hxy)) _ _ hsP))
    (fun hsQ => Or.inr ((subsetF_iff.mp (hQ hxy)) _ _ hsQ))

/-
(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)
-/

theorem mono_failures_Rep_int_choice
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → mono (failures (Pf c))) →
      mono (failures (proc.Rep_int_choice C Pf)) := by
  intro hPf x y hxy
  apply subsetFI
  intro s X hs
  rw [in_failures_Rep_int_choice_sum] at hs ⊢
  rcases hs with ⟨c, hc, hsC⟩
  exact ⟨c, hc, (subsetF_iff.mp (hPf c hc hxy)) _ _ hsC⟩

/-
(*--------------------------------*
 |              IF                |
 *--------------------------------*)
-/

theorem mono_failures_IF
    {b : Bool} {P Q : proc p α} :
    mono (failures P) → mono (failures Q) →
      mono (failures (IF b THEN P ELSE Q)) := by
  intro hP hQ
  cases b with
  | false => simpa [failures] using hQ
  | true => simpa [failures] using hP

/-
(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)
-/

theorem mono_failures_Parallel
    {P Q : proc p α} {X : Set α} :
    mono (failures P) → mono (failures Q) →
      mono (failures (P |[X]| Q)) := by
  intro hP hQ x y hxy
  apply subsetFI
  intro u Y hs
  rw [in_failures_Parallel] at hs ⊢
  rcases hs with ⟨t, Y1, Z1, hEq, hYZ, s, v, ht, hsY, hvZ⟩
  exact ⟨t, Y1, Z1, hEq, hYZ, s, v, ht,
    (subsetF_iff.mp (hP hxy)) _ _ hsY, (subsetF_iff.mp (hQ hxy)) _ _ hvZ⟩

/-
(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)
-/

theorem mono_failures_Hiding
    {P : proc p α} {X : Set α} :
    mono (failures P) →
      mono (failures (proc.Hiding P X)) := by
  intro hP x y hxy
  apply subsetFI
  intro s Y hs
  rw [in_failures_Hiding] at hs ⊢
  rcases hs with ⟨t, Z, hEq, htZ⟩
  exact ⟨t, Z, hEq, (subsetF_iff.mp (hP hxy)) _ _ htZ⟩

/-
(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)
-/

theorem mono_failures_Renaming
    {P : proc p α} {r : Set (α × α)} :
    mono (failures P) →
      mono (failures (P[[r]])) := by
  intro hP x y hxy
  apply subsetFI
  intro s Y hs
  rw [in_failures_Renaming] at hs ⊢
  rcases hs with ⟨t, u, Z, hEq, hRen, htZ⟩
  exact ⟨t, u, Z, hEq, hRen, (subsetF_iff.mp (hP hxy)) _ _ htZ⟩

/-
(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)
-/

theorem mono_failures_Seq_compo
    {P Q : proc p α} :
    mono (traces P) → mono (failures P) →
      mono (traces Q) → mono (failures Q) →
        mono (failures (P ;; Q)) := by
  intro hTP hFP hTQ hFQ x y hxy
  have hfstxy : (fstF ∘ x) <= (fstF ∘ y) := by
    intro p0
    exact mono_fstF (hxy p0)
  apply subsetFI
  intro u X hs
  rw [in_failures_Seq_compo] at hs ⊢
  rcases hs with hs | hs
  · rcases hs with ⟨t, Y, hEq, htY, hNo⟩
    exact Or.inl ⟨t, Y, hEq, (subsetF_iff.mp (hFP hxy)) _ _ htY, hNo⟩
  · rcases hs with ⟨s, t, Y, hEq, hTick, htY, hNo⟩
    exact Or.inr ⟨s, t, Y, hEq, (subdomT_iff.mp (hTP hfstxy)) _ hTick,
      (subsetF_iff.mp (hFQ hxy)) _ _ htY, hNo⟩

/-
(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)
-/

theorem mono_failures_Depth_rest
    {P : proc p α} {n : Nat} :
    mono (failures P) →
      mono (failures (P |. n)) := by
  intro hP x y hxy
  apply subsetFI
  intro t X hs
  rw [in_failures_Depth_rest] at hs ⊢
  rcases hs with ⟨u, Y, hEq, huY, hRest⟩
  exact ⟨u, Y, hEq, (subsetF_iff.mp (hP hxy)) _ _ huY, hRest⟩

/-
(*--------------------------------*
 |            variable            |
 *--------------------------------*)
-/

theorem mono_failures_variable
    {p0 : p} :
    mono (failures (proc.Proc_name p0 : proc p α)) := by
  intro x y hxy
  apply subsetFI
  intro s X hs
  rw [in_failures_Proc_name] at hs ⊢
  exact (subsetF_iff.mp (mono_sndF (hxy p0))) _ _ hs

/-
(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)
-/

theorem mono_failures
    {P : proc p α} :
    mono (failures P) := by
  induction P with
  | STOP =>
      exact mono_failures_STOP
  | SKIP =>
      exact mono_failures_SKIP
  | DIV =>
      exact mono_failures_DIV
  | Act_prefix a P ih =>
      exact mono_failures_Act_prefix ih
  | Ext_pre_choice X Pf ih =>
      exact mono_failures_Ext_pre_choice (fun a => ih a)
  | Ext_choice P Q ihP ihQ =>
      exact mono_failures_Ext_choice (mono_traces (P := P)) (mono_traces (P := Q)) ihP ihQ
  | Int_choice P Q ihP ihQ =>
      exact mono_failures_Int_choice ihP ihQ
  | Rep_int_choice C Pf ih =>
      exact mono_failures_Rep_int_choice (fun c hc => ih c)
  | «IF» b P Q ihP ihQ =>
      exact mono_failures_IF ihP ihQ
  | Parallel P X Q ihP ihQ =>
      exact mono_failures_Parallel ihP ihQ
  | Hiding P X ih =>
      exact mono_failures_Hiding ih
  | Renaming P r ih =>
      exact mono_failures_Renaming ih
  | Seq_compo P Q ihP ihQ =>
      exact mono_failures_Seq_compo (mono_traces (P := P)) ihP (mono_traces (P := Q)) ihQ
  | Depth_rest P n ih =>
      exact mono_failures_Depth_rest ih
  | Proc_name p0 =>
      exact mono_failures_variable

/-
(*=============================================================*
 |                         [[P]]Ff                             |
 *=============================================================*)
-/

theorem mono_semFf
    {P : proc p α} :
    mono (semFf P) := by
  intro x y hxy
  have hfstxy : (fstF ∘ x) <= (fstF ∘ y) := by
    intro p0
    exact mono_fstF (hxy p0)
  apply (subdomF_decompo (SF := semFf P x) (SE := semFf P y)).2
  constructor
  · simpa [fstF_semFf] using (mono_traces (P := P) hfstxy)
  · simpa [sndF_semFf] using (mono_failures (P := P) hxy)

/-
(*=============================================================*
 |                         [[P]]Ffun                           |
 *=============================================================*)
-/

theorem mono_semFfun
    {Pf : p → proc p α} :
    mono (semFfun Pf) := by
  intro x y hxy p0
  simpa [semFfun_def] using (mono_semFf (P := Pf p0) hxy)

end
