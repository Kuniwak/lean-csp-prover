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

open Function
open SumType

noncomputable section

/-
(*****************************************************************

         1. mono check of tracesfun
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

theorem mono_traces_STOP : mono (traces (proc.STOP : proc p α)) := by
  intro x y hxy
  simp [traces]

theorem mono_traces_SKIP : mono (traces (proc.SKIP : proc p α)) := by
  intro x y hxy
  simp [traces]

theorem mono_traces_DIV : mono (traces (proc.DIV : proc p α)) := by
  intro x y hxy
  simp [traces]

/-
(*--------------------------------*
 |          Act_prefix            |
 *--------------------------------*)
-/

theorem mono_traces_Act_prefix
    {a : α} {P : proc p α} :
    mono (traces P) → mono (traces (a ~> P)) := by
  intro hP x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Act_prefix] at ht ⊢
  rcases ht with rfl | ⟨s, rfl, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨s, rfl, (subdomT_iff.mp (hP hxy)) s hs⟩

/-
(*--------------------------------*
 |        Ext_pre_choice          |
 *--------------------------------*)
-/

theorem mono_traces_Ext_pre_choice
    {X : Set α} {Pf : α → proc p α} :
    (∀ a, mono (traces (Pf a))) →
      mono (traces (proc.Ext_pre_choice X Pf)) := by
  intro hPf x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Ext_pre_choice] at ht ⊢
  rcases ht with rfl | ⟨a, s, rfl, hs, haX⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨a, s, rfl, (subdomT_iff.mp (hPf a hxy)) s hs, haX⟩

/-
(*--------------------------------*
 |          Ext_choice            |
 *--------------------------------*)
-/

theorem mono_traces_Ext_choice
    {P Q : proc p α} :
    mono (traces P) → mono (traces Q) →
      mono (traces (P [+] Q)) := by
  intro hP hQ x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Ext_choice] at ht ⊢
  exact ht.elim
    (fun hs => Or.inl ((subdomT_iff.mp (hP hxy)) t hs))
    (fun hs => Or.inr ((subdomT_iff.mp (hQ hxy)) t hs))

/-
(*--------------------------------*
 |          Int_choice            |
 *--------------------------------*)
-/

theorem mono_traces_Int_choice
    {P Q : proc p α} :
    mono (traces P) → mono (traces Q) →
      mono (traces (P |~| Q)) := by
  intro hP hQ x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Int_choice] at ht ⊢
  exact ht.elim
    (fun hs => Or.inl ((subdomT_iff.mp (hP hxy)) t hs))
    (fun hs => Or.inr ((subdomT_iff.mp (hQ hxy)) t hs))

/-
(*--------------------------------*
 |        Rep_int_choice          |
 *--------------------------------*)
-/

theorem mono_traces_Rep_int_choice
    {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ c, c ∈ sumset C → mono (traces (Pf c))) →
      mono (traces (proc.Rep_int_choice C Pf)) := by
  intro hPf x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Rep_int_choice_sum] at ht ⊢
  rcases ht with rfl | ⟨c, hc, hs⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨c, hc, (subdomT_iff.mp (hPf c hc hxy)) t hs⟩

/-
(*--------------------------------*
 |              IF                |
 *--------------------------------*)
-/

theorem mono_traces_IF
    {b : Bool} {P Q : proc p α} :
    mono (traces P) → mono (traces Q) →
      mono (traces (IF b THEN P ELSE Q)) := by
  intro hP hQ
  cases b with
  | false => simpa [traces] using hQ
  | true => simpa [traces] using hP

/-
(*--------------------------------*
 |           Parallel             |
 *--------------------------------*)
-/

theorem mono_traces_Parallel
    {P Q : proc p α} {X : Set α} :
    mono (traces P) → mono (traces Q) →
      mono (traces (P |[X]| Q)) := by
  intro hP hQ x y hxy
  apply subdomTI
  intro u hu
  rw [in_traces_Parallel] at hu ⊢
  rcases hu with ⟨s, t, hup, hs, ht⟩
  exact ⟨s, t, hup, (subdomT_iff.mp (hP hxy)) s hs, (subdomT_iff.mp (hQ hxy)) t ht⟩

/-
(*--------------------------------*
 |            Hiding              |
 *--------------------------------*)
-/

theorem mono_traces_Hiding
    {P : proc p α} {X : Set α} :
    mono (traces P) →
      mono (traces (proc.Hiding P X)) := by
  intro hP x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Hiding] at ht ⊢
  rcases ht with ⟨s, rfl, hs⟩
  exact ⟨s, rfl, (subdomT_iff.mp (hP hxy)) s hs⟩

/-
(*--------------------------------*
 |           Renaming             |
 *--------------------------------*)
-/

theorem mono_traces_Renaming
    {P : proc p α} {r : Set (α × α)} :
    mono (traces P) →
      mono (traces (P[[r]])) := by
  intro hP x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Renaming] at ht ⊢
  rcases ht with ⟨s, hs, htP⟩
  exact ⟨s, hs, (subdomT_iff.mp (hP hxy)) s htP⟩

/-
(*--------------------------------*
 |           Seq_compo            |
 *--------------------------------*)
-/

theorem mono_traces_Seq_compo
    {P Q : proc p α} :
    mono (traces P) → mono (traces Q) →
      mono (traces (P ;; Q)) := by
  intro hP hQ x y hxy
  apply subdomTI
  intro u hu
  rw [in_traces_Seq_compo] at hu ⊢
  rcases hu with ⟨s, rfl, hs⟩ | ⟨s, t, rfl, hs, ht, hnt⟩
  · exact Or.inl ⟨s, rfl, (subdomT_iff.mp (hP hxy)) s hs⟩
  · exact Or.inr ⟨s, t, rfl, (subdomT_iff.mp (hP hxy)) _ hs, (subdomT_iff.mp (hQ hxy)) _ ht, hnt⟩

/-
(*--------------------------------*
 |          Depth_rest            |
 *--------------------------------*)
-/

theorem mono_traces_Depth_rest
    {P : proc p α} {n : Nat} :
    mono (traces P) →
      mono (traces (P |. n)) := by
  intro hP x y hxy
  apply subdomTI
  intro t ht
  rw [in_traces_Depth_rest] at ht ⊢
  exact ⟨(subdomT_iff.mp (hP hxy)) t ht.1, ht.2⟩

/-
(*--------------------------------*
 |            variable            |
 *--------------------------------*)
-/

theorem mono_traces_variable
    {p0 : p} :
    mono (traces (proc.Proc_name p0 : proc p α)) := by
  intro x y hxy
  simpa [traces] using hxy p0

/-
(*--------------------------------*
 |            Procfun             |
 *--------------------------------*)
-/

theorem mono_traces
    {P : proc p α} :
    mono (traces P) := by
  induction P with
  | STOP =>
      exact mono_traces_STOP
  | SKIP =>
      exact mono_traces_SKIP
  | DIV =>
      exact mono_traces_DIV
  | Act_prefix a P ih =>
      exact mono_traces_Act_prefix ih
  | Ext_pre_choice X Pf ih =>
      exact mono_traces_Ext_pre_choice (fun a => ih a)
  | Ext_choice P Q ihP ihQ =>
      exact mono_traces_Ext_choice ihP ihQ
  | Int_choice P Q ihP ihQ =>
      exact mono_traces_Int_choice ihP ihQ
  | Rep_int_choice C Pf ih =>
      exact mono_traces_Rep_int_choice (fun c _ => ih c)
  | «IF» b P Q ihP ihQ =>
      exact mono_traces_IF ihP ihQ
  | Parallel P X Q ihP ihQ =>
      exact mono_traces_Parallel ihP ihQ
  | Hiding P X ih =>
      exact mono_traces_Hiding ih
  | Renaming P r ih =>
      exact mono_traces_Renaming ih
  | Seq_compo P Q ihP ihQ =>
      exact mono_traces_Seq_compo ihP ihQ
  | Depth_rest P n ih =>
      exact mono_traces_Depth_rest ih
  | Proc_name p0 =>
      exact mono_traces_variable

/-
(*=============================================================*
 |                          [[P]]Tf                            |
 *=============================================================*)
-/

theorem mono_semTf
    {Pf : p → proc p α} :
    mono (semTfun Pf) := by
  intro x y hxy p0
  simpa [semTfun_def] using (mono_traces (P := Pf p0) hxy)
