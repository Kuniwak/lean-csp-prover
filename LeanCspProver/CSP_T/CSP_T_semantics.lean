           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Trace_op
import LeanCspProver.CSP.CSP_syntax
import LeanCspProver.CSP_T.Domain_T_cms

open SumType

noncomputable section

/-
(*****************************************************************

         1. semantic clause
         2.
         3.
         4.

 *****************************************************************)
-/

/-
(*********************************************************
                    semantic clause
 *********************************************************)
-/

def traces (P : proc p α) (M : p → domTType α) : domTType α :=
  match P with
  | .STOP => Abs_domT ({<>} : Set (traceType α))
  | .SKIP =>
      Abs_domT ((({<>} : Set (traceType α)) ∪ ({Abs_trace [event.Tick]} : Set (traceType α))))
  | .DIV => Abs_domT ({<>} : Set (traceType α))
  | .Act_prefix a P =>
      Abs_domT {t | t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t traces P M}
  | proc.Ext_pre_choice X Pf =>
      Abs_domT
        {t | t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t traces (Pf a) M ∧ a ∈ X}
  | .Ext_choice P Q => traces P M UnT traces Q M
  | .Int_choice P Q => traces P M UnT traces Q M
  | proc.Rep_int_choice C Pf =>
      Abs_domT {t | t = <> ∨ ∃ c, c ∈ sumset C ∧ t :t traces (Pf c) M}
  | proc.IF b P Q => if b then traces P M else traces Q M
  | proc.Parallel P X Q =>
      Abs_domT {u | ∃ s t, u ∈ par_tr s X t ∧ s :t traces P M ∧ t :t traces Q M}
  | proc.Hiding P X =>
      Abs_domT {t | ∃ s, t = hide_tr s X ∧ s :t traces P M}
  | proc.Renaming P r =>
      Abs_domT {t | ∃ s, ren_tr s r t ∧ s :t traces P M}
  | proc.Seq_compo P Q =>
      Abs_domT {u |
        (∃ s, u = rmTick s ∧ s :t traces P M) ∨
        (∃ s t : traceType α,
          u = s ^^^ t ∧
          s ^^^ (Abs_trace [event.Tick] : traceType α) :t traces P M ∧
          t :t traces Q M ∧
          noTick s)}
  | proc.Depth_rest P n => traces P M .|. n
  | proc.Proc_name p => M p

/-
(*** for dealing with both !nat and !set ***)
-/

theorem traces_inv_inj [Inhabited β] {f : β → γ} (hf : Function.Injective f)
    {N : Set β} {Pf : β → proc p α} {t : traceType α} {x : p → domTType α} :
    (∃ c : γ, (∃ n, c = f n ∧ n ∈ N) ∧ t :t traces (Pf (Function.invFun f c)) x) ↔
      ∃ z, z ∈ N ∧ t :t traces (Pf z) x := by
  constructor
  · rintro ⟨c, ⟨n, rfl, hn⟩, ht⟩
    rw [Function.leftInverse_invFun hf n] at ht
    exact ⟨n, hn, ht⟩
  · rintro ⟨z, hz, ht⟩
    refine ⟨f z, ⟨z, rfl, hz⟩, ?_⟩
    rw [Function.leftInverse_invFun hf z]
    exact ht

theorem Rep_int_choice_traces_nat (N : Set Nat) (Pf : Nat → proc p α) :
    traces (Rep_int_choice_nat N Pf) =
      fun M => Abs_domT {t | t = <> ∨ ∃ n, n ∈ N ∧ t :t traces (Pf n) M} := by
  funext M
  rw [Rep_int_choice_nat_def]
  simp only [traces, sumset]
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨c, hc, ht⟩)
    · exact Or.inl rfl
    · obtain ⟨n, hn, rfl⟩ := hc
      rw [Function.leftInverse_invFun inj_type2 n] at ht
      exact Or.inr ⟨n, hn, ht⟩
  · rintro (rfl | ⟨n, hn, ht⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨type2 n, ⟨n, hn, rfl⟩, ?_⟩
      rw [Function.leftInverse_invFun inj_type2 n]
      exact ht

theorem Rep_int_choice_traces_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    traces (Rep_int_choice_set Xs Pf) =
      fun M => Abs_domT {t | t = <> ∨ ∃ X, X ∈ Xs ∧ t :t traces (Pf X) M} := by
  funext M
  rw [Rep_int_choice_set_def]
  simp only [traces, sumset]
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨c, hc, ht⟩)
    · exact Or.inl rfl
    · obtain ⟨X, hX, rfl⟩ := hc
      rw [Function.leftInverse_invFun inj_type1 X] at ht
      exact Or.inr ⟨X, hX, ht⟩
  · rintro (rfl | ⟨X, hX, ht⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨type1 X, ⟨X, hX, rfl⟩, ?_⟩
      rw [Function.leftInverse_invFun inj_type1 X]
      exact ht

theorem Rep_int_choice_traces_com_lm [Inhabited α] {X : Set α} {Pf : α → proc p α}
    {t : traceType α} {M : p → domTType α} :
    (∃ z, (∃ a, z = ({a} : Set α) ∧ a ∈ X) ∧ t :t traces (Pf (the_elem z)) M) ↔
      ∃ a, a ∈ X ∧ t :t traces (Pf a) M := by
  constructor
  · rintro ⟨z, ⟨a, rfl, ha⟩, ht⟩
    rw [the_elem_singleton] at ht
    exact ⟨a, ha, ht⟩
  · rintro ⟨a, ha, ht⟩
    refine ⟨{a}, ⟨a, rfl, ha⟩, ?_⟩
    rw [the_elem_singleton]
    exact ht

theorem Rep_int_choice_traces_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    traces (Rep_int_choice_com X Pf) =
      fun M => Abs_domT {t | t = <> ∨ ∃ a, a ∈ X ∧ t :t traces (Pf a) M} := by
  rw [Rep_int_choice_com_def, Rep_int_choice_traces_set]
  funext M
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨Y, ⟨a, ha, rfl⟩, ht⟩)
    · exact Or.inl rfl
    · rw [the_elem_singleton] at ht
      exact Or.inr ⟨a, ha, ht⟩
  · rintro (rfl | ⟨a, ha, ht⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨{a}, ⟨a, ha, rfl⟩, ?_⟩
      rw [the_elem_singleton]
      exact ht

theorem Rep_int_choice_traces_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Function.Injective f) (X : Set β) (Pf : β → proc p α) :
    traces (Rep_int_choice_f f X Pf) =
      fun M => Abs_domT {t | t = <> ∨ ∃ a, a ∈ X ∧ t :t traces (Pf a) M} := by
  rw [Rep_int_choice_f_def, Rep_int_choice_traces_com]
  funext M
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨a, ⟨b, hb, rfl⟩, ht⟩)
    · exact Or.inl rfl
    · rw [Function.leftInverse_invFun hf b] at ht
      exact Or.inr ⟨b, hb, ht⟩
  · rintro (rfl | ⟨b, hb, ht⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨f b, ⟨b, hb, rfl⟩, ?_⟩
      rw [Function.leftInverse_invFun hf b]
      exact ht

/- The Isabelle theorem bundle `Rep_int_choice_traces` is represented by
   `Rep_int_choice_traces_nat`, `Rep_int_choice_traces_set`,
   `Rep_int_choice_traces_com`, and `Rep_int_choice_traces_f`. -/

/- The Isabelle theorem bundle `traces_iff` is represented by the equations for
   `traces` together with the replicated-choice lemmas above. -/

/-==================================================================*
                            traces model
 *==================================================================-/

theorem traces_Int_choice_Ext_choice (P Q : proc p α) :
    traces (P |~| Q) = traces (P [+] Q) := by
  simp [traces]

/-
(*************************************************************
                   set of length of traces+
  lengthset is related to Depth restriction operator (P |. n)
 *************************************************************)
-/

def lengthset (P : proc p α) : (p → domTType α) → Set Nat :=
  fun M => {n | ∃ t, t :t traces P M ∧ (n = lengtht t ∨ n = Nat.succ (lengtht t) ∧ noTick t)}

theorem lengthset_def (P : proc p α) :
    lengthset P =
      fun M => {n | ∃ t, t :t traces P M ∧ (n = lengtht t ∨ n = Nat.succ (lengtht t) ∧ noTick t)} :=
  rfl

/-
(*********************************************************
                     semantics
 *********************************************************)
-/

def semTf (P : proc p α) : (p → domTType α) → domTType α :=
  fun M => traces P M

theorem semTf_def (P : proc p α) :
    semTf P = fun M => traces P M :=
  rfl

def semTfun (Pf : p → proc p α) : (p → domTType α) → (p → domTType α) :=
  fun M p => semTf (Pf p) M

theorem semTfun_def (Pf : p → proc p α) :
    semTfun Pf = fun M p => semTf (Pf p) M :=
  rfl

theorem semTf_semTfun (Pf : p → proc p α) (M : p → domTType α) :
    (fun p => semTf (Pf p) M) = semTfun Pf M :=
  rfl

theorem traces_semTfun (Pf : p → proc p α) (M : p → domTType α) :
    (fun p => traces (Pf p) M) = semTfun Pf M :=
  rfl

section

attribute [local instance] Classical.propDecidable

def semTfix [HasFPmode] (Pf : p → proc p α) : p → domTType α :=
  if FPmode = fpmode.CMSmode then UFP (semTfun Pf) else LFP (semTfun Pf)

theorem semTfix_def [HasFPmode] (Pf : p → proc p α) :
    semTfix Pf = (if FPmode = fpmode.CMSmode then UFP (semTfun Pf) else LFP (semTfun Pf)) :=
  rfl

end

def MT [HasPNfun p α] [HasFPmode] : p → domTType α :=
  semTfix PNfun

theorem MT_def [HasPNfun p α] [HasFPmode] :
    (MT : p → domTType α) = semTfix PNfun :=
  rfl

def semT [HasPNfun p α] [HasFPmode] (P : proc p α) : domTType α :=
  semTf P MT

theorem semT_def [HasPNfun p α] [HasFPmode] (P : proc p α) :
    semT P = semTf P MT :=
  rfl

/-
(*********************************************************
              relations over processes
 *********************************************************)
-/

def refT (P1 : proc p α) (M1 : p → domTType α) (M2 : q → domTType α) (P2 : proc q α) : Prop :=
  semTf P2 M2 <= semTf P1 M1

theorem refT_def (P1 : proc p α) (M1 : p → domTType α) (M2 : q → domTType α) (P2 : proc q α) :
    refT P1 M1 M2 P2 ↔ semTf P2 M2 <= semTf P1 M1 :=
  Iff.rfl

def eqT (P1 : proc p α) (M1 : p → domTType α) (M2 : q → domTType α) (P2 : proc q α) : Prop :=
  semTf P1 M1 = semTf P2 M2

theorem eqT_def (P1 : proc p α) (M1 : p → domTType α) (M2 : q → domTType α) (P2 : proc q α) :
    eqT P1 M1 M2 P2 ↔ semTf P1 M1 = semTf P2 M2 :=
  Iff.rfl

/-
(*********************************************************
        relations over processes (fixed point)
 *********************************************************)
-/

abbrev refTfix [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) : Prop :=
  refT P1 MT MT P2

abbrev eqTfix [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) : Prop :=
  eqT P1 MT MT P2

theorem refT_semT [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) :
    refTfix P1 P2 ↔ semT P2 <= semT P1 :=
  Iff.rfl

theorem eqT_semT [HasPNfun p α] [HasFPmode] (P1 P2 : proc p α) :
    eqTfix P1 P2 ↔ semT P1 = semT P2 :=
  Iff.rfl

/-
(*------------------*
 |      csp law     |
 *------------------*)
-/

theorem cspT_eqT_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT P M1 M2 Q ↔ traces P M1 = traces Q M2 := by
  rfl

theorem cspT_refT_semantics
    {P : proc p α} {Q : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    refT P M1 M2 Q ↔ traces Q M2 <= traces P M1 := by
  rfl

/- The Isabelle theorem bundle `cspT_semantics` is represented by
   `cspT_eqT_semantics` and `cspT_refT_semantics`. -/

theorem cspT_eq_ref_iff {P1 : proc p α} {P2 : proc q α} {M1 : p → domTType α}
    {M2 : q → domTType α} :
    eqT P1 M1 M2 P2 ↔ (refT P1 M1 M2 P2 ∧ refT P2 M2 M1 P1) := by
  constructor
  · intro h
    exact ⟨le_of_eq (Eq.symm h), le_of_eq h⟩
  · rintro ⟨h1, h2⟩
    exact le_antisymm h2 h1

theorem cspT_eq_ref {P1 : proc p α} {P2 : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT P1 M1 M2 P2 → refT P1 M1 M2 P2 := by
  intro h
  exact le_of_eq (Eq.symm h)

theorem cspT_ref_eq {P1 : proc p α} {P2 : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    refT P1 M1 M2 P2 → refT P2 M2 M1 P1 → eqT P1 M1 M2 P2 := by
  intro h1 h2
  exact le_antisymm h2 h1

theorem cspT_reflex_eq_P {P : proc p α} {M : p → domTType α} :
    eqT P M M P := by
  rfl

theorem cspT_reflex_eq_STOP {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.STOP : proc p α) M1 M2 (proc.STOP : proc q α) := by
  simp [eqT, semTf, traces]

theorem cspT_reflex_eq_SKIP {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.SKIP : proc p α) M1 M2 (proc.SKIP : proc q α) := by
  simp [eqT, semTf, traces]

theorem cspT_reflex_eq_DIV {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.DIV : proc p α) M1 M2 (proc.DIV : proc q α) := by
  simp [eqT, semTf, traces]

/- The Isabelle theorem bundle `cspT_reflex_eq` is represented by
   `cspT_reflex_eq_P`, `cspT_reflex_eq_STOP`, `cspT_reflex_eq_SKIP`,
   and `cspT_reflex_eq_DIV`. -/

theorem cspT_reflex_ref_P {P : proc p α} {M : p → domTType α} :
    refT P M M P := by
  exact le_rfl

theorem cspT_reflex_ref_STOP {M1 : p → domTType α} {M2 : q → domTType α} :
    refT (proc.STOP : proc p α) M1 M2 (proc.STOP : proc q α) := by
  simp [refT, semTf, traces]

theorem cspT_reflex_ref_SKIP {M1 : p → domTType α} {M2 : q → domTType α} :
    refT (proc.SKIP : proc p α) M1 M2 (proc.SKIP : proc q α) := by
  simp [refT, semTf, traces]

theorem cspT_reflex_ref_DIV {M1 : p → domTType α} {M2 : q → domTType α} :
    refT (proc.DIV : proc p α) M1 M2 (proc.DIV : proc q α) := by
  simp [refT, semTf, traces]

/- The Isabelle theorem bundle `cspT_reflex_ref` is represented by
   `cspT_reflex_ref_P`, `cspT_reflex_ref_STOP`, `cspT_reflex_ref_SKIP`,
   and `cspT_reflex_ref_DIV`. -/

/- The Isabelle theorem bundle `cspT_reflex` is represented by
   `cspT_reflex_eq` and `cspT_reflex_ref`. -/

theorem cspT_sym {P1 : proc p α} {P2 : proc q α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT P1 M1 M2 P2 → eqT P2 M2 M1 P1 := by
  intro h
  exact Eq.symm h

theorem cspT_symE
    {P1 : proc p α} {P2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α} {Z : Prop} :
    eqT P1 M1 M2 P2 → (eqT P2 M2 M1 P1 → Z) → Z := by
  intro h hZ
  exact hZ (Eq.symm h)

theorem cspT_trans_left_eq
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domTType α} {M2 : q → domTType α} {M3 : r → domTType α} :
    eqT P1 M1 M2 P2 → eqT P2 M2 M3 P3 → eqT P1 M1 M3 P3 := by
  intro h1 h2
  exact Eq.trans h1 h2

theorem cspT_trans_left_ref
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domTType α} {M2 : q → domTType α} {M3 : r → domTType α} :
    refT P1 M1 M2 P2 → refT P2 M2 M3 P3 → refT P1 M1 M3 P3 := by
  intro h1 h2
  exact le_trans h2 h1

/- The Isabelle theorem bundles `cspT_trans_left` and `cspT_trans` are
   represented by `cspT_trans_left_eq` and `cspT_trans_left_ref`. -/

theorem cspT_trans_right_eq
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domTType α} {M2 : q → domTType α} {M3 : r → domTType α} :
    eqT P2 M2 M3 P3 → eqT P1 M1 M2 P2 → eqT P1 M1 M3 P3 := by
  intro h1 h2
  exact Eq.trans h2 h1

theorem cspT_trans_right_ref
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domTType α} {M2 : q → domTType α} {M3 : r → domTType α} :
    refT P2 M2 M3 P3 → refT P1 M1 M2 P2 → refT P1 M1 M3 P3 := by
  intro h1 h2
  exact le_trans h1 h2

/- The Isabelle theorem bundle `cspT_trans_right` is represented by
   `cspT_trans_right_eq` and `cspT_trans_right_ref`. -/

theorem cspT_rw_left_eq_MT [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqTfix P1 P2 → eqTfix P2 P3 → eqTfix P1 P3 := by
  intro h1 h2
  exact Eq.trans h1 h2

theorem cspT_rw_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    eqT P1 M1 M1 P2 → eqT P2 M1 M3 P3 → eqT P1 M1 M3 P3 := by
  intro h1 h2
  exact Eq.trans h1 h2

theorem cspT_rw_left_ref_MT [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqTfix P1 P2 → refTfix P2 P3 → refTfix P1 P3 := by
  intro h1 h2
  exact le_of_le_of_eq h2 (Eq.symm h1)

theorem cspT_rw_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    eqT P1 M1 M1 P2 → refT P2 M1 M3 P3 → refT P1 M1 M3 P3 := by
  intro h1 h2
  exact le_of_le_of_eq h2 (Eq.symm h1)

/- The Isabelle theorem bundle `cspT_rw_left` is represented by
   `cspT_rw_left_eq_MT`, `cspT_rw_left_ref_MT`, `cspT_rw_left_eq`,
   and `cspT_rw_left_ref`. -/

theorem cspT_rw_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    eqT P3 M3 M3 P2 → eqT P1 M1 M3 P2 → eqT P1 M1 M3 P3 := by
  intro h1 h2
  exact Eq.trans h2 (Eq.symm h1)

theorem cspT_rw_right_eq_MT [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqTfix P3 P2 → eqTfix P1 P2 → eqTfix P1 P3 := by
  intro h1 h2
  exact Eq.trans h2 (Eq.symm h1)

theorem cspT_rw_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    eqT P3 M3 M3 P2 → refT P1 M1 M3 P2 → refT P1 M1 M3 P3 := by
  intro h1 h2
  exact le_of_eq_of_le h1 h2

theorem cspT_rw_right_ref_MT [HasPNfun p α] [HasFPmode] {P1 P2 P3 : proc p α} :
    eqTfix P3 P2 → refTfix P1 P2 → refTfix P1 P3 := by
  intro h1 h2
  exact le_of_eq_of_le h1 h2

/- The Isabelle theorem bundle `cspT_rw_right` is represented by
   `cspT_rw_right_eq_MT`, `cspT_rw_right_ref_MT`, `cspT_rw_right_eq`,
   and `cspT_rw_right_ref`. -/

theorem cspT_tr_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    eqT P1 M1 M1 P2 → eqT P2 M1 M3 P3 → eqT P1 M1 M3 P3 := by
  intro h1 h2
  exact Eq.trans h1 h2

theorem cspT_tr_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    refT P1 M1 M1 P2 → refT P2 M1 M3 P3 → refT P1 M1 M3 P3 := by
  intro h1 h2
  exact le_trans h2 h1

/- The Isabelle theorem bundle `cspT_tr_left` is represented by
   `cspT_tr_left_eq` and `cspT_tr_left_ref`. -/

theorem cspT_tr_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    eqT P2 M3 M3 P3 → eqT P1 M1 M3 P2 → eqT P1 M1 M3 P3 := by
  intro h1 h2
  exact Eq.trans h2 h1

theorem cspT_tr_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} :
    refT P2 M3 M3 P3 → refT P1 M1 M3 P2 → refT P1 M1 M3 P3 := by
  intro h1 h2
  exact le_trans h1 h2

/- The Isabelle theorem bundle `cspT_tr_right` is represented by
   `cspT_tr_right_eq` and `cspT_tr_right_ref`. -/

theorem cspT_rw_left_eqE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    eqTfix P1 P3 → eqTfix P1 P2 → (eqTfix P2 P3 → R) → R := by
  intro h1 h2 hR
  exact hR (Eq.trans (Eq.symm h2) h1)

theorem cspT_rw_left_eqE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop} :
    eqT P1 M1 M3 P3 → eqT P1 M1 M1 P2 → (eqT P2 M1 M3 P3 → R) → R := by
  intro h1 h2 hR
  exact hR (Eq.trans (Eq.symm h2) h1)

theorem cspT_rw_left_refE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    refTfix P1 P3 → eqTfix P1 P2 → (refTfix P2 P3 → R) → R := by
  intro h1 h2 hR
  exact hR (le_of_le_of_eq h1 h2)

theorem cspT_rw_left_refE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop} :
    refT P1 M1 M3 P3 → eqT P1 M1 M1 P2 → (refT P2 M1 M3 P3 → R) → R := by
  intro h1 h2 hR
  exact hR (le_of_le_of_eq h1 h2)

/- The Isabelle theorem bundle `cspT_rw_leftE` is represented by
   `cspT_rw_left_eqE_MF`, `cspT_rw_left_refE_MF`, `cspT_rw_left_eqE`,
   and `cspT_rw_left_refE`. -/

theorem cspT_rw_right_eqE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    eqTfix P1 P3 → eqTfix P3 P2 → (eqTfix P1 P2 → R) → R := by
  intro h1 h2 hR
  exact hR (Eq.trans h1 h2)

theorem cspT_rw_right_eqE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop} :
    eqT P1 M1 M3 P3 → eqT P3 M3 M3 P2 → (eqT P1 M1 M3 P2 → R) → R := by
  intro h1 h2 hR
  exact hR (Eq.trans h1 h2)

theorem cspT_rw_right_refE_MF [HasPNfun p α] [HasFPmode]
    {P1 P2 P3 : proc p α} {R : Prop} :
    refTfix P1 P3 → eqTfix P3 P2 → (refTfix P1 P2 → R) → R := by
  intro h1 h2 hR
  exact hR (le_of_eq_of_le (Eq.symm h2) h1)

theorem cspT_rw_right_refE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop} :
    refT P1 M1 M3 P3 → eqT P3 M3 M3 P2 → (refT P1 M1 M3 P2 → R) → R := by
  intro h1 h2 hR
  exact hR (le_of_eq_of_le (Eq.symm h2) h1)

/- The Isabelle theorem bundle `cspT_rw_rightE` is represented by
   `cspT_rw_right_eqE_MF`, `cspT_rw_right_refE_MF`, `cspT_rw_right_eqE`,
   and `cspT_rw_right_refE`. -/

/-
(*-----------------------------------------*
 |                   noPN                  |
 *-----------------------------------------*)
-/

theorem traces_noPN_Constant_lm_EC {X : Set α} {Pf : α → proc p α} :
    (∀ P ∈ Set.range Pf, ∃ T, traces P = fun _ => T) →
      ∃ T2, traces (proc.Ext_pre_choice X Pf) = fun _ => T2 := by
  intro h
  choose T hT using fun a => h (Pf a) ⟨a, rfl⟩
  refine ⟨Abs_domT {t | t = <> ∨ ∃ a s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t T a ∧ a ∈ X}, ?_⟩
  funext M
  simp only [traces, hT]

theorem traces_noPN_Constant_lm_RIC {C : sets_nats α} {Pf : aset_anat α → proc p α} :
    (∀ P ∈ Set.range Pf, ∃ T, traces P = fun _ => T) →
      ∃ T2, traces (proc.Rep_int_choice C Pf) = fun _ => T2 := by
  intro h
  choose T hT using fun c => h (Pf c) ⟨c, rfl⟩
  refine ⟨Abs_domT {t | t = <> ∨ ∃ c, c ∈ sumset C ∧ t :t T c}, ?_⟩
  funext M
  simp only [traces, hT]

theorem traces_noPN_Constant_lm {P : proc p α} :
  noPN P → ∃ T, traces P = fun _ => T := by
  induction P with
  | STOP =>
      intro _
      exact ⟨_, rfl⟩
  | SKIP =>
      intro _
      exact ⟨_, rfl⟩
  | DIV =>
      intro _
      exact ⟨_, rfl⟩
  | Act_prefix a P ih =>
      intro hn
      obtain ⟨T, hT⟩ := ih hn
      refine ⟨Abs_domT {t | t = <> ∨ ∃ s, t = Abs_trace [event.Ev a] ^^^ s ∧ s :t T}, ?_⟩
      funext M
      simp only [traces, hT]
  | Ext_pre_choice X Pf ih =>
      intro hn
      refine traces_noPN_Constant_lm_EC ?_
      rintro P ⟨a, rfl⟩
      exact ih a (hn a)
  | Ext_choice P Q ihP ihQ =>
      intro hn
      obtain ⟨TP, hP⟩ := ihP hn.1
      obtain ⟨TQ, hQ⟩ := ihQ hn.2
      refine ⟨TP UnT TQ, ?_⟩
      funext M
      simp only [traces, hP, hQ]
  | Int_choice P Q ihP ihQ =>
      intro hn
      obtain ⟨TP, hP⟩ := ihP hn.1
      obtain ⟨TQ, hQ⟩ := ihQ hn.2
      refine ⟨TP UnT TQ, ?_⟩
      funext M
      simp only [traces, hP, hQ]
  | Rep_int_choice C Pf ih =>
      intro hn
      refine traces_noPN_Constant_lm_RIC ?_
      rintro P ⟨c, rfl⟩
      exact ih c (hn c)
  | «IF» b P Q ihP ihQ =>
      intro hn
      obtain ⟨TP, hP⟩ := ihP hn.1
      obtain ⟨TQ, hQ⟩ := ihQ hn.2
      refine ⟨if b then TP else TQ, ?_⟩
      funext M
      simp only [traces, hP, hQ]
  | Parallel P X Q ihP ihQ =>
      intro hn
      obtain ⟨TP, hP⟩ := ihP hn.1
      obtain ⟨TQ, hQ⟩ := ihQ hn.2
      refine ⟨Abs_domT {u | ∃ s t, u ∈ par_tr s X t ∧ s :t TP ∧ t :t TQ}, ?_⟩
      funext M
      simp only [traces, hP, hQ]
  | Hiding P X ih =>
      intro hn
      obtain ⟨TP, hP⟩ := ih hn
      refine ⟨Abs_domT {t | ∃ s, t = hide_tr s X ∧ s :t TP}, ?_⟩
      funext M
      simp only [traces, hP]
  | Renaming P r ih =>
      intro hn
      obtain ⟨TP, hP⟩ := ih hn
      refine ⟨Abs_domT {t | ∃ s, ren_tr s r t ∧ s :t TP}, ?_⟩
      funext M
      simp only [traces, hP]
  | Seq_compo P Q ihP ihQ =>
      intro hn
      obtain ⟨TP, hP⟩ := ihP hn.1
      obtain ⟨TQ, hQ⟩ := ihQ hn.2
      refine ⟨Abs_domT {u |
        (∃ s, u = rmTick s ∧ s :t TP) ∨
        (∃ s t : traceType α,
          u = s ^^^ t ∧
          s ^^^ (Abs_trace [event.Tick] : traceType α) :t TP ∧
          t :t TQ ∧
          noTick s)}, ?_⟩
      funext M
      simp only [traces, hP, hQ]
  | Depth_rest P n ih =>
      intro hn
      obtain ⟨TP, hP⟩ := ih hn
      refine ⟨TP .|. n, ?_⟩
      funext M
      simp only [traces, hP]
  | Proc_name x =>
      intro hn
      exact False.elim hn

theorem traces_noPN_Constant {P : proc p α} :
    noPN P → ∃ T, traces P = fun _ => T :=
  traces_noPN_Constant_lm

/-
(*-----------------------------------------*
 |              substitution               |
 *-----------------------------------------*)
-/

theorem traces_subst {P : proc p α} {f : p → proc q α} {M : q → domTType α} :
    traces (P << f) M = traces P (fun q => traces (f q) M) := by
  induction P with
  | STOP => rfl
  | SKIP => rfl
  | DIV => rfl
  | Act_prefix a P ih => simp only [Subst_procfun, traces, ih]
  | Ext_pre_choice X Pf ih => simp only [Subst_procfun, traces, ih]
  | Ext_choice P Q ihP ihQ => simp only [Subst_procfun, traces, ihP, ihQ]
  | Int_choice P Q ihP ihQ => simp only [Subst_procfun, traces, ihP, ihQ]
  | Rep_int_choice C Pf ih => simp only [Subst_procfun, traces, ih]
  | «IF» b P Q ihP ihQ => simp only [Subst_procfun, traces, ihP, ihQ]
  | Parallel P X Q ihP ihQ => simp only [Subst_procfun, traces, ihP, ihQ]
  | Hiding P X ih => simp only [Subst_procfun, traces, ih]
  | Renaming P r ih => simp only [Subst_procfun, traces, ih]
  | Seq_compo P Q ihP ihQ => simp only [Subst_procfun, traces, ihP, ihQ]
  | Depth_rest P n ih => simp only [Subst_procfun, traces, ih]
  | Proc_name x => rfl

theorem semT_subst [HasPNfun q α] [HasFPmode] {P : proc p α} {f : p → proc q α} :
    semT (P << f) = semTf P (fun q => semT (f q)) := by
  exact traces_subst

theorem semT_subst_semTfun [HasPNfun q α] [HasFPmode] {Pf : p → proc p α} {f : p → proc q α} :
    (fun q => semT ((Pf q) << f)) = semTfun Pf (fun q => semT (f q)) := by
  funext x
  exact semT_subst

end
