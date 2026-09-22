           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law
import LeanCspProver.CSP_T.CSP_T_law_aux

open Function
open SumType

noncomputable section

/-
(*---------------------------------------------------------------*
 |                                                               |
 |           convenient laws, especially for tactics             |
 |                                                               |
 *---------------------------------------------------------------*)

(*****************************************************************
                            Internal
 *****************************************************************)
-/

/-
(*------------------*
 |     singleton    |
 *------------------*)

(*** ! :{a} ***)
-/

theorem cspF_Rep_int_choice_sum1_singleton
    {c : Set α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice (type1 ({c} : Set (Set α))) Pf) M M (Pf (type1 c)) := by
  apply cspF_Rep_int_choice_sum_const
  · simp [sumset]
  · intro d hd
    have hd' : d = type1 c := by
      simpa [sumset] using hd
    simp [hd']

theorem cspF_Rep_int_choice_sum2_singleton
    {c : Nat} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice (type2 ({c} : Set Nat)) Pf) M M (Pf (type2 c)) := by
  apply cspF_Rep_int_choice_sum_const
  · simp [sumset]
  · intro d hd
    have hd' : d = type2 c := by
      simpa [sumset] using hd
    simp [hd']

theorem cspF_Rep_int_choice_nat_singleton
    {n : Nat} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat ({n} : Set Nat) Pf) M M (Pf n) := by
  apply cspF_Rep_int_choice_nat_const
  · simp
  · intro m hm
    rcases Set.mem_singleton_iff.mp hm with rfl
    rfl

theorem cspF_Rep_int_choice_set_singleton
    {X : Set α} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set ({X} : Set (Set α)) Pf) M M (Pf X) := by
  apply cspF_Rep_int_choice_set_const
  · simp
  · intro Y hY
    rcases Set.mem_singleton_iff.mp hY with rfl
    rfl

theorem cspF_Rep_int_choice_com_singleton
    {a : α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com ({a} : Set α) Pf) M M (Pf a) := by
  apply cspF_Rep_int_choice_com_const
  · simp
  · intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    rfl

theorem cspF_Rep_int_choice_f_singleton [Inhabited β]
    {f : β → α} (hf : Injective f) {x : β} {Pf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f ({x} : Set β) Pf) M M (Pf x) := by
  apply cspF_Rep_int_choice_f_const hf
  · simp
  · intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rfl

/- The Isabelle theorem bundle `cspF_Rep_int_choice_singleton` is represented by
   `cspF_Rep_int_choice_sum1_singleton`,
   `cspF_Rep_int_choice_sum2_singleton`,
   `cspF_Rep_int_choice_nat_singleton`,
   `cspF_Rep_int_choice_set_singleton`,
   `cspF_Rep_int_choice_com_singleton`, and
   `cspF_Rep_int_choice_f_singleton`. -/

theorem cspF_Rep_int_choice_const_sum_rule
    {C : sets_nats α} {P : proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C (fun _ => P)) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α) P) := by
  cspF_auto

theorem cspF_Rep_int_choice_const_nat_rule
    {N : Set Nat} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N (fun _ => P)) M M
      (procIte (N = ∅) (proc.DIV : proc p α) P) := by
  cspF_auto

theorem cspF_Rep_int_choice_const_set_rule
    {Xs : Set (Set α)} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs (fun _ => P)) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α) P) := by
  cspF_auto

theorem cspF_Rep_int_choice_const_com_rule
    {X : Set α} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X (fun _ => P)) M M
      (procIte (X = ∅) (proc.DIV : proc p α) P) := by
  cspF_auto

theorem cspF_Rep_int_choice_const_f_rule [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f X (fun _ => P)) M M
      (procIte (X = ∅) (proc.DIV : proc p α) P) := by
  -- `in_failures_Rep_int_choice_f` needs `Injective f`; go through the `_com` form
  rw [Rep_int_choice_f_def]
  by_cases h : X = ∅
  · subst h
    simp only [Set.image_empty, procIte]
    cspF_auto
  · have h' : f '' X ≠ ∅ := by
      simpa [Set.image_eq_empty] using h
    simp only [procIte, if_neg h]
    cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_const_rule` is represented by
   `cspF_Rep_int_choice_const_sum_rule`,
   `cspF_Rep_int_choice_const_nat_rule`,
   `cspF_Rep_int_choice_const_set_rule`,
   `cspF_Rep_int_choice_const_com_rule`, and
   `cspF_Rep_int_choice_const_f_rule`. -/

/- The Isabelle theorem bundle `cspF_Int_choice_rule` is represented by
   `cspF_Rep_int_choice_sum_DIV`, `cspF_Rep_int_choice_nat_DIV`,
   `cspF_Rep_int_choice_set_DIV`, `cspF_Rep_int_choice_com_DIV`,
   `cspF_Rep_int_choice_f_DIV`, `cspF_Rep_int_choice_sum1_singleton`,
   `cspF_Rep_int_choice_sum2_singleton`, `cspF_Rep_int_choice_nat_singleton`,
   `cspF_Rep_int_choice_set_singleton`, `cspF_Rep_int_choice_com_singleton`,
   `cspF_Rep_int_choice_f_singleton`, `cspF_Int_choice_idem`,
   `cspF_Rep_int_choice_const_sum_rule`, `cspF_Rep_int_choice_const_nat_rule`,
   `cspF_Rep_int_choice_const_set_rule`, `cspF_Rep_int_choice_const_com_rule`,
   and `cspF_Rep_int_choice_const_f_rule`. -/

/-
(*****************************************************************
                          External
 *****************************************************************)

(* to make produced process be concrete *)
-/

theorem cspF_Ext_pre_choice_empty_DIV
    {Pf : α → proc p α} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (proc.Ext_pre_choice (∅ : Set α) Pf) M1 M2
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => (proc.DIV : proc q α))) := by
  exact cspF_trans_left_eq (cspF_sym (cspF_STOP_step (Pf := Pf) (M1 := M1) (M2 := M1)))
    (cspF_STOP_step_DIV (M1 := M1) (M2 := M2))

theorem cspF_Ext_choice_unit_l_hsf
    {Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice (∅ : Set α) Qf) [+] P) M M P := by
  have h₁ :
      eqF (proc.Ext_pre_choice (∅ : Set α) Qf) M M (proc.STOP : proc p α) :=
    cspF_sym (cspF_STOP_step (Pf := Qf) (M1 := M) (M2 := M))
  have h₂ :
      eqF ((proc.Ext_pre_choice (∅ : Set α) Qf) [+] P) M M ((proc.STOP : proc p α) [+] P) :=
    cspF_Ext_choice_cong h₁ cspF_reflex_eq_P
  exact cspF_trans_left_eq h₂ cspF_Ext_choice_unit_l

theorem cspF_Ext_choice_unit_r_hsf
    {Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] proc.Ext_pre_choice (∅ : Set α) Qf) M M P := by
  exact cspF_trans_left_eq cspF_Ext_choice_commut cspF_Ext_choice_unit_l_hsf

/- The Isabelle theorem bundle `cspF_Ext_choice_rule` is represented by
   `cspF_Ext_pre_choice_empty_DIV`, `cspF_Ext_choice_unit_l`,
   `cspF_Ext_choice_unit_l_hsf`, `cspF_Ext_choice_unit_r`,
   `cspF_Ext_choice_unit_r_hsf`, and `cspF_Ext_choice_idem`. -/

/- The Isabelle theorem bundle `cspF_choice_rule` is represented by
   `cspF_Int_choice_rule` and `cspF_Ext_choice_rule`. -/

/-
(*****************************************************************
                          Timeout
 *****************************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(*** <= Timeout ***)
-/

theorem cspF_Timeout_right
    {P : proc p α} {Q1 Q2 : proc q α} {M1 : p → domFType α} {M2 : q → domFType α}
    (h1 : refF P M1 M2 Q1) (h2 : refF P M1 M2 Q2) :
    refF P M1 M2 (Q1 [> Q2) := by
  have hDist :
      eqF (((Q1 |~| (proc.STOP : proc q α)) [+] Q2)) M2 M2
        ((Q1 [+] Q2) |~| ((proc.STOP : proc q α) [+] Q2)) := by
    simpa using
      (cspF_Ext_choice_dist_l
        (P1 := Q1) (P2 := (proc.STOP : proc q α)) (Q := Q2) (M := M2))
  have hLeft : refF P M1 M2 (Q1 [+] Q2) :=
    cspF_Ext_choice_right h1 h2
  have hRight : refF P M1 M2 (((proc.STOP : proc q α) [+] Q2)) :=
    cspF_rw_right_ref cspF_Ext_choice_unit_l h2
  have hRef :
      refF P M1 M2 ((Q1 [+] Q2) |~| ((proc.STOP : proc q α) [+] Q2)) :=
    cspF_Int_choice_right hLeft hRight
  simpa [Timeout_abb] using cspF_rw_right_ref hDist hRef

/-
(*** STOP [> P  =  P ***)
-/

theorem cspF_STOP_Timeout
    {P : proc p α} {M : p → domFType α} :
    eqF ((proc.STOP : proc p α) [> P) M M P := by
  have h₁ :
      eqF (((proc.STOP : proc p α) |~| proc.STOP) [+] P) M M ((proc.STOP : proc p α) [+] P) :=
    cspF_Ext_choice_cong cspF_Int_choice_idem cspF_reflex_eq_P
  exact cspF_trans_left_eq h₁ cspF_Ext_choice_unit_l

/-
(*================================================*
 |                                                |
 |               auxiliary step laws              |
 |                                                |
 *================================================*)

(* split + resolve *)
-/

private def cspF_Parallel_Timeout_split_resolve_rhs
    (X Y Z : Set α) (Pf Qf : α → proc p α) (P Q : proc p α) : proc p α :=
  Timeout
    (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
      procIte (x ∈ X) (Pf x |[X]| Qf x)
        (procIte (x ∈ Y ∧ x ∈ Z)
          ((Pf x |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) |~|
            ((((proc.Ext_pre_choice Y Pf) [+] P) |[X]| Qf x)))
          (procIte (x ∈ Y)
            (Pf x |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q))
            ((((proc.Ext_pre_choice Y Pf) [+] P) |[X]| Qf x)))))
    (((P |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) |~|
      ((((proc.Ext_pre_choice Y Pf) [+] P) |[X]| Q))))

private def cspF_Parallel_Timeout_input_resolve_l_rhs
    (X Y Z : Set α) (Pf Qf : α → proc p α) (P : proc p α) : proc p α :=
  Timeout
    (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
      procIte (x ∈ X) (Pf x |[X]| Qf x)
        (procIte (x ∈ Y ∧ x ∈ Z)
          ((Pf x |[X]| proc.Ext_pre_choice Z Qf) |~|
            ((((proc.Ext_pre_choice Y Pf) [+] P) |[X]| Qf x)))
          (procIte (x ∈ Y)
            (Pf x |[X]| proc.Ext_pre_choice Z Qf)
            ((((proc.Ext_pre_choice Y Pf) [+] P) |[X]| Qf x)))))
    ((P |[X]| proc.Ext_pre_choice Z Qf))

private def cspF_Parallel_Timeout_input_resolve_r_rhs
    (X Y Z : Set α) (Pf Qf : α → proc p α) (Q : proc p α) : proc p α :=
  Timeout
    (proc.Ext_pre_choice ((X ∩ Y ∩ Z) ∪ (Y \ X) ∪ (Z \ X)) fun x =>
      procIte (x ∈ X) (Pf x |[X]| Qf x)
        (procIte (x ∈ Y ∧ x ∈ Z)
          ((Pf x |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) |~|
            ((proc.Ext_pre_choice Y Pf |[X]| Qf x)))
          (procIte (x ∈ Y)
            (Pf x |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q))
            ((proc.Ext_pre_choice Y Pf |[X]| Qf x)))))
    ((proc.Ext_pre_choice Y Pf |[X]| Q))

-- Algebraic proof following the Isabelle original (CSP_F_law_aux.thy):
-- resolve `[+]` into `[>` on both sides, apply `cspF_Parallel_Timeout_split`,
-- then rewrite `[>` back to `[+]` inside the branches by congruence.
theorem cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV
    {P Q : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (P = proc.SKIP ∨ P = proc.DIV) →
      (Q = proc.SKIP ∨ Q = proc.DIV) →
        eqF (((proc.Ext_pre_choice Y Pf) [+] P) |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) M M
          (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf P Q) := by
  intro hP hQ
  rw [cspF_Parallel_Timeout_split_resolve_rhs]
  have hresP := cspF_Ext_choice_SKIP_or_DIV_resolve
    (P := proc.Ext_pre_choice Y Pf) (M := M) hP
  have hresQ := cspF_Ext_choice_SKIP_or_DIV_resolve
    (P := proc.Ext_pre_choice Z Qf) (M := M) hQ
  refine cspF_rw_left_eq (cspF_Parallel_cong rfl hresP hresQ) ?_
  refine cspF_rw_left_eq cspF_Parallel_Timeout_split ?_
  refine cspF_Timeout_cong
    (cspF_Ext_pre_choice_cong rfl fun a _ => ?_)
    (cspF_Int_choice_cong
      (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hresQ))
      (cspF_Parallel_cong rfl (cspF_sym hresP) cspF_reflex_eq_P))
  exact cspF_procIte_cong cspF_reflex_eq_P
    (cspF_procIte_cong
      (cspF_Int_choice_cong
        (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hresQ))
        (cspF_Parallel_cong rfl (cspF_sym hresP) cspF_reflex_eq_P))
      (cspF_procIte_cong
        (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hresQ))
        (cspF_Parallel_cong rfl (cspF_sym hresP) cspF_reflex_eq_P)))

theorem cspF_Parallel_Timeout_split_resolve_SKIP_SKIP
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.SKIP)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.SKIP proc.SKIP) :=
  cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inl rfl) (Or.inl rfl)

theorem cspF_Parallel_Timeout_split_resolve_DIV_DIV
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.DIV)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.DIV proc.DIV) :=
  cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inr rfl) (Or.inr rfl)

theorem cspF_Parallel_Timeout_split_resolve_SKIP_DIV
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.DIV)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.SKIP proc.DIV) :=
  cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inl rfl) (Or.inr rfl)

theorem cspF_Parallel_Timeout_split_resolve_DIV_SKIP
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.SKIP)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.DIV proc.SKIP) :=
  cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inr rfl) (Or.inl rfl)

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_split_resolve` is represented by
   `cspF_Parallel_Timeout_split_resolve_SKIP_SKIP`,
   `cspF_Parallel_Timeout_split_resolve_DIV_DIV`,
   `cspF_Parallel_Timeout_split_resolve_SKIP_DIV`, and
   `cspF_Parallel_Timeout_split_resolve_DIV_SKIP`. -/

/-
(* input + resolve *)
-/

-- Algebraic proof; see `cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV`.
theorem cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l
    {P : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (P = proc.SKIP ∨ P = proc.DIV) →
      eqF (((proc.Ext_pre_choice Y Pf) [+] P) |[X]| proc.Ext_pre_choice Z Qf) M M
        (cspF_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf P) := by
  intro hP
  rw [cspF_Parallel_Timeout_input_resolve_l_rhs]
  have hresP := cspF_Ext_choice_SKIP_or_DIV_resolve
    (P := proc.Ext_pre_choice Y Pf) (M := M) hP
  refine cspF_rw_left_eq (cspF_Parallel_cong rfl hresP cspF_reflex_eq_P) ?_
  refine cspF_rw_left_eq cspF_Parallel_Timeout_input_l ?_
  refine cspF_Timeout_cong
    (cspF_Ext_pre_choice_cong rfl fun a _ => ?_) cspF_reflex_eq_P
  exact cspF_procIte_cong cspF_reflex_eq_P
    (cspF_procIte_cong
      (cspF_Int_choice_cong cspF_reflex_eq_P
        (cspF_Parallel_cong rfl (cspF_sym hresP) cspF_reflex_eq_P))
      (cspF_procIte_cong cspF_reflex_eq_P
        (cspF_Parallel_cong rfl (cspF_sym hresP) cspF_reflex_eq_P)))

-- Algebraic proof; see `cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV`.
theorem cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r
    {Q : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV) →
      eqF (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) M M
        (cspF_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf Q) := by
  intro hQ
  rw [cspF_Parallel_Timeout_input_resolve_r_rhs]
  have hresQ := cspF_Ext_choice_SKIP_or_DIV_resolve
    (P := proc.Ext_pre_choice Z Qf) (M := M) hQ
  refine cspF_rw_left_eq (cspF_Parallel_cong rfl cspF_reflex_eq_P hresQ) ?_
  refine cspF_rw_left_eq cspF_Parallel_Timeout_input_r ?_
  refine cspF_Timeout_cong
    (cspF_Ext_pre_choice_cong rfl fun a _ => ?_) cspF_reflex_eq_P
  exact cspF_procIte_cong cspF_reflex_eq_P
    (cspF_procIte_cong
      (cspF_Int_choice_cong
        (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hresQ))
        cspF_reflex_eq_P)
      (cspF_procIte_cong
        (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hresQ))
        cspF_reflex_eq_P))

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV` is represented by
   `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l` and
   `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r`. -/

theorem cspF_Parallel_Timeout_input_resolve_SKIP_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]| proc.Ext_pre_choice Z Qf) M M
      (cspF_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf proc.SKIP) :=
  cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l (Or.inl rfl)

theorem cspF_Parallel_Timeout_input_resolve_DIV_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]| proc.Ext_pre_choice Z Qf) M M
      (cspF_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf proc.DIV) :=
  cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l (Or.inr rfl)

theorem cspF_Parallel_Timeout_input_resolve_SKIP_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] (proc.SKIP : proc p α))) M M
      (cspF_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf proc.SKIP) :=
  cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r (Or.inl rfl)

theorem cspF_Parallel_Timeout_input_resolve_DIV_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] (proc.DIV : proc p α))) M M
      (cspF_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf proc.DIV) :=
  cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r (Or.inr rfl)

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_input_resolve` is represented by
   `cspF_Parallel_Timeout_input_resolve_SKIP_l`,
   `cspF_Parallel_Timeout_input_resolve_SKIP_r`,
   `cspF_Parallel_Timeout_input_resolve_DIV_l`, and
   `cspF_Parallel_Timeout_input_resolve_DIV_r`. -/

/-
(**************** |[X]| + input/output prefix ****************)
-/

/- Lean note:
   Isabelle derives the four laws below on the fly inside `cspF_hsf`, by
   combining `cspF_Parallel_Dist_com`, `cspF_Act_prefix_step` and
   `cspF_Parallel_step` and then simplifying the resulting event sets.
   The Lean port has no such tactic, so the composite is recorded here as
   named laws.  They say that when a process offering the inputs `A`
   synchronises (over an alphabet `X` containing `A`) with a process
   offering the outputs `B ⊆ A`, the result is the internal choice over
   `B` of the componentwise parallel compositions. -/

theorem cspF_Parallel_Ext_Int_pre_choice
    {A B X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α}
    (hA : A ⊆ X) (hBA : B ⊆ A) (hB : B ≠ ∅) :
    eqF ((proc.Ext_pre_choice A Pf) |[X]| (Int_pre_choice B Qf)) M M
      (Int_pre_choice B fun x => Pf x |[X]| Qf x) := by
  rw [Int_pre_choice_def, Int_pre_choice_def]
  refine cspF_trans_left_eq (cspF_Parallel_Dist_com_r_nonempty hB) ?_
  refine cspF_Rep_int_choice_cong_com rfl (fun a ha => ?_)
  refine cspF_trans_left_eq
    (cspF_Parallel_cong (X := X) (P1 := proc.Ext_pre_choice A Pf)
      (Q1 := proc.Ext_pre_choice A Pf)
      (P2 := proc.Act_prefix a (Qf a))
      (Q2 := proc.Ext_pre_choice ({a} : Set α) (fun _ => Qf a))
      rfl cspF_reflex_eq_P (cspF_Act_prefix_step (a := a) (P := Qf a))) ?_
  refine cspF_trans_left_eq
    (cspF_Parallel_step (X := X) (Y := A) (Z := ({a} : Set α))
      (Pf := Pf) (Qf := fun _ => Qf a)) ?_
  refine cspF_trans_left_eq ?_
    (cspF_sym (cspF_Act_prefix_step (a := a) (P := Pf a |[X]| Qf a) (M := M)))
  have haX : a ∈ X := hA (hBA ha)
  have hset : ((X ∩ A ∩ ({a} : Set α)) ∪ (A \ X) ∪ (({a} : Set α) \ X)) = ({a} : Set α) := by
    have h1 : A \ X = (∅ : Set α) := Set.diff_eq_empty.mpr hA
    have h2 : ({a} : Set α) \ X = (∅ : Set α) :=
      Set.diff_eq_empty.mpr (Set.singleton_subset_iff.mpr haX)
    rw [h1, h2]
    simp only [Set.union_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, rfl⟩; rfl
    · rintro rfl; exact ⟨⟨haX, hBA ha⟩, rfl⟩
  refine cspF_Ext_pre_choice_cong hset (fun x hx => ?_)
  rw [Set.mem_singleton_iff] at hx
  subst hx
  rw [procIte_pos haX]
  exact cspF_reflex_eq_P

theorem cspF_Parallel_Int_Ext_pre_choice
    {A B X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α}
    (hA : A ⊆ X) (hBA : B ⊆ A) (hB : B ≠ ∅) :
    eqF ((Int_pre_choice B Pf) |[X]| (proc.Ext_pre_choice A Qf)) M M
      (Int_pre_choice B fun x => Pf x |[X]| Qf x) := by
  refine cspF_trans_left_eq
    (cspF_Parallel_commut (P := Int_pre_choice B Pf)
      (Q := proc.Ext_pre_choice A Qf) (X := X) (M := M)) ?_
  refine cspF_trans_left_eq
    (cspF_Parallel_Ext_Int_pre_choice (Pf := Qf) (Qf := Pf) hA hBA hB) ?_
  rw [Int_pre_choice_def, Int_pre_choice_def]
  refine cspF_Rep_int_choice_cong_com rfl (fun a _ => ?_)
  exact cspF_Act_prefix_cong rfl cspF_Parallel_commut

theorem cspF_Parallel_Rec_Nondet_send_prefix [Inhabited β]
    {f : β → α} {A B : Set β} {X : Set α} {Pf Qf : β → proc p α}
    {M : p → domFType α}
    (hA : f '' A ⊆ X) (hBA : B ⊆ A) (hB : B ≠ ∅) :
    eqF ((Rec_prefix f A Pf) |[X]| (Nondet_send_prefix f B Qf)) M M
      (Nondet_send_prefix f B fun x => Pf x |[X]| Qf x) :=
  cspF_Parallel_Ext_Int_pre_choice hA (Set.image_mono hBA)
    (fun h => hB (Set.image_eq_empty.mp h))

theorem cspF_Parallel_Nondet_send_Rec_prefix [Inhabited β]
    {f : β → α} {A B : Set β} {X : Set α} {Pf Qf : β → proc p α}
    {M : p → domFType α}
    (hA : f '' A ⊆ X) (hBA : B ⊆ A) (hB : B ≠ ∅) :
    eqF ((Nondet_send_prefix f B Pf) |[X]| (Rec_prefix f A Qf)) M M
      (Nondet_send_prefix f B fun x => Pf x |[X]| Qf x) :=
  cspF_Parallel_Int_Ext_pre_choice hA (Set.image_mono hBA)
    (fun h => hB (Set.image_eq_empty.mp h))

/-
(**************** ! prefix + left ****************)
-/

/- Lean note:
   `cspF_Rep_int_choice_com_left_x` phrased for the sugared internal
   prefixes, which is how Isabelle uses it once `csp_prefix_ss_def` has
   been unfolded. -/

theorem cspF_Int_pre_choice_left_x
    {X : Set α} {Pf : α → proc p α} {Q : proc q α} {a : α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (ha : a ∈ X) (hPQ : refF (a ~> Pf a) M1 M2 Q) :
    refF (Int_pre_choice X Pf) M1 M2 Q := by
  rw [Int_pre_choice_def]
  exact cspF_Rep_int_choice_com_left_x ha hPQ

theorem cspF_Nondet_send_prefix_left_x [Inhabited β]
    {f : β → α} {X : Set β} {Pf : β → proc p α} {Q : proc q α} {a : β}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (hf : Injective f) (ha : a ∈ X) (hPQ : refF (f a ~> Pf a) M1 M2 Q) :
    refF (Nondet_send_prefix f X Pf) M1 M2 Q := by
  rw [Nondet_send_prefix_def]
  refine cspF_Int_pre_choice_left_x (a := f a) ⟨a, ha, rfl⟩ ?_
  rwa [Function.leftInverse_invFun hf a]

/-
(**************** -- X + prefixes outside X ****************)
-/

/- Lean note:
   Another composite that Isabelle derives inside `cspF_hsf`: hiding a set
   `X` distributes over a prefix whose events all lie outside `X`.  The
   base case is `cspF_Hiding_step` on the positive branch of its `procIte`;
   the sugared versions follow by unfolding. -/

theorem cspF_Hiding_Act_prefix_notin [Inhabited α]
    {a : α} {X : Set α} {P : proc p α} {M : p → domFType α} (ha : a ∉ X) :
    eqF (proc.Hiding (a ~> P) X) M M (a ~> proc.Hiding P X) := by
  have hdisj : ({a} : Set α) ∩ X = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨rfl, hx⟩
    exact ha hx
  refine cspF_trans_left_eq
    (cspF_Hiding_cong (X := X) rfl (cspF_Act_prefix_step (a := a) (P := P) (M := M))) ?_
  refine cspF_trans_left_eq
    (cspF_Hiding_step (X := X) (Y := ({a} : Set α)) (Pf := fun _ => P) (M := M)) ?_
  rw [procIte_pos hdisj]
  exact cspF_sym (cspF_Act_prefix_step (a := a) (P := proc.Hiding P X) (M := M))

theorem cspF_Hiding_Act_prefix_in [Inhabited α]
    {a : α} {X : Set α} {P : proc p α} {M : p → domFType α} (ha : a ∈ X) :
    eqF (proc.Hiding (a ~> P) X) M M (proc.Hiding P X) := by
  have hdisj : ¬ (({a} : Set α) ∩ X = ∅) := by
    intro h
    have hm : a ∈ ({a} : Set α) ∩ X := ⟨rfl, ha⟩
    rw [h] at hm
    exact hm
  have hdiff : ({a} : Set α) \ X = (∅ : Set α) :=
    Set.diff_eq_empty.mpr (Set.singleton_subset_iff.mpr ha)
  have hinter : ({a} : Set α) ∩ X = ({a} : Set α) := Set.inter_eq_self_of_subset_left
    (Set.singleton_subset_iff.mpr ha)
  refine cspF_trans_left_eq
    (cspF_Hiding_cong (X := X) rfl (cspF_Act_prefix_step (a := a) (P := P) (M := M))) ?_
  refine cspF_trans_left_eq
    (cspF_Hiding_step (X := X) (Y := ({a} : Set α)) (Pf := fun _ => P) (M := M)) ?_
  rw [procIte_neg hdisj, hdiff, hinter]
  refine cspF_trans_left_eq
    (cspF_Timeout_cong (cspF_sym (cspF_STOP_step (M1 := M)
      (Pf := fun x => proc.Hiding ((fun _ => P) x) X))) cspF_reflex_eq_P) ?_
  exact cspF_trans_left_eq cspF_STOP_Timeout cspF_Rep_int_choice_com_singleton

theorem cspF_Hiding_Ext_pre_choice_notin [Inhabited α]
    {A X : Set α} {Pf : α → proc p α} {M : p → domFType α} (hA : A ∩ X = ∅) :
    eqF (proc.Hiding (proc.Ext_pre_choice A Pf) X) M M
      (proc.Ext_pre_choice A fun x => proc.Hiding (Pf x) X) := by
  refine cspF_trans_left_eq
    (cspF_Hiding_step (X := X) (Y := A) (Pf := Pf) (M := M)) ?_
  rw [procIte_pos hA]
  exact cspF_reflex_eq_P

theorem cspF_Hiding_IF
    {b : Bool} {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (IF b THEN P ELSE Q) X) M M
      (IF b THEN proc.Hiding P X ELSE proc.Hiding Q X) := by
  cases b with
  | false =>
      exact cspF_trans_left_eq (cspF_Hiding_cong rfl cspF_IF_False) (cspF_sym cspF_IF_False)
  | true =>
      exact cspF_trans_left_eq (cspF_Hiding_cong rfl cspF_IF_True) (cspF_sym cspF_IF_True)

theorem cspF_STOP_Hiding_Id [Inhabited α]
    {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (proc.STOP : proc p α) X) M M (proc.STOP : proc p α) := by
  refine cspF_trans_left_eq
    (cspF_Hiding_cong (X := X) rfl
      (cspF_STOP_step (M1 := M) (M2 := M) (Pf := fun _ => (proc.STOP : proc p α)))) ?_
  refine cspF_trans_left_eq (cspF_Hiding_Ext_pre_choice_notin (by simp)) ?_
  exact cspF_sym (cspF_STOP_step (M1 := M) (M2 := M)
    (Pf := fun x => proc.Hiding ((fun _ => (proc.STOP : proc p α)) x) X))

theorem cspF_Hiding_Int_pre_choice_notin [Inhabited α]
    {B X : Set α} {Qf : α → proc p α} {M : p → domFType α} (hB : B ∩ X = ∅) :
    eqF (proc.Hiding (Int_pre_choice B Qf) X) M M
      (Int_pre_choice B fun x => proc.Hiding (Qf x) X) := by
  rw [Int_pre_choice_def, Int_pre_choice_def]
  refine cspF_trans_left_eq (cspF_Hiding_Dist_com (X := X) (Y := B)) ?_
  refine cspF_Rep_int_choice_cong_com rfl (fun a ha => ?_)
  refine cspF_Hiding_Act_prefix_notin (fun haX => ?_)
  have hm : a ∈ B ∩ X := ⟨ha, haX⟩
  rw [hB] at hm
  exact hm

theorem cspF_Hiding_Rec_prefix_notin [Inhabited α] [Inhabited β]
    {f : β → α} {A : Set β} {X : Set α} {Pf : β → proc p α} {M : p → domFType α}
    (hA : f '' A ∩ X = ∅) :
    eqF (proc.Hiding (Rec_prefix f A Pf) X) M M
      (Rec_prefix f A fun x => proc.Hiding (Pf x) X) :=
  cspF_Hiding_Ext_pre_choice_notin hA

theorem cspF_Hiding_Nondet_send_prefix_notin [Inhabited α] [Inhabited β]
    {f : β → α} {B : Set β} {X : Set α} {Qf : β → proc p α} {M : p → domFType α}
    (hB : f '' B ∩ X = ∅) :
    eqF (proc.Hiding (Nondet_send_prefix f B Qf) X) M M
      (Nondet_send_prefix f B fun x => proc.Hiding (Qf x) X) :=
  cspF_Hiding_Int_pre_choice_notin hB

/-
(**************** ;; + resolve ****************)
-/

theorem cspF_SKIP_Seq_compo_step_resolve
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> Q)) := by
  have h₁ :
      eqF ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) ;; Q)) M M
        ((((proc.Ext_pre_choice X Pf) [> (proc.SKIP : proc p α)) ;; Q)) :=
    cspF_Seq_compo_cong cspF_Ext_choice_SKIP_resolve cspF_reflex_eq_P
  exact cspF_trans_left_eq h₁ cspF_SKIP_Seq_compo_step

theorem cspF_DIV_Seq_compo_step_resolve
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [+] (proc.DIV : proc p α))) := by
  have h₁ :
      eqF ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) ;; Q)) M M
        ((((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α)) ;; Q)) :=
    cspF_Seq_compo_cong cspF_Ext_choice_DIV_resolve cspF_reflex_eq_P
  have h₂ :
      eqF ((((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α)) ;; Q)) M M
        (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> (proc.DIV : proc p α))) :=
    cspF_DIV_Seq_compo_step
  have h₃ :
      eqF (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> (proc.DIV : proc p α))) M M
        (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [+] (proc.DIV : proc p α))) :=
    cspF_sym cspF_Ext_choice_DIV_resolve
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_SKIP_DIV_Seq_compo_step_resolve` is represented by
   `cspF_SKIP_Seq_compo_step_resolve` and
   `cspF_DIV_Seq_compo_step_resolve`. -/

/- The Isabelle theorem bundle `cspF_SKIP_DIV_resolve` is represented by
   `cspF_SKIP_DIV`, `cspF_Parallel_Timeout_split_resolve`,
   `cspF_Parallel_Timeout_input_resolve`, and
   `cspF_SKIP_DIV_Seq_compo_step_resolve`. -/

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV_resolve` is represented by
   `cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV` and
   `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV`. -/

/-
(*=========================================================*
 |                                                         |
 |   for convenience, especially for fully sequntialising  |
 |                                                         |
 *=========================================================*)
-/

/-- Failures of `((? :Y -> Pf) [+] Z) |[X]| SKIP` for `Z` equal to `SKIP` or `DIV`;
    the shared core of `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l`. -/
private theorem par_SKIP_Ext_choice_failures
    {X Y : Set α} {Pf : α → proc p α} {Z : proc p α} {M : p → domFType α}
    (hZ : Z = proc.SKIP ∨ Z = proc.DIV) (t : traceType α) (W : Set (event α)) :
    ((t, W) :f failures (((proc.Ext_pre_choice Y Pf) [+] Z) |[X]| (proc.SKIP : proc p α)) M) ↔
      ((t, W) :f failures
        ((proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) [+] Z) M) := by
  rw [in_failures_Parallel, in_failures_Ext_pre_choice_Ext_choice hZ]
  constructor
  · rintro ⟨u, A, B, hEq, hAB, s, t1, hpar, hs, ht1⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Ext_pre_choice_Ext_choice hZ] at hs
    rw [in_failures_SKIP_split] at ht1
    rcases hs with ⟨a, s', rfl, hPf, haY⟩ | ⟨hZS, rfl⟩ | ⟨hZS, rfl, hA⟩
    · rcases ht1 with ⟨rfl, hB⟩ | rfl
      · rw [par_tr_nil_right] at hpar
        obtain ⟨rfl, hnoT, hEmpty⟩ := hpar
        have haX : a ∉ X := by
          intro ha
          have hm : (event.Ev a : event α) ∈
              sett (Abs_trace [event.Ev a] ^^^ s') ∩ event.Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inl rfl), ⟨a, ha, rfl⟩⟩
          rw [hEmpty] at hm
          exact hm
        refine Or.inl ⟨a, s', rfl, ?_, ⟨haY, haX⟩⟩
        rw [in_failures_Parallel]
        refine ⟨s', A, B, rfl, hAB, s', <>, par_tr_nil_right.mpr ⟨rfl, ?_, ?_⟩, hPf,
          in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hB⟩)⟩
        · intro hTk
          exact hnoT (sett_Ev_head_mem.mpr (Or.inr hTk))
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          have hm : e ∈ sett (Abs_trace [event.Ev a] ^^^ s') ∩ event.Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inr he1), he2⟩
          rw [hEmpty] at hm
          exact hm
      · rw [par_tr_Tick_right] at hpar
        obtain ⟨rfl, hTk, hEmpty⟩ := hpar
        have haX : a ∉ X := by
          intro ha
          have hm : (event.Ev a : event α) ∈
              sett (Abs_trace [event.Ev a] ^^^ s') ∩ event.Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inl rfl), ⟨a, ha, rfl⟩⟩
          rw [hEmpty] at hm
          exact hm
        refine Or.inl ⟨a, s', rfl, ?_, ⟨haY, haX⟩⟩
        rw [in_failures_Parallel]
        refine ⟨s', A, B, rfl, hAB, s', Abs_trace [event.Tick],
          par_tr_Tick_right.mpr ⟨rfl, ?_, ?_⟩, hPf,
          in_failures_SKIP_split.mpr (Or.inr rfl)⟩
        · rcases sett_Ev_head_mem.mp hTk with hEq2 | h
          · exact absurd hEq2 (by simp)
          · exact h
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          have hm : e ∈ sett (Abs_trace [event.Ev a] ^^^ s') ∩ event.Ev '' X :=
            ⟨sett_Ev_head_mem.mpr (Or.inr he1), he2⟩
          rw [hEmpty] at hm
          exact hm
    · rcases ht1 with ⟨rfl, -⟩ | rfl
      · exact absurd hpar (by simp)
      · rw [par_tr_Tick2] at hpar
        subst hpar
        exact Or.inr (Or.inl ⟨hZS, rfl⟩)
    · rcases ht1 with ⟨rfl, hB⟩ | rfl
      · rw [par_tr_nil2] at hpar
        subst hpar
        refine Or.inr (Or.inr ⟨hZS, rfl, ?_⟩)
        rintro e (he | he)
        · exact hA he
        · exact hB he
      · exact absurd hpar (by simp)
  · rintro (⟨a, v, rfl, hv, ⟨haY, haX⟩⟩ | ⟨hZS, rfl⟩ | ⟨hZS, rfl, hW⟩)
    · rw [in_failures_Parallel] at hv
      obtain ⟨v', A, B, hEqv, hAB, s, t1, hpar, hs, ht1⟩ := hv
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqv
      rw [in_failures_SKIP_split] at ht1
      rcases ht1 with ⟨rfl, hB⟩ | rfl
      · rw [par_tr_nil_right] at hpar
        obtain ⟨rfl, hnoT, hEmpty⟩ := hpar
        refine ⟨Abs_trace [event.Ev a] ^^^ v, A, B, rfl, hAB, Abs_trace [event.Ev a] ^^^ v, <>,
          par_tr_nil_right.mpr ⟨rfl, ?_, ?_⟩, ?_,
          in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hB⟩)⟩
        · intro hTk
          rcases sett_Ev_head_mem.mp hTk with hEq2 | h
          · exact absurd hEq2 (by simp)
          · exact hnoT h
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rcases sett_Ev_head_mem.mp he1 with rfl | h
          · rcases he2 with ⟨b, hb, hEv⟩
            exact haX (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
          · have hm : e ∈ sett v ∩ event.Ev '' X := ⟨h, he2⟩
            rw [hEmpty] at hm
            exact hm
        · exact (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inl ⟨a, v, rfl, hs, haY⟩)
      · rw [par_tr_Tick_right] at hpar
        obtain ⟨rfl, hTk, hEmpty⟩ := hpar
        refine ⟨Abs_trace [event.Ev a] ^^^ v, A, B, rfl, hAB, Abs_trace [event.Ev a] ^^^ v,
          Abs_trace [event.Tick], par_tr_Tick_right.mpr ⟨rfl, ?_, ?_⟩, ?_,
          in_failures_SKIP_split.mpr (Or.inr rfl)⟩
        · exact sett_Ev_head_mem.mpr (Or.inr hTk)
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rcases sett_Ev_head_mem.mp he1 with rfl | h
          · rcases he2 with ⟨b, hb, hEv⟩
            exact haX (by rw [← (by cases hEv; rfl : a = b)] at hb; exact hb)
          · have hm : e ∈ sett v ∩ event.Ev '' X := ⟨h, he2⟩
            rw [hEmpty] at hm
            exact hm
        · exact (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inl ⟨a, v, rfl, hs, haY⟩)
    · exact ⟨Abs_trace [event.Tick], W, W, by rw [Set.union_self], rfl,
        Abs_trace [event.Tick], Abs_trace [event.Tick], par_tr_Tick_Tick,
        (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inr (Or.inl ⟨hZS, rfl⟩)),
        in_failures_SKIP_split.mpr (Or.inr rfl)⟩
    · exact ⟨<>, W, W, by rw [Set.union_self], rfl, <>, <>, par_tr_nil_nil,
        (in_failures_Ext_pre_choice_Ext_choice hZ).mpr (Or.inr (Or.inr ⟨hZS, rfl, hW⟩)),
        in_failures_SKIP_split.mpr (Or.inl ⟨rfl, hW⟩)⟩

theorem cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF ((P [+] Q) |[X]| (proc.DIV : proc p α)) M M (P |[X]| (proc.DIV : proc p α)) := by
  rintro (rfl | rfl | rfl)
  · cspF_auto
  · cspF_auto
  · cspF_auto

theorem cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_r
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF ((proc.DIV : proc p α) |[X]| (P [+] Q)) M M ((proc.DIV : proc p α) |[X]| P) := by
  intro hQ
  have h₁ :
      eqF ((proc.DIV : proc p α) |[X]| (P [+] Q)) M M ((P [+] Q) |[X]| (proc.DIV : proc p α)) :=
    cspF_Parallel_commut
  have h₂ :
      eqF ((P [+] Q) |[X]| (proc.DIV : proc p α)) M M (P |[X]| (proc.DIV : proc p α)) :=
    cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l hQ
  have h₃ :
      eqF (P |[X]| (proc.DIV : proc p α)) M M ((proc.DIV : proc p α) |[X]| P) :=
    cspF_Parallel_commut
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV` is represented by
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l` and
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_r`. -/

theorem cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l
    {Y X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF ((((proc.Ext_pre_choice Y Pf) [+] Q) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) [+] Q)) := by
  rintro (rfl | rfl | rfl)
  · exact cspF_SKIP_Parallel_Ext_choice_SKIP_l
  · exact cspF_eqF_of_eqT (by cspT_auto_step) (par_SKIP_Ext_choice_failures (Or.inr rfl))
  · have h₁ :
        eqF ((((proc.Ext_pre_choice Y Pf) [+] proc.STOP) |[X]| (proc.SKIP : proc p α))) M M
          ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) :=
      cspF_Parallel_cong rfl cspF_Ext_choice_unit_r cspF_reflex_eq_P
    have h₂ :
        eqF ((proc.Ext_pre_choice Y Pf) |[X]| (proc.SKIP : proc p α)) M M
          (proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) :=
      cspF_Parallel_preterm_r
    have h₃ :
        eqF (proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) M M
          (((proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α)))
            [+] proc.STOP)) :=
      cspF_sym cspF_Ext_choice_unit_r
    exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

theorem cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_r
    {Y X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] Q))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (proc.SKIP : proc p α) |[X]| Pf x)) [+] Q)) := by
  intro hQ
  have h₁ :
      eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] Q))) M M
        ((((proc.Ext_pre_choice Y Pf) [+] Q) |[X]| (proc.SKIP : proc p α))) :=
    cspF_Parallel_commut
  have h₂ :
      eqF ((((proc.Ext_pre_choice Y Pf) [+] Q) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) [+] Q)) :=
    cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l hQ
  have h₃₁ :
      eqF (proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) M M
        (proc.Ext_pre_choice (Y \ X) (fun x => (proc.SKIP : proc p α) |[X]| Pf x)) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    exact cspF_Parallel_commut
  have h₃ :
      eqF (((proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) [+] Q)) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (proc.SKIP : proc p α) |[X]| Pf x)) [+] Q)) :=
    cspF_Ext_choice_cong h₃₁ cspF_reflex_eq_P
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP` is represented by
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l` and
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_r`. -/

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice` is represented by
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV` and
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP`. -/

/-
(* renaming *)
-/

theorem cspF_SKIP_or_DIV_or_STOP_Renaming_Id
    {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (P = proc.SKIP ∨ P = proc.DIV ∨ P = proc.STOP) →
      eqF (P[[r]]) M M P := by
  rintro (rfl | rfl | rfl)
  · cspF_auto
  · cspF_auto
  · cspF_auto

/-
(* restg *)
-/

theorem cspF_STOP_Depth_rest
    {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.STOP : proc p α) |. Nat.succ n)) M1 M2 (proc.STOP : proc q α) := by
  cspF_auto

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(*********************************************************
                       P |[X,Y]| Q (aux)
 *********************************************************)
-/

-- Algebraic proof following the Isabelle original (CSP_F_law_aux.thy) and the
-- `cspT_Alpha_Parallel_step` port: unfold `|[X,Y]|`, absorb the `SKIP`
-- components with `cspF_Parallel_preterm_r`, apply `cspF_Parallel_step`, then
-- align the index set and the `procIte` branches case by case.
theorem cspF_Alpha_Parallel_step
    {A B X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice A Pf) |[X,Y]| proc.Ext_pre_choice B Qf) M M
      (proc.Ext_pre_choice ((A ∩ (X \ Y)) ∪ (B ∩ (Y \ X)) ∪ (A ∩ B ∩ X ∩ Y)) fun x =>
        procIte (x ∈ X ∧ x ∈ Y) (Pf x |[X,Y]| Qf x)
          (procIte (x ∈ X) (Pf x |[X,Y]| proc.Ext_pre_choice B Qf)
            (proc.Ext_pre_choice A Pf |[X,Y]| Qf x))) := by
  simp only [Alpha_parallel_def]
  refine cspF_rw_left_eq
    (cspF_Parallel_cong rfl cspF_Parallel_preterm_r cspF_Parallel_preterm_r) ?_
  refine cspF_rw_left_eq cspF_Parallel_step ?_
  have hS : (((X ∩ Y) ∩ (A \ Xᶜ) ∩ (B \ Yᶜ)) ∪ ((A \ Xᶜ) \ (X ∩ Y)) ∪ ((B \ Yᶜ) \ (X ∩ Y)))
      = ((A ∩ (X \ Y)) ∪ (B ∩ (Y \ X)) ∪ (A ∩ B ∩ X ∩ Y)) := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff, Set.mem_compl_iff, not_not,
      not_and]
    tauto
  refine cspF_Ext_pre_choice_cong hS fun a ha => ?_
  simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff] at ha
  by_cases hx : a ∈ X <;> by_cases hy : a ∈ Y
  · rw [procIte_pos (Set.mem_inter hx hy), procIte_pos ⟨hx, hy⟩]
    exact cspF_reflex_eq_P
  · have hB' : a ∉ B \ Yᶜ := by simp [hy]
    rw [procIte_neg (by simp [Set.mem_inter_iff, hy] : a ∉ X ∩ Y),
        procIte_neg (fun h => hB' h.2),
        procIte_pos (show a ∈ A \ Xᶜ by
          have hA : a ∈ A := by tauto
          simp [hA, hx]),
        procIte_neg (fun h => hy h.2), procIte_pos hx]
    exact cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym cspF_Parallel_preterm_r)
  · have hA' : a ∉ A \ Xᶜ := by simp [hx]
    rw [procIte_neg (by simp [Set.mem_inter_iff, hx] : a ∉ X ∩ Y),
        procIte_neg (fun h => hA' h.1),
        procIte_neg hA',
        procIte_neg (fun h => hx h.1), procIte_neg hx]
    exact cspF_Parallel_cong rfl (cspF_sym cspF_Parallel_preterm_r) cspF_reflex_eq_P
  · exact absurd ha (by tauto)

/-
(*==============================================================*
 |                                                              |
 |       Associativity and Commutativity for SKIP and DIV       |
 |                    (for sequentialising)                     |
 |                                                              |
 *==============================================================*)
-/

theorem cspF_Ext_pre_choice_SKIP_commut
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.SKIP : proc p α) [+] proc.Ext_pre_choice X Pf) M M
      ((proc.Ext_pre_choice X Pf) [+] proc.SKIP) := by
  exact cspF_Ext_choice_commut

theorem cspF_Ext_pre_choice_DIV_commut
    {X : Set α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.DIV : proc p α) [+] proc.Ext_pre_choice X Pf) M M
      ((proc.Ext_pre_choice X Pf) [+] proc.DIV) := by
  exact cspF_Ext_choice_commut

theorem cspF_Ext_pre_choice_SKIP_assoc
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF
      ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
      ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.SKIP)) := by
  have h₁ :
      eqF
        ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] ((proc.SKIP : proc p α) [+] proc.Ext_pre_choice Y Qf)) :=
    cspF_Ext_choice_assoc_sym
  have h₂ :
      eqF ((proc.Ext_pre_choice X Pf) [+] ((proc.SKIP : proc p α) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.SKIP)) :=
    cspF_Ext_choice_cong cspF_reflex_eq_P cspF_Ext_pre_choice_SKIP_commut
  have h₃ :
      eqF ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.SKIP)) M M
        ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.SKIP)) :=
    cspF_Ext_choice_assoc
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

theorem cspF_Ext_pre_choice_DIV_assoc
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF
      ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
      ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.DIV)) := by
  have h₁ :
      eqF
        ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] ((proc.DIV : proc p α) [+] proc.Ext_pre_choice Y Qf)) :=
    cspF_Ext_choice_assoc_sym
  have h₂ :
      eqF ((proc.Ext_pre_choice X Pf) [+] ((proc.DIV : proc p α) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.DIV)) :=
    cspF_Ext_choice_cong cspF_reflex_eq_P cspF_Ext_pre_choice_DIV_commut
  have h₃ :
      eqF ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.DIV)) M M
        ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.DIV)) :=
    cspF_Ext_choice_assoc
  exact cspF_trans_left_eq h₁ (cspF_trans_left_eq h₂ h₃)

theorem cspF_Ext_choice_idem_assoc
    {P Q : proc p α} {M : p → domFType α} :
    eqF (((P [+] Q) [+] Q)) M M (P [+] Q) := by
  have h₁ : eqF (((P [+] Q) [+] Q)) M M (P [+] (Q [+] Q)) := cspF_Ext_choice_assoc_sym
  have h₂ :
      eqF (P [+] (Q [+] Q)) M M (P [+] Q) :=
    cspF_Ext_choice_cong cspF_reflex_eq_P cspF_Ext_choice_idem
  exact cspF_trans_left_eq h₁ h₂

theorem cspF_Ext_choice_SKIP_DIV_assoc
    {P : proc p α} {M : p → domFType α} :
    eqF (((P [+] (proc.SKIP : proc p α)) [+] proc.DIV)) M M (P [+] proc.SKIP) := by
  have h₁ :
      eqF (((P [+] (proc.SKIP : proc p α)) [+] proc.DIV)) M M
        (P [+] ((proc.SKIP : proc p α) [+] proc.DIV)) :=
    cspF_Ext_choice_assoc_sym
  have h₂ :
      eqF (P [+] ((proc.SKIP : proc p α) [+] proc.DIV)) M M (P [+] proc.SKIP) :=
    cspF_Ext_choice_cong cspF_reflex_eq_P cspF_SKIP_DIV_Ext_choice1
  exact cspF_trans_left_eq h₁ h₂

theorem cspF_Ext_choice_DIV_SKIP_assoc
    {P : proc p α} {M : p → domFType α} :
    eqF (((P [+] (proc.DIV : proc p α)) [+] proc.SKIP)) M M (P [+] proc.SKIP) := by
  have h₁ :
      eqF (((P [+] (proc.DIV : proc p α)) [+] proc.SKIP)) M M
        (P [+] ((proc.DIV : proc p α) [+] proc.SKIP)) :=
    cspF_Ext_choice_assoc_sym
  have h₂ :
      eqF (P [+] ((proc.DIV : proc p α) [+] proc.SKIP)) M M (P [+] proc.SKIP) :=
    cspF_Ext_choice_cong cspF_reflex_eq_P cspF_SKIP_DIV_Ext_choice2
  exact cspF_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspF_SKIP_DIV_sort` is represented by
   `cspF_Ext_choice_assoc`, `cspF_Ext_pre_choice_SKIP_commut`,
   `cspF_Ext_pre_choice_DIV_commut`, `cspF_Ext_pre_choice_SKIP_assoc`,
   `cspF_Ext_pre_choice_DIV_assoc`, `cspF_Ext_choice_idem_assoc`,
   `cspF_Ext_choice_SKIP_DIV_assoc`, and
   `cspF_Ext_choice_DIV_SKIP_assoc`. -/

/-
(*==============================================================*
 |                                                              |
 |    decompostion control by the flag "Not_Decompo_Flag"       |
 |                                                              |
 *==============================================================*)

(*------------------------------------------------*
 |              trans with Flag                   |
 *------------------------------------------------*)

(*** rewrite (eq) ***)
-/

theorem cspF_rw_flag_left_eq
    {R1 R2 : proc p α} {R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : eqF R1 M1 M1 R2) (h23 : Not_Decompo_Flag ∧ eqF R2 M1 M3 R3) :
    eqF R1 M1 M3 R3 := by
  cspF_auto

theorem cspF_rw_flag_left_ref
    {R1 R2 : proc p α} {R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : eqF R1 M1 M1 R2) (h23 : Not_Decompo_Flag ∧ refF R2 M1 M3 R3) :
    refF R1 M1 M3 R3 := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_rw_flag_left` is represented by
   `cspF_rw_flag_left_eq` and `cspF_rw_flag_left_ref`. -/

theorem cspF_rw_flag_right_eq
    {R1 : proc p α} {R2 R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h32 : eqF R3 M3 M3 R2) (h12 : Not_Decompo_Flag ∧ eqF R1 M1 M3 R2) :
    eqF R1 M1 M3 R3 := by
  cspF_auto

theorem cspF_rw_flag_right_ref
    {R1 : proc p α} {R2 R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h32 : eqF R3 M3 M3 R2) (h12 : Not_Decompo_Flag ∧ refF R1 M1 M3 R2) :
    refF R1 M1 M3 R3 := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_rw_flag_right` is represented by
   `cspF_rw_flag_right_eq` and `cspF_rw_flag_right_ref`. -/

/-
(*------------------------------------------------*
 |              trans with Flag (ref)             |
 *------------------------------------------------*)
-/

theorem cspF_tr_flag_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : eqF P1 M1 M1 P2) (h23 : Not_Decompo_Flag ∧ eqF P2 M1 M3 P3) :
    eqF P1 M1 M3 P3 := by
  cspF_auto

theorem cspF_tr_flag_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : refF P1 M1 M1 P2) (h23 : Not_Decompo_Flag ∧ refF P2 M1 M3 P3) :
    refF P1 M1 M3 P3 := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_tr_flag_left` is represented by
   `cspF_tr_flag_left_eq` and `cspF_tr_flag_left_ref`. -/

theorem cspF_tr_flag_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h23 : eqF P2 M3 M3 P3) (h12 : Not_Decompo_Flag ∧ eqF P1 M1 M3 P2) :
    eqF P1 M1 M3 P3 := by
  cspF_auto

theorem cspF_tr_flag_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h23 : refF P2 M3 M3 P3) (h12 : Not_Decompo_Flag ∧ refF P1 M1 M3 P2) :
    refF P1 M1 M3 P3 := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_tr_flag_right` is represented by
   `cspF_tr_flag_right_eq` and `cspF_tr_flag_right_ref`. -/

/-
(*------------------------------------------------*
 |           trans with Flag (erule)              |
 *------------------------------------------------*)

(*** rewrite (eq) ***)
-/

theorem cspF_rw_flag_left_eqE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : eqF P1 M1 M3 P3) (h12 : eqF P1 M1 M1 P2)
    (hR : Not_Decompo_Flag ∧ eqF P2 M1 M3 P3 → R) :
    R :=
  cspF_rw_left_eqE h13 h12 (fun h => hR ⟨trivial, h⟩)

theorem cspF_rw_flag_left_refE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : refF P1 M1 M3 P3) (h12 : eqF P1 M1 M1 P2)
    (hR : Not_Decompo_Flag ∧ refF P2 M1 M3 P3 → R) :
    R :=
  cspF_rw_left_refE h13 h12 (fun h => hR ⟨trivial, h⟩)

/- The Isabelle theorem bundle `cspF_rw_flag_leftE` is represented by
   `cspF_rw_flag_left_eqE` and `cspF_rw_flag_left_refE`. -/

theorem cspF_rw_flag_right_eqE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : eqF P1 M1 M3 P3) (h32 : eqF P3 M3 M3 P2)
    (hR : Not_Decompo_Flag ∧ eqF P1 M1 M3 P2 → R) :
    R :=
  cspF_rw_right_eqE h13 h32 (fun h => hR ⟨trivial, h⟩)

theorem cspF_rw_flag_right_refE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : refF P1 M1 M3 P3) (h32 : eqF P3 M3 M3 P2)
    (hR : Not_Decompo_Flag ∧ refF P1 M1 M3 P2 → R) :
    R :=
  cspF_rw_right_refE h13 h32 (fun h => hR ⟨trivial, h⟩)

/- The Isabelle theorem bundle `cspF_rw_flag_rightE` is represented by
   `cspF_rw_flag_right_eqE` and `cspF_rw_flag_right_refE`. -/

/-
(*===============================================================*
 |  decompostion of Sequential composition with a flag           |
 |  It is often useful that the second process is not rewritten. |
 |                    (since CSP-Prover 5)                       |
 *===============================================================*)
-/

theorem cspF_Seq_compo_mono_flag
    {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (h1 : refF P1 M1 M2 Q1) (h2 : Not_Rewrite_Flag ∧ refF P2 M1 M2 Q2) :
    refF (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  exact cspF_Seq_compo_mono h1 h2.2

theorem cspF_Seq_compo_cong_flag
    {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domFType α} {M2 : q → domFType α}
    (h1 : eqF P1 M1 M2 Q1) (h2 : Not_Rewrite_Flag ∧ eqF P2 M1 M2 Q2) :
    eqF (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  exact cspF_Seq_compo_cong h1 h2.2

/- The Isabelle theorem bundle `cspF_free_mono_flag` is represented by
   `cspF_Ext_choice_mono`, `cspF_Int_choice_mono`, `cspF_Parallel_mono`,
   `cspF_Hiding_mono`, `cspF_Renaming_mono`, `cspF_Seq_compo_mono_flag`,
   `cspF_Depth_rest_mono`, `cspF_Rep_int_choice_mono_UNIV`, and
   `cspF_Alpha_parallel_mono`. -/

/- The Isabelle theorem bundle `cspF_free_cong_flag` is represented by
   `cspF_Ext_choice_cong`, `cspF_Int_choice_cong`, `cspF_Parallel_cong`,
   `cspF_Hiding_cong`, `cspF_Renaming_cong`, `cspF_Seq_compo_cong_flag`,
   `cspF_Depth_rest_cong`, `cspF_Rep_int_choice_cong_UNIV`, and
   `cspF_Alpha_parallel_cong`. -/

/- The Isabelle theorem bundle `cspF_free_decompo_flag` is represented by
   `cspF_free_mono_flag` and `cspF_free_cong_flag`. -/

end
