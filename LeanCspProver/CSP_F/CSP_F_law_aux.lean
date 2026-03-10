           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law

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

theorem cspF_Rep_int_choice_com_singleton [Inhabited α]
    {a : α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com ({a} : Set α) Pf) M M (Pf a) := by
  apply cspF_Rep_int_choice_com_const
  · simp
  · intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    rfl

theorem cspF_Rep_int_choice_f_singleton [Inhabited α] [Inhabited β]
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

axiom cspF_Rep_int_choice_const_sum_rule
    {C : sets_nats α} {P : proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C (fun _ => P)) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α) P)

axiom cspF_Rep_int_choice_const_nat_rule
    {N : Set Nat} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N (fun _ => P)) M M
      (procIte (N = ∅) (proc.DIV : proc p α) P)

axiom cspF_Rep_int_choice_const_set_rule
    {Xs : Set (Set α)} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs (fun _ => P)) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α) P)

axiom cspF_Rep_int_choice_const_com_rule [Inhabited α]
    {X : Set α} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X (fun _ => P)) M M
      (procIte (X = ∅) (proc.DIV : proc p α) P)

axiom cspF_Rep_int_choice_const_f_rule [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f X (fun _ => P)) M M
      (procIte (X = ∅) (proc.DIV : proc p α) P)

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

axiom cspF_Parallel_Timeout_split_resolve_SKIP_or_DIV
    {P Q : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (P = proc.SKIP ∨ P = proc.DIV) →
      (Q = proc.SKIP ∨ Q = proc.DIV) →
        eqF (((proc.Ext_pre_choice Y Pf) [+] P) |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) M M
          (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf P Q)

axiom cspF_Parallel_Timeout_split_resolve_SKIP_SKIP
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.SKIP)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.SKIP proc.SKIP)

axiom cspF_Parallel_Timeout_split_resolve_DIV_DIV
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.DIV)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.DIV proc.DIV)

axiom cspF_Parallel_Timeout_split_resolve_SKIP_DIV
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.DIV)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.SKIP proc.DIV)

axiom cspF_Parallel_Timeout_split_resolve_DIV_SKIP
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.SKIP)) M M
      (cspF_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.DIV proc.SKIP)

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_split_resolve` is represented by
   `cspF_Parallel_Timeout_split_resolve_SKIP_SKIP`,
   `cspF_Parallel_Timeout_split_resolve_DIV_DIV`,
   `cspF_Parallel_Timeout_split_resolve_SKIP_DIV`, and
   `cspF_Parallel_Timeout_split_resolve_DIV_SKIP`. -/

/-
(* input + resolve *)
-/

axiom cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l
    {P : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (P = proc.SKIP ∨ P = proc.DIV) →
      eqF (((proc.Ext_pre_choice Y Pf) [+] P) |[X]| proc.Ext_pre_choice Z Qf) M M
        (cspF_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf P)

axiom cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r
    {Q : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV) →
      eqF (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) M M
        (cspF_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf Q)

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV` is represented by
   `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_l` and
   `cspF_Parallel_Timeout_input_resolve_SKIP_or_DIV_r`. -/

axiom cspF_Parallel_Timeout_input_resolve_SKIP_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]| proc.Ext_pre_choice Z Qf) M M
      (cspF_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf proc.SKIP)

axiom cspF_Parallel_Timeout_input_resolve_DIV_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]| proc.Ext_pre_choice Z Qf) M M
      (cspF_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf proc.DIV)

axiom cspF_Parallel_Timeout_input_resolve_SKIP_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] (proc.SKIP : proc p α))) M M
      (cspF_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf proc.SKIP)

axiom cspF_Parallel_Timeout_input_resolve_DIV_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] (proc.DIV : proc p α))) M M
      (cspF_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf proc.DIV)

/- The Isabelle theorem bundle `cspF_Parallel_Timeout_input_resolve` is represented by
   `cspF_Parallel_Timeout_input_resolve_SKIP_l`,
   `cspF_Parallel_Timeout_input_resolve_SKIP_r`,
   `cspF_Parallel_Timeout_input_resolve_DIV_l`, and
   `cspF_Parallel_Timeout_input_resolve_DIV_r`. -/

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

axiom cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV_l
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF ((P [+] Q) |[X]| (proc.DIV : proc p α)) M M (P |[X]| (proc.DIV : proc p α))

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

axiom cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l
    {Y X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF ((((proc.Ext_pre_choice Y Pf) [+] Q) |[X]| (proc.SKIP : proc p α))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => Pf x |[X]| (proc.SKIP : proc p α))) [+] Q))

axiom cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_r
    {Y X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV ∨ Q = proc.STOP) →
      eqF (((proc.SKIP : proc p α) |[X]| ((proc.Ext_pre_choice Y Pf) [+] Q))) M M
        (((proc.Ext_pre_choice (Y \ X) (fun x => (proc.SKIP : proc p α) |[X]| Pf x)) [+] Q))

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP` is represented by
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_l` and
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP_r`. -/

/- The Isabelle theorem bundle `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice` is represented by
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_DIV` and
   `cspF_SKIP_or_DIV_or_STOP_Parallel_Ext_choice_SKIP`. -/

/-
(* renaming *)
-/

axiom cspF_SKIP_or_DIV_or_STOP_Renaming_Id
    {P : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    (P = proc.SKIP ∨ P = proc.DIV ∨ P = proc.STOP) →
      eqF (P[[r]]) M M P

/-
(* restg *)
-/

axiom cspF_STOP_Depth_rest
    {n : Nat} {M1 : p → domFType α} {M2 : q → domFType α} :
    eqF (((proc.STOP : proc p α) |. Nat.succ n)) M1 M2 (proc.STOP : proc q α)

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)

(*********************************************************
                       P |[X,Y]| Q (aux)
 *********************************************************)
-/

axiom cspF_Alpha_Parallel_step
    {A B X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice A Pf) |[X,Y]| proc.Ext_pre_choice B Qf) M M
      (proc.Ext_pre_choice ((A ∩ (X \ Y)) ∪ (B ∩ (Y \ X)) ∪ (A ∩ B ∩ X ∩ Y)) fun x =>
        procIte (x ∈ X ∧ x ∈ Y) (Pf x |[X,Y]| Qf x)
          (procIte (x ∈ X) (Pf x |[X,Y]| proc.Ext_pre_choice B Qf)
            (proc.Ext_pre_choice A Pf |[X,Y]| Qf x)))

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

axiom cspF_rw_flag_left_eq
    {R1 R2 : proc p α} {R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : eqF R1 M1 M1 R2) (h23 : Not_Decompo_Flag ∧ eqF R2 M1 M3 R3) :
    eqF R1 M1 M3 R3

axiom cspF_rw_flag_left_ref
    {R1 R2 : proc p α} {R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : eqF R1 M1 M1 R2) (h23 : Not_Decompo_Flag ∧ refF R2 M1 M3 R3) :
    refF R1 M1 M3 R3

/- The Isabelle theorem bundle `cspF_rw_flag_left` is represented by
   `cspF_rw_flag_left_eq` and `cspF_rw_flag_left_ref`. -/

axiom cspF_rw_flag_right_eq
    {R1 : proc p α} {R2 R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h32 : eqF R3 M3 M3 R2) (h12 : Not_Decompo_Flag ∧ eqF R1 M1 M3 R2) :
    eqF R1 M1 M3 R3

axiom cspF_rw_flag_right_ref
    {R1 : proc p α} {R2 R3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h32 : eqF R3 M3 M3 R2) (h12 : Not_Decompo_Flag ∧ refF R1 M1 M3 R2) :
    refF R1 M1 M3 R3

/- The Isabelle theorem bundle `cspF_rw_flag_right` is represented by
   `cspF_rw_flag_right_eq` and `cspF_rw_flag_right_ref`. -/

/-
(*------------------------------------------------*
 |              trans with Flag (ref)             |
 *------------------------------------------------*)
-/

axiom cspF_tr_flag_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : eqF P1 M1 M1 P2) (h23 : Not_Decompo_Flag ∧ eqF P2 M1 M3 P3) :
    eqF P1 M1 M3 P3

axiom cspF_tr_flag_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h12 : refF P1 M1 M1 P2) (h23 : Not_Decompo_Flag ∧ refF P2 M1 M3 P3) :
    refF P1 M1 M3 P3

/- The Isabelle theorem bundle `cspF_tr_flag_left` is represented by
   `cspF_tr_flag_left_eq` and `cspF_tr_flag_left_ref`. -/

axiom cspF_tr_flag_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h23 : eqF P2 M3 M3 P3) (h12 : Not_Decompo_Flag ∧ eqF P1 M1 M3 P2) :
    eqF P1 M1 M3 P3

axiom cspF_tr_flag_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α}
    (h23 : refF P2 M3 M3 P3) (h12 : Not_Decompo_Flag ∧ refF P1 M1 M3 P2) :
    refF P1 M1 M3 P3

/- The Isabelle theorem bundle `cspF_tr_flag_right` is represented by
   `cspF_tr_flag_right_eq` and `cspF_tr_flag_right_ref`. -/

/-
(*------------------------------------------------*
 |           trans with Flag (erule)              |
 *------------------------------------------------*)

(*** rewrite (eq) ***)
-/

axiom cspF_rw_flag_left_eqE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : eqF P1 M1 M3 P3) (h12 : eqF P1 M1 M1 P2)
    (hR : Not_Decompo_Flag ∧ eqF P2 M1 M3 P3 → R) :
    R

axiom cspF_rw_flag_left_refE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : refF P1 M1 M3 P3) (h12 : eqF P1 M1 M1 P2)
    (hR : Not_Decompo_Flag ∧ refF P2 M1 M3 P3 → R) :
    R

/- The Isabelle theorem bundle `cspF_rw_flag_leftE` is represented by
   `cspF_rw_flag_left_eqE` and `cspF_rw_flag_left_refE`. -/

axiom cspF_rw_flag_right_eqE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : eqF P1 M1 M3 P3) (h32 : eqF P3 M3 M3 P2)
    (hR : Not_Decompo_Flag ∧ eqF P1 M1 M3 P2 → R) :
    R

axiom cspF_rw_flag_right_refE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domFType α} {M3 : q → domFType α} {R : Prop}
    (h13 : refF P1 M1 M3 P3) (h32 : eqF P3 M3 M3 P2)
    (hR : Not_Decompo_Flag ∧ refF P1 M1 M3 P2 → R) :
    R

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
