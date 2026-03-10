           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.CSP_T_law

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

theorem cspT_Rep_int_choice_sum1_singleton
    {c : Set α} {Pf : aset_anat α → proc p α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice (type1 ({c} : Set (Set α))) Pf) M M (Pf (type1 c)) := by
  apply cspT_Rep_int_choice_sum_const
  · simp [sumset]
  · intro d hd
    have hd' : d = type1 c := by
      simpa [sumset] using hd
    simp [hd']

theorem cspT_Rep_int_choice_sum2_singleton
    {c : Nat} {Pf : aset_anat α → proc p α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice (type2 ({c} : Set Nat)) Pf) M M (Pf (type2 c)) := by
  apply cspT_Rep_int_choice_sum_const
  · simp [sumset]
  · intro d hd
    have hd' : d = type2 c := by
      simpa [sumset] using hd
    simp [hd']

theorem cspT_Rep_int_choice_nat_singleton
    {n : Nat} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat ({n} : Set Nat) Pf) M M (Pf n) := by
  apply cspT_Rep_int_choice_nat_const
  · simp
  · intro m hm
    rcases Set.mem_singleton_iff.mp hm with rfl
    rfl

theorem cspT_Rep_int_choice_set_singleton
    {X : Set α} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set ({X} : Set (Set α)) Pf) M M (Pf X) := by
  apply cspT_Rep_int_choice_set_const
  · simp
  · intro Y hY
    rcases Set.mem_singleton_iff.mp hY with rfl
    rfl

theorem cspT_Rep_int_choice_com_singleton [Inhabited α]
    {a : α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com ({a} : Set α) Pf) M M (Pf a) := by
  apply cspT_Rep_int_choice_com_const
  · simp
  · intro b hb
    rcases Set.mem_singleton_iff.mp hb with rfl
    rfl

theorem cspT_Rep_int_choice_f_singleton [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {x : β} {Pf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f ({x} : Set β) Pf) M M (Pf x) := by
  apply cspT_Rep_int_choice_f_const hf
  · simp
  · intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    rfl

/- The Isabelle theorem bundle `cspT_Rep_int_choice_singleton` is represented by
   `cspT_Rep_int_choice_sum1_singleton`,
   `cspT_Rep_int_choice_sum2_singleton`,
   `cspT_Rep_int_choice_nat_singleton`,
   `cspT_Rep_int_choice_set_singleton`,
   `cspT_Rep_int_choice_com_singleton`, and
   `cspT_Rep_int_choice_f_singleton`. -/

axiom cspT_Rep_int_choice_const_sum_rule
    {C : sets_nats α} {P : proc p α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice C (fun _ => P)) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α) P)

axiom cspT_Rep_int_choice_const_nat_rule
    {N : Set Nat} {P : proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N (fun _ => P)) M M
      (procIte (N = ∅) (proc.DIV : proc p α) P)

axiom cspT_Rep_int_choice_const_set_rule
    {Xs : Set (Set α)} {P : proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs (fun _ => P)) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α) P)

axiom cspT_Rep_int_choice_const_com_rule [Inhabited α]
    {X : Set α} {P : proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com X (fun _ => P)) M M
      (procIte (X = ∅) (proc.DIV : proc p α) P)

axiom cspT_Rep_int_choice_const_f_rule [Inhabited α] [Inhabited β]
    {f : β → α} {X : Set β} {P : proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f X (fun _ => P)) M M
      (procIte (X = ∅) (proc.DIV : proc p α) P)

/- The Isabelle theorem bundle `cspT_Rep_int_choice_const_rule` is represented by
   `cspT_Rep_int_choice_const_sum_rule`,
   `cspT_Rep_int_choice_const_nat_rule`,
   `cspT_Rep_int_choice_const_set_rule`,
   `cspT_Rep_int_choice_const_com_rule`, and
   `cspT_Rep_int_choice_const_f_rule`. -/

/- The Isabelle theorem bundle `cspT_Int_choice_rule` is represented by
   `cspT_Rep_int_choice_sum_DIV`, `cspT_Rep_int_choice_nat_DIV`,
   `cspT_Rep_int_choice_set_DIV`, `cspT_Rep_int_choice_com_DIV`,
   `cspT_Rep_int_choice_f_DIV`, `cspT_Rep_int_choice_sum1_singleton`,
   `cspT_Rep_int_choice_sum2_singleton`, `cspT_Rep_int_choice_nat_singleton`,
   `cspT_Rep_int_choice_set_singleton`, `cspT_Rep_int_choice_com_singleton`,
   `cspT_Rep_int_choice_f_singleton`, `cspT_Int_choice_idem`,
   `cspT_Rep_int_choice_const_sum_rule`, `cspT_Rep_int_choice_const_nat_rule`,
   `cspT_Rep_int_choice_const_set_rule`, `cspT_Rep_int_choice_const_com_rule`,
   and `cspT_Rep_int_choice_const_f_rule`. -/

/-
(*****************************************************************
                          External
 *****************************************************************)

(* to make produced process be concrete *)
-/

theorem cspT_Ext_pre_choice_empty_DIV
    {Pf : α → proc p α} {M1 : p → domTType α} {M2 : q → domTType α} :
    eqT (proc.Ext_pre_choice (∅ : Set α) Pf) M1 M2
      (proc.Ext_pre_choice (∅ : Set α) (fun _ => (proc.DIV : proc q α))) := by
  exact cspT_trans_left_eq (cspT_sym (cspT_STOP_step (Pf := Pf) (M1 := M1) (M2 := M1)))
    (cspT_STOP_step_DIV (M1 := M1) (M2 := M2))

theorem cspT_Ext_choice_unit_l_hsf
    {Qf : α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice (∅ : Set α) Qf) [+] P) M M P := by
  have h₁ :
      eqT (proc.Ext_pre_choice (∅ : Set α) Qf) M M (proc.STOP : proc p α) :=
    cspT_sym (cspT_STOP_step (Pf := Qf) (M1 := M) (M2 := M))
  have h₂ :
      eqT ((proc.Ext_pre_choice (∅ : Set α) Qf) [+] P) M M ((proc.STOP : proc p α) [+] P) :=
    cspT_Ext_choice_cong h₁ cspT_reflex_eq_P
  exact cspT_trans_left_eq h₂ cspT_Ext_choice_unit_l

theorem cspT_Ext_choice_unit_r_hsf
    {Qf : α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT (P [+] proc.Ext_pre_choice (∅ : Set α) Qf) M M P := by
  exact cspT_trans_left_eq cspT_Ext_choice_commut cspT_Ext_choice_unit_l_hsf

/- The Isabelle theorem bundle `cspT_Ext_choice_rule` is represented by
   `cspT_Ext_pre_choice_empty_DIV`, `cspT_Ext_choice_unit_l`,
   `cspT_Ext_choice_unit_l_hsf`, `cspT_Ext_choice_unit_r`,
   `cspT_Ext_choice_unit_r_hsf`, and `cspT_Ext_choice_idem`. -/

/- The Isabelle theorem bundle `cspT_choice_rule` is represented by
   `cspT_Int_choice_rule` and `cspT_Ext_choice_rule`. -/

/-
(*****************************************************************
                          Timeout
 *****************************************************************)

(*------------------*
 |      csp law     |
 *------------------*)

(*** <= Timeout ***)
-/

theorem cspT_Timeout_right
    {P : proc p α} {Q1 Q2 : proc q α} {M1 : p → domTType α} {M2 : q → domTType α}
    (h1 : refT P M1 M2 Q1) (h2 : refT P M1 M2 Q2) :
    refT P M1 M2 (Q1 [> Q2) := by
  have hDist :
      eqT (((Q1 |~| (proc.STOP : proc q α)) [+] Q2)) M2 M2
        ((Q1 [+] Q2) |~| ((proc.STOP : proc q α) [+] Q2)) := by
    simpa using
      (cspT_Ext_choice_dist_l
        (P1 := Q1) (P2 := (proc.STOP : proc q α)) (Q := Q2) (M := M2))
  have hLeft : refT P M1 M2 (Q1 [+] Q2) :=
    cspT_Ext_choice_right h1 h2
  have hRight : refT P M1 M2 (((proc.STOP : proc q α) [+] Q2)) :=
    cspT_rw_right_ref cspT_Ext_choice_unit_l h2
  have hRef :
      refT P M1 M2 ((Q1 [+] Q2) |~| ((proc.STOP : proc q α) [+] Q2)) :=
    cspT_Int_choice_right hLeft hRight
  simpa [Timeout_abb] using cspT_rw_right_ref hDist hRef

/-
(*** STOP [> P  =  P ***)
-/

theorem cspT_STOP_Timeout
    {P : proc p α} {M : p → domTType α} :
    eqT ((proc.STOP : proc p α) [> P) M M P := by
  have h₁ :
      eqT (((proc.STOP : proc p α) |~| proc.STOP) [+] P) M M ((proc.STOP : proc p α) [+] P) :=
    cspT_Ext_choice_cong cspT_Int_choice_idem cspT_reflex_eq_P
  exact cspT_trans_left_eq h₁ cspT_Ext_choice_unit_l

/-
(*================================================*
 |                                                |
 |               auxiliary step laws              |
 |                                                |
 *================================================*)

(* split + resolve *)
-/

private def cspT_Parallel_Timeout_split_resolve_rhs
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

private def cspT_Parallel_Timeout_input_resolve_l_rhs
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

private def cspT_Parallel_Timeout_input_resolve_r_rhs
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

axiom cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV
    {P Q : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    (P = proc.SKIP ∨ P = proc.DIV) →
      (Q = proc.SKIP ∨ Q = proc.DIV) →
        eqT (((proc.Ext_pre_choice Y Pf) [+] P) |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) M M
          (cspT_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf P Q)

theorem cspT_Parallel_Timeout_split_resolve_SKIP_SKIP
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.SKIP)) M M
      (cspT_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.SKIP proc.SKIP) := by
  exact cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inl rfl) (Or.inl rfl)

theorem cspT_Parallel_Timeout_split_resolve_DIV_DIV
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.DIV)) M M
      (cspT_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.DIV proc.DIV) := by
  exact cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inr rfl) (Or.inr rfl)

theorem cspT_Parallel_Timeout_split_resolve_SKIP_DIV
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.DIV)) M M
      (cspT_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.SKIP proc.DIV) := by
  exact cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inl rfl) (Or.inr rfl)

theorem cspT_Parallel_Timeout_split_resolve_DIV_SKIP
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]|
      ((proc.Ext_pre_choice Z Qf) [+] proc.SKIP)) M M
      (cspT_Parallel_Timeout_split_resolve_rhs X Y Z Pf Qf proc.DIV proc.SKIP) := by
  exact cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV (Or.inr rfl) (Or.inl rfl)

/- The Isabelle theorem bundle `cspT_Parallel_Timeout_split_resolve` is represented by
   `cspT_Parallel_Timeout_split_resolve_SKIP_SKIP`,
   `cspT_Parallel_Timeout_split_resolve_DIV_DIV`,
   `cspT_Parallel_Timeout_split_resolve_SKIP_DIV`, and
   `cspT_Parallel_Timeout_split_resolve_DIV_SKIP`. -/

/-
(* input + resolve *)
-/

axiom cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_l
    {P : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    (P = proc.SKIP ∨ P = proc.DIV) →
      eqT (((proc.Ext_pre_choice Y Pf) [+] P) |[X]| proc.Ext_pre_choice Z Qf) M M
        (cspT_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf P)

axiom cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_r
    {Q : proc p α} {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    (Q = proc.SKIP ∨ Q = proc.DIV) →
      eqT (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] Q)) M M
        (cspT_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf Q)

/- The Isabelle theorem bundle `cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV` is represented by
   `cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_l` and
   `cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_r`. -/

theorem cspT_Parallel_Timeout_input_resolve_SKIP_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.Ext_pre_choice Y Pf) [+] (proc.SKIP : proc p α)) |[X]| proc.Ext_pre_choice Z Qf) M M
      (cspT_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf proc.SKIP) := by
  exact cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_l (Or.inl rfl)

theorem cspT_Parallel_Timeout_input_resolve_DIV_l
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (((proc.Ext_pre_choice Y Pf) [+] (proc.DIV : proc p α)) |[X]| proc.Ext_pre_choice Z Qf) M M
      (cspT_Parallel_Timeout_input_resolve_l_rhs X Y Z Pf Qf proc.DIV) := by
  exact cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_l (Or.inr rfl)

theorem cspT_Parallel_Timeout_input_resolve_SKIP_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] (proc.SKIP : proc p α))) M M
      (cspT_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf proc.SKIP) := by
  exact cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_r (Or.inl rfl)

theorem cspT_Parallel_Timeout_input_resolve_DIV_r
    {X Y Z : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice Y Pf |[X]| ((proc.Ext_pre_choice Z Qf) [+] (proc.DIV : proc p α))) M M
      (cspT_Parallel_Timeout_input_resolve_r_rhs X Y Z Pf Qf proc.DIV) := by
  exact cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV_r (Or.inr rfl)

/- The Isabelle theorem bundle `cspT_Parallel_Timeout_input_resolve` is represented by
   `cspT_Parallel_Timeout_input_resolve_SKIP_l`,
   `cspT_Parallel_Timeout_input_resolve_SKIP_r`,
   `cspT_Parallel_Timeout_input_resolve_DIV_l`, and
   `cspT_Parallel_Timeout_input_resolve_DIV_r`. -/

/-
(**************** ;; + resolve ****************)
-/

theorem cspT_SKIP_Seq_compo_step_resolve
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> Q)) := by
  have h₁ :
      eqT ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) ;; Q)) M M
        ((((proc.Ext_pre_choice X Pf) [> (proc.SKIP : proc p α)) ;; Q)) :=
    cspT_Seq_compo_cong cspT_Ext_choice_SKIP_resolve cspT_reflex_eq_P
  exact cspT_trans_left_eq h₁ cspT_SKIP_Seq_compo_step

theorem cspT_DIV_Seq_compo_step_resolve
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) ;; Q)) M M
      (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [+] (proc.DIV : proc p α))) := by
  have h₁ :
      eqT ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) ;; Q)) M M
        ((((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α)) ;; Q)) :=
    cspT_Seq_compo_cong cspT_Ext_choice_DIV_resolve cspT_reflex_eq_P
  have h₂ :
      eqT ((((proc.Ext_pre_choice X Pf) [> (proc.DIV : proc p α)) ;; Q)) M M
        (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> (proc.DIV : proc p α))) :=
    cspT_DIV_Seq_compo_step
  have h₃ :
      eqT (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [> (proc.DIV : proc p α))) M M
        (((proc.Ext_pre_choice X (fun x => Pf x ;; Q)) [+] (proc.DIV : proc p α))) :=
    cspT_sym cspT_Ext_choice_DIV_resolve
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

/- The Isabelle theorem bundle `cspT_SKIP_DIV_Seq_compo_step_resolve` is represented by
   `cspT_SKIP_Seq_compo_step_resolve` and
   `cspT_DIV_Seq_compo_step_resolve`. -/

/- The Isabelle theorem bundle `cspT_SKIP_DIV_resolve` is represented by
   `cspT_SKIP_DIV`, `cspT_Parallel_Timeout_split_resolve`,
   `cspT_Parallel_Timeout_input_resolve`, and
   `cspT_SKIP_DIV_Seq_compo_step_resolve`. -/

/- The Isabelle theorem bundle `cspT_SKIP_or_DIV_resolve` is represented by
   `cspT_Parallel_Timeout_split_resolve_SKIP_or_DIV` and
   `cspT_Parallel_Timeout_input_resolve_SKIP_or_DIV`. -/

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)


(*********************************************************
                       P |[X,Y]| Q
 *********************************************************)
-/

axiom cspT_Alpha_Parallel_step
    {A B X Y : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice A Pf) |[X,Y]| proc.Ext_pre_choice B Qf) M M
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

theorem cspT_Ext_pre_choice_SKIP_commut
    {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.SKIP : proc p α) [+] proc.Ext_pre_choice X Pf) M M
      ((proc.Ext_pre_choice X Pf) [+] proc.SKIP) := by
  exact cspT_Ext_choice_commut

theorem cspT_Ext_pre_choice_DIV_commut
    {X : Set α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.DIV : proc p α) [+] proc.Ext_pre_choice X Pf) M M
      ((proc.Ext_pre_choice X Pf) [+] proc.DIV) := by
  exact cspT_Ext_choice_commut

theorem cspT_Ext_pre_choice_SKIP_assoc
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT
      ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
      ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.SKIP)) := by
  have h₁ :
      eqT
        ((((proc.Ext_pre_choice X Pf) [+] (proc.SKIP : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] ((proc.SKIP : proc p α) [+] proc.Ext_pre_choice Y Qf)) :=
    cspT_Ext_choice_assoc_sym
  have h₂ :
      eqT ((proc.Ext_pre_choice X Pf) [+] ((proc.SKIP : proc p α) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.SKIP)) :=
    cspT_Ext_choice_cong cspT_reflex_eq_P cspT_Ext_pre_choice_SKIP_commut
  have h₃ :
      eqT ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.SKIP)) M M
        ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.SKIP)) :=
    cspT_Ext_choice_assoc
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

theorem cspT_Ext_pre_choice_DIV_assoc
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT
      ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
      ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.DIV)) := by
  have h₁ :
      eqT
        ((((proc.Ext_pre_choice X Pf) [+] (proc.DIV : proc p α)) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] ((proc.DIV : proc p α) [+] proc.Ext_pre_choice Y Qf)) :=
    cspT_Ext_choice_assoc_sym
  have h₂ :
      eqT ((proc.Ext_pre_choice X Pf) [+] ((proc.DIV : proc p α) [+] proc.Ext_pre_choice Y Qf)) M M
        ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.DIV)) :=
    cspT_Ext_choice_cong cspT_reflex_eq_P cspT_Ext_pre_choice_DIV_commut
  have h₃ :
      eqT ((proc.Ext_pre_choice X Pf) [+] (proc.Ext_pre_choice Y Qf [+] proc.DIV)) M M
        ((((proc.Ext_pre_choice X Pf) [+] proc.Ext_pre_choice Y Qf) [+] proc.DIV)) :=
    cspT_Ext_choice_assoc
  exact cspT_trans_left_eq h₁ (cspT_trans_left_eq h₂ h₃)

theorem cspT_Ext_choice_idem_assoc
    {P Q : proc p α} {M : p → domTType α} :
    eqT (((P [+] Q) [+] Q)) M M (P [+] Q) := by
  have h₁ : eqT (((P [+] Q) [+] Q)) M M (P [+] (Q [+] Q)) := cspT_Ext_choice_assoc_sym
  have h₂ :
      eqT (P [+] (Q [+] Q)) M M (P [+] Q) :=
    cspT_Ext_choice_cong cspT_reflex_eq_P cspT_Ext_choice_idem
  exact cspT_trans_left_eq h₁ h₂

theorem cspT_Ext_choice_SKIP_DIV_assoc
    {P : proc p α} {M : p → domTType α} :
    eqT (((P [+] (proc.SKIP : proc p α)) [+] proc.DIV)) M M (P [+] proc.SKIP) := by
  have h₁ :
      eqT (((P [+] (proc.SKIP : proc p α)) [+] proc.DIV)) M M
        (P [+] ((proc.SKIP : proc p α) [+] proc.DIV)) :=
    cspT_Ext_choice_assoc_sym
  have h₂ :
      eqT (P [+] ((proc.SKIP : proc p α) [+] proc.DIV)) M M (P [+] proc.SKIP) :=
    cspT_Ext_choice_cong cspT_reflex_eq_P cspT_SKIP_DIV_Ext_choice1
  exact cspT_trans_left_eq h₁ h₂

theorem cspT_Ext_choice_DIV_SKIP_assoc
    {P : proc p α} {M : p → domTType α} :
    eqT (((P [+] (proc.DIV : proc p α)) [+] proc.SKIP)) M M (P [+] proc.SKIP) := by
  have h₁ :
      eqT (((P [+] (proc.DIV : proc p α)) [+] proc.SKIP)) M M
        (P [+] ((proc.DIV : proc p α) [+] proc.SKIP)) :=
    cspT_Ext_choice_assoc_sym
  have h₂ :
      eqT (P [+] ((proc.DIV : proc p α) [+] proc.SKIP)) M M (P [+] proc.SKIP) :=
    cspT_Ext_choice_cong cspT_reflex_eq_P cspT_SKIP_DIV_Ext_choice2
  exact cspT_trans_left_eq h₁ h₂

/- The Isabelle theorem bundle `cspT_SKIP_DIV_sort` is represented by
   `cspT_Ext_choice_assoc`, `cspT_Ext_pre_choice_SKIP_commut`,
   `cspT_Ext_pre_choice_DIV_commut`, `cspT_Ext_pre_choice_SKIP_assoc`,
   `cspT_Ext_pre_choice_DIV_assoc`, `cspT_Ext_choice_idem_assoc`,
   `cspT_Ext_choice_SKIP_DIV_assoc`, and
   `cspT_Ext_choice_DIV_SKIP_assoc`. -/

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

theorem cspT_rw_flag_left_eq
    {R1 R2 : proc p α} {R3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h12 : eqT R1 M1 M1 R2) (h23 : Not_Decompo_Flag ∧ eqT R2 M1 M3 R3) :
    eqT R1 M1 M3 R3 := by
  exact cspT_rw_left_eq h12 h23.2

theorem cspT_rw_flag_left_ref
    {R1 R2 : proc p α} {R3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h12 : eqT R1 M1 M1 R2) (h23 : Not_Decompo_Flag ∧ refT R2 M1 M3 R3) :
    refT R1 M1 M3 R3 := by
  exact cspT_rw_left_ref h12 h23.2

/- The Isabelle theorem bundle `cspT_rw_flag_left` is represented by
   `cspT_rw_flag_left_eq` and `cspT_rw_flag_left_ref`. -/

theorem cspT_rw_flag_right_eq
    {R1 : proc p α} {R2 R3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h32 : eqT R3 M3 M3 R2) (h12 : Not_Decompo_Flag ∧ eqT R1 M1 M3 R2) :
    eqT R1 M1 M3 R3 := by
  exact cspT_rw_right_eq h32 h12.2

theorem cspT_rw_flag_right_ref
    {R1 : proc p α} {R2 R3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h32 : eqT R3 M3 M3 R2) (h12 : Not_Decompo_Flag ∧ refT R1 M1 M3 R2) :
    refT R1 M1 M3 R3 := by
  exact cspT_rw_right_ref h32 h12.2

/- The Isabelle theorem bundle `cspT_rw_flag_right` is represented by
   `cspT_rw_flag_right_eq` and `cspT_rw_flag_right_ref`. -/

/-
(*------------------------------------------------*
 |              trans with Flag (ref)             |
 *------------------------------------------------*)

(*** rewrite (ref) ***)
-/

theorem cspT_tr_flag_left_eq
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h12 : eqT P1 M1 M1 P2) (h23 : Not_Decompo_Flag ∧ eqT P2 M1 M3 P3) :
    eqT P1 M1 M3 P3 := by
  exact cspT_tr_left_eq h12 h23.2

theorem cspT_tr_flag_left_ref
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h12 : refT P1 M1 M1 P2) (h23 : Not_Decompo_Flag ∧ refT P2 M1 M3 P3) :
    refT P1 M1 M3 P3 := by
  exact cspT_tr_left_ref h12 h23.2

/- The Isabelle theorem bundle `cspT_tr_flag_left` is represented by
   `cspT_tr_flag_left_eq` and `cspT_tr_flag_left_ref`. -/

theorem cspT_tr_flag_right_eq
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h23 : eqT P2 M3 M3 P3) (h12 : Not_Decompo_Flag ∧ eqT P1 M1 M3 P2) :
    eqT P1 M1 M3 P3 := by
  exact cspT_tr_right_eq h23 h12.2

theorem cspT_tr_flag_right_ref
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α}
    (h23 : refT P2 M3 M3 P3) (h12 : Not_Decompo_Flag ∧ refT P1 M1 M3 P2) :
    refT P1 M1 M3 P3 := by
  exact cspT_tr_right_ref h23 h12.2

/- The Isabelle theorem bundle `cspT_tr_flag_right` is represented by
   `cspT_tr_flag_right_eq` and `cspT_tr_flag_right_ref`. -/

/-
(*------------------------------------------------*
 |           trans with Flag (erule)              |
 *------------------------------------------------*)

(*** rewrite (eq) ***)
-/

theorem cspT_rw_flag_left_eqE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop}
    (h13 : eqT P1 M1 M3 P3) (h12 : eqT P1 M1 M1 P2)
    (hR : Not_Decompo_Flag ∧ eqT P2 M1 M3 P3 → R) :
    R := by
  have h23 : eqT P2 M1 M3 P3 := cspT_trans_left_eq (cspT_sym h12) h13
  exact hR ⟨off_Not_Decompo_Flag_True, h23⟩

theorem cspT_rw_flag_left_refE
    {P1 P2 : proc p α} {P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop}
    (h13 : refT P1 M1 M3 P3) (h12 : eqT P1 M1 M1 P2)
    (hR : Not_Decompo_Flag ∧ refT P2 M1 M3 P3 → R) :
    R := by
  have h23 : refT P2 M1 M3 P3 := cspT_rw_left_refE h13 h12 (fun h => h)
  exact hR ⟨off_Not_Decompo_Flag_True, h23⟩

/- The Isabelle theorem bundle `cspT_rw_flag_leftE` is represented by
   `cspT_rw_flag_left_eqE` and `cspT_rw_flag_left_refE`. -/

theorem cspT_rw_flag_right_eqE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop}
    (h13 : eqT P1 M1 M3 P3) (h32 : eqT P3 M3 M3 P2)
    (hR : Not_Decompo_Flag ∧ eqT P1 M1 M3 P2 → R) :
    R := by
  have h12 : eqT P1 M1 M3 P2 := cspT_rw_right_eqE h13 h32 (fun h => h)
  exact hR ⟨off_Not_Decompo_Flag_True, h12⟩

theorem cspT_rw_flag_right_refE
    {P1 : proc p α} {P2 P3 : proc q α}
    {M1 : p → domTType α} {M3 : q → domTType α} {R : Prop}
    (h13 : refT P1 M1 M3 P3) (h32 : eqT P3 M3 M3 P2)
    (hR : Not_Decompo_Flag ∧ refT P1 M1 M3 P2 → R) :
    R := by
  have h12 : refT P1 M1 M3 P2 := cspT_rw_right_refE h13 h32 (fun h => h)
  exact hR ⟨off_Not_Decompo_Flag_True, h12⟩

/- The Isabelle theorem bundle `cspT_rw_flag_rightE` is represented by
   `cspT_rw_flag_right_eqE` and `cspT_rw_flag_right_refE`. -/

/-
(*===============================================================*
 |  decompostion of Sequential composition with a flag           |
 |  It is often useful that the second process is not rewritten. |
 |                    (since CSP-Prover 5)                       |
 *===============================================================*)
-/

theorem cspT_Seq_compo_mono_flag
    {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (h1 : refT P1 M1 M2 Q1) (h2 : Not_Rewrite_Flag ∧ refT P2 M1 M2 Q2) :
    refT (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  exact cspT_Seq_compo_mono h1 h2.2

theorem cspT_Seq_compo_cong_flag
    {P1 P2 : proc p α} {Q1 Q2 : proc q α}
    {M1 : p → domTType α} {M2 : q → domTType α}
    (h1 : eqT P1 M1 M2 Q1) (h2 : Not_Rewrite_Flag ∧ eqT P2 M1 M2 Q2) :
    eqT (P1 ;; P2) M1 M2 (Q1 ;; Q2) := by
  exact cspT_Seq_compo_cong h1 h2.2

/- The Isabelle theorem bundle `cspT_free_mono_flag` is represented by
   `cspT_Ext_choice_mono`, `cspT_Int_choice_mono`, `cspT_Parallel_mono`,
   `cspT_Hiding_mono`, `cspT_Renaming_mono`, `cspT_Seq_compo_mono_flag`,
   `cspT_Depth_rest_mono`, `cspT_Rep_int_choice_mono_UNIV`, and
   `cspT_Alpha_parallel_mono`. -/

/- The Isabelle theorem bundle `cspT_free_cong_flag` is represented by
   `cspT_Ext_choice_cong`, `cspT_Int_choice_cong`, `cspT_Parallel_cong`,
   `cspT_Hiding_cong`, `cspT_Renaming_cong`, `cspT_Seq_compo_cong_flag`,
   `cspT_Depth_rest_cong`, `cspT_Rep_int_choice_cong_UNIV`, and
   `cspT_Alpha_parallel_cong`. -/

/- The Isabelle theorem bundle `cspT_free_decompo_flag` is represented by
   `cspT_free_mono_flag` and `cspT_free_cong_flag`. -/

end
