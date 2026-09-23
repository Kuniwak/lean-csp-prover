           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2005         |
            |               February 2006               |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.FNF_F.FNF_F

open Function
open SumType
open fpmode

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Counter_EX

/-  The following simplification rules are deleted in this theory file -/
/-  because they unexpectly rewrite `Set.sUnion` and `Set.sInter`.     -/
/-                  `disj_not1: (~ P | Q) = (P --> Q)`                 -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `disj_not1`, so there is -/
/-  nothing to disable or re-enable here.                              -/

/-  The following simplification rules are deleted in this theory file -/
/-       `P (if Q then x else y) = ((Q --> P x) & (~ Q --> P y))`      -/
/- Isabelle 2017: `split_if --> if_split`                              -/
/-                                                                     -/
/-  Lean has no direct analogue of Isabelle's `if_split`, so there is  -/
/-  nothing to disable or re-enable here.                              -/

/-
(*****************************************************************

         1.
         2.
         3.

 *****************************************************************)
-/

/- there is a process which is not contained in fsfF_proc -/

/- Lean note:
   Isabelle's `typedecl nopn` was ported as two axioms; it is now an
   `opaque` `NonemptyType` — the same abstraction without extending the
   axiom base. -/

private opaque nopn_spec : NonemptyType.{0}

def nopn : Type := nopn_spec.type

@[reducible] noncomputable def nopn_inhabited : Inhabited nopn :=
  ⟨Classical.choice nopn_spec.property⟩

attribute [instance] nopn_inhabited

inductive event where
  | event_a
deriving DecidableEq, Inhabited

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

instance Set_nopnfun : HasPNfun nopn event where
  PNfun := fun _ => proc.STOP

def PAf : Nat → proc nopn event
  | 0 => proc.DIV
  | Nat.succ n => event.event_a ~> PAf n

def PA : proc nopn event :=
  Rep_int_choice_nat Set.univ PAf

theorem PA_def :
    PA = Rep_int_choice_nat Set.univ PAf :=
  rfl

private def CounterTarget (P : proc nopn event) : proc nopn event :=
  (((proc.Ext_pre_choice ({event.event_a} : Set event)
      (fun a => if a = event.event_a then P else proc.DIV)) [+] proc.DIV) |~|
    Rep_int_choice_set ({({event.event_a} : Set event)} : Set (Set event))
      (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))

/-- `PA` is its own successor: the zero branch contributes `DIV`, which is the
    unit of internal choice, and the rest re-indexes to `PA` behind one event. -/
private theorem PA_unfold : eqFfix PA (event.event_a ~> PA) := by
  have hsplit : (Set.univ : Set Nat) = ({0} : Set Nat) ∪ {m | ∃ n, m = Nat.succ n} := by
    ext m
    cases m with
    | zero => exact ⟨fun _ => Or.inl rfl, fun _ => trivial⟩
    | succ k => exact ⟨fun _ => Or.inr ⟨k, rfl⟩, fun _ => trivial⟩
  rw [PA_def]
  refine cspF_trans_left_eq (cspF_Rep_int_choice_cong_nat hsplit (fun n _ => cspF_reflex_eq_P)) ?_
  refine cspF_trans_left_eq cspF_Rep_int_choice_nat_union_Int ?_
  refine cspF_trans_left_eq
    (cspF_Int_choice_cong cspF_Rep_int_choice_nat_singleton cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq (cspF_Int_choice_unit_l (P :=
    Rep_int_choice_nat {m | ∃ n, m = Nat.succ n} PAf)) ?_
  -- re-index the successors
  have hreindex : eqFfix (Rep_int_choice_nat {m | ∃ n, m = Nat.succ n} PAf)
      (Rep_int_choice_nat Set.univ (fun n => event.event_a ~> PAf n)) := by
    refine cspF_eq_ref_iff.mpr ⟨?_, ?_⟩
    · refine cspF_Rep_int_choice_nat_right (fun n _ => ?_)
      exact cspF_Rep_int_choice_nat_left_x (n := Nat.succ n) ⟨n, rfl⟩ cspF_reflex_ref_P
    · refine cspF_Rep_int_choice_nat_right (fun m hm => ?_)
      obtain ⟨n, rfl⟩ := hm
      exact cspF_Rep_int_choice_nat_left_x (n := n) (Set.mem_univ n) cspF_reflex_ref_P
  refine cspF_trans_left_eq hreindex ?_
  exact cspF_sym (cspF_Act_prefix_Dist_nat (by
    intro h
    have : (0 : Nat) ∈ (Set.univ : Set Nat) := trivial
    rw [h] at this
    exact this))

theorem PA_eqF :
    eqFfix PA
      ((((proc.Ext_pre_choice ({event.event_a} : Set event)
            (fun a => if a = event.event_a then PA else proc.DIV)) [+] proc.DIV) |~|
        Rep_int_choice_set ({({event.event_a} : Set event)} : Set (Set event))
          (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) := by
  refine cspF_trans_left_eq PA_unfold ?_
  refine cspF_trans_left_eq cspF_Act_prefix_step ?_
  refine cspF_trans_left_eq (cspF_input_DIV
    (A := ({event.event_a} : Set event)) (Pf := fun _ => PA)) ?_
  refine cspF_Int_choice_cong ?_ ?_
  · refine cspF_Ext_choice_cong (cspF_Ext_pre_choice_cong rfl (fun a ha => ?_))
      cspF_reflex_eq_P
    have : a = event.event_a := ha
    subst this
    rw [if_pos rfl]
    exact cspF_reflex_eq_P
  · exact cspF_sym cspF_Rep_int_choice_set_singleton

theorem NPA_fnfF_proc {NPA : proc nopn event} :
    fnfF_proc NPA →
      fnfF_proc
        ((((proc.Ext_pre_choice ({event.event_a} : Set event)
              (fun a => if a = event.event_a then NPA else proc.DIV)) [+] proc.DIV) |~|
          Rep_int_choice_set ({({event.event_a} : Set event)} : Set (Set event))
            (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) := by
  intro hNPA
  apply fnfF_proc_EX_I
  refine ⟨({event.event_a} : Set event),
    ({({event.event_a} : Set event)} : Set (Set event)),
    (fun a => if a = event.event_a then NPA else proc.DIV),
    proc.DIV, rfl, ?_, ?_, ?_, ?_⟩
  · intro a
    by_cases ha : a ∈ ({event.event_a} : Set event)
    · have ha' : a = event.event_a := Set.mem_singleton_iff.mp ha
      subst ha'
      simp [ha, hNPA]
    · exfalso
      exact ha (by cases a; simp)
  · intro Y hY
    rcases hY with ⟨⟨Y0, hY0, hY0subY⟩, hYsub⟩
    rcases Set.mem_singleton_iff.mp hY0 with rfl
    apply Set.mem_singleton_iff.mpr
    ext a
    constructor
    · intro _ha
      have haSingleton : a ∈ ({event.event_a} : Set event) := by
        cases a
        simp
      exact haSingleton
    · intro ha
      exact hY0subY ha
  · intro a ha
    rcases ha with ⟨Y, hY, haY⟩
    rcases Set.mem_singleton_iff.mp hY with rfl
    exact haY
  · exact Or.inr rfl

theorem PA_not_fnfF_proc_lm {NPA : proc nopn event} :
    eqFfix PA NPA →
      fnfF_proc NPA →
        eqFfix PA
          ((((proc.Ext_pre_choice ({event.event_a} : Set event)
                (fun a => if a = event.event_a then NPA else proc.DIV)) [+] proc.DIV) |~|
            Rep_int_choice_set ({({event.event_a} : Set event)} : Set (Set event))
              (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) := by
  intro hPA _hNPA
  change eqFfix PA (CounterTarget NPA)
  have hInput :
      eqFfix
        (proc.Ext_pre_choice ({event.event_a} : Set event)
          (fun a => if a = event.event_a then PA else proc.DIV))
        (proc.Ext_pre_choice ({event.event_a} : Set event)
          (fun a => if a = event.event_a then NPA else proc.DIV)) := by
    apply cspF_Ext_pre_choice_cong rfl
    intro a ha
    have ha' : a = event.event_a := by
      cases a
      rfl
    subst ha'
    simpa using hPA
  have hTargetCong : eqFfix (CounterTarget PA) (CounterTarget NPA) := by
    unfold CounterTarget
    exact cspF_Int_choice_cong
      (cspF_Ext_choice_cong hInput cspF_reflex_eq_DIV)
      cspF_reflex_eq_P
  exact cspF_trans_left_eq PA_eqF hTargetCong

private theorem CounterTarget_not_self :
    ∀ {P : proc nopn event}, fnfF_proc P → P ≠ CounterTarget P := by
  intro P hP
  induction hP with
  | fnfF_proc_rule hPf hPfDiv hCond hUnion hQ ih =>
      rename_i A Ys Pf Q
      intro hEq
      have hEq0 := hEq
      unfold CounterTarget at hEq
      injection hEq with hLeft _hRight
      injection hLeft with hExt _hQ
      injection hExt with hA hPfEq
      have hEventA : event.event_a ∈ A := by
        simp [hA]
      have hPfSelf :
          Pf event.event_a =
            ((((proc.Ext_pre_choice A Pf) [+] Q) |~|
              Rep_int_choice_set Ys (fun Y => proc.Ext_pre_choice Y (fun _ => proc.DIV)))) := by
        have h := congrArg (fun f => f event.event_a) hPfEq
        simpa using h
      have hSubEq : Pf event.event_a = CounterTarget (Pf event.event_a) := by
        simpa [CounterTarget, hPfSelf] using hEq0
      exact (ih event.event_a hEventA) hSubEq

theorem PA_not_fnfF_proc {NPA : proc nopn event} :
    eqFfix PA NPA →
      ¬ fnfF_proc NPA := by
  intro hPA hNPA
  have hCounter : eqFfix NPA (CounterTarget NPA) := by
    exact cspF_trans_left_eq (cspF_sym hPA) (PA_not_fnfF_proc_lm hPA hNPA)
  have hEq : NPA = CounterTarget NPA :=
    fnfF_syntactical_equality_only_if hNPA (NPA_fnfF_proc hNPA) hCounter
  exact CounterTarget_not_self hNPA hEq

/- (****************** to add them again ******************) -/

/-  Lean has no direct analogue of Isabelle's `declare if_split [split]` -/
/-  and `declare disj_not1 [simp]`, so there is nothing to re-enable.   -/

end Counter_EX
