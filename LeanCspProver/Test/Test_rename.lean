           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2009-1       |
            |              January 2010                 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

noncomputable section

namespace Test_rename

local infix:50 " =F " => eqFfix

/- Lean note: `STOPp` and `A123` only exist to keep the statements below inside
   the line limit.  Both are `abbrev`, hence reducible, so the propositions are
   the same terms they were spelled out as. -/

inductive Event where
  | a1
  | a2
  | a3
  | aa
deriving DecidableEq, Inhabited

private abbrev STOPp (p : Type _) : proc p Event := proc.STOP

private abbrev A123 : Set Event := {Event.a1, Event.a2, Event.a3}

def RenList : List (Set (Event × Event)) :=
  [Event.a1 <-- Event.aa, Event.a2 <-- Event.aa, Event.a3 <-- Event.aa]

theorem RenList_def :
    RenList = [Event.a1 <-- Event.aa, Event.a2 <-- Event.aa, Event.a3 <-- Event.aa] :=
  rfl

/- automatic proof -/

/- note: `Renaming_List` is used in Lean for the Isabelle syntax `[[ ]] *`. -/

theorem automatic_proof {p : Type _} [HasPNfun p Event] [HasFPmode] :
    Renaming_List
        (Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)
        RenList =F
      (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) := by
  have hSTOP_r1 :
      ((STOPp p[[Event.a1 <-- Event.aa]])) =F
        STOPp p := by
    exact
      cspF_SKIP_or_DIV_or_STOP_Renaming_Id
        (P := STOPp p)
        (r := Event.a1 <-- Event.aa)
        (M := MF)
        (Or.inr (Or.inr rfl))
  have hA3_r1 :
      (((Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])) =F
        (Event.a3 ~> STOPp p) := by
    have h1 :
        (((Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])) =F
          (Event.a3 ~> ((STOPp p)[[Event.a1 <-- Event.aa]])) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_notin
          (a := Event.a1) (b := Event.aa) (c := Event.a3)
          (P := STOPp p) (M := MF) (by decide)
    have h2 :
        (Event.a3 ~> ((STOPp p)[[Event.a1 <-- Event.aa]])) =F
          (Event.a3 ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hSTOP_r1
    exact cspF_trans_left_eq h1 h2
  have hA23_r1 :
      (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])) =F
        (Event.a2 ~> Event.a3 ~> STOPp p) := by
    have h1 :
        (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])) =F
          (Event.a2 ~> (((Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_notin
          (a := Event.a1) (b := Event.aa) (c := Event.a2)
          (P := Event.a3 ~> STOPp p) (M := MF) (by decide)
    have h2 :
        (Event.a2 ~> (((Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]]))) =F
          (Event.a2 ~> Event.a3 ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA3_r1
    exact cspF_trans_left_eq h1 h2
  have hRename1 :
      (((Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])) =F
        (Event.aa ~> Event.a2 ~> Event.a3 ~> STOPp p) := by
    have h1 :
        (((Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])) =F
          (Event.aa ~> (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_in
          (a := Event.a1) (b := Event.aa)
          (P := Event.a2 ~> Event.a3 ~> STOPp p)
          (M := MF)
    have h2 :
        (Event.aa ~> (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]]))) =F
          (Event.aa ~> Event.a2 ~> Event.a3 ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA23_r1
    exact cspF_trans_left_eq h1 h2
  -- second renaming: a2 <-- aa
  have hSTOP_r2 :
      ((STOPp p[[Event.a2 <-- Event.aa]])) =F
        STOPp p := by
    exact
      cspF_SKIP_or_DIV_or_STOP_Renaming_Id
        (P := STOPp p)
        (r := Event.a2 <-- Event.aa)
        (M := MF)
        (Or.inr (Or.inr rfl))
  have hA3_r2 :
      (((Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])) =F
        (Event.a3 ~> STOPp p) := by
    have h1 :
        (((Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])) =F
          (Event.a3 ~> ((STOPp p)[[Event.a2 <-- Event.aa]])) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_notin
          (a := Event.a2) (b := Event.aa) (c := Event.a3)
          (P := STOPp p) (M := MF) (by decide)
    have h2 :
        (Event.a3 ~> ((STOPp p)[[Event.a2 <-- Event.aa]])) =F
          (Event.a3 ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hSTOP_r2
    exact cspF_trans_left_eq h1 h2
  have hA23_r2 :
      (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])) =F
        (Event.aa ~> Event.a3 ~> STOPp p) := by
    have h1 :
        (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])) =F
          (Event.aa ~> (((Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_in
          (a := Event.a2) (b := Event.aa)
          (P := Event.a3 ~> STOPp p)
          (M := MF)
    have h2 :
        (Event.aa ~> (((Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]]))) =F
          (Event.aa ~> Event.a3 ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA3_r2
    exact cspF_trans_left_eq h1 h2
  have hRename2 :
      (((Event.aa ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])) =F
        (Event.aa ~> Event.aa ~> Event.a3 ~> STOPp p) := by
    have h1 :
        (((Event.aa ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])) =F
          (Event.aa ~> (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_notin
          (a := Event.a2) (b := Event.aa) (c := Event.aa)
          (P := Event.a2 ~> Event.a3 ~> STOPp p)
          (M := MF) (by decide)
    have h2 :
        (Event.aa ~> (((Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]]))) =F
          (Event.aa ~> Event.aa ~> Event.a3 ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA23_r2
    exact cspF_trans_left_eq h1 h2
  -- third renaming: a3 <-- aa
  have hSTOP_r3 :
      ((STOPp p[[Event.a3 <-- Event.aa]])) =F
        STOPp p := by
    exact
      cspF_SKIP_or_DIV_or_STOP_Renaming_Id
        (P := STOPp p)
        (r := Event.a3 <-- Event.aa)
        (M := MF)
        (Or.inr (Or.inr rfl))
  have hA3_r3 :
      (((Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
        (Event.aa ~> STOPp p) := by
    have h1 :
        (((Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
          (Event.aa ~> ((STOPp p)[[Event.a3 <-- Event.aa]])) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_in
          (a := Event.a3) (b := Event.aa)
          (P := STOPp p)
          (M := MF)
    have h2 :
        (Event.aa ~> ((STOPp p)[[Event.a3 <-- Event.aa]])) =F
          (Event.aa ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hSTOP_r3
    exact cspF_trans_left_eq h1 h2
  have hA23_r3 :
      (((Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
        (Event.aa ~> Event.aa ~> STOPp p) := by
    have h1 :
        (((Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
          (Event.aa ~> (((Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_notin
          (a := Event.a3) (b := Event.aa) (c := Event.aa)
          (P := Event.a3 ~> STOPp p)
          (M := MF) (by decide)
    have h2 :
        (Event.aa ~> (((Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]]))) =F
          (Event.aa ~> Event.aa ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA3_r3
    exact cspF_trans_left_eq h1 h2
  have hRename3 :
      (((Event.aa ~> Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
        (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) := by
    have h1 :
        (((Event.aa ~> Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
          (Event.aa ~> (((Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_event_step_notin
          (a := Event.a3) (b := Event.aa) (c := Event.aa)
          (P := Event.aa ~> Event.a3 ~> STOPp p)
          (M := MF) (by decide)
    have h2 :
        (Event.aa ~> (((Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]]))) =F
          (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA23_r3
    exact cspF_trans_left_eq h1 h2
  -- compose the three renamings
  have h1 :
      ((((Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a1 <-- Event.aa]])
          [[Event.a2 <-- Event.aa]])[[Event.a3 <-- Event.aa]]) =F
        ((((Event.aa ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])
          [[Event.a3 <-- Event.aa]])) := by
    exact cspF_Renaming_cong rfl (cspF_Renaming_cong rfl hRename1)
  have h2 :
      ((((Event.aa ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Event.a2 <-- Event.aa]])
          [[Event.a3 <-- Event.aa]])) =F
        (((Event.aa ~> Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) := by
    exact cspF_Renaming_cong rfl hRename2
  have h3 :
      (((Event.aa ~> Event.aa ~> Event.a3 ~> STOPp p)[[Event.a3 <-- Event.aa]])) =F
        (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) := by
    exact hRename3
  simpa [RenList_def, Renaming_List] using
    (cspF_trans_left_eq h1 (cspF_trans_left_eq h2 h3))

/- step by step proof -/

theorem step_by_step_proof {p : Type _} [HasPNfun p Event] [HasFPmode] :
    Renaming_List
        (Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)
        RenList =F
      (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) :=
  automatic_proof

/- the other renaming technique -/

def Ren : Set (Event × Event) :=
  A123 <<- Event.aa

theorem Ren_def :
    Ren = (A123 <<- Event.aa) :=
  rfl

/- note: Lean keeps the single-renaming notation `[[ ]]`. -/

theorem automatic_proof_other_renaming_technique {p : Type _} [HasPNfun p Event] [HasFPmode] :
    ((Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)[[Ren]]) =F
      (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) := by
  have hSTOP :
      ((STOPp p[[A123 <<- Event.aa]])) =F
        STOPp p := by
    exact
      cspF_SKIP_or_DIV_or_STOP_Renaming_Id
        (P := STOPp p)
        (r := (A123 <<- Event.aa))
        (M := MF)
        (Or.inr (Or.inr rfl))
  have hA3 :
      (((Event.a3 ~> STOPp p)[[A123 <<- Event.aa]])) =F
        (Event.aa ~> STOPp p) := by
    have h1 :
        (((Event.a3 ~> STOPp p)[[A123 <<- Event.aa]])) =F
          (Event.aa ~> ((STOPp p[[A123 <<- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_set_event_step_in
          (a := Event.a3) (A := A123) (b := Event.aa)
          (P := STOPp p)
          (M := MF)
          (by simp)
    have h2 :
        (Event.aa ~> ((STOPp p[[A123 <<- Event.aa]]))) =F
          (Event.aa ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hSTOP
    exact cspF_trans_left_eq h1 h2
  have hA23 :
      (((Event.a2 ~> Event.a3 ~> STOPp p)[[A123 <<- Event.aa]])) =F
        (Event.aa ~> Event.aa ~> STOPp p) := by
    have h1 :
        (((Event.a2 ~> Event.a3 ~> STOPp p)[[A123 <<- Event.aa]])) =F
          (Event.aa ~> (((Event.a3 ~> STOPp p)[[A123 <<- Event.aa]]))) := by
      exact
        cspF_Act_prefix_Renaming2_set_event_step_in
          (a := Event.a2) (A := A123) (b := Event.aa)
          (P := Event.a3 ~> STOPp p)
          (M := MF)
          (by simp)
    have h2 :
        (Event.aa ~> (((Event.a3 ~> STOPp p)[[A123 <<- Event.aa]]))) =F
          (Event.aa ~> Event.aa ~> STOPp p) := by
      exact cspF_Act_prefix_cong rfl hA3
    exact cspF_trans_left_eq h1 h2
  have h1 :
      (((Event.a1 ~> Event.a2 ~> Event.a3 ~> STOPp p)[[A123 <<- Event.aa]])) =F
        (Event.aa ~> (((Event.a2 ~> Event.a3 ~> STOPp p)[[A123 <<- Event.aa]]))) := by
    exact
      cspF_Act_prefix_Renaming2_set_event_step_in
        (a := Event.a1) (A := A123) (b := Event.aa)
        (P := Event.a2 ~> Event.a3 ~> STOPp p)
        (M := MF)
        (by simp)
  have h2 :
      (Event.aa ~> (((Event.a2 ~> Event.a3 ~> STOPp p)[[A123 <<- Event.aa]]))) =F
        (Event.aa ~> Event.aa ~> Event.aa ~> STOPp p) := by
    exact cspF_Act_prefix_cong rfl hA23
  simpa [Ren_def] using cspF_trans_left_eq h1 h2

end Test_rename
