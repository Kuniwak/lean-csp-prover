           /- -------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |           November 2012 for Isabelle 2012 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.UCD.UCD_proc1

open Classical
open fpmode

noncomputable section

local infix:50 " =F " => eqFfix
local notation:50 P " <=F " Q => refFfix P Q

/- 
(*****************************************************************

         1.

 *****************************************************************)
-/

/- ======================= Circ ======================= -/

inductive PNRC where
  | PreCircSpecC : Nat × List Att → PNRC
  | PreCircSpecL : Nat × List Att → PNRC
  | PreCircSpecR : Nat × List Att → PNRC
deriving DecidableEq, Inhabited

private abbrev pChild (c : Nat) : proc PN Event :=
  proc.Proc_name (PN.Child c)

private abbrev pChildL (cx : Nat × Nat) : proc PN Event :=
  proc.Proc_name (PN.ChildL cx)

private abbrev pChildR (c : Nat) : proc PN Event :=
  proc.Proc_name (PN.ChildR c)

private abbrev pLineSpec (s : List Att) : proc PN Event :=
  proc.Proc_name (PN.LineSpec s)

private abbrev pPreCircSpecC (n : Nat) (s : List Att) : proc PNRC Event :=
  proc.Proc_name (PNRC.PreCircSpecC (n, s))

private abbrev pPreCircSpecL (n : Nat) (s : List Att) : proc PNRC Event :=
  proc.Proc_name (PNRC.PreCircSpecL (n, s))

private abbrev pPreCircSpecR (n : Nat) (s : List Att) : proc PNRC Event :=
  proc.Proc_name (PNRC.PreCircSpecR (n, s))

def PNRCdef : PNRC → proc PNRC Event
  | PNRC.PreCircSpecC (n, s) =>
      IF ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s THEN
        (Send_prefix Event.left (n / 2) (pPreCircSpecR (n / 2) s)) [+]
          (Send_prefix Event.right (getNat (hd s) / 2) (pPreCircSpecL n s))
      ELSE
        proc.STOP
  | PNRC.PreCircSpecL (n, s) =>
      IF ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s THEN
        Send_prefix Event.left (n / 2)
          (pPreCircSpecC (fill (n / 2 + getNat (hd s) / 2)) (nextR (nextL s, n / 2)))
      ELSE
        proc.STOP
  | PNRC.PreCircSpecR (n, s) =>
      IF ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s THEN
        Send_prefix Event.right (getNat (hd s) / 2)
          (pPreCircSpecC (fill (n + getNat (hd s) / 2)) (nextL (nextR (s, n))))
      ELSE
        proc.STOP

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_PNRCdef : HasPNfun PNRC Event where
  PNfun := PNRCdef

@[simp]
theorem Set_PNRCdef_def (pn : PNRC) :
    PNfun pn = PNRCdef pn :=
  rfl

/- ------------------ *
      guardedness
 * ------------------ -/

@[simp] theorem guardedfun_PNRC :
    guardedfun PNRCdef := by
  intro pn
  rcases pn with ⟨n, s⟩ | ⟨n, s⟩ | ⟨n, s⟩ <;>
    simp [PNRCdef, Send_prefix, guarded, noHide]

/- -----------------------DF---------------------------------- -/

inductive DFtickName where
  | DFtick
deriving DecidableEq, Inhabited

private abbrev pDFtick : proc DFtickName Event :=
  proc.Proc_name DFtickName.DFtick

def DFtickfun : DFtickName → proc DFtickName Event
  | DFtickName.DFtick =>
      (Nondet_send_prefix (fun x : Event => x) Set.univ (fun _ => pDFtick)) |~| proc.SKIP

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_DFtickfun : HasPNfun DFtickName Event where
  PNfun := DFtickfun

@[simp]
theorem Set_DFtickfun_def (pn : DFtickName) :
    PNfun pn = DFtickfun pn :=
  rfl

@[simp] theorem guardedfun_DFtick :
    guardedfun DFtickfun := by
  intro pn
  cases pn
  simp [DFtickfun, Nondet_send_prefix, guarded, noHide]

/- Lean note:
   Isabelle's `!<f> :X .. Pf` (`CSP_syntax.thy:252`,
   `!<f> :X .. Pf == ! :(f ` X) .. (%x. Pf ((inv f) x))`) is a replicated
   *internal choice* indexed through `f`; it performs no event.  The port had
   `Nondet_send_prefix`, which is `!<f> :X -> Pf` and prefixes each branch
   with `f x`.  The source here writes `..`, so it is `Rep_int_choice_f`. -/

def DF_to_PreCircSpecC : DFtickName → proc PNRC Event
  | DFtickName.DFtick =>
      (Rep_int_choice_nat Set.univ fun n =>
        Rep_int_choice_f Event.stlist {s | ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s} fun s =>
          pPreCircSpecC n s)
      |~|
      (Rep_int_choice_nat Set.univ fun n =>
        Rep_int_choice_f Event.stlist {s | ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s} fun s =>
          pPreCircSpecL n s)
      |~|
      (Rep_int_choice_nat Set.univ fun n =>
        Rep_int_choice_f Event.stlist {s | ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s} fun s =>
          pPreCircSpecR n s)

/- --------------------------------------- *
            deadlock freeness
 * --------------------------------------- -/

private abbrev okAtt (s : List Att) : Prop :=
  ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s

/-- Every state the spec can reach is again a legal state. -/
private theorem okAtt_nextR_nextL {s : List Att} (h : okAtt s) (z : Nat) :
    okAtt (nextR (nextL s, z)) := by
  obtain ⟨hchk, hne, hgL, hgR⟩ := h
  have hchkL : ChkLCR (nextL s) := (ChkLCR_nextL hgL).mpr hchk
  have hgRL : guardR (nextL s) := ChkLCR_guardL_guardR_nextL hchk hgL
  refine ⟨(ChkLCR_nextR hgRL).mpr hchkL, ?_, ?_, guardR_nextR_nextL hchk hgL hgR⟩
  · exact not_nil_nextR_not_nil (not_nil_nextL_not_nil hne)
  · exact ChkLCR_guardR_guardL_nextR hchkL hgRL

private theorem okAtt_nextL_nextR {s : List Att} (h : okAtt s) (z : Nat) :
    okAtt (nextL (nextR (s, z))) := by
  obtain ⟨hchk, hne, hgL, hgR⟩ := h
  have hchkR : ChkLCR (nextR (s, z)) := (ChkLCR_nextR hgR).mpr hchk
  have hgLR : guardL (nextR (s, z)) := ChkLCR_guardR_guardL_nextR hchk hgR
  refine ⟨(ChkLCR_nextL hgLR).mpr hchkR, ?_, guardL_nextL_nextR hchk hgL hgR, ?_⟩
  · exact not_nil_nextL_not_nil (not_nil_nextR_not_nil hne)
  · exact ChkLCR_guardL_guardR_nextL hchkR hgLR

private theorem IF_posRC {c : Prop} [Decidable c] (h : c) (P Q : proc PNRC Event) :
    eqF (IF c THEN P ELSE Q) MF MF P := by
  rw [decide_eq_true h]
  exact cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

/-- Selecting one component of `DF_to_PreCircSpecC`. -/
private theorem DF_to_C {m : Nat} {r : List Att} (hr : okAtt r) :
    refF (DF_to_PreCircSpecC DFtickName.DFtick) MF MF (pPreCircSpecC m r) := by
  refine cspF_Int_choice_left1 (cspF_Int_choice_left1 ?_)
  refine cspF_Rep_int_choice_nat_left_x (n := m) (Set.mem_univ m) ?_
  exact cspF_Rep_int_choice_f_left_x (f := Event.stlist)
    (X := {r' | ChkLCR r' ∧ r' ≠ [] ∧ guardL r' ∧ guardR r'})
    (Pf := fun r' => pPreCircSpecC m r') (a := r) inj_stlist hr cspF_reflex_ref_P

private theorem DF_to_L {m : Nat} {r : List Att} (hr : okAtt r) :
    refF (DF_to_PreCircSpecC DFtickName.DFtick) MF MF (pPreCircSpecL m r) := by
  refine cspF_Int_choice_left1 (cspF_Int_choice_left2 ?_)
  refine cspF_Rep_int_choice_nat_left_x (n := m) (Set.mem_univ m) ?_
  exact cspF_Rep_int_choice_f_left_x (f := Event.stlist)
    (X := {r' | ChkLCR r' ∧ r' ≠ [] ∧ guardL r' ∧ guardR r'})
    (Pf := fun r' => pPreCircSpecL m r') (a := r) inj_stlist hr cspF_reflex_ref_P

private theorem DF_to_R {m : Nat} {r : List Att} (hr : okAtt r) :
    refF (DF_to_PreCircSpecC DFtickName.DFtick) MF MF (pPreCircSpecR m r) := by
  refine cspF_Int_choice_left2 ?_
  refine cspF_Rep_int_choice_nat_left_x (n := m) (Set.mem_univ m) ?_
  exact cspF_Rep_int_choice_f_left_x (f := Event.stlist)
    (X := {r' | ChkLCR r' ∧ r' ≠ [] ∧ guardL r' ∧ guardR r'})
    (Pf := fun r' => pPreCircSpecR m r') (a := r) inj_stlist hr cspF_reflex_ref_P

private theorem unwRC (pn : PNRC) :
    eqF (proc.Proc_name pn : proc PNRC Event) MF MF (PNRCdef pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PNRC⟩))

/-- `$DFtick` after one step: it can offer any single event and then be
    `$DFtick` again. -/
private theorem DF_step_one {a : Event} {Q : proc PNRC Event}
    (h : refF (DF_to_PreCircSpecC DFtickName.DFtick) MF MF Q) :
    refF (Int_pre_choice Set.univ
        (fun _ : Event => DF_to_PreCircSpecC DFtickName.DFtick)) MF MF (a ~> Q) :=
  cspF_Int_pre_choice_left_x (a := a) (Set.mem_univ a) (cspF_Act_prefix_mono rfl h)

theorem PreCircSpecC_DF {n : Nat} {s : List Att} :
  ChkLCR s → s ≠ [] → guardL s → guardR s →
    refF pDFtick MF MF (pPreCircSpecC n s) := by
  intro hchk hne hgL hgR
  refine cspF_fp_induct_ref_left (Pf := DFtickfun) (f := DF_to_PreCircSpecC)
    (p0 := DFtickName.DFtick) rfl (Or.inl rfl) guardedfun_DFtick
    (DF_to_C ⟨hchk, hne, hgL, hgR⟩) ?_
  intro p
  cases p
  have hDF : eqFfix ((DFtickfun DFtickName.DFtick) << DF_to_PreCircSpecC)
      ((Int_pre_choice Set.univ
          (fun _ : Event => DF_to_PreCircSpecC DFtickName.DFtick)) |~| proc.SKIP) := by
    simp only [DFtickfun, Subst_procfun, Nondet_send_prefix_def,
      Subst_procfun_Int_pre_choice, Set.image_id']
    exact cspF_reflex_eq_P
  refine cspF_rw_left_ref hDF ?_
  refine cspF_Int_choice_left1 ?_
  refine cspF_Int_choice_right (cspF_Int_choice_right ?_ ?_) ?_
  · refine cspF_Rep_int_choice_nat_right (fun m _ => ?_)
    refine cspF_Rep_int_choice_f_right inj_stlist (fun r hr => ?_)
    refine cspF_rw_right_ref (unwRC (PNRC.PreCircSpecC (m, r))) ?_
    refine cspF_rw_right_ref (IF_posRC hr _ _) ?_
    exact cspF_Ext_choice_right
      (DF_step_one (DF_to_R (m := m / 2) hr))
      (DF_step_one (DF_to_L (m := m) hr))
  · refine cspF_Rep_int_choice_nat_right (fun m _ => ?_)
    refine cspF_Rep_int_choice_f_right inj_stlist (fun r hr => ?_)
    refine cspF_rw_right_ref (unwRC (PNRC.PreCircSpecL (m, r))) ?_
    refine cspF_rw_right_ref (IF_posRC hr _ _) ?_
    exact DF_step_one (DF_to_C (okAtt_nextR_nextL hr (m / 2)))
  · refine cspF_Rep_int_choice_nat_right (fun m _ => ?_)
    refine cspF_Rep_int_choice_f_right inj_stlist (fun r hr => ?_)
    refine cspF_rw_right_ref (unwRC (PNRC.PreCircSpecR (m, r))) ?_
    refine cspF_rw_right_ref (IF_posRC hr _ _) ?_
    exact DF_step_one (DF_to_C (okAtt_nextL_nextR hr m))

/- ------------------------------------------------------------ -/

def PreCircSpecC_to_Step : PNRC → proc PN Event
  | PNRC.PreCircSpecC (n, s) =>
      IF ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s THEN
        pChild n <=-=> pLineSpec s
      ELSE
        proc.STOP
  | PNRC.PreCircSpecL (n, s) =>
      IF ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s THEN
        pChildL (n, getNat (hd s) / 2) <=-=> pLineSpec (nextL s)
      ELSE
        proc.STOP
  | PNRC.PreCircSpecR (n, s) =>
      IF ChkLCR s ∧ s ≠ [] ∧ guardL s ∧ guardR s THEN
        pChildR n <=-=> pLineSpec (nextR (s, n))
      ELSE
        proc.STOP

/- ----------------------------------- *
                 Circ
 * ----------------------------------- -/

axiom PreCircSpecC_Step_lm {n : Nat} {s : List Att} :
  refF (pPreCircSpecC n s) MF MF (PreCircSpecC_to_Step (PNRC.PreCircSpecC (n, s)))

/- --------------------------------- *
          PreCircSpecC (step main)
 * --------------------------------- -/

theorem cspF_tr_left_ref2
    {P1 : proc p α} {P2 : proc q α} {P3 : proc r α}
    {M1 : p → domFType α} {M2 : q → domFType α} {M3 : r → domFType α} :
    refF P1 M1 M2 P2 → refF P2 M2 M3 P3 → refF P1 M1 M3 P3 :=
  cspF_trans_left_ref

theorem PreCircSpecC_Step {n : Nat} {s : List Att} :
  ChkLCR s → s ≠ [] → guardL s → guardR s →
    refF (pPreCircSpecC n s) MF MF (pChild n <=-=> pLineSpec s) := by
  intro hChk hs hGuardL hGuardR
  simpa [PreCircSpecC_to_Step, hChk, hs, hGuardL, hGuardR] using
    (PreCircSpecC_Step_lm (n := n) (s := s))

/- --------------------------------- *
               lemmas
 * --------------------------------- -/

axiom PreCircSpecC_PreCircChild {n : Nat} {s : List Nat} :
  s ≠ [] → refF (pPreCircSpecC n (toStb (List.map Att.AttC s))) MF MF (PreCircChild (n :: s))

/- --------------------------------- *
 |       DF <= PreCircSpecC          |
 * --------------------------------- -/

theorem DF_PreCircSpecC_toStb {n : Nat} {s : List Nat} :
  s ≠ [] →
    refF pDFtick MF MF (pPreCircSpecC n (toStb (List.map Att.AttC s))) := by
  intro hs
  have hmap : List.map Att.AttC s ≠ [] := by
    simpa using hs
  exact PreCircSpecC_DF
    (n := n)
    (s := toStb (List.map Att.AttC s))
    (ChkLCR_toStb (t := List.map Att.AttC s))
    (by simpa using hmap)
    (guardL_toStb_AttC (s := s) hs)
    (guardR_toStb_AttC (s := s) hs)

/- ---------------------------------------------------- *
 |                                                      |
 |          PreCircChild s is dealock-free.             |
 |                                                      |
 * ---------------------------------------------------- -/

theorem DF_PreCircChild {n : Nat} {s : List Nat} :
  s ≠ [] → refF pDFtick MF MF (PreCircChild (n :: s)) := by
  intro hs
  exact cspF_tr_left_ref2
    (DF_PreCircSpecC_toStb (n := n) (s := s) hs)
    (PreCircSpecC_PreCircChild (n := n) (s := s) hs)

/- ======================= CircSpec ======================= -/

inductive PNR where
  | CircSpec : List Nat → PNR
deriving DecidableEq, Inhabited

private abbrev pCircSpec (s : List Nat) : proc PNR Event :=
  proc.Proc_name (PNR.CircSpec s)

def PNRdef : PNR → proc PNR Event
  | PNR.CircSpec s =>
      IF tl s ≠ [] THEN
        Send_prefix Event.left (hd s / 2) (pCircSpec (circNext s))
      ELSE
        proc.STOP

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_PNRdef : HasPNfun PNR Event where
  PNfun := PNRdef

@[simp]
theorem Set_PNRdef_def (pn : PNR) :
    PNfun pn = PNRdef pn :=
  rfl

/- ------------------ *
      guardedness
 * ------------------ -/

@[simp] theorem guardedfun_PNR :
    guardedfun PNRdef := by
  intro pn
  cases pn
  simp [PNRdef, Send_prefix, guarded, noHide]

/- ------------------------------------------------------------ -/

/- Lean note:
   Isabelle's `declare toStb_simp [simp]` has no direct Lean analogue. -/

def CircSpec_to_PreCircSpecC : PNR → proc PNRC Event
  | PNR.CircSpec s =>
      IF tl s ≠ [] THEN
        proc.Hiding (pPreCircSpecC (hd s) (toStb (List.map Att.AttC (tl s)))) (Set.range Event.right)
      ELSE
        proc.STOP

/- ------------- lemma ------------- -/

axiom CircSpec_PreCircSpecC_lm {s : List Nat} :
  tl s ≠ [] → refF (pCircSpec s) MF MF (CircSpec_to_PreCircSpecC (PNR.CircSpec s))

/- ---------------------------------------------------- *
 |                                                      |
 |     CircSpec s <=F PreCircSpecC s -- range right     |
 |                                                      |
 * ---------------------------------------------------- -/

theorem CircSpec_PreCircSpecC {s : List Nat} :
  tl s ≠ [] →
    refF (pCircSpec s) MF MF
      (proc.Hiding (pPreCircSpecC (hd s) (toStb (List.map Att.AttC (tl s)))) (Set.range Event.right)) := by
  intro hs
  simpa [CircSpec_to_PreCircSpecC, hs] using
    (CircSpec_PreCircSpecC_lm (s := s) hs)

/- ---------------------------------------------------- *
 |                                                      |
 |               CircSpec s <=F CircChild s             |
 |                                                      |
 * ---------------------------------------------------- -/

axiom CircSpec_CircChild {s : List Nat} :
  tl s ≠ [] → refF (pCircSpec s) MF MF (CircChild s)

/- *********************************************************
               Eventually Stable spec
 ********************************************************* -/

inductive PNS where
  | Stable : Nat → PNS
deriving DecidableEq, Inhabited

private abbrev pStable (n : Nat) : proc PNS Event :=
  proc.Proc_name (PNS.Stable n)

def PNSdef : PNS → proc PNS Event
  | PNS.Stable n =>
      Send_prefix Event.left n (pStable n)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_PNSdef : HasPNfun PNS Event where
  PNfun := PNSdef

@[simp]
theorem Set_PNSdef_def (pn : PNS) :
    PNfun pn = PNSdef pn :=
  rfl

/- ------------------ *
      guardedness
 * ------------------ -/

@[simp] theorem guardedfun_PNS :
    guardedfun PNSdef := by
  intro pn
  cases pn
  simp [PNSdef, Send_prefix, guarded, noHide]

/- `(a ~> P) ;; Q =F a ~> (P ;; Q)` -/

private theorem prefix_Seq {a : Event} {P Q : proc PNS Event} :
    eqF ((a ~> P) ;; Q) MF MF (a ~> (P ;; Q)) := by
  refine cspF_trans_left_eq (cspF_Seq_compo_cong cspF_Act_prefix_step cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq cspF_Seq_compo_step ?_
  exact cspF_sym cspF_Act_prefix_step

private theorem IF_true' (P Q : proc PNR Event) :
    eqF (IF true THEN P ELSE Q) MF MF P :=
  cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem unwind_CircSpec {s : List Nat} (hs : tl s ≠ []) :
    eqF (pCircSpec s) MF MF (Event.left (hd s / 2) ~> pCircSpec (circNext s)) := by
  refine cspF_trans_left_eq
    («cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PNR⟩))) ?_
  change eqF (IF decide (tl s ≠ []) THEN _ ELSE _) MF MF _
  rw [decide_eq_true hs]
  exact IF_true' _ _

def Unstable : Nat → List Nat → proc PNS Event
  | 0, _ => proc.SKIP
  | Nat.succ n, s => Send_prefix Event.left (hd s / 2) (Unstable n (circNext s))

def EventuallyStable (s : List Nat) : proc PNS Event :=
  (Rep_int_choice_nat Set.univ fun N => Unstable N s) ;;
    (Rep_int_choice_nat Set.univ fun n => pStable n)

/- ----------------------------------------------- *
          eventually stable specification
 * ----------------------------------------------- -/

def EventuallyStable_to_CircSpec : Nat → PNS → proc PNR Event
  | l, PNS.Stable n => pCircSpec (makeStableList l (2 * n))

/- ---------- lemmas ---------- -/

theorem Unstable_CircSpec_lm {N : Nat} {P : proc PNS Event} :
    ∀ s : List Nat, tl s ≠ [] → refF P MF MF (pCircSpec (circNexts N s)) →
      refF (Unstable N s ;; P) MF MF (pCircSpec s) := by
  induction N with
  | zero =>
      intro s _ hP
      exact cspF_rw_left_ref cspF_Seq_compo_unit_l hP
  | succ N ih =>
      intro s hs hP
      refine cspF_rw_left_ref (prefix_Seq (a := Event.left (hd s / 2))) ?_
      refine cspF_rw_right_ref (unwind_CircSpec hs) ?_
      exact cspF_Act_prefix_mono rfl (ih (circNext s) (by simpa using hs) hP)

theorem Unstable_CircSpec {N : Nat} {s : List Nat} {P : proc PNS Event} :
    tl s ≠ [] → refF P MF MF (pCircSpec (circNexts N s)) →
      refF (Unstable N s ;; P) MF MF (pCircSpec s) :=
  fun hs hP => Unstable_CircSpec_lm s hs hP

theorem Stable_CircSpec {l n : Nat} {s : List Nat} :
    LT.lt (Nat.succ 0) l → s = makeStableList l (2 * n) →
      refF (pStable n) MF MF (pCircSpec s) := by
  intro hl hs
  subst hs
  refine cspF_fp_induct_ref_left (Pf := PNSdef) (f := EventuallyStable_to_CircSpec l)
    rfl (Or.inl rfl) guardedfun_PNS cspF_reflex_ref_P ?_
  intro p
  cases p with
  | Stable m =>
      have hEven : allEven (makeStableList l (2 * m)) :=
        allEven_makeStableList ⟨m, by omega⟩
      have hStable : stableList (makeStableList l (2 * m)) := stableList_makeStableList_lm
      have hcirc : circNext (makeStableList l (2 * m)) = makeStableList l (2 * m) :=
        stable_circNext hEven hStable
      have htl : tl (makeStableList l (2 * m)) ≠ [] := by
        intro hc
        have := tl_makeStableList_nil (l := l) (n := 2 * m) |>.mp hc
        omega
      have hhd : hd (makeStableList l (2 * m)) = 2 * m := makeStableList_hd (by omega)
      refine cspF_rw_right_ref (unwind_CircSpec htl) ?_
      rw [hcirc, hhd, Nat.mul_div_cancel_left m (by omega : 0 < 2)]
      exact cspF_reflex_ref_P

theorem EventuallyStable_CircSpec {s : List Nat} :
    LT.lt (Nat.succ 0) s.length → allEven s → refF (EventuallyStable s) MF MF (pCircSpec s) := by
  intro hlen hEven
  obtain ⟨hs, htl⟩ := list_length_more_one.mp hlen
  obtain ⟨N, hStable⟩ := circNexts_eventually_stable hs hEven
  have hEvenN : allEven (circNexts N s) := circNexts_even hEven
  have hsN : circNexts N s ≠ [] := by
    intro hc
    exact hs ((circNexts_nil_iff (N := N) s).mp hc)
  rw [EventuallyStable]
  refine cspF_rw_left_ref cspF_Seq_compo_Dist_nat ?_
  refine cspF_Rep_int_choice_nat_left_x (Set.mem_univ N) ?_
  refine Unstable_CircSpec htl ?_
  refine cspF_Rep_int_choice_nat_left_x
    (n := hd (circNexts N s) / 2) (Set.mem_univ _) ?_
  refine Stable_CircSpec (l := s.length) hlen ?_
  rw [allEven_div hsN hEvenN]
  exact makeStableList_hd_stableList.mpr ⟨length_circNexts (N := N) s, hStable⟩

/- -------------------------------------------- *

                  Finally ...

     for any number of children more than two
     and any initial number of candies,

 * -------------------------------------------- -/

theorem EventuallyStable_CircChild {s : List Nat} :
    LT.lt 1 s.length → allEven s → refF (EventuallyStable s) MF MF (CircChild s) := by
  intro hlen hEven
  exact cspF_tr_left_ref2 (EventuallyStable_CircSpec hlen hEven)
    (CircSpec_CircChild (list_length_more_one.mp hlen).2)