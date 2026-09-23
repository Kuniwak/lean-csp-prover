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

private theorem IF_negRC {c : Prop} [Decidable c] (h : ¬ c) (P Q : proc PNRC Event) :
    eqF (IF c THEN P ELSE Q) MF MF Q := by
  rw [decide_eq_false h]
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

/- *********************************************************
        expanding the ring operator `<=-=>`
 ********************************************************* -/

/- `<=-=>` is a plain parallel over `left`/`right` with the two channels
   swapped on the right component: no hiding, no alphabetised parallel, so
   the expansion is just `cspF_Parallel_step_sub`. -/

private abbrev fC : Event → Event := Renaming1_channel_fun Event.right Event.left

private theorem right_ne_left : ∀ x y, Event.right x ≠ Event.left y := by
  intro x y h; cases h

private theorem fC_right (n : Nat) : fC (Event.right n) = Event.left n :=
  Renaming1_channel_fun_f inj_event.2.1 right_ne_left

private theorem fC_left (n : Nat) : fC (Event.left n) = Event.right n :=
  Renaming_channel_fun_g inj_event.1 right_ne_left

private theorem fC_mid (n : Nat) : fC (Event.mid n) = Event.mid n :=
  Renaming1_channel_fun_h right_ne_left
    (fun x y => by intro h; cases h) (fun x y => by intro h; cases h)

private theorem fC_stlist (l : List Att) : fC (Event.stlist l) = Event.stlist l :=
  Renaming1_channel_fun_h right_ne_left
    (fun x y => by intro h; cases h) (fun x y => by intro h; cases h)

private theorem inj_fC : Function.Injective fC := by
  intro a b h
  cases a <;> cases b <;>
    simp only [fC_left, fC_right, fC_mid, fC_stlist] at h <;>
    first
      | rfl
      | (cases h; rfl)
      | exact absurd h (by simp)

private theorem invC_left (n : Nat) : Function.invFun fC (Event.left n) = Event.right n := by
  have h := Function.leftInverse_invFun inj_fC (Event.right n)
  rwa [fC_right] at h

private theorem invC_right (n : Nat) : Function.invFun fC (Event.right n) = Event.left n := by
  have h := Function.leftInverse_invFun inj_fC (Event.left n)
  rwa [fC_left] at h

private theorem image_fC_right : fC '' (Set.range Event.right) = Set.range Event.left := by
  ext e
  constructor
  · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (fC_right n).symm ▸ rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨Event.right n, ⟨n, rfl⟩, fC_right n⟩

private theorem PreCirc_eq (P Q : proc PN Event) :
    (P <=-=> Q) = P |[LeftRight]| (Q[[fun_to_rel fC]]) := rfl

/- ---------- renamed normal forms of the line spec ---------- -/

private theorem renC_L (v : Nat) (P : proc PN Event) :
    eqFfix ((Event.left v ~> P)[[fun_to_rel fC]])
      (proc.Ext_pre_choice ({Event.right v} : Set Event)
        (fun _ => P[[fun_to_rel fC]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_fun_Act_prefix inj_fC) ?_
  rw [fC_left]
  exact cspF_Act_prefix_step

private theorem renC_R (Qf : Nat → proc PN Event) :
    eqFfix ((Rec_prefix Event.right Set.univ Qf)[[fun_to_rel fC]])
      (proc.Ext_pre_choice (Set.range Event.left) fun x =>
        (Qf (Function.invFun Event.left x))[[fun_to_rel fC]]) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq (cspF_Renaming_fun_Ext_pre_choice inj_fC) ?_
  have himg : fC '' (Event.right '' (Set.univ : Set Nat)) = Set.range Event.left := by
    rw [Set.image_univ]; exact image_fC_right
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  obtain ⟨n, rfl⟩ := hy
  rw [invC_left n, Function.leftInverse_invFun inj_event.2.1 n,
    Function.leftInverse_invFun inj_event.1 n]
  exact cspF_reflex_eq_P

private theorem renC_LR (v : Nat) (P : proc PN Event) (Qf : Nat → proc PN Event) :
    eqFfix (((Event.left v ~> P) [+] (Rec_prefix Event.right Set.univ Qf))[[fun_to_rel fC]])
      (proc.Ext_pre_choice (({Event.right v} : Set Event) ∪ Set.range Event.left) fun x =>
        procIte (x = Event.right v) (P[[fun_to_rel fC]])
          ((Qf (Function.invFun Event.left x))[[fun_to_rel fC]])) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq
    (cspF_Renaming_cong rfl
      (cspF_Ext_choice_cong (cspF_Act_prefix_step (a := Event.left v) (P := P))
        cspF_reflex_eq_P)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_step) ?_
  refine cspF_trans_left_eq (cspF_Renaming_fun_Ext_pre_choice inj_fC) ?_
  have himg : fC '' ((({Event.left v} : Set Event)) ∪ Event.right '' (Set.univ : Set Nat))
      = (({Event.right v} : Set Event)) ∪ Set.range Event.left := by
    rw [Set.image_univ, Set.image_union, Set.image_singleton, fC_left, image_fC_right]
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  rcases hy with hy | ⟨n, rfl⟩
  · have hyv : y = Event.right v := hy
    subst hyv
    have hmem : Event.left v ∈ ({Event.left v} : Set Event) := Set.mem_singleton_iff.mpr rfl
    have hnot : ¬ (Event.left v ∈ ({Event.left v} : Set Event) ∧
        Event.left v ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    rw [invC_right v]
    simp only [procIte_neg hnot, procIte_pos hmem, procIte_pos True.intro]
    exact cspF_reflex_eq_P
  · have hnot1 : ¬ (Event.right n ∈ ({Event.left v} : Set Event) ∧
        Event.right n ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    have hnot2 : ¬ (Event.right n ∈ ({Event.left v} : Set Event)) := by simp
    have hnot3 : ¬ (Event.left n = Event.right v) := by simp
    rw [invC_left n]
    simp only [procIte_neg hnot1, procIte_neg hnot2, procIte_neg hnot3]
    rw [Function.leftInverse_invFun inj_event.2.1 n,
      Function.leftInverse_invFun inj_event.1 n]
    exact cspF_reflex_eq_P

/- ---------- the generic ring step ---------- -/

private theorem PreCirc_step {P Q : proc PN Event} {A B : Set Event}
    {Pf Qf : Event → proc PN Event}
    (hP : eqFfix P (proc.Ext_pre_choice A Pf))
    (hQ : eqFfix (Q[[fun_to_rel fC]]) (proc.Ext_pre_choice B Qf))
    (hA : A ⊆ LeftRight) (hB : B ⊆ LeftRight) :
    eqFfix (P <=-=> Q)
      (proc.Ext_pre_choice (A ∩ B) fun x => Pf x |[LeftRight]| Qf x) := by
  rw [PreCirc_eq]
  refine cspF_trans_left_eq (cspF_Parallel_cong rfl hP hQ) ?_
  exact cspF_Parallel_step_sub hA hB

private theorem PreCirc_fold (P' Q' : proc PN Event) :
    (P' |[LeftRight]| (Q'[[fun_to_rel fC]])) = (P' <=-=> Q') := rfl

/- ---------- normal forms of the two sides ---------- -/

private theorem renC_LineSpec_both {t : List Att}
    (hchk : ChkLCR t) (hgL : guardL t) (hgR : guardR t) :
    eqFfix ((pLineSpec t)[[fun_to_rel fC]])
      (proc.Ext_pre_choice
        (({Event.right (getNat (hd t) / 2)} : Set Event) ∪ Set.range Event.left)
        (fun y => procIte (y = Event.right (getNat (hd t) / 2))
          ((pLineSpec (nextL t))[[fun_to_rel fC]])
          ((pLineSpec (nextR (t, Function.invFun Event.left y)))[[fun_to_rel fC]]))) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.LineSpec t))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (IF_pos hchk _ _)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl
    (cspF_Ext_choice_cong (IF_pos hgL _ _) (IF_pos hgR _ _))) ?_
  exact renC_LR (getNat (hd t) / 2) (pLineSpec (nextL t)) (fun x => pLineSpec (nextR (t, x)))

private theorem renC_LineSpec_L {t : List Att}
    (hchk : ChkLCR t) (hgL : guardL t) (hgR : ¬ guardR t) :
    eqFfix ((pLineSpec t)[[fun_to_rel fC]])
      (proc.Ext_pre_choice ({Event.right (getNat (hd t) / 2)} : Set Event)
        (fun _ => (pLineSpec (nextL t))[[fun_to_rel fC]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.LineSpec t))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (IF_pos hchk _ _)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl
    (cspF_Ext_choice_cong (IF_pos hgL _ _) (IF_neg hgR _ _))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_unit_r) ?_
  exact renC_L (getNat (hd t) / 2) (pLineSpec (nextL t))

private theorem renC_LineSpec_R {t : List Att}
    (hchk : ChkLCR t) (hgL : ¬ guardL t) (hgR : guardR t) :
    eqFfix ((pLineSpec t)[[fun_to_rel fC]])
      (proc.Ext_pre_choice (Set.range Event.left)
        (fun y => (pLineSpec (nextR (t, Function.invFun Event.left y)))[[fun_to_rel fC]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.LineSpec t))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (IF_pos hchk _ _)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl
    (cspF_Ext_choice_cong (IF_neg hgL _ _) (IF_pos hgR _ _))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_unit_l) ?_
  exact renC_R (fun x => pLineSpec (nextR (t, x)))

private theorem norm_Child (m : Nat) :
    eqFfix (pChild m)
      (proc.Ext_pre_choice (({Event.left (m / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.left (m / 2)) (pChildR (m / 2))
          (pChildL (m, Function.invFun Event.right y)))) :=
  cspF_trans_left_eq (unw (PN.Child m))
    (LR_normal (m / 2) (pChildR (m / 2)) (fun x => pChildL (m, x)))

private theorem norm_ChildL (cx : Nat × Nat) :
    eqFfix (pChildL cx)
      (proc.Ext_pre_choice ({Event.left (cx.1 / 2)} : Set Event)
        (fun _ => pChild (fill (cx.1 / 2 + cx.2)))) :=
  cspF_trans_left_eq (unw (PN.ChildL cx)) cspF_Act_prefix_step

private theorem norm_ChildR (c : Nat) :
    eqFfix (pChildR c)
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => pChild (fill (c + Function.invFun Event.right y)))) := by
  refine cspF_trans_left_eq (unw (PN.ChildR c)) ?_
  simp only [PNdef, Rec_prefix_def]
  refine cspF_Ext_pre_choice_cong (by rw [Set.image_univ]) (fun y hy => ?_)
  obtain ⟨k, rfl⟩ := hy
  exact cspF_reflex_eq_P

private theorem getNat_hd_nextR {r : List Att} {z : Nat}
    (hgL : guardL r) (hgR : guardR r) :
    getNat (hd (nextR (r, z))) = getNat (hd r) := by
  cases r with
  | nil => exact absurd hgL (by simp [guardL])
  | cons a t =>
      rcases Att_or a with ⟨p, q, rfl⟩ | ⟨p, rfl⟩ | ⟨p, rfl⟩
      · have hgRt : guardR t := by rwa [guardR_AttL] at hgR
        rw [guardR_nextR_AttL hgRt]
        rfl
      · exact getNat_hd_nextR_AttC
      · rcases hgL with ⟨u, v, hu⟩ | ⟨u, hu⟩ <;> cases hu

/- ---------- set computations for the ring step ---------- -/

private theorem leftR_sub_LR (v : Nat) :
    (({Event.left v} : Set Event) ∪ Set.range Event.right) ⊆ LeftRight := by
  rintro e (he | ⟨k, rfl⟩)
  · have : e = Event.left v := he
    subst this
    exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨k, rfl⟩

private theorem rightL_sub_LR (w : Nat) :
    (({Event.right w} : Set Event) ∪ Set.range Event.left) ⊆ LeftRight := by
  rintro e (he | ⟨k, rfl⟩)
  · have : e = Event.right w := he
    subst this
    exact Or.inr ⟨w, rfl⟩
  · exact Or.inl ⟨k, rfl⟩

private theorem left_sub_LR (v : Nat) : ({Event.left v} : Set Event) ⊆ LeftRight := by
  rintro e he
  have : e = Event.left v := he
  subst this
  exact Or.inl ⟨v, rfl⟩

private theorem right_sub_LR (w : Nat) : ({Event.right w} : Set Event) ⊆ LeftRight := by
  rintro e he
  have : e = Event.right w := he
  subst this
  exact Or.inr ⟨w, rfl⟩

private theorem rangeL_sub_LR : Set.range Event.left ⊆ LeftRight :=
  fun _ h => Or.inl h

private theorem rangeR_sub_LR : Set.range Event.right ⊆ LeftRight :=
  fun _ h => Or.inr h

private theorem inter_LR_RL (v w : Nat) :
    ((({Event.left v} : Set Event) ∪ Set.range Event.right) ∩
      (({Event.right w} : Set Event) ∪ Set.range Event.left))
      = (({Event.left v} : Set Event) ∪ ({Event.right w} : Set Event)) := by
  ext e
  cases e <;> simp

private theorem inter_L_RL (v w : Nat) :
    ((({Event.left v} : Set Event)) ∩
      (({Event.right w} : Set Event) ∪ Set.range Event.left))
      = ({Event.left v} : Set Event) := by
  ext e
  cases e <;> simp

private theorem inter_L_L (v : Nat) :
    ((({Event.left v} : Set Event)) ∩ Set.range Event.left)
      = ({Event.left v} : Set Event) := by
  ext e
  cases e <;> simp

private theorem inter_R_RL (w : Nat) :
    (Set.range Event.right ∩
      (({Event.right w} : Set Event) ∪ Set.range Event.left))
      = ({Event.right w} : Set Event) := by
  ext e
  cases e <;> simp

private theorem inter_R_R (w : Nat) :
    (Set.range Event.right ∩ ({Event.right w} : Set Event))
      = ({Event.right w} : Set Event) := by
  ext e
  cases e <;> simp

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

private theorem two_prefix_normal {q : Type} (a b : Event) (P Q : proc q Event)
    {M : q → domFType Event} :
    eqF ((a ~> P) [+] (b ~> Q)) M M
      (proc.Ext_pre_choice (({a} : Set Event) ∪ ({b} : Set Event))
        (fun x => procIte (x ∈ ({a} : Set Event) ∧ x ∈ ({b} : Set Event)) (P |~| Q)
          (procIte (x ∈ ({a} : Set Event)) P Q))) :=
  cspF_trans_left_eq
    (cspF_Ext_choice_cong (cspF_Act_prefix_step (a := a) (P := P))
      (cspF_Act_prefix_step (a := b) (P := Q)))
    cspF_Ext_choice_step

private theorem one_prefix_normal {q : Type} (a : Event) (P : proc q Event)
    {M : q → domFType Event} :
    eqF (a ~> P) M M (proc.Ext_pre_choice ({a} : Set Event) (fun _ => P)) :=
  cspF_Act_prefix_step

theorem PreCircSpecC_Step_lm {n : Nat} {s : List Att} :
  refF (pPreCircSpecC n s) MF MF (PreCircSpecC_to_Step (PNRC.PreCircSpecC (n, s))) := by
  refine cspF_fp_induct_ref_left (Pf := PNRCdef) (f := PreCircSpecC_to_Step)
    (p0 := PNRC.PreCircSpecC (n, s)) rfl (Or.inl rfl) guardedfun_PNRC
    cspF_reflex_ref_P ?_
  intro p
  cases p with
  | PreCircSpecC mr =>
      obtain ⟨m, r⟩ := mr
      by_cases hok : ChkLCR r ∧ r ≠ [] ∧ guardL r ∧ guardR r
      · simp only [PNRCdef, PreCircSpecC_to_Step, Subst_procfun, Send_prefix]
        refine cspF_rw_right_ref (IF_pos hok _ _) ?_
        refine cspF_rw_left_ref (IF_pos hok _ _) ?_
        refine cspF_rw_left_ref
          (cspF_Ext_choice_cong
            (cspF_Act_prefix_cong rfl (IF_pos hok _ _))
            (cspF_Act_prefix_cong rfl (IF_pos hok _ _))) ?_
        refine cspF_rw_right_ref
          (PreCirc_step (norm_Child m)
            (renC_LineSpec_both hok.1 hok.2.2.1 hok.2.2.2)
            (leftR_sub_LR (m / 2)) (rightL_sub_LR (getNat (hd r) / 2))) ?_
        rw [inter_LR_RL (m / 2) (getNat (hd r) / 2)]
        refine cspF_rw_left_ref
          (two_prefix_normal (Event.left (m / 2)) (Event.right (getNat (hd r) / 2)) _ _) ?_
        refine cspF_Ext_pre_choice_mono rfl (fun y hy => ?_)
        have hlrne : ¬ (Event.left (m / 2) = Event.right (getNat (hd r) / 2)) := by simp
        rcases hy with hy | hy
        · have hyv : y = Event.left (m / 2) := hy
          subst hyv
          have hnotB : ¬ (Event.left (m / 2) = Event.right (getNat (hd r) / 2)) := hlrne
          have hnand : ¬ (Event.left (m / 2) ∈ ({Event.left (m / 2)} : Set Event) ∧
              Event.left (m / 2) ∈ ({Event.right (getNat (hd r) / 2)} : Set Event)) := by simp
          have hmemS : Event.left (m / 2) ∈ ({Event.left (m / 2)} : Set Event) :=
            Set.mem_singleton_iff.mpr rfl
          simp only [procIte_neg hnand, procIte_pos hmemS,
            procIte_neg hnotB, procIte_pos True.intro]
          rw [Function.leftInverse_invFun inj_event.1 (m / 2), PreCirc_fold]
          exact cspF_reflex_ref_P
        · have hyv : y = Event.right (getNat (hd r) / 2) := hy
          subst hyv
          have hnotA : ¬ (Event.right (getNat (hd r) / 2) = Event.left (m / 2)) := by simp
          have hmemA : Event.right (getNat (hd r) / 2) ∈
              (({Event.left (m / 2)} : Set Event) ∪ Set.range Event.right) :=
            Or.inr ⟨getNat (hd r) / 2, rfl⟩
          have hnotS : ¬ (Event.right (getNat (hd r) / 2) ∈
              ({Event.left (m / 2)} : Set Event)) := by simp
          have hnand : ¬ (Event.right (getNat (hd r) / 2) ∈
              ({Event.left (m / 2)} : Set Event) ∧
              Event.right (getNat (hd r) / 2) ∈
              ({Event.right (getNat (hd r) / 2)} : Set Event)) := by simp
          simp only [procIte_neg hnand, procIte_neg hnotS, procIte_neg hnotA,
            procIte_pos True.intro]
          rw [Function.leftInverse_invFun inj_event.2.1 (getNat (hd r) / 2), PreCirc_fold]
          exact cspF_reflex_ref_P
      · simp only [PNRCdef, PreCircSpecC_to_Step, Subst_procfun]
        refine cspF_rw_left_ref (IF_neg hok _ _) ?_
        exact cspF_rw_right_ref (IF_neg hok _ _) cspF_reflex_ref_P
  | PreCircSpecL mr =>
      obtain ⟨m, r⟩ := mr
      by_cases hok : ChkLCR r ∧ r ≠ [] ∧ guardL r ∧ guardR r
      · have hokL := okAtt_nextR_nextL hok (m / 2)
        have hchkL : ChkLCR (nextL r) := (ChkLCR_nextL hok.2.2.1).mpr hok.1
        have hgRL : guardR (nextL r) := ChkLCR_guardL_guardR_nextL hok.1 hok.2.2.1
        simp only [PNRCdef, PreCircSpecC_to_Step, Subst_procfun, Send_prefix]
        refine cspF_rw_right_ref (IF_pos hok _ _) ?_
        refine cspF_rw_left_ref (IF_pos hok _ _) ?_
        refine cspF_rw_left_ref (cspF_Act_prefix_cong rfl (IF_pos hokL _ _)) ?_
        refine cspF_rw_left_ref
          (one_prefix_normal (Event.left (m / 2)) _) ?_
        by_cases hgLL : guardL (nextL r)
        · refine cspF_rw_right_ref
            (PreCirc_step (norm_ChildL (m, getNat (hd r) / 2))
              (renC_LineSpec_both hchkL hgLL hgRL)
              (left_sub_LR (m / 2)) (rightL_sub_LR (getNat (hd (nextL r)) / 2))) ?_
          rw [inter_L_RL (m / 2) (getNat (hd (nextL r)) / 2)]
          refine cspF_Ext_pre_choice_mono rfl (fun y hy => ?_)
          have hyv : y = Event.left (m / 2) := hy
          subst hyv
          have hnotB : ¬ (Event.left (m / 2) = Event.right (getNat (hd (nextL r)) / 2)) := by
            simp
          simp only [procIte_neg hnotB]
          rw [Function.leftInverse_invFun inj_event.1 (m / 2), PreCirc_fold]
          exact cspF_reflex_ref_P
        · refine cspF_rw_right_ref
            (PreCirc_step (norm_ChildL (m, getNat (hd r) / 2))
              (renC_LineSpec_R hchkL hgLL hgRL)
              (left_sub_LR (m / 2)) rangeL_sub_LR) ?_
          rw [inter_L_L (m / 2)]
          refine cspF_Ext_pre_choice_mono rfl (fun y hy => ?_)
          have hyv : y = Event.left (m / 2) := hy
          subst hyv
          rw [Function.leftInverse_invFun inj_event.1 (m / 2), PreCirc_fold]
          exact cspF_reflex_ref_P
      · simp only [PNRCdef, PreCircSpecC_to_Step, Subst_procfun]
        refine cspF_rw_left_ref (IF_neg hok _ _) ?_
        exact cspF_rw_right_ref (IF_neg hok _ _) cspF_reflex_ref_P
  | PreCircSpecR mr =>
      obtain ⟨m, r⟩ := mr
      by_cases hok : ChkLCR r ∧ r ≠ [] ∧ guardL r ∧ guardR r
      · have hokR := okAtt_nextL_nextR hok m
        have hchkR : ChkLCR (nextR (r, m)) := (ChkLCR_nextR hok.2.2.2).mpr hok.1
        have hgLR : guardL (nextR (r, m)) := ChkLCR_guardR_guardL_nextR hok.1 hok.2.2.2
        have hgetR : getNat (hd (nextR (r, m))) = getNat (hd r) :=
          getNat_hd_nextR hok.2.2.1 hok.2.2.2
        simp only [PNRCdef, PreCircSpecC_to_Step, Subst_procfun, Send_prefix]
        refine cspF_rw_right_ref (IF_pos hok _ _) ?_
        refine cspF_rw_left_ref (IF_pos hok _ _) ?_
        refine cspF_rw_left_ref (cspF_Act_prefix_cong rfl (IF_pos hokR _ _)) ?_
        refine cspF_rw_left_ref
          (one_prefix_normal (Event.right (getNat (hd r) / 2)) _) ?_
        by_cases hgRR : guardR (nextR (r, m))
        · refine cspF_rw_right_ref
            (PreCirc_step (norm_ChildR m)
              (renC_LineSpec_both hchkR hgLR hgRR)
              rangeR_sub_LR (rightL_sub_LR (getNat (hd (nextR (r, m))) / 2))) ?_
          rw [inter_R_RL (getNat (hd (nextR (r, m))) / 2), hgetR]
          refine cspF_Ext_pre_choice_mono rfl (fun y hy => ?_)
          have hyv : y = Event.right (getNat (hd r) / 2) := hy
          subst hyv
          rw [← hgetR]
          simp only [procIte_pos True.intro]
          rw [Function.leftInverse_invFun inj_event.2.1 (getNat (hd (nextR (r, m))) / 2),
            PreCirc_fold, hgetR]
          exact cspF_reflex_ref_P
        · refine cspF_rw_right_ref
            (PreCirc_step (norm_ChildR m)
              (renC_LineSpec_L hchkR hgLR hgRR)
              rangeR_sub_LR (right_sub_LR (getNat (hd (nextR (r, m))) / 2))) ?_
          rw [inter_R_R (getNat (hd (nextR (r, m))) / 2), hgetR]
          refine cspF_Ext_pre_choice_mono rfl (fun y hy => ?_)
          have hyv : y = Event.right (getNat (hd r) / 2) := hy
          subst hyv
          rw [← hgetR,
            Function.leftInverse_invFun inj_event.2.1 (getNat (hd (nextR (r, m))) / 2),
            PreCirc_fold, hgetR]
          exact cspF_reflex_ref_P
      · simp only [PNRCdef, PreCircSpecC_to_Step, Subst_procfun]
        refine cspF_rw_left_ref (IF_neg hok _ _) ?_
        exact cspF_rw_right_ref (IF_neg hok _ _) cspF_reflex_ref_P

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

theorem PreCircSpecC_PreCircChild {n : Nat} {s : List Nat} :
  s ≠ [] → refF (pPreCircSpecC n (toStb (List.map Att.AttC s))) MF MF (PreCircChild (n :: s)) := by
  intro hs
  have hmap : List.map Att.AttC s ≠ [] := by
    simpa using hs
  refine cspF_trans_left_ref
    (PreCircSpecC_Step (n := n) (s := toStb (List.map Att.AttC s))
      (ChkLCR_toStb (t := List.map Att.AttC s))
      (by simpa using hmap)
      (guardL_toStb_AttC (s := s) hs)
      (guardR_toStb_AttC (s := s) hs)) ?_
  exact PreCirc_mono (LineSpec_LineChild hs)

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

private theorem lineNext_ne_nil {t : List Nat} {x : Nat} (h : t ≠ []) :
    lineNext t x ≠ [] := by
  cases t with
  | nil => exact absurd rfl h
  | cons a u =>
      cases u with
      | nil => simp [lineNext]
      | cons b w => simp [lineNext]

private theorem set_lr_inter_right (v g : Nat) :
    ((({Event.left v} : Set Event) ∪ ({Event.right g} : Set Event)) ∩
      Set.range Event.right) = ({Event.right g} : Set Event) := by
  ext e
  cases e <;> simp

private theorem set_lr_diff_right (v g : Nat) :
    ((({Event.left v} : Set Event) ∪ ({Event.right g} : Set Event)) \
      Set.range Event.right) = ({Event.left v} : Set Event) := by
  ext e
  cases e <;> simp

private theorem singleton_right_ne_empty (g : Nat) :
    ({Event.right g} : Set Event) ≠ ∅ := by
  intro h
  have : Event.right g ∈ ({Event.right g} : Set Event) := rfl
  rw [h] at this
  exact this

theorem CircSpec_PreCircSpecC_lm {s : List Nat} :
  tl s ≠ [] → refF (pCircSpec s) MF MF (CircSpec_to_PreCircSpecC (PNR.CircSpec s)) := by
  intro hs
  refine cspF_fp_induct_ref_left (Pf := PNRdef) (f := CircSpec_to_PreCircSpecC)
    (p0 := PNR.CircSpec s) rfl (Or.inl rfl) guardedfun_PNR cspF_reflex_ref_P ?_
  intro p
  cases p with
  | CircSpec u =>
      by_cases htl : tl u ≠ []
      · have hune : u ≠ [] := by
          intro he
          rw [he] at htl
          exact htl rfl
        have hmap : List.map Att.AttC (tl u) ≠ [] := by
          cases h : tl u with
          | nil => exact absurd h htl
          | cons a w => simp
        have hokr : ChkLCR (toStb (List.map Att.AttC (tl u))) ∧
            toStb (List.map Att.AttC (tl u)) ≠ [] ∧
            guardL (toStb (List.map Att.AttC (tl u))) ∧
            guardR (toStb (List.map Att.AttC (tl u))) :=
          ⟨ChkLCR_toStb, by simpa using hmap, guardL_toStb_AttC htl, guardR_toStb_AttC htl⟩
        -- the two list identities that make the circle close
        have hcircdef : circNext u = lineNext u (hd u / 2) := by simp [circNext, hune]
        have hcirctl : tl (circNext u) ≠ [] := by
          rw [hcircdef, ← tl_lineNext htl]
          exact lineNext_ne_nil htl
        have hgetr : getNat (hd (toStb (List.map Att.AttC (tl u)))) = hd (tl u) :=
          getNat_hd_toStb_map_AttC htl
        have hcirchd : hd (circNext u)
            = fill (hd u / 2 + getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2) := by
          rw [hgetr]
          exact hd_circNext htl
        have hcircstb : toStb (List.map Att.AttC (tl (circNext u)))
            = nextL (nextR (toStb (List.map Att.AttC (tl u)), hd u / 2)) := by
          rw [nextL_nextR_toStb_lineNext, hcircdef, ← tl_lineNext htl]
        -- the common continuation of both limbs
        have hcont : refF (CircSpec_to_PreCircSpecC (PNR.CircSpec (circNext u))) MF MF
            (proc.Hiding (pPreCircSpecC
              (fill (hd u / 2 + getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2))
              (nextL (nextR (toStb (List.map Att.AttC (tl u)), hd u / 2))))
              (Set.range Event.right)) := by
          simp only [CircSpec_to_PreCircSpecC]
          refine cspF_rw_left_ref (IF_posRC hcirctl _ _) ?_
          rw [hcirchd, hcircstb]
          exact cspF_reflex_ref_P
        simp only [PNRdef, CircSpec_to_PreCircSpecC, Subst_procfun, Send_prefix]
        refine cspF_rw_right_ref (IF_posRC htl _ _) ?_
        refine cspF_rw_right_ref
          (cspF_Hiding_cong rfl (unwRC (PNRC.PreCircSpecC (hd u,
            toStb (List.map Att.AttC (tl u)))))) ?_
        refine cspF_rw_right_ref (cspF_Hiding_cong rfl (IF_posRC hokr _ _)) ?_
        refine cspF_rw_right_ref
          (cspF_Hiding_cong rfl
            (two_prefix_normal (Event.left (hd u / 2))
              (Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2)) _ _)) ?_
        refine cspF_rw_right_ref (cspF_Hiding_step (X := Set.range Event.right)) ?_
        rw [procIte_neg (by
            rw [set_lr_inter_right]
            exact singleton_right_ne_empty _),
          set_lr_diff_right, set_lr_inter_right]
        refine cspF_rw_left_ref (IF_posRC htl _ _) ?_
        refine cspF_rw_left_ref (one_prefix_normal (Event.left (hd u / 2)) _) ?_
        refine cspF_Timeout_right_subset (subset_refl _) (fun y hy => ?_) ?_
        · have hyv : y = Event.left (hd u / 2) := hy
          subst hyv
          have hmemS : Event.left (hd u / 2) ∈ ({Event.left (hd u / 2)} : Set Event) :=
            Set.mem_singleton_iff.mpr rfl
          have hnand : ¬ (Event.left (hd u / 2) ∈ ({Event.left (hd u / 2)} : Set Event) ∧
              Event.left (hd u / 2) ∈
                ({Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2)}
                  : Set Event)) := by simp
          simp only [procIte_neg hnand, procIte_pos hmemS]
          refine cspF_rw_right_ref
            (cspF_Hiding_cong rfl (unwRC (PNRC.PreCircSpecR (hd u / 2,
              toStb (List.map Att.AttC (tl u)))))) ?_
          refine cspF_rw_right_ref (cspF_Hiding_cong rfl (IF_posRC hokr _ _)) ?_
          refine cspF_rw_right_ref
            (cspF_Hiding_Act_prefix_in
              ⟨getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2, rfl⟩) ?_
          exact hcont
        · refine cspF_Rep_int_choice_com_right (fun a ha => ?_)
          have hav : a = Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2) := ha
          subst hav
          have hnand : ¬ (Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2)
              ∈ ({Event.left (hd u / 2)} : Set Event) ∧
              Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2) ∈
                ({Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2)}
                  : Set Event)) := by simp
          have hnotS : ¬ (Event.right (getNat (hd (toStb (List.map Att.AttC (tl u)))) / 2)
              ∈ ({Event.left (hd u / 2)} : Set Event)) := by simp
          simp only [procIte_neg hnand, procIte_neg hnotS]
          refine cspF_rw_right_ref
            (cspF_Hiding_cong rfl (unwRC (PNRC.PreCircSpecL (hd u,
              toStb (List.map Att.AttC (tl u)))))) ?_
          refine cspF_rw_right_ref (cspF_Hiding_cong rfl (IF_posRC hokr _ _)) ?_
          refine cspF_rw_right_ref
            (cspF_Hiding_Act_prefix_notin (a := Event.left (hd u / 2)) (by simp)) ?_
          refine cspF_rw_right_ref (one_prefix_normal (Event.left (hd u / 2)) _) ?_
          refine cspF_Ext_pre_choice_mono rfl (fun y hy => ?_)
          have hyv : y = Event.left (hd u / 2) := hy
          subst hyv
          rw [nextR_nextL_toStb_nextR_nextL_toStb htl]
          exact hcont
      · simp only [PNRdef, CircSpec_to_PreCircSpecC, Subst_procfun]
        refine cspF_rw_left_ref (IF_negRC htl _ _) ?_
        exact cspF_rw_right_ref (IF_negRC htl _ _) cspF_reflex_ref_P

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

theorem CircSpec_CircChild {s : List Nat} :
  tl s ≠ [] → refF (pCircSpec s) MF MF (CircChild s) := by
  intro hs
  cases s with
  | nil => exact absurd (rfl : tl ([] : List Nat) = []) hs
  | cons c t =>
      refine cspF_trans_left_ref (CircSpec_PreCircSpecC hs) ?_
      have hcc : CircChild (c :: t)
          = proc.Hiding (PreCircChild (c :: t)) (Set.range Event.right) := rfl
      rw [hcc]
      refine cspF_Hiding_mono rfl ?_
      exact PreCircSpecC_PreCircChild (n := c) (s := t) hs

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