           /- -------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |                May 2008 (modified)        |
            |           November 2008 for Isabelle 2008 |
            |                May 2016 for Isabelle 2016 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F
import LeanCspProver.UCD.UCD_data2

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

/-=============================================================*
 |                                                             |
 |                           Process                           |
 |                                                             |
 *=============================================================-/

/- *********************************************************
               process names and events
 ********************************************************* -/

inductive Event where
  | left : Nat → Event
  | right : Nat → Event
  | mid : Nat → Event
  | stlist : List Att → Event
deriving DecidableEq, Inhabited

inductive PN where
  | Child : Nat → PN
  | ChildL : Nat × Nat → PN
  | ChildR : Nat → PN
  | LineSpec : List Att → PN
deriving DecidableEq, Inhabited

@[simp]
theorem inj_stlist :
    Function.Injective Event.stlist := by
  intro a b h
  cases h
  rfl

@[simp]
theorem inj_event :
    Function.Injective Event.left ∧ Function.Injective Event.right ∧ Function.Injective Event.mid := by
  constructor
  · intro a b h
    cases h
    rfl
  constructor
  · intro a b h
    cases h
    rfl
  · intro a b h
    cases h
    rfl

/- *********************************************************
                  Recursivey Process
 ********************************************************* -/

private abbrev pChild (c : Nat) : proc PN Event :=
  proc.Proc_name (PN.Child c)

private abbrev pChildL (cx : Nat × Nat) : proc PN Event :=
  proc.Proc_name (PN.ChildL cx)

private abbrev pChildR (c : Nat) : proc PN Event :=
  proc.Proc_name (PN.ChildR c)

private abbrev pLineSpec (s : List Att) : proc PN Event :=
  proc.Proc_name (PN.LineSpec s)

def PNdef : PN → proc PN Event
  | PN.Child c =>
      (Send_prefix Event.left (c / 2) (pChildR (c / 2))) [+]
        (Rec_prefix Event.right Set.univ fun x => pChildL (c, x))
  | PN.ChildL cx =>
      Send_prefix Event.left (cx.1 / 2) (pChild (fill (cx.1 / 2 + cx.2)))
  | PN.ChildR c =>
      Rec_prefix Event.right Set.univ fun x => pChild (fill (c + x))
  | PN.LineSpec s =>
      IF ChkLCR s THEN
        ((IF guardL s THEN
            Send_prefix Event.left (getNat (hd s) / 2) (pLineSpec (nextL s))
          ELSE
            proc.STOP) [+]
         (IF guardR s THEN
            Rec_prefix Event.right Set.univ fun x => pLineSpec (nextR (s, x))
          ELSE
            proc.STOP))
      ELSE
        proc.STOP

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_PNfun : HasPNfun PN Event where
  PNfun := PNdef

@[simp]
theorem Set_PNfun_def (pn : PN) :
    PNfun pn = PNdef pn :=
  rfl

/- ------------------ *
      guardedness
 * ------------------ -/

@[simp] theorem guardedfun_PN :
    guardedfun PNdef := by
  intro pn
  cases pn <;>
    simp [PNdef, Send_prefix, Rec_prefix, guarded, noHide]

/- Lean note:
   Isabelle's overloaded constant `FPmode` is represented by a typeclass
   instance. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

/- *********************************************************
                     Composition
 ********************************************************* -/

def ChildAtt : Att → proc PN Event
  | Att.AttL c => pChildL c
  | Att.AttC c => pChild c
  | Att.AttR c => pChildR c

abbrev LeftRight : Set Event :=
  Set.range Event.left ∪ Set.range Event.right

abbrev Line (P Q : proc PN Event) : proc PN Event :=
  Pipe P Event.left Event.mid Event.right Q

infixr:76 " <---> " => Line

abbrev PreCirc (P Q : proc PN Event) : proc PN Event :=
  P |[LeftRight]| (Q[[Event.right <==> Event.left]])

infixr:76 " <=-=> " => PreCirc

abbrev Circ (P Q : proc PN Event) : proc PN Event :=
  proc.Hiding (P <=-=> Q) (Set.range Event.right)

infixr:76 " <===> " => Circ

def LineChild : List Nat → proc PN Event
  | [] => proc.STOP
  | [c] => pChild c
  | c :: s@(_ :: _) => pChild c <---> LineChild s

def LineChildAtt : List Att → proc PN Event
  | [] => proc.STOP
  | [c] => ChildAtt c
  | c :: s@(_ :: _) => ChildAtt c <---> LineChildAtt s

def PreCircChild : List Nat → proc PN Event
  | [] => proc.STOP
  | c :: s => pChild c <=-=> LineChild s

def CircChild : List Nat → proc PN Event
  | [] => proc.STOP
  | c :: s => pChild c <===> LineChild s

/- --------------------------------- *
               lemmas
 * --------------------------------- -/

@[simp]
theorem LineChild_not_nil {c : Nat} {s : List Nat} :
    s ≠ [] → LineChild (c :: s) = pChild c <---> LineChild s := by
  intro hs
  cases s with
  | nil =>
      cases hs rfl
  | cons a t =>
      simp [LineChild]

@[simp]
theorem LineChildAtt_not_nil {c : Att} {s : List Att} :
    s ≠ [] → LineChildAtt (c :: s) = ChildAtt c <---> LineChildAtt s := by
  intro hs
  cases s with
  | nil =>
      cases hs rfl
  | cons a t =>
      simp [LineChildAtt]

private theorem LineChildAtt_one (a : Att) : LineChildAtt [a] = ChildAtt a := by
  simp [LineChildAtt]

/- *********************************************************
                  for convenience
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare simp_event_set [simp]` has no direct Lean analogue. -/

theorem Line_cong {P Q R : proc PN Event} :
    Q =F R → P <---> Q =F P <---> R := by
  intro hQR
  unfold Line Pipe
  apply cspF_Hiding_cong rfl
  apply cspF_Alpha_parallel_cong rfl rfl
  · exact cspF_Renaming_cong rfl cspF_reflex_eq_P
  · exact cspF_Renaming_cong rfl hQR

theorem Line_mono {P Q R : proc PN Event} :
    (Q <=F R) → (P <---> Q <=F P <---> R) := by
  intro hQR
  unfold Line Pipe
  apply cspF_Hiding_mono rfl
  apply cspF_Alpha_parallel_mono rfl rfl
  · exact cspF_Renaming_mono rfl cspF_reflex_ref_P
  · exact cspF_Renaming_mono rfl hQR

theorem PreCirc_cong {P Q R : proc PN Event} :
    Q =F R → P <=-=> Q =F P <=-=> R := by
  intro hQR
  unfold PreCirc
  exact cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_Renaming_cong rfl hQR)

theorem Circ_cong {P Q R : proc PN Event} :
    Q =F R → P <===> Q =F P <===> R := by
  intro hQR
  unfold Circ
  exact cspF_Hiding_cong rfl (PreCirc_cong (P := P) (Q := Q) (R := R) hQR)

/- *********************************************************
                  for induction (sub)
 ********************************************************* -/

/- Lean note:
   Isabelle's `!<f> :X .. Pf` (`CSP_syntax.thy:252`,
   `!<f> :X .. Pf == ! :(f ` X) .. (%x. Pf ((inv f) x))`) is a replicated
   *internal choice* indexed through `f`; it performs no event.  The port had
   `Nondet_send_prefix`, which is `!<f> :X -> Pf` and prefixes each branch
   with `f x`.  The source here writes `..`, so it is `Rep_int_choice_f`. -/

private abbrev lineSpecSendStep (s : List Att) : proc PN Event :=
  Rep_int_choice_f Event.stlist {t | toStbOne t = s} fun t =>
    ChildAtt (hd t) <---> pLineSpec (tl t)

def LineSpec_to_Step : PN → proc PN Event
  | PN.Child n => pChild n
  | PN.ChildL n => pChildL n
  | PN.ChildR n => pChildR n
  | PN.LineSpec s =>
      IF ChkLCR s THEN
        IF tl s = [] THEN
          pLineSpec s
        ELSE
          lineSpecSendStep s
      ELSE
        proc.STOP

private abbrev lineSpecStepBody (s : List Att) : proc PN Event :=
  (IF guardL s THEN
      Send_prefix Event.left (getNat (hd s) / 2) (LineSpec_to_Step (PN.LineSpec (nextL s)))
    ELSE
      proc.STOP) [+]
  (IF guardR s THEN
      Rec_prefix Event.right Set.univ fun x =>
        LineSpec_to_Step (PN.LineSpec (nextR (s, x)))
    ELSE
      proc.STOP)

private theorem IF_pos {c : Prop} [Decidable c] (h : c) (P Q : proc PN Event) :
    eqF (IF c THEN P ELSE Q) MF MF P := by
  rw [decide_eq_true h]
  exact cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem IF_neg {c : Prop} [Decidable c] (h : ¬ c) (P Q : proc PN Event) :
    eqF (IF c THEN P ELSE Q) MF MF Q := by
  rw [decide_eq_false h]
  exact cspF_trans_left_eq cspF_IF_split cspF_reflex_eq_P

private theorem rec_right_cong {Pf Qf : Nat → proc PN Event}
    (h : ∀ y, eqF (Pf y) MF MF (Qf y)) :
    eqF (Rec_prefix Event.right Set.univ Pf) MF MF (Rec_prefix Event.right Set.univ Qf) := by
  rw [Rec_prefix, Rec_prefix]
  exact cspF_Ext_pre_choice_cong rfl (fun e _ => h _)

private theorem unw (pn : PN) : eqF (proc.Proc_name pn : proc PN Event) MF MF (PNdef pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩))

/- --------------------- LineSpec_Step (lemmas) --------------------- -/

axiom LineSpec_Step_ref1_AttL_AttL {t : List Att} {n x na xa : Nat} :
    ChkLCR t →
      lineSpecStepBody (Att.AttL (n, x) :: Att.AttL (na, xa) :: t) <=F
        (pChildL (n, x) <---> pLineSpec (Att.AttL (na, xa) :: t))

axiom LineSpec_Step_ref1_AttL_AttC {t : List Att} {n x na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttL (n, x) :: Att.AttC na :: t) <=F
        (pChildL (n, x) <---> pLineSpec (Att.AttC na :: t))

axiom LineSpec_Step_ref1_AttL_AttR {t : List Att} {n x na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttL (n, x) :: Att.AttR na :: t) <=F
        (pChildL (n, x) <---> pLineSpec (Att.AttR na :: t))

axiom LineSpec_Step_ref1_AttC_AttC {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t) <=F
        (pChild n <---> pLineSpec (Att.AttC na :: t))

axiom LineSpec_Step_ref1_AttC_AttL {t : List Att} {na n x : Nat} :
    ChkLCR t →
      lineSpecStepBody (Att.AttL (na, n / 2) :: nextL (Att.AttL (n, x) :: t)) <=F
        (pChild na <---> pLineSpec (Att.AttL (n, x) :: t))

axiom LineSpec_Step_ref1_AttR_AttL {t : List Att} {na n x : Nat} :
    ChkLCR (toStbOne (Att.AttR na :: Att.AttL (n, x) :: t)) →
      lineSpecStepBody (toStbOne (Att.AttR na :: Att.AttL (n, x) :: t)) <=F
        (pChildR na <---> pLineSpec (Att.AttL (n, x) :: t))

axiom LineSpec_Step_ref1_AttC_AttR {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttC n :: Att.AttR na :: t) <=F
        (pChild n <---> pLineSpec (Att.AttR na :: t))

axiom LineSpec_Step_ref1_AttR_AttC {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttC (fill (n + na / 2)) :: Att.AttR (na / 2) :: t) <=F
        (pChildR n <---> pLineSpec (Att.AttC na :: t))

axiom LineSpec_Step_ref1_AttR_AttR {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttR n :: Att.AttR na :: t) <=F
        (pChildR n <---> pLineSpec (Att.AttR na :: t))

/- -------------------------- LineSpec_Step -------------------------- -/

/- ---------- list-level computations ---------- -/

private theorem toStbOne_AttC_AttL (n m z : Nat) (s : List Att) :
    toStbOne (Att.AttC n :: Att.AttL (m, z) :: s)
      = Att.AttL (n, m / 2) :: nextL (Att.AttL (m, z) :: s) := by simp [toStbOne]

private theorem toStbOne_AttC_AttC' (n m : Nat) (s : List Att) :
    toStbOne (Att.AttC n :: Att.AttC m :: s)
      = Att.AttL (n, m / 2) :: nextL (Att.AttC m :: s) := by simp [toStbOne]

private theorem toStbOne_AttC_AttR (n m : Nat) (s : List Att) :
    toStbOne (Att.AttC n :: Att.AttR m :: s) = Att.AttC n :: Att.AttR m :: s := by
  simp [toStbOne]

private theorem toStbOne_AttR_AttC (n m : Nat) (s : List Att) :
    toStbOne (Att.AttR n :: Att.AttC m :: s)
      = Att.AttC (fill (n + m / 2)) :: nextL (Att.AttC m :: s) := by simp [toStbOne]

private theorem toStbOne_AttR_AttR (n m : Nat) (s : List Att) :
    toStbOne (Att.AttR n :: Att.AttR m :: s) = Att.AttR n :: Att.AttR m :: s := by
  simp [toStbOne]

private theorem nextL_AttC_cons (m : Nat) (s : List Att) :
    nextL (Att.AttC m :: s) = Att.AttR (m / 2) :: s := by simp [nextL]

private theorem chkLCR_of_AttL {nx : Nat × Nat} {t : List Att}
    (h : ChkLCR (Att.AttL nx :: t)) : ChkLCR t := by
  rcases h with ⟨-, h⟩ | (⟨⟨m, hm⟩, -⟩ | ⟨⟨m, hm⟩, -⟩)
  · exact h
  · cases hm
  · cases hm

private theorem chkR_of_AttC {n : Nat} {t : List Att}
    (h : ChkLCR (Att.AttC n :: t)) : ChkR t := by
  rcases h with ⟨⟨m, hm⟩, -⟩ | (⟨-, h⟩ | ⟨⟨m, hm⟩, -⟩)
  · cases hm
  · exact h
  · cases hm

private theorem chkR_of_AttR {n : Nat} {t : List Att}
    (h : ChkLCR (Att.AttR n :: t)) : ChkR t := by
  rcases h with ⟨⟨m, hm⟩, -⟩ | (⟨⟨m, hm⟩, -⟩ | ⟨-, h⟩)
  · cases hm
  · cases hm
  · exact h

/- ---------- `tl x ≠ []`: the nine shapes ---------- -/

private theorem step_pair (a1 a2 : Att) (rest : List Att)
    (hchk : ChkLCR (toStbOne (a1 :: a2 :: rest))) :
    refF (lineSpecStepBody (toStbOne (a1 :: a2 :: rest))) MF MF
      (ChildAtt a1 <---> pLineSpec (a2 :: rest)) := by
  have hc2 : ChkLCR (a2 :: rest) := ChkLCR_toStbOne_iff.mp hchk
  rcases Att_or a1 with ⟨n, x, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rw [toStbOne_AttL]
    rcases Att_or a2 with ⟨na, xa, rfl⟩ | ⟨na, rfl⟩ | ⟨na, rfl⟩
    · exact LineSpec_Step_ref1_AttL_AttL (chkLCR_of_AttL hc2)
    · exact LineSpec_Step_ref1_AttL_AttC (chkR_of_AttC hc2)
    · exact LineSpec_Step_ref1_AttL_AttR (chkR_of_AttR hc2)
  · rcases Att_or a2 with ⟨m, z, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [toStbOne_AttC_AttL]
      exact LineSpec_Step_ref1_AttC_AttL (chkLCR_of_AttL hc2)
    · rw [toStbOne_AttC_AttC', nextL_AttC_cons]
      exact LineSpec_Step_ref1_AttC_AttC (chkR_of_AttC hc2)
    · rw [toStbOne_AttC_AttR]
      exact LineSpec_Step_ref1_AttC_AttR (chkR_of_AttR hc2)
  · rcases Att_or a2 with ⟨m, z, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact LineSpec_Step_ref1_AttR_AttL hchk
    · rw [toStbOne_AttR_AttC, nextL_AttC_cons]
      exact LineSpec_Step_ref1_AttR_AttC (chkR_of_AttC hc2)
    · rw [toStbOne_AttR_AttR]
      exact LineSpec_Step_ref1_AttR_AttR (chkR_of_AttR hc2)

private theorem step_long {x : List Att} (hchk : ChkLCR x) (htl : tl x ≠ []) :
    refF (lineSpecStepBody x) MF MF (lineSpecSendStep x) := by
  refine cspF_Rep_int_choice_f_right inj_stlist ?_
  rintro t (ht : toStbOne t = x)
  subst ht
  obtain ⟨a1, a2, rest, rfl⟩ := tl_toStbOne_not_nil.mp htl
  exact step_pair a1 a2 rest hchk

/- ---------- `tl x = []` ---------- -/

private theorem chk_single (b : Att) : ChkLCR [b] := by
  rcases Att_or b with ⟨n, z, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact Or.inl ⟨⟨(n, z), rfl⟩, trivial⟩
  · exact Or.inr (Or.inl ⟨⟨n, rfl⟩, trivial⟩)
  · exact Or.inr (Or.inr ⟨⟨n, rfl⟩, trivial⟩)

private theorem toStep_single (b : Att) :
    eqF (LineSpec_to_Step (PN.LineSpec [b])) MF MF (pLineSpec [b]) := by
  refine cspF_trans_left_eq (IF_pos (chk_single b) _ _) ?_
  exact IF_pos (show tl [b] = [] from rfl) _ _

private theorem nextL_single {a : Att} (h : guardL [a]) : ∃ b, nextL [a] = [b] := by
  rcases Att_or a with ⟨n, z, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
  · exact ⟨Att.AttC (fill (n / 2 + z)), by simp [nextL]⟩
  · exact ⟨Att.AttR (n / 2), by simp [nextL]⟩
  · rcases h with ⟨m, y, hm⟩ | ⟨m, hm⟩ <;> cases hm

private theorem nextR_single {a : Att} {y : Nat} (h : guardR [a]) :
    ∃ b, nextR ([a], y) = [b] := by
  rcases Att_or a with ⟨n, z, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
  · rcases h with ⟨m, hm⟩ | ⟨m, hm⟩ <;> cases hm
  · exact ⟨Att.AttL (n, y), by simp [nextR]⟩
  · exact ⟨Att.AttC (fill (n + y)), by simp [nextR]⟩

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_Step` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_short {x : List Att} (hchk : ChkLCR x) (htl : tl x = []) :
    refF (lineSpecStepBody x) MF MF (pLineSpec x) := by
  refine cspF_rw_right_ref (unw (PN.LineSpec x)) ?_
  refine cspF_rw_right_ref (IF_pos hchk _ _) ?_
  refine cspF_Ext_choice_mono ?_ ?_
  · by_cases hgL : guardL x
    · refine cspF_rw_left_ref (IF_pos hgL _ _) ?_
      refine cspF_rw_right_ref (IF_pos hgL _ _) ?_
      refine cspF_Act_prefix_mono rfl ?_
      obtain ⟨a, rfl⟩ : ∃ a, x = [a] := by
        cases x with
        | nil => exact absurd hgL (by simp [guardL])
        | cons a t => exact ⟨a, by simp_all [tl]⟩
      obtain ⟨b, hb⟩ := nextL_single hgL
      rw [hb]
      exact cspF_rw_left_ref (toStep_single b) cspF_reflex_ref_P
    · refine cspF_rw_left_ref (IF_neg hgL _ _) ?_
      exact cspF_rw_right_ref (IF_neg hgL _ _) cspF_reflex_ref_P
  · by_cases hgR : guardR x
    · refine cspF_rw_left_ref (IF_pos hgR _ _) ?_
      refine cspF_rw_right_ref (IF_pos hgR _ _) ?_
      obtain ⟨a, rfl⟩ : ∃ a, x = [a] := by
        cases x with
        | nil => exact absurd hgR (by simp [guardR])
        | cons a t => exact ⟨a, by simp_all [tl]⟩
      have hpt : ∀ y : Nat,
          eqF (LineSpec_to_Step (PN.LineSpec (nextR ([a], y)))) MF MF
            (pLineSpec (nextR ([a], y))) := by
        intro y
        obtain ⟨b, hb⟩ := nextR_single (a := a) (y := y) hgR
        rw [hb]
        exact toStep_single b
      refine cspF_rw_left_ref
        (rec_right_cong
          (Pf := fun y => LineSpec_to_Step (PN.LineSpec (nextR ([a], y))))
          (Qf := fun y => pLineSpec (nextR ([a], y))) hpt) cspF_reflex_ref_P
    · refine cspF_rw_left_ref (IF_neg hgR _ _) ?_
      exact cspF_rw_right_ref (IF_neg hgR _ _) cspF_reflex_ref_P

/- ---------- the step ---------- -/

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_Step` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_LineSpec (x : List Att) :
    refF ((PNdef (PN.LineSpec x)) << LineSpec_to_Step) MF MF
      (LineSpec_to_Step (PN.LineSpec x)) := by
  by_cases hchk : ChkLCR x
  · refine cspF_rw_left_ref (IF_pos hchk _ _) ?_
    refine cspF_rw_right_ref (IF_pos hchk _ _) ?_
    by_cases htl : tl x = []
    · refine cspF_rw_right_ref (IF_pos htl _ _) ?_
      exact step_short hchk htl
    · refine cspF_rw_right_ref (IF_neg htl _ _) ?_
      exact step_long hchk htl
  · refine cspF_rw_left_ref (IF_neg hchk _ _) ?_
    exact cspF_rw_right_ref (IF_neg hchk _ _) cspF_reflex_ref_P

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_Step` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
theorem LineSpec_Step {s : List Att} :
    pLineSpec s <=F LineSpec_to_Step (PN.LineSpec s) := by
  refine cspF_fp_induct_ref_left (Pf := PNdef) (f := LineSpec_to_Step) (p0 := PN.LineSpec s)
    rfl (Or.inl rfl) guardedfun_PN cspF_reflex_ref_P ?_
  intro p
  cases p with
  | Child n => exact cspF_rw_right_ref (unw (PN.Child n)) cspF_reflex_ref_P
  | ChildL cx => exact cspF_rw_right_ref (unw (PN.ChildL cx)) cspF_reflex_ref_P
  | ChildR c => exact cspF_rw_right_ref (unw (PN.ChildR c)) cspF_reflex_ref_P
  | LineSpec x => exact step_LineSpec x

/- *********************************************************
                          one
 ********************************************************* -/

def LineSpec_to_One : PN → proc PN Event
  | PN.Child n => pChild n
  | PN.ChildL n => pChildL n
  | PN.ChildR n => pChildR n
  | PN.LineSpec s =>
      IF ∃ a, s = [a] THEN
        ChildAtt (hd s)
      ELSE
        pLineSpec s

/- ---------- LineSpec [a] <=F ChildAtt a ---------- -/

/- ---------- `ChkLCR` / `guardL` / `guardR` on singletons ---------- -/

private theorem chk_AttL (n z : Nat) : ChkLCR [Att.AttL (n, z)] :=
  Or.inl ⟨⟨(n, z), rfl⟩, trivial⟩
private theorem chk_AttC (n : Nat) : ChkLCR [Att.AttC n] :=
  Or.inr (Or.inl ⟨⟨n, rfl⟩, trivial⟩)
private theorem chk_AttR (n : Nat) : ChkLCR [Att.AttR n] :=
  Or.inr (Or.inr ⟨⟨n, rfl⟩, trivial⟩)

private theorem gL_AttL (n z : Nat) : guardL [Att.AttL (n, z)] := Or.inl ⟨n, z, rfl⟩
private theorem gL_AttC (n : Nat) : guardL [Att.AttC n] := Or.inr ⟨n, rfl⟩
private theorem gL_AttR (n : Nat) : ¬ guardL [Att.AttR n] := by
  rintro (⟨m, y, hm⟩ | ⟨m, hm⟩) <;> cases hm

private theorem gR_AttL (n z : Nat) : ¬ guardR [Att.AttL (n, z)] := by
  rintro (⟨m, hm⟩ | ⟨m, hm⟩) <;> cases hm
private theorem gR_AttC (n : Nat) : guardR [Att.AttC n] := Or.inl ⟨n, rfl⟩
private theorem gR_AttR (n : Nat) : guardR [Att.AttR n] := Or.inr ⟨n, rfl⟩

private theorem nextL_AttL (n z : Nat) :
    nextL [Att.AttL (n, z)] = [Att.AttC (fill (n / 2 + z))] := by simp [nextL]
private theorem nextL_AttC (n : Nat) : nextL [Att.AttC n] = [Att.AttR (n / 2)] := by simp [nextL]
private theorem nextR_AttC (n y : Nat) :
    nextR ([Att.AttC n], y) = [Att.AttL (n, y)] := by simp [nextR]
private theorem nextR_AttR (n y : Nat) :
    nextR ([Att.AttR n], y) = [Att.AttC (fill (n + y))] := by simp [nextR]

/- ---------- one step of `$LineSpec [a]` ---------- -/

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_One` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_AttL (n z : Nat) :
    refF ((PNdef (PN.LineSpec [Att.AttL (n, z)])) << LineSpec_to_One) MF MF
      (ChildAtt (Att.AttL (n, z))) := by
  refine cspF_rw_left_ref (IF_pos (chk_AttL n z) _ _) ?_
  refine cspF_rw_left_ref
    (cspF_Ext_choice_cong (IF_pos (gL_AttL n z) _ _) (IF_neg (gR_AttL n z) _ _)) ?_
  refine cspF_rw_left_ref cspF_Ext_choice_unit_r ?_
  rw [nextL_AttL n z]
  refine cspF_rw_left_ref
    (cspF_Act_prefix_cong rfl (IF_pos ⟨Att.AttC (fill (n / 2 + z)), rfl⟩ _ _)) ?_
  exact cspF_rw_right_ref (unw (PN.ChildL (n, z))) cspF_reflex_ref_P

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_One` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_AttC (n : Nat) :
    refF ((PNdef (PN.LineSpec [Att.AttC n])) << LineSpec_to_One) MF MF
      (ChildAtt (Att.AttC n)) := by
  have hpt : ∀ y : Nat,
      eqF (LineSpec_to_One (PN.LineSpec (nextR ([Att.AttC n], y)))) MF MF (pChildL (n, y)) := by
    intro y
    rw [nextR_AttC n y]
    exact IF_pos ⟨Att.AttL (n, y), rfl⟩ _ _
  refine cspF_rw_left_ref (IF_pos (chk_AttC n) _ _) ?_
  refine cspF_rw_left_ref
    (cspF_Ext_choice_cong (IF_pos (gL_AttC n) _ _) (IF_pos (gR_AttC n) _ _)) ?_
  rw [nextL_AttC n]
  refine cspF_rw_left_ref
    (cspF_Ext_choice_cong
      (cspF_Act_prefix_cong rfl (IF_pos ⟨Att.AttR (n / 2), rfl⟩ _ _))
      (rec_right_cong hpt)) ?_
  exact cspF_rw_right_ref (unw (PN.Child n)) cspF_reflex_ref_P

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_One` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_AttR (n : Nat) :
    refF ((PNdef (PN.LineSpec [Att.AttR n])) << LineSpec_to_One) MF MF
      (ChildAtt (Att.AttR n)) := by
  have hpt : ∀ y : Nat,
      eqF (LineSpec_to_One (PN.LineSpec (nextR ([Att.AttR n], y)))) MF MF
        (pChild (fill (n + y))) := by
    intro y
    rw [nextR_AttR n y]
    exact IF_pos ⟨Att.AttC (fill (n + y)), rfl⟩ _ _
  refine cspF_rw_left_ref (IF_pos (chk_AttR n) _ _) ?_
  refine cspF_rw_left_ref
    (cspF_Ext_choice_cong (IF_neg (gL_AttR n) _ _) (IF_pos (gR_AttR n) _ _)) ?_
  refine cspF_rw_left_ref cspF_Ext_choice_unit_l ?_
  refine cspF_rw_left_ref (rec_right_cong hpt) ?_
  exact cspF_rw_right_ref (unw (PN.ChildR n)) cspF_reflex_ref_P

/- ---------- the non-singleton case ---------- -/

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_One` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_many {x : List Att} (hchk : ChkLCR x) (hone : ¬ ∃ b : Att, x = [b]) :
    refF ((PNdef (PN.LineSpec x)) << LineSpec_to_One) MF MF (pLineSpec x) := by
  have hptR : ∀ y : Nat,
      eqF (LineSpec_to_One (PN.LineSpec (nextR (x, y)))) MF MF (pLineSpec (nextR (x, y))) := by
    intro y
    refine IF_neg ?_ _ _
    rintro ⟨b, hb⟩
    exact hone (nextR_one_EX hchk hb)
  have hptL : eqF (LineSpec_to_One (PN.LineSpec (nextL x))) MF MF (pLineSpec (nextL x)) := by
    refine IF_neg ?_ _ _
    rintro ⟨b, hb⟩
    exact hone (nextL_one_EX hchk hb)
  refine cspF_rw_right_ref (unw (PN.LineSpec x)) ?_
  refine cspF_rw_left_ref (IF_pos hchk _ _) ?_
  refine cspF_rw_right_ref (IF_pos hchk _ _) ?_
  refine cspF_Ext_choice_mono ?_ ?_
  · by_cases hgL : guardL x
    · refine cspF_rw_left_ref (IF_pos hgL _ _) ?_
      refine cspF_rw_right_ref (IF_pos hgL _ _) ?_
      exact cspF_Act_prefix_mono rfl (cspF_rw_left_ref hptL cspF_reflex_ref_P)
    · refine cspF_rw_left_ref (IF_neg hgL _ _) ?_
      exact cspF_rw_right_ref (IF_neg hgL _ _) cspF_reflex_ref_P
  · by_cases hgR : guardR x
    · refine cspF_rw_left_ref (IF_pos hgR _ _) ?_
      refine cspF_rw_right_ref (IF_pos hgR _ _) ?_
      exact cspF_rw_left_ref
        (rec_right_cong (Pf := fun y => LineSpec_to_One (PN.LineSpec (nextR (x, y))))
          (Qf := fun y => pLineSpec (nextR (x, y))) hptR) cspF_reflex_ref_P
    · refine cspF_rw_left_ref (IF_neg hgR _ _) ?_
      exact cspF_rw_right_ref (IF_neg hgR _ _) cspF_reflex_ref_P

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_One` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
private theorem step_many' {x : List Att} (hone : ¬ ∃ b : Att, x = [b]) :
    refF ((PNdef (PN.LineSpec x)) << LineSpec_to_One) MF MF (pLineSpec x) := by
  by_cases hchk : ChkLCR x
  · exact step_many hchk hone
  · refine cspF_rw_right_ref (unw (PN.LineSpec x)) ?_
    refine cspF_rw_left_ref (IF_neg hchk _ _) ?_
    exact cspF_rw_right_ref (IF_neg hchk _ _) cspF_reflex_ref_P

set_option maxHeartbeats 1000000 in
-- `PNdef (PN.LineSpec _) << LineSpec_to_One` has to be unfolded through
-- `Rec_prefix`, whose index set is `Event.right '' Set.univ` and whose
-- branch function goes through `Function.invFun`; the defeq checks that
-- drives are past the default budget.
theorem LineSpec_One {a : Att} :
    pLineSpec [a] <=F ChildAtt a := by
  refine cspF_fp_induct_ref_left (Pf := PNdef) (f := LineSpec_to_One) (p0 := PN.LineSpec [a])
    rfl (Or.inl rfl) guardedfun_PN ?_ ?_
  · exact cspF_rw_left_ref (IF_pos ⟨a, rfl⟩ _ _) cspF_reflex_ref_P
  · intro p
    cases p with
    | Child n => exact cspF_rw_right_ref (unw (PN.Child n)) cspF_reflex_ref_P
    | ChildL cx => exact cspF_rw_right_ref (unw (PN.ChildL cx)) cspF_reflex_ref_P
    | ChildR c => exact cspF_rw_right_ref (unw (PN.ChildR c)) cspF_reflex_ref_P
    | LineSpec x =>
        by_cases hone : ∃ b : Att, x = [b]
        · obtain ⟨b, rfl⟩ := hone
          refine cspF_rw_right_ref (IF_pos ⟨b, rfl⟩ _ _) ?_
          rcases Att_or b with ⟨n, z, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩
          · exact step_AttL n z
          · exact step_AttC n
          · exact step_AttR n
        · exact cspF_rw_right_ref (IF_neg hone _ _) (step_many' hone)

/- Lean note:
   Isabelle's local simp-set updates for `ChkLCR.simps` do not have a direct
   Lean analogue here. -/

set_option maxHeartbeats 1000000 in
-- the `Rep_int_choice_f` index set is `Event.stlist '' {t | toStbOne t = s}`
-- and its branch function goes through `Function.invFun`; the defeq checks
-- that drives are past the default budget.
theorem LineSpec_LineChild_toStbOne_lm (n : Nat) :
    ∀ s, (s.length = n ∧ ChkLCR s ∧ s ≠ []) →
      pLineSpec s <=F
        Rep_int_choice_f Event.stlist {t | toStbOne t = s} fun t => LineChildAtt t := by
  induction n with
  | zero =>
      rintro s ⟨hlen, -, hne⟩
      exact absurd (List.length_eq_zero_iff.mp hlen) hne
  | succ n ih =>
      rintro s ⟨hlen, hchk, hne⟩
      refine cspF_trans_left_ref LineSpec_Step ?_
      refine cspF_rw_left_ref (IF_pos hchk _ _) ?_
      refine cspF_Rep_int_choice_f_right inj_stlist ?_
      rintro t (ht : toStbOne t = s)
      by_cases htl : tl s = []
      · refine cspF_rw_left_ref (IF_pos htl _ _) ?_
        obtain ⟨a, rfl⟩ : ∃ a, s = [a] := by
          cases s with
          | nil => exact absurd rfl hne
          | cons a u =>
              cases u with
              | nil => exact ⟨a, rfl⟩
              | cons b v => exact absurd htl (by simp [tl])
        obtain rfl : t = [a] := toStbOne_one.mp ht
        rw [LineChildAtt_one]
        exact LineSpec_One
      · refine cspF_rw_left_ref (IF_neg htl _ _) ?_
        refine cspF_Rep_int_choice_f_left_x inj_stlist ht ?_
        have htl' : tl (toStbOne t) ≠ [] := by rw [ht]; exact htl
        obtain ⟨a1, a2, rest, rfl⟩ := tl_toStbOne_not_nil.mp htl'
        have hchk2 : ChkLCR (a2 :: rest) := ChkLCR_toStbOne_iff.mp (ht ▸ hchk)
        have hlen2 : (a2 :: rest).length = n := by
          have h := toStbOne_length (t := a2 :: rest) a1 hchk2
          rw [ht] at h
          omega
        rw [LineChildAtt_not_nil (by simp)]
        refine Line_mono ?_
        refine cspF_trans_left_ref (ih (a2 :: rest) ⟨hlen2, hchk2, by simp⟩) ?_
        exact cspF_Rep_int_choice_f_left_x inj_stlist
          (show toStbOne (a2 :: rest) = a2 :: rest from ChkLCR_toStbOne_id hchk2)
          cspF_reflex_ref_P

theorem LineSpec_LineChild_toStbOne {s : List Att} :
    ChkLCR s → s ≠ [] →
      pLineSpec s <=F
        Rep_int_choice_f Event.stlist {t | toStbOne t = s} fun t => LineChildAtt t := by
  intro hChk hs
  exact LineSpec_LineChild_toStbOne_lm s.length s ⟨rfl, hChk, hs⟩

set_option maxHeartbeats 1000000 in
-- the `Rep_int_choice_f` index set is `Event.stlist '' {t | toStbOne t = s}`
-- and its branch function goes through `Function.invFun`; the defeq checks
-- that drives are past the default budget.
theorem LineSpec_LineChild_toStb_lm (n : Nat) :
    ∀ t, (t.length = n ∧ t ≠ []) → pLineSpec (toStb t) <=F LineChildAtt t := by
  induction n with
  | zero =>
      rintro t ⟨hlen, hne⟩
      exact absurd (List.length_eq_zero_iff.mp hlen) hne
  | succ n ih =>
      rintro t ⟨hlen, hne⟩
      cases t with
      | nil => exact absurd rfl hne
      | cons a u =>
          cases u with
          | nil =>
              have h : toStb [a] = [a] := by simp [toStb, toStbOne]
              rw [h, LineChildAtt_one]
              exact LineSpec_One
          | cons b v =>
              have hu : (b :: v) ≠ [] := by simp
              have hst : toStb (a :: b :: v) = toStbOne (a :: toStb (b :: v)) := by
                simp [toStb]
              have hchkst : ChkLCR (toStb (b :: v)) := ChkLCR_toStb
              have hchk : ChkLCR (toStb (a :: b :: v)) := ChkLCR_toStb
              have hstne : toStb (b :: v) ≠ [] := by simp
              obtain ⟨c, w, hcw⟩ : ∃ c w, toStb (b :: v) = c :: w := by
                cases hbv : toStb (b :: v) with
                | nil => exact absurd hbv hstne
                | cons c w => exact ⟨c, w, rfl⟩
              have htl : tl (toStb (a :: b :: v)) ≠ [] := by
                rw [hst, hcw]
                exact tl_toStbOne_not_nil.mpr ⟨a, c, w, rfl⟩
              refine cspF_trans_left_ref LineSpec_Step ?_
              refine cspF_rw_left_ref (IF_pos hchk _ _) ?_
              refine cspF_rw_left_ref (IF_neg htl _ _) ?_
              refine cspF_Rep_int_choice_f_left_x inj_stlist
                (a := a :: toStb (b :: v)) (show toStbOne (a :: toStb (b :: v))
                  = toStb (a :: b :: v) from hst.symm) ?_
              rw [LineChildAtt_not_nil (by simp)]
              refine Line_mono ?_
              exact ih (b :: v) ⟨by simp only [List.length_cons] at hlen ⊢; omega, hu⟩

/- --------------------------------- *
          LineSpec (main)
 * --------------------------------- -/

theorem LineSpec_LineChildAtt {t : List Att} :
    t ≠ [] → pLineSpec (toStb t) <=F LineChildAtt t := by
  intro ht
  exact LineSpec_LineChild_toStb_lm t.length t ⟨rfl, ht⟩

theorem LineChild_LineChildAtt {s : List Nat} :
    s ≠ [] → LineChild s = LineChildAtt (List.map Att.AttC s) := by
  intro hs
  induction s with
  | nil =>
      cases hs rfl
  | cons a t ih =>
      cases t with
      | nil =>
          simp [LineChild, LineChildAtt, ChildAtt]
      | cons b u =>
          have ht : b :: u ≠ [] := by simp
          simp [ChildAtt, ih ht]

theorem LineSpec_LineChild {t : List Nat} :
    t ≠ [] → pLineSpec (toStb (List.map Att.AttC t)) <=F LineChild t := by
  intro ht
  have hmap : List.map Att.AttC t ≠ [] := by
    cases t with
    | nil =>
        cases ht rfl
    | cons a s =>
        simp
  simpa [LineChild_LineChildAtt (s := t) ht] using
    (LineSpec_LineChildAtt (t := List.map Att.AttC t) hmap)
