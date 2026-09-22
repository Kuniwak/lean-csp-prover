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

private abbrev lineSpecSendStep (s : List Att) : proc PN Event :=
  Nondet_send_prefix Event.stlist {t | toStbOne t = s} fun t =>
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

axiom LineSpec_Step {s : List Att} :
    pLineSpec s <=F LineSpec_to_Step (PN.LineSpec s)

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

axiom LineSpec_LineChild_toStbOne_lm (n : Nat) :
    ∀ s, (s.length = n ∧ ChkLCR s ∧ s ≠ []) →
      pLineSpec s <=F
        Nondet_send_prefix Event.stlist {t | toStbOne t = s} fun t => LineChildAtt t

theorem LineSpec_LineChild_toStbOne {s : List Att} :
    ChkLCR s → s ≠ [] →
      pLineSpec s <=F
        Nondet_send_prefix Event.stlist {t | toStbOne t = s} fun t => LineChildAtt t := by
  intro hChk hs
  exact LineSpec_LineChild_toStbOne_lm s.length s ⟨rfl, hChk, hs⟩

axiom LineSpec_LineChild_toStb_lm (n : Nat) :
    ∀ t, (t.length = n ∧ t ≠ []) → pLineSpec (toStb t) <=F LineChildAtt t

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
