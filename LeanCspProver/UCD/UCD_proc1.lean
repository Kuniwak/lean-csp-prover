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

@[simp] axiom guardedfun_PN :
    guardedfun PNdef

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

axiom LineSpec_One {a : Att} :
    pLineSpec [a] <=F ChildAtt a

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
