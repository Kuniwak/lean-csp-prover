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

/- *********************************************************
          expanding the pipe operator `<--->`
 ********************************************************* -/

/- the two renaming functions of the pipe -/

private abbrev fL : Event → Event := Renaming1_channel_fun Event.right Event.mid
private abbrev fR : Event → Event := Renaming1_channel_fun Event.left Event.mid

private theorem right_ne_mid : ∀ x y, Event.right x ≠ Event.mid y := by
  intro x y h; cases h

private theorem left_ne_mid : ∀ x y, Event.left x ≠ Event.mid y := by
  intro x y h; cases h

private theorem left_ne_right : ∀ x y, Event.left x ≠ Event.right y := by
  intro x y h; cases h

private theorem fL_right (n : Nat) : fL (Event.right n) = Event.mid n :=
  Renaming1_channel_fun_f inj_event.2.1 right_ne_mid

private theorem fL_mid (n : Nat) : fL (Event.mid n) = Event.right n :=
  Renaming_channel_fun_g inj_event.2.2 right_ne_mid

private theorem fL_left (n : Nat) : fL (Event.left n) = Event.left n :=
  Renaming1_channel_fun_h right_ne_mid
    (fun x y => fun h => left_ne_right y x h.symm) (fun x y => fun h => left_ne_mid y x h.symm)

private theorem fL_stlist (l : List Att) : fL (Event.stlist l) = Event.stlist l :=
  Renaming1_channel_fun_h right_ne_mid
    (fun x y => by intro h; cases h) (fun x y => by intro h; cases h)

private theorem fR_left (n : Nat) : fR (Event.left n) = Event.mid n :=
  Renaming1_channel_fun_f inj_event.1 left_ne_mid

private theorem fR_mid (n : Nat) : fR (Event.mid n) = Event.left n :=
  Renaming_channel_fun_g inj_event.2.2 left_ne_mid

private theorem fR_right (n : Nat) : fR (Event.right n) = Event.right n :=
  Renaming1_channel_fun_h left_ne_mid
    (fun x y => left_ne_right x y) (fun x y => fun h => by cases h)

private theorem fR_stlist (l : List Att) : fR (Event.stlist l) = Event.stlist l :=
  Renaming1_channel_fun_h left_ne_mid
    (fun x y => by intro h; cases h) (fun x y => by intro h; cases h)

private theorem inj_fL : Function.Injective fL := by
  intro a b h
  cases a <;> cases b <;>
    simp only [fL_left, fL_right, fL_mid, fL_stlist] at h <;>
    first
      | rfl
      | (cases h; rfl)
      | exact absurd h (by simp)

private theorem inj_fR : Function.Injective fR := by
  intro a b h
  cases a <;> cases b <;>
    simp only [fR_left, fR_right, fR_mid, fR_stlist] at h <;>
    first
      | rfl
      | (cases h; rfl)
      | exact absurd h (by simp)

/- the pipe alphabets -/

private abbrev XL : Set Event := Set.range Event.left ∪ Set.range Event.mid
private abbrev XR : Set Event := Set.range Event.mid ∪ Set.range Event.right

private theorem XL_inter_XR : XL ∩ XR = Set.range Event.mid := by
  ext e
  cases e <;> simp

private theorem Line_eq_pipe (P Q : proc PN Event) :
    Line P Q =
      proc.Hiding (Alpha_parallel (P[[fun_to_rel fL]]) XL XR (Q[[fun_to_rel fR]]))
        (XL ∩ XR) := by
  rw [XL_inter_XR]
  rfl

/- a left-output prefix after the left renaming -/

private theorem renL_Act_left (n : Nat) (P : proc PN Event) :
    eqFfix ((Event.left n ~> P)[[fun_to_rel fL]])
      (proc.Ext_pre_choice ({Event.left n} : Set Event)
        (fun _ => P[[fun_to_rel fL]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_fun_Act_prefix inj_fL) ?_
  rw [fL_left]
  exact cspF_Act_prefix_step

/- ---------- renamed normal forms of the UCD process shapes ---------- -/

private theorem invL_mid (n : Nat) : Function.invFun fL (Event.mid n) = Event.right n := by
  have h := Function.leftInverse_invFun inj_fL (Event.right n)
  rwa [fL_right] at h

private theorem invL_left (n : Nat) : Function.invFun fL (Event.left n) = Event.left n := by
  have h := Function.leftInverse_invFun inj_fL (Event.left n)
  rwa [fL_left] at h

private theorem image_fL_right : fL '' (Set.range Event.right) = Set.range Event.mid := by
  ext e
  constructor
  · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (fL_right n).symm ▸ rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨Event.right n, ⟨n, rfl⟩, fL_right n⟩

private theorem renL_R (Qf : Nat → proc PN Event) :
    eqFfix ((Rec_prefix Event.right Set.univ Qf)[[fun_to_rel fL]])
      (proc.Ext_pre_choice (Set.range Event.mid) fun x =>
        (Qf (Function.invFun Event.mid x))[[fun_to_rel fL]]) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq (cspF_Renaming_fun_Ext_pre_choice inj_fL) ?_
  have himg : fL '' (Event.right '' (Set.univ : Set Nat)) = Set.range Event.mid := by
    rw [Set.image_univ]; exact image_fL_right
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  obtain ⟨n, rfl⟩ := hy
  rw [invL_mid n, Function.leftInverse_invFun inj_event.2.1 n,
    Function.leftInverse_invFun inj_event.2.2 n]
  exact cspF_reflex_eq_P

private theorem invR_mid (n : Nat) : Function.invFun fR (Event.mid n) = Event.left n := by
  have h := Function.leftInverse_invFun inj_fR (Event.left n)
  rwa [fR_left] at h

private theorem invR_right (n : Nat) : Function.invFun fR (Event.right n) = Event.right n := by
  have h := Function.leftInverse_invFun inj_fR (Event.right n)
  rwa [fR_right] at h

private theorem image_fR_right : fR '' (Set.range Event.right) = Set.range Event.right := by
  ext e
  constructor
  · rintro ⟨x, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, (fR_right n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨Event.right n, ⟨n, rfl⟩, fR_right n⟩

private theorem renR_R (Qf : Nat → proc PN Event) :
    eqFfix ((Rec_prefix Event.right Set.univ Qf)[[fun_to_rel fR]])
      (proc.Ext_pre_choice (Set.range Event.right) fun x =>
        (Qf (Function.invFun Event.right x))[[fun_to_rel fR]]) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq (cspF_Renaming_fun_Ext_pre_choice inj_fR) ?_
  have himg : fR '' (Event.right '' (Set.univ : Set Nat)) = Set.range Event.right := by
    rw [Set.image_univ]; exact image_fR_right
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  obtain ⟨n, rfl⟩ := hy
  rw [invR_right n]
  exact cspF_reflex_eq_P

private theorem renR_L (v : Nat) (P : proc PN Event) :
    eqFfix ((Event.left v ~> P)[[fun_to_rel fR]])
      (proc.Ext_pre_choice ({Event.mid v} : Set Event)
        (fun _ => P[[fun_to_rel fR]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_fun_Act_prefix inj_fR) ?_
  rw [fR_left]
  exact cspF_Act_prefix_step

private theorem renL_LR (v : Nat) (P : proc PN Event) (Qf : Nat → proc PN Event) :
    eqFfix (((Event.left v ~> P) [+] (Rec_prefix Event.right Set.univ Qf))[[fun_to_rel fL]])
      (proc.Ext_pre_choice (({Event.left v} : Set Event) ∪ Set.range Event.mid) fun x =>
        procIte (x = Event.left v) (P[[fun_to_rel fL]])
          ((Qf (Function.invFun Event.mid x))[[fun_to_rel fL]])) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq
    (cspF_Renaming_cong rfl
      (cspF_Ext_choice_cong (cspF_Act_prefix_step (a := Event.left v) (P := P))
        cspF_reflex_eq_P)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_step) ?_
  refine cspF_trans_left_eq (cspF_Renaming_fun_Ext_pre_choice inj_fL) ?_
  have himg : fL '' ((({Event.left v} : Set Event)) ∪ Event.right '' (Set.univ : Set Nat))
      = (({Event.left v} : Set Event)) ∪ Set.range Event.mid := by
    rw [Set.image_univ, Set.image_union, Set.image_singleton, fL_left, image_fL_right]
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  rcases hy with hy | ⟨n, rfl⟩
  · have hyv : y = Event.left v := hy
    subst hyv
    have hmem : Event.left v ∈ ({Event.left v} : Set Event) := Set.mem_singleton_iff.mpr rfl
    have hnot : ¬ (Event.left v ∈ ({Event.left v} : Set Event) ∧
        Event.left v ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    rw [invL_left v]
    simp only [procIte_neg hnot, procIte_pos hmem, procIte_pos True.intro]
    exact cspF_reflex_eq_P
  · have hnot1 : ¬ (Event.right n ∈ ({Event.left v} : Set Event) ∧
        Event.right n ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    have hnot2 : ¬ (Event.right n ∈ ({Event.left v} : Set Event)) := by simp
    have hnot3 : ¬ (Event.mid n = Event.left v) := by simp
    rw [invL_mid n]
    simp only [procIte_neg hnot1, procIte_neg hnot2, procIte_neg hnot3]
    rw [Function.leftInverse_invFun inj_event.2.1 n,
      Function.leftInverse_invFun inj_event.2.2 n]
    exact cspF_reflex_eq_P

private theorem renR_LR (v : Nat) (P : proc PN Event) (Qf : Nat → proc PN Event) :
    eqFfix (((Event.left v ~> P) [+] (Rec_prefix Event.right Set.univ Qf))[[fun_to_rel fR]])
      (proc.Ext_pre_choice (({Event.mid v} : Set Event) ∪ Set.range Event.right) fun x =>
        procIte (x = Event.mid v) (P[[fun_to_rel fR]])
          ((Qf (Function.invFun Event.right x))[[fun_to_rel fR]])) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq
    (cspF_Renaming_cong rfl
      (cspF_Ext_choice_cong (cspF_Act_prefix_step (a := Event.left v) (P := P))
        cspF_reflex_eq_P)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_step) ?_
  refine cspF_trans_left_eq (cspF_Renaming_fun_Ext_pre_choice inj_fR) ?_
  have himg : fR '' ((({Event.left v} : Set Event)) ∪ Event.right '' (Set.univ : Set Nat))
      = (({Event.mid v} : Set Event)) ∪ Set.range Event.right := by
    rw [Set.image_univ, Set.image_union, Set.image_singleton, fR_left, image_fR_right]
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  rcases hy with hy | ⟨n, rfl⟩
  · have hyv : y = Event.mid v := hy
    subst hyv
    have hmem : Event.left v ∈ ({Event.left v} : Set Event) := Set.mem_singleton_iff.mpr rfl
    have hnot : ¬ (Event.left v ∈ ({Event.left v} : Set Event) ∧
        Event.left v ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    rw [invR_mid v]
    simp only [procIte_neg hnot, procIte_pos hmem, procIte_pos True.intro]
    exact cspF_reflex_eq_P
  · have hnot1 : ¬ (Event.right n ∈ ({Event.left v} : Set Event) ∧
        Event.right n ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    have hnot2 : ¬ (Event.right n ∈ ({Event.left v} : Set Event)) := by simp
    have hnot3 : ¬ (Event.right n = Event.mid v) := by simp
    rw [invR_right n]
    simp only [procIte_neg hnot1, procIte_neg hnot2, procIte_neg hnot3]
    rw [Function.leftInverse_invFun inj_event.2.1 n]
    exact cspF_reflex_eq_P

/- ---------- the generic Line step ---------- -/

private theorem Line_step_nosync {P Q : proc PN Event} {A B : Set Event}
    {Pf Qf : Event → proc PN Event}
    (hP : eqFfix (P[[fun_to_rel fL]]) (proc.Ext_pre_choice A Pf))
    (hQ : eqFfix (Q[[fun_to_rel fR]]) (proc.Ext_pre_choice B Qf))
    (hA : A ⊆ XL) (hB : B ⊆ XR) (hsync : A ∩ B = ∅) :
    eqFfix (Line P Q)
      (proc.Ext_pre_choice ((A \ XR) ∪ (B \ XL)) fun x =>
        procIte (x ∈ A)
          (proc.Hiding (Alpha_parallel (Pf x) XL XR (proc.Ext_pre_choice B Qf)) (XL ∩ XR))
          (proc.Hiding (Alpha_parallel (proc.Ext_pre_choice A Pf) XL XR (Qf x)) (XL ∩ XR))) := by
  rw [Line_eq_pipe]
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Alpha_parallel_cong rfl rfl hP hQ)) ?_
  exact cspF_Pipe_step_nosync hA hB hsync

private theorem Line_step_sync {P Q : proc PN Event} {A B : Set Event}
    {Pf Qf : Event → proc PN Event}
    (hP : eqFfix (P[[fun_to_rel fL]]) (proc.Ext_pre_choice A Pf))
    (hQ : eqFfix (Q[[fun_to_rel fR]]) (proc.Ext_pre_choice B Qf))
    (hA : A ⊆ XL) (hB : B ⊆ XR) (hsync : A ∩ B ≠ ∅) :
    eqFfix (Line P Q)
      ((proc.Ext_pre_choice ((A \ XR) ∪ (B \ XL)) fun x =>
          procIte (x ∈ A)
            (proc.Hiding (Alpha_parallel (Pf x) XL XR (proc.Ext_pre_choice B Qf)) (XL ∩ XR))
            (proc.Hiding (Alpha_parallel (proc.Ext_pre_choice A Pf) XL XR (Qf x)) (XL ∩ XR)))
        [> Rep_int_choice_com (A ∩ B) fun x =>
            proc.Hiding (Alpha_parallel (Pf x) XL XR (Qf x)) (XL ∩ XR)) := by
  rw [Line_eq_pipe]
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Alpha_parallel_cong rfl rfl hP hQ)) ?_
  exact cspF_Pipe_step_sync hA hB hsync

/- ---------- folding the expansion back into a Line ---------- -/

private theorem Line_fold_left {P' Q : proc PN Event} {B : Set Event} {Qf : Event → proc PN Event}
    (hQ : eqFfix (Q[[fun_to_rel fR]]) (proc.Ext_pre_choice B Qf)) :
    eqFfix
      (proc.Hiding (Alpha_parallel (P'[[fun_to_rel fL]]) XL XR (proc.Ext_pre_choice B Qf))
        (XL ∩ XR))
      (Line P' Q) := by
  rw [Line_eq_pipe]
  exact cspF_Hiding_cong rfl
    (cspF_Alpha_parallel_cong rfl rfl cspF_reflex_eq_P (cspF_sym hQ))

private theorem Line_fold_right {P Q' : proc PN Event} {A : Set Event} {Pf : Event → proc PN Event}
    (hP : eqFfix (P[[fun_to_rel fL]]) (proc.Ext_pre_choice A Pf)) :
    eqFfix
      (proc.Hiding (Alpha_parallel (proc.Ext_pre_choice A Pf) XL XR (Q'[[fun_to_rel fR]]))
        (XL ∩ XR))
      (Line P Q') := by
  rw [Line_eq_pipe]
  exact cspF_Hiding_cong rfl
    (cspF_Alpha_parallel_cong rfl rfl (cspF_sym hP) cspF_reflex_eq_P)

private theorem Line_fold_both {P' Q' : proc PN Event} :
    eqFfix
      (proc.Hiding (Alpha_parallel (P'[[fun_to_rel fL]]) XL XR (Q'[[fun_to_rel fR]]))
        (XL ∩ XR))
      (Line P' Q') := by
  rw [Line_eq_pipe]
  exact cspF_reflex_eq_P


/- ---------- normal forms of the UCD processes ---------- -/

private theorem LR_normal (v : Nat) (P : proc PN Event) (Qf : Nat → proc PN Event) :
    eqFfix ((Event.left v ~> P) [+] (Rec_prefix Event.right Set.univ Qf))
      (proc.Ext_pre_choice (({Event.left v} : Set Event) ∪ Set.range Event.right) fun y =>
        procIte (y = Event.left v) P (Qf (Function.invFun Event.right y))) := by
  rw [Rec_prefix_def]
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong (cspF_Act_prefix_step (a := Event.left v) (P := P))
      cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq cspF_Ext_choice_step ?_
  have himg : (({Event.left v} : Set Event)) ∪ Event.right '' (Set.univ : Set Nat)
      = (({Event.left v} : Set Event)) ∪ Set.range Event.right := by
    rw [Set.image_univ]
  refine cspF_Ext_pre_choice_cong himg (fun y hy => ?_)
  rcases hy with hy | ⟨m, rfl⟩
  · have hyv : y = Event.left v := hy
    subst hyv
    have hmem : Event.left v ∈ ({Event.left v} : Set Event) := Set.mem_singleton_iff.mpr rfl
    have hnot : ¬ (Event.left v ∈ ({Event.left v} : Set Event) ∧
        Event.left v ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    simp only [procIte_neg hnot, procIte_pos hmem, procIte_pos True.intro]
    exact cspF_reflex_eq_P
  · have hnot1 : ¬ (Event.right m ∈ ({Event.left v} : Set Event) ∧
        Event.right m ∈ Event.right '' (Set.univ : Set Nat)) := by simp
    have hnot2 : ¬ (Event.right m ∈ ({Event.left v} : Set Event)) := by simp
    have hnot3 : ¬ (Event.right m = Event.left v) := by simp
    simp only [procIte_neg hnot1, procIte_neg hnot2, procIte_neg hnot3]
    exact cspF_reflex_eq_P

private theorem renL_ChildL (cx : Nat × Nat) :
    eqFfix ((pChildL cx)[[fun_to_rel fL]])
      (proc.Ext_pre_choice ({Event.left (cx.1 / 2)} : Set Event)
        (fun _ => (pChild (fill (cx.1 / 2 + cx.2)))[[fun_to_rel fL]])) :=
  cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.ChildL cx)))
    (renL_Act_left (cx.1 / 2) _)

private theorem renL_ChildR (c : Nat) :
    eqFfix ((pChildR c)[[fun_to_rel fL]])
      (proc.Ext_pre_choice (Set.range Event.mid)
        (fun y => (pChild (fill (c + Function.invFun Event.mid y)))[[fun_to_rel fL]])) :=
  cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.ChildR c)))
    (renL_R (fun x => pChild (fill (c + x))))

private theorem renL_Child (c : Nat) :
    eqFfix ((pChild c)[[fun_to_rel fL]])
      (proc.Ext_pre_choice (({Event.left (c / 2)} : Set Event) ∪ Set.range Event.mid)
        (fun y => procIte (y = Event.left (c / 2))
          ((pChildR (c / 2))[[fun_to_rel fL]])
          ((pChildL (c, Function.invFun Event.mid y))[[fun_to_rel fL]]))) :=
  cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.Child c)))
    (renL_LR (c / 2) (pChildR (c / 2)) (fun x => pChildL (c, x)))

private theorem renR_LineSpec_both {s : List Att}
    (hchk : ChkLCR s) (hgL : guardL s) (hgR : guardR s) :
    eqFfix ((pLineSpec s)[[fun_to_rel fR]])
      (proc.Ext_pre_choice
        (({Event.mid (getNat (hd s) / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.mid (getNat (hd s) / 2))
          ((pLineSpec (nextL s))[[fun_to_rel fR]])
          ((pLineSpec (nextR (s, Function.invFun Event.right y)))[[fun_to_rel fR]]))) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.LineSpec s))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (IF_pos hchk _ _)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl
    (cspF_Ext_choice_cong (IF_pos hgL _ _) (IF_pos hgR _ _))) ?_
  exact renR_LR (getNat (hd s) / 2) (pLineSpec (nextL s)) (fun x => pLineSpec (nextR (s, x)))

private theorem renR_LineSpec_L {s : List Att}
    (hchk : ChkLCR s) (hgL : guardL s) (hgR : ¬ guardR s) :
    eqFfix ((pLineSpec s)[[fun_to_rel fR]])
      (proc.Ext_pre_choice ({Event.mid (getNat (hd s) / 2)} : Set Event)
        (fun _ => (pLineSpec (nextL s))[[fun_to_rel fR]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.LineSpec s))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (IF_pos hchk _ _)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl
    (cspF_Ext_choice_cong (IF_pos hgL _ _) (IF_neg hgR _ _))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_unit_r) ?_
  exact renR_L (getNat (hd s) / 2) (pLineSpec (nextL s))

private theorem stepBody_LR {s : List Att} (hgL : guardL s) (hgR : guardR s) :
    eqFfix (lineSpecStepBody s)
      (proc.Ext_pre_choice
        (({Event.left (getNat (hd s) / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.left (getNat (hd s) / 2))
          (LineSpec_to_Step (PN.LineSpec (nextL s)))
          (LineSpec_to_Step (PN.LineSpec (nextR (s, Function.invFun Event.right y)))))) := by
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong (IF_pos hgL _ _) (IF_pos hgR _ _)) ?_
  exact LR_normal (getNat (hd s) / 2) (LineSpec_to_Step (PN.LineSpec (nextL s)))
    (fun x => LineSpec_to_Step (PN.LineSpec (nextR (s, x))))

private theorem toStep_long {w : List Att} (hchk : ChkLCR w) (htl : tl w ≠ []) :
    eqFfix (LineSpec_to_Step (PN.LineSpec w)) (lineSpecSendStep w) := by
  refine cspF_trans_left_eq (IF_pos hchk _ _) ?_
  exact IF_neg htl _ _


private theorem stepBody_L {s : List Att} (hgL : guardL s) (hgR : ¬ guardR s) :
    eqFfix (lineSpecStepBody s)
      (proc.Ext_pre_choice ({Event.left (getNat (hd s) / 2)} : Set Event)
        (fun _ => LineSpec_to_Step (PN.LineSpec (nextL s)))) := by
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong (IF_pos hgL _ _) (IF_neg hgR _ _)) ?_
  refine cspF_trans_left_eq cspF_Ext_choice_unit_r ?_
  exact cspF_Act_prefix_step

/- ---------- set computations for the pipe expansion ---------- -/

private theorem left_sub_XL (v : Nat) : ({Event.left v} : Set Event) ⊆ XL := by
  rintro e he
  have : e = Event.left v := he
  subst this
  exact Or.inl ⟨v, rfl⟩

private theorem midR_sub_XR (w : Nat) :
    (({Event.mid w} : Set Event) ∪ Set.range Event.right) ⊆ XR := by
  rintro e (he | ⟨m, rfl⟩)
  · have : e = Event.mid w := he
    subst this
    exact Or.inl ⟨w, rfl⟩
  · exact Or.inr ⟨m, rfl⟩

private theorem mid_sub_XR (w : Nat) : ({Event.mid w} : Set Event) ⊆ XR := by
  rintro e he
  have : e = Event.mid w := he
  subst this
  exact Or.inl ⟨w, rfl⟩

private theorem sync_empty_LR (v w : Nat) :
    ({Event.left v} : Set Event) ∩ (({Event.mid w} : Set Event) ∪ Set.range Event.right) = ∅ := by
  ext e
  cases e <;> simp

private theorem sync_empty_L (v w : Nat) :
    ({Event.left v} : Set Event) ∩ ({Event.mid w} : Set Event) = ∅ := by
  ext e
  cases e <;> simp

private theorem expand_set_LR (v w : Nat) :
    ((({Event.left v} : Set Event) \ XR) ∪
      ((({Event.mid w} : Set Event) ∪ Set.range Event.right) \ XL))
      = (({Event.left v} : Set Event) ∪ Set.range Event.right) := by
  ext e
  cases e <;> simp

private theorem expand_set_L (v w : Nat) :
    ((({Event.left v} : Set Event) \ XR) ∪ (({Event.mid w} : Set Event) \ XL))
      = ({Event.left v} : Set Event) := by
  ext e
  cases e <;> simp

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


private theorem renR_LineSpec_R {s : List Att}
    (hchk : ChkLCR s) (hgL : ¬ guardL s) (hgR : guardR s) :
    eqFfix ((pLineSpec s)[[fun_to_rel fR]])
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => (pLineSpec (nextR (s, Function.invFun Event.right y)))[[fun_to_rel fR]])) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw (PN.LineSpec s))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (IF_pos hchk _ _)) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl
    (cspF_Ext_choice_cong (IF_neg hgL _ _) (IF_pos hgR _ _))) ?_
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl cspF_Ext_choice_unit_l) ?_
  exact renR_R (fun x => pLineSpec (nextR (s, x)))

private theorem right_sub_XR : Set.range Event.right ⊆ XR := by
  rintro e ⟨m, rfl⟩
  exact Or.inr ⟨m, rfl⟩

private theorem sync_empty_R (v : Nat) :
    ({Event.left v} : Set Event) ∩ Set.range Event.right = ∅ := by
  ext e
  cases e <;> simp

private theorem expand_set_R (v : Nat) :
    ((({Event.left v} : Set Event) \ XR) ∪ (Set.range Event.right \ XL))
      = (({Event.left v} : Set Event) ∪ Set.range Event.right) := by
  ext e
  cases e <;> simp


private theorem stepBody_R {s : List Att} (hgL : ¬ guardL s) (hgR : guardR s) :
    eqFfix (lineSpecStepBody s)
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => LineSpec_to_Step (PN.LineSpec (nextR (s, Function.invFun Event.right y))))) := by
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong (IF_neg hgL _ _) (IF_pos hgR _ _)) ?_
  refine cspF_trans_left_eq cspF_Ext_choice_unit_l ?_
  rw [Rec_prefix_def]
  refine cspF_Ext_pre_choice_cong (by rw [Set.image_univ]) (fun y hy => ?_)
  obtain ⟨m, rfl⟩ := hy
  rw [Function.leftInverse_invFun inj_event.2.1 m]
  exact cspF_reflex_eq_P

private theorem mid_sub_XL : Set.range Event.mid ⊆ XL := by
  rintro e ⟨m, rfl⟩
  exact Or.inr ⟨m, rfl⟩

private theorem sync_empty_mid_right :
    Set.range Event.mid ∩ Set.range Event.right = ∅ := by
  ext e
  cases e <;> simp

private theorem expand_set_mid_right :
    ((Set.range Event.mid \ XR) ∪ (Set.range Event.right \ XL)) = Set.range Event.right := by
  ext e
  cases e <;> simp

/-- Pushing one `AttR` through `nextR` is the same as normalising it with
    `toStbOne` afterwards. -/
private theorem nextR_AttR_AttR {n na m : Nat} {t : List Att} :
    nextR (Att.AttR n :: Att.AttR na :: t, m)
      = toStbOne (Att.AttR n :: nextR (Att.AttR na :: t, m)) := by
  cases t <;> simp [nextR, updateR, toStbOne, nextL, getNat]


private theorem leftmid_sub_XL (v : Nat) :
    (({Event.left v} : Set Event) ∪ Set.range Event.mid) ⊆ XL := by
  rintro e (he | ⟨m, rfl⟩)
  · have : e = Event.left v := he
    subst this
    exact Or.inl ⟨v, rfl⟩
  · exact Or.inr ⟨m, rfl⟩

private theorem sync_empty_leftmid_right (v : Nat) :
    (({Event.left v} : Set Event) ∪ Set.range Event.mid) ∩ Set.range Event.right = ∅ := by
  ext e
  cases e <;> simp

private theorem expand_set_leftmid_right (v : Nat) :
    (((({Event.left v} : Set Event) ∪ Set.range Event.mid) \ XR) ∪
      (Set.range Event.right \ XL))
      = (({Event.left v} : Set Event) ∪ Set.range Event.right) := by
  ext e
  cases e <;> simp

/-- Pushing one `AttC` through `nextR` is the same as normalising it with
    `toStbOne` afterwards. -/
private theorem nextR_AttC_AttR {n na m : Nat} {t : List Att} :
    nextR (Att.AttC n :: Att.AttR na :: t, m)
      = toStbOne (Att.AttC n :: nextR (Att.AttR na :: t, m)) := by
  cases t <;> simp [nextR, updateR, toStbOne, nextL, getNat]


private theorem sync_set_leftmid_midright (v w : Nat) :
    ((({Event.left v} : Set Event) ∪ Set.range Event.mid) ∩
      (({Event.mid w} : Set Event) ∪ Set.range Event.right))
      = ({Event.mid w} : Set Event) := by
  ext e
  cases e <;> simp

private theorem expand_set_leftmid_midright (v w : Nat) :
    (((({Event.left v} : Set Event) ∪ Set.range Event.mid) \ XR) ∪
      ((({Event.mid w} : Set Event) ∪ Set.range Event.right) \ XL))
      = (({Event.left v} : Set Event) ∪ Set.range Event.right) := by
  ext e
  cases e <;> simp

private theorem singleton_ne_empty (w : Nat) : ({Event.mid w} : Set Event) ≠ ∅ := by
  intro h
  have : Event.mid w ∈ ({Event.mid w} : Set Event) := rfl
  rw [h] at this
  exact this

/- --------------------- LineSpec_Step (lemmas) --------------------- -/

set_option maxHeartbeats 1000000 in
-- The pipe expansion has to unfold `Rec_prefix`, whose index set is
-- `Event.right '' Set.univ` and whose branch function goes through
-- `Function.invFun`; the defeq checks that drives are past the default budget.
theorem LineSpec_Step_ref1_AttL_AttL {t : List Att} {n x na xa : Nat} :
    ChkLCR t →
      lineSpecStepBody (Att.AttL (n, x) :: Att.AttL (na, xa) :: t) <=F
        (pChildL (n, x) <---> pLineSpec (Att.AttL (na, xa) :: t)) := by
  intro hchk
  have hchk2 : ChkLCR (Att.AttL (na, xa) :: t) := Or.inl ⟨⟨(na, xa), rfl⟩, hchk⟩
  have hchk1 : ChkLCR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t) :=
    Or.inl ⟨⟨(n, x), rfl⟩, hchk2⟩
  have hgL2 : guardL (Att.AttL (na, xa) :: t) := Or.inl ⟨na, xa, rfl⟩
  have hgL1 : guardL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t) := Or.inl ⟨n, x, rfl⟩
  have hP : eqFfix ((pChildL (n, x))[[fun_to_rel fL]])
      (proc.Ext_pre_choice ({Event.left (n / 2)} : Set Event)
        (fun _ => (pChild (fill (n / 2 + x)))[[fun_to_rel fL]])) :=
    renL_ChildL (n, x)
  have hnextL : nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t)
      = Att.AttL (fill (n / 2 + x), na / 2) :: nextL (Att.AttL (na, xa) :: t) := by
    simp [nextL]
  have hleft : refFfix
      (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t))))
      (Line (pChild (fill (n / 2 + x))) (pLineSpec (Att.AttL (na, xa) :: t))) := by
    have hchkL : ChkLCR (nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t)) :=
      (ChkLCR_nextL hgL1).mpr hchk1
    have htlL : tl (nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t)) ≠ [] := by
      rw [hnextL]
      exact nextL_not_nil
    refine cspF_rw_left_ref (toStep_long hchkL htlL) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttC (fill (n / 2 + x)) :: Att.AttL (na, xa) :: t) inj_stlist ?_ ?_
    · show toStbOne (Att.AttC (fill (n / 2 + x)) :: Att.AttL (na, xa) :: t)
        = nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t)
      rw [toStbOne_AttC_AttL, hnextL]
    · exact cspF_reflex_ref_P
  by_cases hgR2 : guardR (Att.AttL (na, xa) :: t)
  · have hgR1 : guardR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t) := by
      rw [guardR_AttL]
      exact hgR2
    have hnextR : ∀ m : Nat, nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t, m)
        = Att.AttL (n, x) :: nextR (Att.AttL (na, xa) :: t, m) := by
      intro m
      simp [nextR]
    have hright : ∀ m : Nat, refFfix
        (LineSpec_to_Step (PN.LineSpec (nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t, m))))
        (Line (pChildL (n, x)) (pLineSpec (nextR (Att.AttL (na, xa) :: t, m)))) := by
      intro m
      have hchkR : ChkLCR (nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t, m)) :=
        (ChkLCR_nextR hgR1).mpr hchk1
      have htlR : tl (nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t, m)) ≠ [] := by
        rw [hnextR m]
        exact nextR_not_nil
      refine cspF_rw_left_ref (toStep_long hchkR htlR) ?_
      refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
        (X := {u | toStbOne u = nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t, m)})
        (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
        (a := Att.AttL (n, x) :: nextR (Att.AttL (na, xa) :: t, m)) inj_stlist ?_ ?_
      · show toStbOne (Att.AttL (n, x) :: nextR (Att.AttL (na, xa) :: t, m))
          = nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t, m)
        rw [toStbOne_AttL, hnextR m]
      · exact cspF_reflex_ref_P
    have hQ : eqFfix ((pLineSpec (Att.AttL (na, xa) :: t))[[fun_to_rel fR]])
        (proc.Ext_pre_choice (({Event.mid (na / 2)} : Set Event) ∪ Set.range Event.right)
          (fun y => procIte (y = Event.mid (na / 2))
            ((pLineSpec (nextL (Att.AttL (na, xa) :: t)))[[fun_to_rel fR]])
            ((pLineSpec (nextR (Att.AttL (na, xa) :: t,
              Function.invFun Event.right y)))[[fun_to_rel fR]]))) :=
      renR_LineSpec_both hchk2 hgL2 hgR2
    refine cspF_rw_right_ref
      (Line_step_nosync hP hQ (left_sub_XL (n / 2)) (midR_sub_XR (na / 2))
        (sync_empty_LR (n / 2) (na / 2))) ?_
    have hL : eqFfix (lineSpecStepBody (Att.AttL (n, x) :: Att.AttL (na, xa) :: t))
        (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.right)
          (fun y => procIte (y = Event.left (n / 2))
            (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t))))
            (LineSpec_to_Step (PN.LineSpec
              (nextR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t,
                Function.invFun Event.right y)))))) :=
      stepBody_LR hgL1 hgR1
    refine cspF_rw_left_ref hL ?_
    refine cspF_Ext_pre_choice_mono (expand_set_LR (n / 2) (na / 2)).symm (fun y hy => ?_)
    rcases hy with ⟨hy, -⟩ | ⟨hy, hyXL⟩
    · have hyv : y = Event.left (n / 2) := hy
      subst hyv
      have hmem : Event.left (n / 2) ∈ ({Event.left (n / 2)} : Set Event) :=
        Set.mem_singleton_iff.mpr rfl
      simp only [procIte_pos hmem, procIte_pos True.intro]
      exact cspF_rw_right_ref (Line_fold_left hQ) hleft
    · rcases hy with hy | ⟨m, rfl⟩
      · have hyw : y = Event.mid (na / 2) := hy
        subst hyw
        exact absurd (Or.inr ⟨na / 2, rfl⟩) hyXL
      · have hn1 : ¬ (Event.right m = Event.left (n / 2)) := by simp
        have hn2 : ¬ (Event.right m ∈ ({Event.left (n / 2)} : Set Event)) := by simp
        have hn3 : ¬ (Event.right m = Event.mid (na / 2)) := by simp
        simp only [procIte_neg hn1, procIte_neg hn2, procIte_neg hn3]
        rw [Function.leftInverse_invFun inj_event.2.1 m]
        exact cspF_rw_right_ref (Line_fold_right hP) (hright m)
  · have hgR1 : ¬ guardR (Att.AttL (n, x) :: Att.AttL (na, xa) :: t) := by
      rw [guardR_AttL]
      exact hgR2
    have hQ : eqFfix ((pLineSpec (Att.AttL (na, xa) :: t))[[fun_to_rel fR]])
        (proc.Ext_pre_choice ({Event.mid (na / 2)} : Set Event)
          (fun _ => (pLineSpec (nextL (Att.AttL (na, xa) :: t)))[[fun_to_rel fR]])) :=
      renR_LineSpec_L hchk2 hgL2 hgR2
    refine cspF_rw_right_ref
      (Line_step_nosync hP hQ (left_sub_XL (n / 2)) (mid_sub_XR (na / 2))
        (sync_empty_L (n / 2) (na / 2))) ?_
    have hL : eqFfix (lineSpecStepBody (Att.AttL (n, x) :: Att.AttL (na, xa) :: t))
        (proc.Ext_pre_choice ({Event.left (n / 2)} : Set Event)
          (fun _ => LineSpec_to_Step (PN.LineSpec
            (nextL (Att.AttL (n, x) :: Att.AttL (na, xa) :: t))))) :=
      stepBody_L hgL1 hgR1
    refine cspF_rw_left_ref hL ?_
    refine cspF_Ext_pre_choice_mono (expand_set_L (n / 2) (na / 2)).symm (fun y hy => ?_)
    rcases hy with ⟨hy, -⟩ | ⟨hy, hyXL⟩
    · have hyv : y = Event.left (n / 2) := hy
      subst hyv
      have hmem : Event.left (n / 2) ∈ ({Event.left (n / 2)} : Set Event) :=
        Set.mem_singleton_iff.mpr rfl
      simp only [procIte_pos hmem]
      exact cspF_rw_right_ref (Line_fold_left hQ) hleft
    · have hyw : y = Event.mid (na / 2) := hy
      subst hyw
      exact absurd (Or.inr ⟨na / 2, rfl⟩) hyXL

set_option maxHeartbeats 1000000 in
-- The pipe expansion has to unfold `Rec_prefix`, whose index set is
-- `Event.right '' Set.univ` and whose branch function goes through
-- `Function.invFun`; the defeq checks that drives are past the default budget.
theorem LineSpec_Step_ref1_AttL_AttC {t : List Att} {n x na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttL (n, x) :: Att.AttC na :: t) <=F
        (pChildL (n, x) <---> pLineSpec (Att.AttC na :: t)) := by
  intro hchk
  have hchk2 : ChkLCR (Att.AttC na :: t) := Or.inr (Or.inl ⟨⟨na, rfl⟩, hchk⟩)
  have hchk1 : ChkLCR (Att.AttL (n, x) :: Att.AttC na :: t) :=
    Or.inl ⟨⟨(n, x), rfl⟩, hchk2⟩
  have hgL2 : guardL (Att.AttC na :: t) := Or.inr ⟨na, rfl⟩
  have hgR2 : guardR (Att.AttC na :: t) := ChkR_guardR_AttC na hchk
  have hgL1 : guardL (Att.AttL (n, x) :: Att.AttC na :: t) := Or.inl ⟨n, x, rfl⟩
  have hgR1 : guardR (Att.AttL (n, x) :: Att.AttC na :: t) := by
    rw [guardR_AttL]
    exact hgR2
  have hP : eqFfix ((pChildL (n, x))[[fun_to_rel fL]])
      (proc.Ext_pre_choice ({Event.left (n / 2)} : Set Event)
        (fun _ => (pChild (fill (n / 2 + x)))[[fun_to_rel fL]])) :=
    renL_ChildL (n, x)
  have hnextL : nextL (Att.AttL (n, x) :: Att.AttC na :: t)
      = Att.AttL (fill (n / 2 + x), na / 2) :: Att.AttR (na / 2) :: t := by
    simp [nextL]
  have hleft : refFfix
      (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttL (n, x) :: Att.AttC na :: t))))
      (Line (pChild (fill (n / 2 + x))) (pLineSpec (Att.AttC na :: t))) := by
    have hchkL : ChkLCR (nextL (Att.AttL (n, x) :: Att.AttC na :: t)) :=
      (ChkLCR_nextL hgL1).mpr hchk1
    have htlL : tl (nextL (Att.AttL (n, x) :: Att.AttC na :: t)) ≠ [] := by
      rw [hnextL]
      exact List.cons_ne_nil _ _
    refine cspF_rw_left_ref (toStep_long hchkL htlL) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextL (Att.AttL (n, x) :: Att.AttC na :: t)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttC (fill (n / 2 + x)) :: Att.AttC na :: t) inj_stlist ?_ ?_
    · show toStbOne (Att.AttC (fill (n / 2 + x)) :: Att.AttC na :: t)
        = nextL (Att.AttL (n, x) :: Att.AttC na :: t)
      rw [toStbOne_AttC_AttC', nextL_AttC_cons, hnextL]
    · exact cspF_reflex_ref_P
  have hnextR : ∀ m : Nat, nextR (Att.AttL (n, x) :: Att.AttC na :: t, m)
      = Att.AttL (n, x) :: nextR (Att.AttC na :: t, m) := fun m =>
    guardR_nextR_AttL hgR2
  have hright : ∀ m : Nat, refFfix
      (LineSpec_to_Step (PN.LineSpec (nextR (Att.AttL (n, x) :: Att.AttC na :: t, m))))
      (Line (pChildL (n, x)) (pLineSpec (nextR (Att.AttC na :: t, m)))) := by
    intro m
    have hchkR : ChkLCR (nextR (Att.AttL (n, x) :: Att.AttC na :: t, m)) :=
      (ChkLCR_nextR hgR1).mpr hchk1
    have htlR : tl (nextR (Att.AttL (n, x) :: Att.AttC na :: t, m)) ≠ [] := by
      rw [hnextR m]
      exact nextR_not_nil
    refine cspF_rw_left_ref (toStep_long hchkR htlR) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextR (Att.AttL (n, x) :: Att.AttC na :: t, m)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttL (n, x) :: nextR (Att.AttC na :: t, m)) inj_stlist ?_ ?_
    · show toStbOne (Att.AttL (n, x) :: nextR (Att.AttC na :: t, m))
        = nextR (Att.AttL (n, x) :: Att.AttC na :: t, m)
      rw [toStbOne_AttL, hnextR m]
    · exact cspF_reflex_ref_P
  have hQ : eqFfix ((pLineSpec (Att.AttC na :: t))[[fun_to_rel fR]])
      (proc.Ext_pre_choice (({Event.mid (na / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.mid (na / 2))
          ((pLineSpec (nextL (Att.AttC na :: t)))[[fun_to_rel fR]])
          ((pLineSpec (nextR (Att.AttC na :: t,
            Function.invFun Event.right y)))[[fun_to_rel fR]]))) :=
    renR_LineSpec_both hchk2 hgL2 hgR2
  refine cspF_rw_right_ref
    (Line_step_nosync hP hQ (left_sub_XL (n / 2)) (midR_sub_XR (na / 2))
      (sync_empty_LR (n / 2) (na / 2))) ?_
  have hL : eqFfix (lineSpecStepBody (Att.AttL (n, x) :: Att.AttC na :: t))
      (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.left (n / 2))
          (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttL (n, x) :: Att.AttC na :: t))))
          (LineSpec_to_Step (PN.LineSpec
            (nextR (Att.AttL (n, x) :: Att.AttC na :: t,
              Function.invFun Event.right y)))))) :=
    stepBody_LR hgL1 hgR1
  refine cspF_rw_left_ref hL ?_
  refine cspF_Ext_pre_choice_mono (expand_set_LR (n / 2) (na / 2)).symm (fun y hy => ?_)
  rcases hy with ⟨hy, -⟩ | ⟨hy, hyXL⟩
  · have hyv : y = Event.left (n / 2) := hy
    subst hyv
    have hmem : Event.left (n / 2) ∈ ({Event.left (n / 2)} : Set Event) :=
      Set.mem_singleton_iff.mpr rfl
    simp only [procIte_pos hmem, procIte_pos True.intro]
    exact cspF_rw_right_ref (Line_fold_left hQ) hleft
  · rcases hy with hy | ⟨m, rfl⟩
    · have hyw : y = Event.mid (na / 2) := hy
      subst hyw
      exact absurd (Or.inr ⟨na / 2, rfl⟩) hyXL
    · have hn1 : ¬ (Event.right m = Event.left (n / 2)) := by simp
      have hn2 : ¬ (Event.right m ∈ ({Event.left (n / 2)} : Set Event)) := by simp
      have hn3 : ¬ (Event.right m = Event.mid (na / 2)) := by simp
      simp only [procIte_neg hn1, procIte_neg hn2, procIte_neg hn3]
      rw [Function.leftInverse_invFun inj_event.2.1 m]
      exact cspF_rw_right_ref (Line_fold_right hP) (hright m)

set_option maxHeartbeats 1000000 in
-- The pipe expansion has to unfold `Rec_prefix`, whose index set is
-- `Event.right '' Set.univ` and whose branch function goes through
-- `Function.invFun`; the defeq checks that drives are past the default budget.
theorem LineSpec_Step_ref1_AttL_AttR {t : List Att} {n x na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttL (n, x) :: Att.AttR na :: t) <=F
        (pChildL (n, x) <---> pLineSpec (Att.AttR na :: t)) := by
  intro hchk
  have hchk2 : ChkLCR (Att.AttR na :: t) := Or.inr (Or.inr ⟨⟨na, rfl⟩, hchk⟩)
  have hchk1 : ChkLCR (Att.AttL (n, x) :: Att.AttR na :: t) :=
    Or.inl ⟨⟨(n, x), rfl⟩, hchk2⟩
  have hgL2 : ¬ guardL (Att.AttR na :: t) := by
    rintro (⟨m, z, hm⟩ | ⟨m, hm⟩) <;> cases hm
  have hgR2 : guardR (Att.AttR na :: t) := ChkR_guardR_AttR na hchk
  have hgL1 : guardL (Att.AttL (n, x) :: Att.AttR na :: t) := Or.inl ⟨n, x, rfl⟩
  have hgR1 : guardR (Att.AttL (n, x) :: Att.AttR na :: t) := by
    rw [guardR_AttL]
    exact hgR2
  have hP : eqFfix ((pChildL (n, x))[[fun_to_rel fL]])
      (proc.Ext_pre_choice ({Event.left (n / 2)} : Set Event)
        (fun _ => (pChild (fill (n / 2 + x)))[[fun_to_rel fL]])) :=
    renL_ChildL (n, x)
  have hnextL : nextL (Att.AttL (n, x) :: Att.AttR na :: t)
      = Att.AttC (fill (n / 2 + x)) :: Att.AttR na :: t := by
    simp [nextL]
  have hleft : refFfix
      (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttL (n, x) :: Att.AttR na :: t))))
      (Line (pChild (fill (n / 2 + x))) (pLineSpec (Att.AttR na :: t))) := by
    have hchkL : ChkLCR (nextL (Att.AttL (n, x) :: Att.AttR na :: t)) :=
      (ChkLCR_nextL hgL1).mpr hchk1
    have htlL : tl (nextL (Att.AttL (n, x) :: Att.AttR na :: t)) ≠ [] := by
      rw [hnextL]
      exact List.cons_ne_nil _ _
    refine cspF_rw_left_ref (toStep_long hchkL htlL) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextL (Att.AttL (n, x) :: Att.AttR na :: t)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttC (fill (n / 2 + x)) :: Att.AttR na :: t) inj_stlist ?_ ?_
    · show toStbOne (Att.AttC (fill (n / 2 + x)) :: Att.AttR na :: t)
        = nextL (Att.AttL (n, x) :: Att.AttR na :: t)
      rw [toStbOne_AttC_AttR, hnextL]
    · exact cspF_reflex_ref_P
  have hnextR : ∀ m : Nat, nextR (Att.AttL (n, x) :: Att.AttR na :: t, m)
      = Att.AttL (n, x) :: nextR (Att.AttR na :: t, m) := fun m =>
    guardR_nextR_AttL hgR2
  have hright : ∀ m : Nat, refFfix
      (LineSpec_to_Step (PN.LineSpec (nextR (Att.AttL (n, x) :: Att.AttR na :: t, m))))
      (Line (pChildL (n, x)) (pLineSpec (nextR (Att.AttR na :: t, m)))) := by
    intro m
    have hchkR : ChkLCR (nextR (Att.AttL (n, x) :: Att.AttR na :: t, m)) :=
      (ChkLCR_nextR hgR1).mpr hchk1
    have htlR : tl (nextR (Att.AttL (n, x) :: Att.AttR na :: t, m)) ≠ [] := by
      rw [hnextR m]
      exact nextR_not_nil
    refine cspF_rw_left_ref (toStep_long hchkR htlR) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextR (Att.AttL (n, x) :: Att.AttR na :: t, m)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttL (n, x) :: nextR (Att.AttR na :: t, m)) inj_stlist ?_ ?_
    · show toStbOne (Att.AttL (n, x) :: nextR (Att.AttR na :: t, m))
        = nextR (Att.AttL (n, x) :: Att.AttR na :: t, m)
      rw [toStbOne_AttL, hnextR m]
    · exact cspF_reflex_ref_P
  have hQ : eqFfix ((pLineSpec (Att.AttR na :: t))[[fun_to_rel fR]])
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => (pLineSpec (nextR (Att.AttR na :: t,
          Function.invFun Event.right y)))[[fun_to_rel fR]])) :=
    renR_LineSpec_R hchk2 hgL2 hgR2
  refine cspF_rw_right_ref
    (Line_step_nosync hP hQ (left_sub_XL (n / 2)) right_sub_XR (sync_empty_R (n / 2))) ?_
  have hL : eqFfix (lineSpecStepBody (Att.AttL (n, x) :: Att.AttR na :: t))
      (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.left (n / 2))
          (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttL (n, x) :: Att.AttR na :: t))))
          (LineSpec_to_Step (PN.LineSpec
            (nextR (Att.AttL (n, x) :: Att.AttR na :: t,
              Function.invFun Event.right y)))))) :=
    stepBody_LR hgL1 hgR1
  refine cspF_rw_left_ref hL ?_
  refine cspF_Ext_pre_choice_mono (expand_set_R (n / 2)).symm (fun y hy => ?_)
  rcases hy with ⟨hy, -⟩ | ⟨⟨m, rfl⟩, -⟩
  · have hyv : y = Event.left (n / 2) := hy
    subst hyv
    have hmem : Event.left (n / 2) ∈ ({Event.left (n / 2)} : Set Event) :=
      Set.mem_singleton_iff.mpr rfl
    simp only [procIte_pos hmem, procIte_pos True.intro]
    exact cspF_rw_right_ref (Line_fold_left hQ) hleft
  · have hn1 : ¬ (Event.right m = Event.left (n / 2)) := by simp
    have hn2 : ¬ (Event.right m ∈ ({Event.left (n / 2)} : Set Event)) := by simp
    simp only [procIte_neg hn1, procIte_neg hn2]
    rw [Function.leftInverse_invFun inj_event.2.1 m]
    exact cspF_rw_right_ref (Line_fold_right hP) (hright m)

set_option maxHeartbeats 1000000 in
-- The pipe expansion has to unfold `Rec_prefix`, whose index set is
-- `Event.right '' Set.univ` and whose branch function goes through
-- `Function.invFun`; the defeq checks that drives are past the default budget.
theorem LineSpec_Step_ref1_AttC_AttC {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t) <=F
        (pChild n <---> pLineSpec (Att.AttC na :: t)) := by
  intro hchk
  have hR2 : ChkR (Att.AttR (na / 2) :: t) := ⟨⟨na / 2, rfl⟩, hchk⟩
  have hchk2 : ChkLCR (Att.AttC na :: t) := Or.inr (Or.inl ⟨⟨na, rfl⟩, hchk⟩)
  have hgL2 : guardL (Att.AttC na :: t) := Or.inr ⟨na, rfl⟩
  have hgR2 : guardR (Att.AttC na :: t) := ChkR_guardR_AttC na hchk
  have hchk1 : ChkLCR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t) :=
    Or.inl ⟨⟨(n, na / 2), rfl⟩, Or.inr (Or.inr hR2)⟩
  have hgL1 : guardL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t) :=
    Or.inl ⟨n, na / 2, rfl⟩
  have hgR1 : guardR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t) := by
    rw [guardR_AttL]
    exact ChkR_guardR_AttR (na / 2) hchk
  have hnextL2 : nextL (Att.AttC na :: t) = Att.AttR (na / 2) :: t := nextL_AttC_cons na t
  have hP : eqFfix ((pChild n)[[fun_to_rel fL]])
      (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.mid)
        (fun y => procIte (y = Event.left (n / 2))
          ((pChildR (n / 2))[[fun_to_rel fL]])
          ((pChildL (n, Function.invFun Event.mid y))[[fun_to_rel fL]]))) :=
    renL_Child n
  have hQ : eqFfix ((pLineSpec (Att.AttC na :: t))[[fun_to_rel fR]])
      (proc.Ext_pre_choice (({Event.mid (na / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.mid (na / 2))
          ((pLineSpec (nextL (Att.AttC na :: t)))[[fun_to_rel fR]])
          ((pLineSpec (nextR (Att.AttC na :: t,
            Function.invFun Event.right y)))[[fun_to_rel fR]]))) :=
    renR_LineSpec_both hchk2 hgL2 hgR2
  -- the visible `left` branch
  have hnextL1 : nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t)
      = Att.AttC (fill (n / 2 + na / 2)) :: Att.AttR (na / 2) :: t := by
    simp [nextL]
  have hleft : refFfix
      (LineSpec_to_Step (PN.LineSpec
        (nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t))))
      (Line (pChildR (n / 2)) (pLineSpec (Att.AttC na :: t))) := by
    have hchkL : ChkLCR (nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t)) :=
      (ChkLCR_nextL hgL1).mpr hchk1
    have htlL : tl (nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t)) ≠ [] := by
      rw [hnextL1]
      exact List.cons_ne_nil _ _
    refine cspF_rw_left_ref (toStep_long hchkL htlL) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttR (n / 2) :: Att.AttC na :: t) inj_stlist ?_ ?_
    · show toStbOne (Att.AttR (n / 2) :: Att.AttC na :: t)
        = nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t)
      rw [toStbOne_AttR_AttC, nextL_AttC_cons, hnextL1]
    · exact cspF_reflex_ref_P
  -- the visible `right` branches
  have hnextR1 : ∀ m : Nat, nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t, m)
      = Att.AttL (n, na / 2) :: nextR (Att.AttR (na / 2) :: t, m) := fun m =>
    guardR_nextR_AttL (ChkR_guardR_AttR (na / 2) hchk)
  have hright : ∀ m : Nat, refFfix
      (LineSpec_to_Step (PN.LineSpec
        (nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t, m))))
      (Line (pChild n) (pLineSpec (nextR (Att.AttC na :: t, m)))) := by
    intro m
    obtain ⟨g, w, hgw⟩ : ∃ g w, nextR (Att.AttC na :: t, m) = Att.AttL (na, g) :: w :=
      hd_nextR_AttC_EX
    have horder : nextL (nextR (Att.AttC na :: t, m))
        = nextR (Att.AttR (na / 2) :: t, m) := by
      rw [nextL_nextR_order (Or.inr ⟨hgL2, hgR2, hchk2⟩), hnextL2]
    have hstb : toStbOne (Att.AttC n :: nextR (Att.AttC na :: t, m))
        = nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t, m) := by
      rw [hgw, toStbOne_AttC_AttL, ← hgw, horder, hnextR1 m]
    have hchkR : ChkLCR (nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t, m)) :=
      (ChkLCR_nextR hgR1).mpr hchk1
    have htlR : tl (nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t, m)) ≠ [] := by
      rw [hnextR1 m]
      exact nextR_not_nil
    refine cspF_rw_left_ref (toStep_long hchkR htlR) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t, m)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttC n :: nextR (Att.AttC na :: t, m)) inj_stlist hstb ?_
    exact cspF_reflex_ref_P
  refine cspF_rw_right_ref
    (Line_step_sync hP hQ (leftmid_sub_XL (n / 2)) (midR_sub_XR (na / 2))
      (by rw [sync_set_leftmid_midright]; exact singleton_ne_empty (na / 2))) ?_
  rw [expand_set_leftmid_midright (n / 2) (na / 2), sync_set_leftmid_midright (n / 2) (na / 2)]
  have hL : eqFfix (lineSpecStepBody (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t))
      (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.left (n / 2))
          (LineSpec_to_Step (PN.LineSpec
            (nextL (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t))))
          (LineSpec_to_Step (PN.LineSpec
            (nextR (Att.AttL (n, na / 2) :: Att.AttR (na / 2) :: t,
              Function.invFun Event.right y)))))) :=
    stepBody_LR hgL1 hgR1
  refine cspF_rw_left_ref hL ?_
  refine cspF_Timeout_right_subset (subset_refl _) (fun y hy => ?_) ?_
  · rcases hy with hy | ⟨m, rfl⟩
    · have hyv : y = Event.left (n / 2) := hy
      subst hyv
      have hmem : Event.left (n / 2) ∈
          (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.mid) :=
        Or.inl (Set.mem_singleton_iff.mpr rfl)
      simp only [procIte_pos hmem, procIte_pos True.intro]
      exact cspF_rw_right_ref (Line_fold_left hQ) hleft
    · have hn1 : ¬ (Event.right m = Event.left (n / 2)) := by simp
      have hn2 : ¬ (Event.right m ∈
          (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.mid)) := by simp
      have hn3 : ¬ (Event.right m = Event.mid (na / 2)) := by simp
      simp only [procIte_neg hn1, procIte_neg hn2, procIte_neg hn3]
      rw [Function.leftInverse_invFun inj_event.2.1 m]
      exact cspF_rw_right_ref (Line_fold_right hP) (hright m)
  · refine cspF_Rep_int_choice_com_right (fun a ha => ?_)
    have hav : a = Event.mid (na / 2) := ha
    subst hav
    have hm1 : ¬ (Event.mid (na / 2) = Event.left (n / 2)) := by simp
    simp only [procIte_neg hm1, procIte_pos True.intro]
    rw [Function.leftInverse_invFun inj_event.2.2 (na / 2), hnextL2]
    refine cspF_rw_left_ref (cspF_sym hL) ?_
    exact cspF_rw_right_ref Line_fold_both (LineSpec_Step_ref1_AttL_AttR hchk)

axiom LineSpec_Step_ref1_AttC_AttL {t : List Att} {na n x : Nat} :
    ChkLCR t →
      lineSpecStepBody (Att.AttL (na, n / 2) :: nextL (Att.AttL (n, x) :: t)) <=F
        (pChild na <---> pLineSpec (Att.AttL (n, x) :: t))

axiom LineSpec_Step_ref1_AttR_AttL {t : List Att} {na n x : Nat} :
    ChkLCR (toStbOne (Att.AttR na :: Att.AttL (n, x) :: t)) →
      lineSpecStepBody (toStbOne (Att.AttR na :: Att.AttL (n, x) :: t)) <=F
        (pChildR na <---> pLineSpec (Att.AttL (n, x) :: t))

set_option maxHeartbeats 1000000 in
-- The pipe expansion has to unfold `Rec_prefix`, whose index set is
-- `Event.right '' Set.univ` and whose branch function goes through
-- `Function.invFun`; the defeq checks that drives are past the default budget.
theorem LineSpec_Step_ref1_AttC_AttR {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttC n :: Att.AttR na :: t) <=F
        (pChild n <---> pLineSpec (Att.AttR na :: t)) := by
  intro hchk
  have hR2 : ChkR (Att.AttR na :: t) := ⟨⟨na, rfl⟩, hchk⟩
  have hchk2 : ChkLCR (Att.AttR na :: t) := Or.inr (Or.inr hR2)
  have hchk1 : ChkLCR (Att.AttC n :: Att.AttR na :: t) := Or.inr (Or.inl ⟨⟨n, rfl⟩, hR2⟩)
  have hgL2 : ¬ guardL (Att.AttR na :: t) := by
    rintro (⟨m, z, hm⟩ | ⟨m, hm⟩) <;> cases hm
  have hgR2 : guardR (Att.AttR na :: t) := ChkR_guardR_AttR na hchk
  have hgL1 : guardL (Att.AttC n :: Att.AttR na :: t) := Or.inr ⟨n, rfl⟩
  have hgR1 : guardR (Att.AttC n :: Att.AttR na :: t) := ChkR_guardR_AttC n hR2
  have hP : eqFfix ((pChild n)[[fun_to_rel fL]])
      (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.mid)
        (fun y => procIte (y = Event.left (n / 2))
          ((pChildR (n / 2))[[fun_to_rel fL]])
          ((pChildL (n, Function.invFun Event.mid y))[[fun_to_rel fL]]))) :=
    renL_Child n
  have hQ : eqFfix ((pLineSpec (Att.AttR na :: t))[[fun_to_rel fR]])
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => (pLineSpec (nextR (Att.AttR na :: t,
          Function.invFun Event.right y)))[[fun_to_rel fR]])) :=
    renR_LineSpec_R hchk2 hgL2 hgR2
  have hnextL : nextL (Att.AttC n :: Att.AttR na :: t)
      = Att.AttR (n / 2) :: Att.AttR na :: t := nextL_AttC_cons n _
  have hleft : refFfix
      (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttC n :: Att.AttR na :: t))))
      (Line (pChildR (n / 2)) (pLineSpec (Att.AttR na :: t))) := by
    have hchkL : ChkLCR (nextL (Att.AttC n :: Att.AttR na :: t)) :=
      (ChkLCR_nextL hgL1).mpr hchk1
    have htlL : tl (nextL (Att.AttC n :: Att.AttR na :: t)) ≠ [] := by
      rw [hnextL]
      exact List.cons_ne_nil _ _
    refine cspF_rw_left_ref (toStep_long hchkL htlL) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextL (Att.AttC n :: Att.AttR na :: t)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttR (n / 2) :: Att.AttR na :: t) inj_stlist ?_ ?_
    · show toStbOne (Att.AttR (n / 2) :: Att.AttR na :: t)
        = nextL (Att.AttC n :: Att.AttR na :: t)
      rw [toStbOne_AttR_AttR, hnextL]
    · exact cspF_reflex_ref_P
  have hright : ∀ m : Nat, refFfix
      (LineSpec_to_Step (PN.LineSpec (nextR (Att.AttC n :: Att.AttR na :: t, m))))
      (Line (pChild n) (pLineSpec (nextR (Att.AttR na :: t, m)))) := by
    intro m
    obtain ⟨v, w, hvw⟩ : ∃ v w, nextR (Att.AttR na :: t, m) = Att.AttC v :: w := by
      cases t with
      | nil => exact ⟨fill (na + m), [], by simp [nextR]⟩
      | cons b u =>
          exact ⟨fill (na + getNat (hd (updateR (b :: u, m)))), updateR (b :: u, m),
            by simp [nextR]⟩
    have hstb : toStbOne (Att.AttC n :: nextR (Att.AttR na :: t, m))
        = nextR (Att.AttC n :: Att.AttR na :: t, m) := nextR_AttC_AttR.symm
    have hchkR : ChkLCR (nextR (Att.AttC n :: Att.AttR na :: t, m)) :=
      (ChkLCR_nextR hgR1).mpr hchk1
    have htlR : tl (nextR (Att.AttC n :: Att.AttR na :: t, m)) ≠ [] := by
      rw [← hstb, hvw, toStbOne_AttC_AttC', nextL_AttC_cons]
      exact List.cons_ne_nil _ _
    refine cspF_rw_left_ref (toStep_long hchkR htlR) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextR (Att.AttC n :: Att.AttR na :: t, m)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttC n :: nextR (Att.AttR na :: t, m)) inj_stlist hstb ?_
    exact cspF_reflex_ref_P
  refine cspF_rw_right_ref
    (Line_step_nosync hP hQ (leftmid_sub_XL (n / 2)) right_sub_XR
      (sync_empty_leftmid_right (n / 2))) ?_
  have hL : eqFfix (lineSpecStepBody (Att.AttC n :: Att.AttR na :: t))
      (proc.Ext_pre_choice (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.right)
        (fun y => procIte (y = Event.left (n / 2))
          (LineSpec_to_Step (PN.LineSpec (nextL (Att.AttC n :: Att.AttR na :: t))))
          (LineSpec_to_Step (PN.LineSpec
            (nextR (Att.AttC n :: Att.AttR na :: t,
              Function.invFun Event.right y)))))) :=
    stepBody_LR hgL1 hgR1
  refine cspF_rw_left_ref hL ?_
  refine cspF_Ext_pre_choice_mono (expand_set_leftmid_right (n / 2)).symm (fun y hy => ?_)
  rcases hy with hy | hy
  · obtain ⟨hyA, hyXR⟩ := hy
    rcases hyA with hyl | ⟨m, rfl⟩
    · have hyv : y = Event.left (n / 2) := hyl
      subst hyv
      have hmem : Event.left (n / 2) ∈
          (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.mid) :=
        Or.inl (Set.mem_singleton_iff.mpr rfl)
      simp only [procIte_pos hmem, procIte_pos True.intro]
      exact cspF_rw_right_ref (Line_fold_left hQ) hleft
    · exact absurd (Or.inl ⟨m, rfl⟩ : Event.mid m ∈ XR) hyXR
  · obtain ⟨⟨m, rfl⟩, -⟩ := hy
    have hn1 : ¬ (Event.right m = Event.left (n / 2)) := by simp
    have hn2 : ¬ (Event.right m ∈
        (({Event.left (n / 2)} : Set Event) ∪ Set.range Event.mid)) := by simp
    simp only [procIte_neg hn1, procIte_neg hn2]
    rw [Function.leftInverse_invFun inj_event.2.1 m]
    exact cspF_rw_right_ref (Line_fold_right hP) (hright m)

axiom LineSpec_Step_ref1_AttR_AttC {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttC (fill (n + na / 2)) :: Att.AttR (na / 2) :: t) <=F
        (pChildR n <---> pLineSpec (Att.AttC na :: t))

set_option maxHeartbeats 1000000 in
-- The pipe expansion has to unfold `Rec_prefix`, whose index set is
-- `Event.right '' Set.univ` and whose branch function goes through
-- `Function.invFun`; the defeq checks that drives are past the default budget.
theorem LineSpec_Step_ref1_AttR_AttR {t : List Att} {n na : Nat} :
    ChkR t →
      lineSpecStepBody (Att.AttR n :: Att.AttR na :: t) <=F
        (pChildR n <---> pLineSpec (Att.AttR na :: t)) := by
  intro hchk
  have hR2 : ChkR (Att.AttR na :: t) := ⟨⟨na, rfl⟩, hchk⟩
  have hchk2 : ChkLCR (Att.AttR na :: t) := Or.inr (Or.inr hR2)
  have hchk1 : ChkLCR (Att.AttR n :: Att.AttR na :: t) :=
    Or.inr (Or.inr ⟨⟨n, rfl⟩, hR2⟩)
  have hgL2 : ¬ guardL (Att.AttR na :: t) := by
    rintro (⟨m, z, hm⟩ | ⟨m, hm⟩) <;> cases hm
  have hgL1 : ¬ guardL (Att.AttR n :: Att.AttR na :: t) := by
    rintro (⟨m, z, hm⟩ | ⟨m, hm⟩) <;> cases hm
  have hgR2 : guardR (Att.AttR na :: t) := ChkR_guardR_AttR na hchk
  have hgR1 : guardR (Att.AttR n :: Att.AttR na :: t) := ChkR_guardR_AttR n hR2
  have hP : eqFfix ((pChildR n)[[fun_to_rel fL]])
      (proc.Ext_pre_choice (Set.range Event.mid)
        (fun y => (pChild (fill (n + Function.invFun Event.mid y)))[[fun_to_rel fL]])) :=
    renL_ChildR n
  have hQ : eqFfix ((pLineSpec (Att.AttR na :: t))[[fun_to_rel fR]])
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => (pLineSpec (nextR (Att.AttR na :: t,
          Function.invFun Event.right y)))[[fun_to_rel fR]])) :=
    renR_LineSpec_R hchk2 hgL2 hgR2
  have hright : ∀ m : Nat, refFfix
      (LineSpec_to_Step (PN.LineSpec (nextR (Att.AttR n :: Att.AttR na :: t, m))))
      (Line (pChildR n) (pLineSpec (nextR (Att.AttR na :: t, m)))) := by
    intro m
    obtain ⟨v, w, hvw⟩ : ∃ v w, nextR (Att.AttR na :: t, m) = Att.AttC v :: w := by
      cases t with
      | nil => exact ⟨fill (na + m), [], by simp [nextR]⟩
      | cons b u =>
          exact ⟨fill (na + getNat (hd (updateR (b :: u, m)))), updateR (b :: u, m),
            by simp [nextR]⟩
    have hstb : toStbOne (Att.AttR n :: nextR (Att.AttR na :: t, m))
        = nextR (Att.AttR n :: Att.AttR na :: t, m) := nextR_AttR_AttR.symm
    have hchkR : ChkLCR (nextR (Att.AttR n :: Att.AttR na :: t, m)) :=
      (ChkLCR_nextR hgR1).mpr hchk1
    have htlR : tl (nextR (Att.AttR n :: Att.AttR na :: t, m)) ≠ [] := by
      rw [← hstb, hvw, toStbOne_AttR_AttC, nextL_AttC_cons]
      exact List.cons_ne_nil _ _
    refine cspF_rw_left_ref (toStep_long hchkR htlR) ?_
    refine cspF_Rep_int_choice_f_left_x (f := Event.stlist)
      (X := {u | toStbOne u = nextR (Att.AttR n :: Att.AttR na :: t, m)})
      (Pf := fun u => ChildAtt (hd u) <---> pLineSpec (tl u))
      (a := Att.AttR n :: nextR (Att.AttR na :: t, m)) inj_stlist hstb ?_
    exact cspF_reflex_ref_P
  refine cspF_rw_right_ref
    (Line_step_nosync hP hQ mid_sub_XL right_sub_XR sync_empty_mid_right) ?_
  have hL : eqFfix (lineSpecStepBody (Att.AttR n :: Att.AttR na :: t))
      (proc.Ext_pre_choice (Set.range Event.right)
        (fun y => LineSpec_to_Step (PN.LineSpec
          (nextR (Att.AttR n :: Att.AttR na :: t, Function.invFun Event.right y))))) :=
    stepBody_R hgL1 hgR1
  refine cspF_rw_left_ref hL ?_
  refine cspF_Ext_pre_choice_mono expand_set_mid_right.symm (fun y hy => ?_)
  rcases hy with ⟨⟨m, rfl⟩, hyXR⟩ | ⟨⟨m, rfl⟩, -⟩
  · exact absurd (Or.inl ⟨m, rfl⟩) hyXR
  · have hn2 : ¬ (Event.right m ∈ Set.range Event.mid) := by simp
    simp only [procIte_neg hn2]
    rw [Function.leftInverse_invFun inj_event.2.1 m]
    exact cspF_rw_right_ref (Line_fold_right hP) (hright m)

/- -------------------------- LineSpec_Step -------------------------- -/

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
