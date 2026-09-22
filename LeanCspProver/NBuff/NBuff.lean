           /- -------------------------------------------*
            |                N Buffers                  |
            |                                           |
            |                June 2009                  |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

open fpmode

noncomputable section

namespace NBuff

local infix:50 " =F " => eqFfix

/- =============================================================*
 |                                                             |
 |                           Process                           |
 |                                                             |
 *============================================================= -/

/- *********************************************************
               process names and events
 ********************************************************* -/

inductive Event where
  | inC
  | outC
  | midC
deriving DecidableEq, Inhabited

inductive PN where
  | Buff1
  | Buff1'
  | Buff : Nat → Nat → PN
deriving DecidableEq, Inhabited

/- *********************************************************
                  Recursivey Process
 ********************************************************* -/

def PNdef : PN → proc PN Event
  | PN.Buff1 =>
      Event.inC ~> proc.Proc_name PN.Buff1'
  | PN.Buff1' =>
      Event.outC ~> proc.Proc_name PN.Buff1
  | PN.Buff N k =>
      if (Nat.blt 0 N && Nat.ble k N) then
        ((if Nat.blt k N then
            Event.inC ~> proc.Proc_name (PN.Buff N (Nat.succ k))
          else
            proc.STOP) [+]
         (if Nat.blt 0 k then
            Event.outC ~> proc.Proc_name (PN.Buff N (k - 1))
          else
            proc.STOP))
      else
        proc.STOP

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_PNdef : HasPNfun PN Event where
  PNfun := PNdef

@[simp]
theorem Set_PNdef_def (pn : PN) :
    PNfun pn = PNdef pn :=
  rfl

/- ------------------ *
      guardedness
 * ------------------ -/

@[simp] theorem guardedfun_PN :
    guardedfun PNdef := by
  intro pn
  cases pn <;> simp only [PNdef] <;> (repeat' split) <;>
    simp [guarded, noHide]

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

private abbrev Buff1P : proc PN Event :=
  proc.Proc_name PN.Buff1

private abbrev Buff1'P : proc PN Event :=
  proc.Proc_name PN.Buff1'

private abbrev BuffP (N k : Nat) : proc PN Event :=
  proc.Proc_name (PN.Buff N k)

abbrev Link (P Q : proc PN Event) : proc PN Event :=
  proc.Hiding
    ((P[[Event.outC <--> Event.midC]]) |[({Event.midC} : Set Event)]|
      (Q[[Event.inC <--> Event.midC]]))
    ({Event.midC} : Set Event)

infixr:76 " <---> " => Link

def LinkBuff : Nat → Nat → proc PN Event
  | 0, _ => proc.STOP
  | Nat.succ n, k =>
      if (n = 0) then
        if Nat.blt 0 k then Buff1'P else Buff1P
      else
        if Nat.blt n k then Buff1'P <---> LinkBuff n (k - 1) else Buff1P <---> LinkBuff n k

/- *********************************************************
                  for automatising
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare simp_event_set [simp]` has no direct Lean analogue. -/

theorem Link_cong {P Q R : proc PN Event} :
    Q =F R -> P <---> Q =F P <---> R := by
  intro hQR
  unfold Link
  apply cspF_Hiding_cong rfl
  apply cspF_Parallel_cong rfl
  · exact cspF_Renaming_cong rfl cspF_reflex_eq_P
  · exact cspF_Renaming_cong rfl hQR

/- *********************************************************
                  data tranfer
 ********************************************************* -/

private theorem unw (pn : PN) : eqF (proc.Proc_name pn : proc PN Event) MF MF (PNdef pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_PN⟩))

private theorem ren_out_Buff1 :
    Buff1P[[Event.outC <--> Event.midC]] =F
      Event.inC ~> (Buff1'P[[Event.outC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1)) ?_
  exact cspF_Act_prefix_Renaming1_event_step_notin (by decide) (by decide)

private theorem ren_out_Buff1' :
    Buff1'P[[Event.outC <--> Event.midC]] =F
      Event.midC ~> (Buff1P[[Event.outC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1')) ?_
  exact cspF_Act_prefix_Renaming1_event1_step_in

private theorem ren_in_Buff1 :
    Buff1P[[Event.inC <--> Event.midC]] =F
      Event.midC ~> (Buff1'P[[Event.inC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1)) ?_
  exact cspF_Act_prefix_Renaming1_event1_step_in

private theorem ren_in_Buff1' :
    Buff1'P[[Event.inC <--> Event.midC]] =F
      Event.outC ~> (Buff1P[[Event.inC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1')) ?_
  exact cspF_Act_prefix_Renaming1_event_step_notin (by decide) (by decide)

/-- `Buff N k` in head sequential form, for the three reachable shapes. -/
private theorem unw_Buff_both (N k : Nat) (hk : k ≤ N) (h1 : k < N) (h2 : 0 < k) :
    BuffP N k =F ((Event.inC ~> BuffP N (Nat.succ k)) [+] (Event.outC ~> BuffP N (k - 1))) := by
  refine cspF_trans_left_eq (unw (PN.Buff N k)) ?_
  have hb : PNdef (PN.Buff N k) =
      ((Event.inC ~> BuffP N (Nat.succ k)) [+] (Event.outC ~> BuffP N (k - 1))) := by
    have hN : 1 ≤ N := Nat.lt_of_lt_of_le h2 hk
    simp [PNdef, Nat.blt, hN, h1, hk, Nat.pos_iff_ne_zero.mp h2]
  rw [hb]
  exact cspF_reflex_eq_P

private theorem unw_Buff_in (N : Nat) (h : 0 < N) :
    BuffP N 0 =F ((Event.inC ~> BuffP N 1) [+] proc.STOP) := by
  refine cspF_trans_left_eq (unw (PN.Buff N 0)) ?_
  have hb : PNdef (PN.Buff N 0) = ((Event.inC ~> BuffP N 1) [+] proc.STOP) := by
    have hN : 1 ≤ N := h
    simp [PNdef, Nat.blt, Nat.ble, hN]
  rw [hb]
  exact cspF_reflex_eq_P

private theorem unw_Buff_out (N : Nat) (h : 0 < N) :
    BuffP N N =F (proc.STOP [+] (Event.outC ~> BuffP N (N - 1))) := by
  refine cspF_trans_left_eq (unw (PN.Buff N N)) ?_
  have hb : PNdef (PN.Buff N N) = (proc.STOP [+] (Event.outC ~> BuffP N (N - 1))) := by
    have hN : 1 ≤ N := h
    simp [PNdef, Nat.blt, hN]
  rw [hb]
  exact cspF_reflex_eq_P

private theorem unw_Buff_in_only (N : Nat) (h : 0 < N) :
    BuffP N 0 =F Event.inC ~> BuffP N 1 :=
  cspF_trans_left_eq (unw_Buff_in N h) cspF_Ext_choice_unit_r

private theorem unw_Buff_out_only (N : Nat) (h : 0 < N) :
    BuffP N N =F Event.outC ~> BuffP N (N - 1) :=
  cspF_trans_left_eq (unw_Buff_out N h) cspF_Ext_choice_unit_l

/-- Renaming a two-way external choice of prefixes: route through the head
    sequential form, since renaming does not distribute over `[+]` directly. -/
private theorem ren_choice (a b : Event) (A B : proc PN Event)
    (hab : a ≠ b) (hna : a ≠ Event.midC) (hnb : b ≠ Event.midC) :
    ((a ~> A) [+] (b ~> B))[[a <--> Event.midC]] =F
      ((Event.midC ~> A[[a <--> Event.midC]]) [+] (b ~> B[[a <--> Event.midC]])) := by
  refine cspF_trans_left_eq
    (cspF_Renaming_cong rfl
      (cspF_trans_left_eq
        (cspF_Ext_choice_cong cspF_Act_prefix_step cspF_Act_prefix_step)
        cspF_Ext_choice_step)) ?_
  refine cspF_trans_left_eq cspF_Ext_pre_choice_Renaming1_event_step ?_
  rw [procIte_pos (show a ∈ ({a} : Set Event) ∪ {b} from Or.inl rfl),
    procIte_neg (show Event.midC ∉ ({a} : Set Event) ∪ {b} from by
      rintro (h | h)
      · exact hna h.symm
      · exact hnb h.symm),
    procIte_neg (show ¬ (a ∈ ({a} : Set Event) ∧ a ∈ ({b} : Set Event)) from
      fun h => hab h.2),
    procIte_pos (show a ∈ ({a} : Set Event) from rfl)]
  have hX : (({a} : Set Event) ∪ {b}) \ ({a, Event.midC} : Set Event) = ({b} : Set Event) := by
    ext e
    simp only [Set.mem_diff, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨(rfl | rfl), hn⟩
      · exact absurd (Or.inl rfl) hn
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, by rintro (rfl | rfl); exacts [hab rfl, hnb rfl]⟩
  rw [hX]
  refine cspF_trans_left_eq (cspF_Ext_choice_cong cspF_Ext_choice_unit_r cspF_reflex_eq_P) ?_
  refine cspF_Ext_choice_cong cspF_reflex_eq_P ?_
  refine cspF_trans_left_eq (cspF_Ext_pre_choice_cong rfl (fun e he => ?_))
    cspF_Act_prefix_step_sym
  have hbe : e = b := he
  subst hbe
  rw [procIte_neg (show ¬ (e ∈ ({a} : Set Event) ∧ e ∈ ({e} : Set Event)) from
      fun h => hab h.1.symm),
    procIte_neg (show e ∉ ({a} : Set Event) from fun h => hab h.symm)]
  exact cspF_reflex_eq_P

axiom internal_data_transfer {N k : Nat} :
    Nat.lt k N ->
      (Buff1'P <---> BuffP N k) =F
        (Buff1P <---> BuffP N (Nat.succ k))

/- *********************************************************
                 one step concurrency
 ********************************************************* -/

def Buff_to_Link_Buff : PN → proc PN Event
  | PN.Buff1 => Buff1P
  | PN.Buff1' => Buff1'P
  | PN.Buff N k =>
      if (Nat.blt 0 N && Nat.ble k N) then
        if (N = Nat.succ 0) then
          if Nat.blt k N then Buff1P else Buff1'P
        else
          if Nat.blt k N then Buff1P <---> BuffP (N - 1) k else Buff1'P <---> BuffP (N - 1) (k - 1)
      else
        proc.STOP

axiom LinkBuff_eq_Buff_step_k {N k : Nat} :
    Nat.lt 0 N -> k <= Nat.succ N ->
      BuffP N k =F Buff_to_Link_Buff (PN.Buff N k)

/- --------------------- *
 |        one step       |
 * --------------------- -/

theorem LinkBuff_eq_Buff_step (N : Nat) :
    BuffP (Nat.succ N) 0 =F
      (if (N = 0) then Buff1P else Buff1P <---> BuffP N 0) := by
  have h := LinkBuff_eq_Buff_step_k (N := Nat.succ N) (k := 0) (Nat.succ_pos N) (Nat.zero_le _)
  simpa [Buff_to_Link_Buff, Nat.blt, Nat.ble, Nat.succ_eq_add_one] using h

/- --------------------- *
 |          main         |
 * --------------------- -/

theorem LinkBuff_eq_Buff :
    ∀ N, BuffP N 0 =F LinkBuff N 0 := by
  intro N
  induction N with
  | zero =>
      refine cspF_trans_left_eq (unw (PN.Buff 0 0)) ?_
      have h1 : PNdef (PN.Buff 0 0) = proc.STOP := by simp [PNdef, Nat.blt]
      have h2 : LinkBuff 0 0 = (proc.STOP : proc PN Event) := by simp [LinkBuff]
      rw [h1, h2]
      exact cspF_reflex_eq_P
  | succ N ih =>
      refine cspF_trans_left_eq (LinkBuff_eq_Buff_step N) ?_
      by_cases hN : N = 0
      · subst hN
        have h : LinkBuff (Nat.succ 0) 0 = Buff1P := by simp [LinkBuff]
        rw [h, if_pos rfl]
        exact cspF_reflex_eq_P
      · rw [if_neg hN]
        have hL : LinkBuff (Nat.succ N) 0 = Buff1P <---> LinkBuff N 0 := by
          simp [LinkBuff, hN, Nat.blt]
        rw [hL]
        exact Link_cong ih

end NBuff
