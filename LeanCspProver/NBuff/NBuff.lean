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
    ((P [[Event.outC <--> Event.midC]]) |[({Event.midC} : Set Event)]|
      (Q [[Event.inC <--> Event.midC]]))
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
    Buff1P [[Event.outC <--> Event.midC]] =F
      Event.inC ~> (Buff1'P [[Event.outC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1)) ?_
  exact cspF_Act_prefix_Renaming1_event_step_notin (by decide) (by decide)

private theorem ren_out_Buff1' :
    Buff1'P [[Event.outC <--> Event.midC]] =F
      Event.midC ~> (Buff1P [[Event.outC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1')) ?_
  exact cspF_Act_prefix_Renaming1_event1_step_in

private theorem ren_in_Buff1 :
    Buff1P [[Event.inC <--> Event.midC]] =F
      Event.midC ~> (Buff1'P [[Event.inC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw PN.Buff1)) ?_
  exact cspF_Act_prefix_Renaming1_event1_step_in

private theorem ren_in_Buff1' :
    Buff1'P [[Event.inC <--> Event.midC]] =F
      Event.outC ~> (Buff1P [[Event.inC <--> Event.midC]]) := by
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
    ((a ~> A) [+] (b ~> B)) [[a <--> Event.midC]] =F
      ((Event.midC ~> A [[a <--> Event.midC]]) [+] (b ~> B [[a <--> Event.midC]])) := by
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

/-- Two prefixes on a synchronised event step together. -/
private theorem par_sync_prefix (a : Event) (A B : proc PN Event) (X : Set Event) (ha : a ∈ X) :
    ((a ~> A) |[X]| (a ~> B)) =F a ~> (A |[X]| B) := by
  refine cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_Act_prefix_step cspF_Act_prefix_step) ?_
  refine cspF_trans_left_eq cspF_Parallel_step ?_
  have hidx : ((X ∩ ({a} : Set Event) ∩ {a}) ∪ (({a} : Set Event) \ X)) ∪
      (({a} : Set Event) \ X) = ({a} : Set Event) := by
    have hd : ({a} : Set Event) \ X = (∅ : Set Event) :=
      Set.diff_eq_empty.mpr (Set.singleton_subset_iff.mpr ha)
    have hi : X ∩ ({a} : Set Event) ∩ {a} = ({a} : Set Event) := by
      ext e
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.2, fun h => ⟨⟨h ▸ ha, h⟩, h⟩⟩
    rw [hd, hi, Set.union_empty, Set.union_empty]
  rw [hidx]
  refine cspF_trans_left_eq (cspF_Ext_pre_choice_cong rfl (fun e he => ?_))
    cspF_Act_prefix_step_sym
  have hea : e = a := he
  subst hea
  rw [procIte_pos ha]
  exact cspF_reflex_eq_P

/-- One internal handshake: the left buffer is full, the right can only accept. -/
private theorem link_tau (Q Q' : proc PN Event)
    (hQ : Q [[Event.inC <--> Event.midC]] =F
      Event.midC ~> (Q' [[Event.inC <--> Event.midC]])) :
    Buff1'P <---> Q =F Buff1P <---> Q' := by
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Parallel_cong rfl ren_out_Buff1' hQ)) ?_
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (par_sync_prefix Event.midC _ _ _ rfl)) ?_
  exact cspF_Hiding_Act_prefix_in rfl

private theorem ren_in_Buff_zero (N : Nat) (h : 0 < N) :
    (BuffP N 0) [[Event.inC <--> Event.midC]] =F
      Event.midC ~> ((BuffP N 1) [[Event.inC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw_Buff_in_only N h)) ?_
  exact cspF_Act_prefix_Renaming1_event1_step_in

private theorem ren_in_Buff_both (N k : Nat) (hk : k ≤ N) (h1 : k < N) (h2 : 0 < k) :
    (BuffP N k) [[Event.inC <--> Event.midC]] =F
      ((Event.midC ~> ((BuffP N (Nat.succ k)) [[Event.inC <--> Event.midC]])) [+]
        (Event.outC ~> ((BuffP N (k - 1)) [[Event.inC <--> Event.midC]]))) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw_Buff_both N k hk h1 h2)) ?_
  exact ren_choice Event.inC Event.outC _ _ (by decide) (by decide) (by decide)

private theorem ren_in_Buff_full (N : Nat) (h : 0 < N) :
    (BuffP N N) [[Event.inC <--> Event.midC]] =F
      Event.outC ~> ((BuffP N (N - 1)) [[Event.inC <--> Event.midC]]) := by
  refine cspF_trans_left_eq (cspF_Renaming_cong rfl (unw_Buff_out_only N h)) ?_
  exact cspF_Act_prefix_Renaming1_event_step_notin (by decide) (by decide)

private theorem two_prefix_fwd (a b : Event) (A B : proc PN Event) :
    ((a ~> A) [+] (b ~> B)) =F
      proc.Ext_pre_choice (({a} : Set Event) ∪ ({b} : Set Event))
        (fun x => procIte (x ∈ ({a} : Set Event) ∧ x ∈ ({b} : Set Event)) (A |~| B)
          (procIte (x ∈ ({a} : Set Event)) A B)) :=
  cspF_trans_left_eq
    (cspF_Ext_choice_cong (cspF_Act_prefix_step (a := a) (P := A))
      (cspF_Act_prefix_step (a := b) (P := B)))
    cspF_Ext_choice_step

private theorem two_prefix_back (a b : Event) (Pf : Event → proc PN Event) (hab : a ≠ b) :
    proc.Ext_pre_choice (({a} : Set Event) ∪ ({b} : Set Event)) Pf =F
      ((a ~> Pf a) [+] (b ~> Pf b)) := by
  refine cspF_trans_left_eq ?_ (cspF_sym (two_prefix_fwd a b (Pf a) (Pf b)))
  refine cspF_Ext_pre_choice_cong rfl (fun e he => ?_)
  rcases he with h | h
  · have : e = a := h
    subst this
    rw [procIte_neg (fun hc => hab hc.2), procIte_pos (show e ∈ ({e} : Set Event) from rfl)]
    exact cspF_reflex_eq_P
  · have : e = b := h
    subst this
    rw [procIte_neg (fun hc => hab hc.1.symm),
      procIte_neg (show e ∉ ({a} : Set Event) from fun hc => hab hc.symm)]
    exact cspF_reflex_eq_P

/-- With the left buffer empty it cannot join the `midC` handshake, so the
    composite just offers the two free events. -/
private theorem link_Buff1_step (N k : Nat) (Z : Set Event) (Rf : Event → proc PN Event)
    (hR : (BuffP N k) [[Event.inC <--> Event.midC]] =F proc.Ext_pre_choice Z Rf)
    (hZd : Z \ ({Event.midC} : Set Event) = ({Event.outC} : Set Event))
    (hIn : Event.inC ∉ Z)
    (hOut : Rf Event.outC =F (BuffP N (k - 1)) [[Event.inC <--> Event.midC]]) :
    Buff1P <---> BuffP N k =F
      ((Event.inC ~> (Buff1'P <---> BuffP N k)) [+]
        (Event.outC ~> (Buff1P <---> BuffP N (k - 1)))) := by
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Parallel_cong rfl
      (cspF_trans_left_eq ren_out_Buff1 (cspF_Act_prefix_step (a := Event.inC))) hR)) ?_
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl cspF_Parallel_step) ?_
  have hidx : ((({Event.midC} : Set Event) ∩ ({Event.inC} : Set Event) ∩ Z) ∪
      (({Event.inC} : Set Event) \ ({Event.midC} : Set Event))) ∪
      (Z \ ({Event.midC} : Set Event))
      = (({Event.inC} : Set Event) ∪ ({Event.outC} : Set Event)) := by
    rw [hZd]
    have h1 : ({Event.midC} : Set Event) ∩ ({Event.inC} : Set Event) ∩ Z = ∅ := by
      ext e
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨rfl, h⟩, -⟩
      cases h
    have h2 : ({Event.inC} : Set Event) \ ({Event.midC} : Set Event) =
        ({Event.inC} : Set Event) := by
      ext e
      simp only [Set.mem_diff, Set.mem_singleton_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, by rintro rfl; cases h⟩⟩
    rw [h1, h2, Set.empty_union]
  rw [hidx]
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_pos (show (({Event.inC} : Set Event) ∪ ({Event.outC} : Set Event)) ∩
      ({Event.midC} : Set Event) = ∅ from by
    ext e
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨(rfl | rfl), h⟩ <;> cases h)]
  refine cspF_trans_left_eq (two_prefix_back Event.inC Event.outC _ (by decide)) ?_
  refine cspF_Ext_choice_cong (cspF_Act_prefix_cong rfl ?_) (cspF_Act_prefix_cong rfl ?_)
  · rw [procIte_neg (show Event.inC ∉ ({Event.midC} : Set Event) from by rintro h; cases h),
      procIte_neg (show ¬ (Event.inC ∈ ({Event.inC} : Set Event) ∧ Event.inC ∈ Z) from
        fun h => hIn h.2),
      procIte_pos (show Event.inC ∈ ({Event.inC} : Set Event) from rfl)]
    exact cspF_Hiding_cong rfl (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hR))
  · rw [procIte_neg (show Event.outC ∉ ({Event.midC} : Set Event) from by rintro h; cases h),
      procIte_neg (show ¬ (Event.outC ∈ ({Event.inC} : Set Event) ∧ Event.outC ∈ Z) from
        fun h => by cases h.1),
      procIte_neg (show Event.outC ∉ ({Event.inC} : Set Event) from by rintro h; cases h)]
    refine cspF_Hiding_cong rfl (cspF_Parallel_cong rfl ?_ hOut)
    exact cspF_sym (cspF_trans_left_eq ren_out_Buff1 (cspF_Act_prefix_step (a := Event.inC)))

private theorem link_Buff1_hsf (N k : Nat) (hk : 0 < k) (hkN : k ≤ N) :
    Buff1P <---> BuffP N k =F
      ((Event.inC ~> (Buff1'P <---> BuffP N k)) [+]
        (Event.outC ~> (Buff1P <---> BuffP N (k - 1)))) := by
  by_cases h1 : k < N
  · refine link_Buff1_step N k _ _
      (cspF_trans_left_eq (ren_in_Buff_both N k hkN h1 hk) (two_prefix_fwd _ _ _ _))
      ?_ (by rintro (h | h) <;> cases h) ?_
    · ext e
      simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨(rfl | rfl), hn⟩
        · exact absurd rfl hn
        · rfl
      · rintro rfl
        exact ⟨Or.inr rfl, by rintro h; cases h⟩
    · rw [procIte_neg (fun h => by cases h.1), procIte_neg (by rintro h; cases h)]
      exact cspF_reflex_eq_P
  · have hkeq : k = N := Nat.le_antisymm hkN (Nat.not_lt.mp h1)
    subst hkeq
    refine link_Buff1_step k k _ _
      (cspF_trans_left_eq (ren_in_Buff_full k hk) (cspF_Act_prefix_step (a := Event.outC)))
      ?_ (by rintro h; cases h) cspF_reflex_eq_P
    ext e
    simp only [Set.mem_diff, Set.mem_singleton_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, by rintro rfl; cases h⟩⟩

/-- With the left buffer full, `midC` is a synchronised handshake and becomes a
    hidden τ, which races the right buffer's free `outC`: a sliding choice. -/
private theorem link_Buff1'_hsf (N k : Nat) (hk : 0 < k) (hkN : k < N) :
    Buff1'P <---> BuffP N k =F
      ((Event.outC ~> (Buff1'P <---> BuffP N (k - 1))) [>
        (Buff1P <---> BuffP N (Nat.succ k))) := by
  have hR := cspF_trans_left_eq (ren_in_Buff_both N k (Nat.le_of_lt hkN) hkN hk)
    (two_prefix_fwd Event.midC Event.outC
      ((BuffP N (Nat.succ k)) [[Event.inC <--> Event.midC]])
      ((BuffP N (k - 1)) [[Event.inC <--> Event.midC]]))
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Parallel_cong rfl
      (cspF_trans_left_eq ren_out_Buff1' (cspF_Act_prefix_step (a := Event.midC))) hR)) ?_
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl cspF_Parallel_step) ?_
  have hidx : ((({Event.midC} : Set Event) ∩ ({Event.midC} : Set Event) ∩
        (({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event))) ∪
      (({Event.midC} : Set Event) \ ({Event.midC} : Set Event))) ∪
      ((({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event)) \
        ({Event.midC} : Set Event))
      = (({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event)) := by
    ext e
    cases e <;> simp
  rw [hidx]
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_neg (show ¬ ((({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event)) ∩
      ({Event.midC} : Set Event) = ∅) from by
    intro h
    have : Event.midC ∈ (({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event)) ∩
        ({Event.midC} : Set Event) := ⟨Or.inl rfl, rfl⟩
    rw [h] at this
    exact this)]
  have hdiff : ((({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event)) \
      ({Event.midC} : Set Event)) = ({Event.outC} : Set Event) := by
    ext e
    cases e <;> simp
  have hint : ((({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event)) ∩
      ({Event.midC} : Set Event)) = ({Event.midC} : Set Event) := by
    ext e
    cases e <;> simp
  rw [hdiff, hint]
  refine cspF_Timeout_cong ?_ ?_
  · refine cspF_trans_left_eq
      (cspF_Ext_pre_choice_cong rfl (fun e he => ?_))
      (cspF_Act_prefix_step_sym (a := Event.outC)
        (P := Buff1'P <---> BuffP N (k - 1)))
    have hee : e = Event.outC := he
    subst hee
    rw [procIte_neg (show Event.outC ∉ ({Event.midC} : Set Event) from by rintro h; cases h),
      procIte_neg (show ¬ (Event.outC ∈ ({Event.midC} : Set Event) ∧
        Event.outC ∈ (({Event.midC} : Set Event) ∪ ({Event.outC} : Set Event))) from
        fun h => by cases h.1),
      procIte_neg (show Event.outC ∉ ({Event.midC} : Set Event) from by rintro h; cases h),
      procIte_neg (fun h => by cases h.1),
      procIte_neg (show Event.outC ∉ ({Event.midC} : Set Event) from by rintro h; cases h)]
    refine cspF_Hiding_cong rfl (cspF_Parallel_cong rfl ?_ cspF_reflex_eq_P)
    exact cspF_sym (cspF_trans_left_eq ren_out_Buff1' (cspF_Act_prefix_step (a := Event.midC)))
  · refine cspF_trans_left_eq cspF_Rep_int_choice_com_singleton ?_
    rw [procIte_pos (show Event.midC ∈ ({Event.midC} : Set Event) from rfl),
      procIte_neg (fun h => by cases h.2),
      procIte_pos (show Event.midC ∈ ({Event.midC} : Set Event) from rfl)]
    exact cspF_reflex_eq_P

private theorem timeout_absorb (Q R : proc PN Event) :
    (Q [> (R [+] Q)) =F (R [+] Q) := by
  refine cspF_trans_left_eq cspF_Timeout_Int_choice ?_
  refine cspF_trans_left_eq (cspF_Int_choice_cong ?_ cspF_reflex_eq_P) cspF_Int_choice_idem
  refine cspF_trans_left_eq cspF_Ext_choice_assoc ?_
  refine cspF_trans_left_eq (cspF_Ext_choice_cong cspF_Ext_choice_commut cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq cspF_Ext_choice_assoc_sym ?_
  exact cspF_Ext_choice_cong cspF_reflex_eq_P cspF_Ext_choice_idem

theorem internal_data_transfer {N k : Nat} :
    Nat.lt k N ->
      (Buff1'P <---> BuffP N k) =F
        (Buff1P <---> BuffP N (Nat.succ k)) := by
  induction k with
  | zero =>
      intro h
      exact link_tau _ _ (ren_in_Buff_zero N h)
  | succ k ih =>
      intro h
      have hk : k < N := Nat.lt_of_succ_lt h
      have hle : Nat.succ (Nat.succ k) ≤ N := h
      have hstep := link_Buff1_hsf N (Nat.succ (Nat.succ k)) (Nat.succ_pos _) hle
      refine cspF_trans_left_eq (link_Buff1'_hsf N (Nat.succ k) (Nat.succ_pos k) h) ?_
      refine cspF_trans_left_eq
        (cspF_Timeout_cong (cspF_Act_prefix_cong rfl (ih hk)) hstep) ?_
      refine cspF_trans_left_eq (timeout_absorb _ _) ?_
      exact cspF_sym hstep

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

/-- Both buffers empty: nothing to hand over, only the external `inC`. -/
private theorem link_Buff1_empty (M : Nat) (h : 0 < M) :
    Buff1P <---> BuffP M 0 =F Event.inC ~> (Buff1'P <---> BuffP M 0) := by
  have hR := cspF_trans_left_eq (ren_in_Buff_zero M h)
    (cspF_Act_prefix_step (a := Event.midC)
      (P := (BuffP M 1) [[Event.inC <--> Event.midC]]))
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Parallel_cong rfl
      (cspF_trans_left_eq ren_out_Buff1 (cspF_Act_prefix_step (a := Event.inC))) hR)) ?_
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl cspF_Parallel_step) ?_
  rw [show ((({Event.midC} : Set Event) ∩ ({Event.inC} : Set Event) ∩
        ({Event.midC} : Set Event)) ∪
      (({Event.inC} : Set Event) \ ({Event.midC} : Set Event))) ∪
      (({Event.midC} : Set Event) \ ({Event.midC} : Set Event))
      = ({Event.inC} : Set Event) from by ext e; cases e <;> simp]
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_pos (show ({Event.inC} : Set Event) ∩ ({Event.midC} : Set Event) = ∅ from by
    ext e; cases e <;> simp)]
  refine cspF_trans_left_eq
    (cspF_Ext_pre_choice_cong rfl (fun e he => ?_))
    (cspF_Act_prefix_step_sym (a := Event.inC) (P := Buff1'P <---> BuffP M 0))
  have hee : e = Event.inC := he
  subst hee
  rw [procIte_neg (show Event.inC ∉ ({Event.midC} : Set Event) from by rintro hc; cases hc),
    procIte_neg (fun hc => by cases hc.2),
    procIte_pos (show Event.inC ∈ ({Event.inC} : Set Event) from rfl)]
  exact cspF_Hiding_cong rfl (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_sym hR))

/-- Both buffers full: the handshake is blocked, only the external `outC`. -/
private theorem link_Buff1'_full (M : Nat) (h : 0 < M) :
    Buff1'P <---> BuffP M M =F Event.outC ~> (Buff1'P <---> BuffP M (M - 1)) := by
  have hR := cspF_trans_left_eq (ren_in_Buff_full M h)
    (cspF_Act_prefix_step (a := Event.outC)
      (P := (BuffP M (M - 1)) [[Event.inC <--> Event.midC]]))
  have hL := cspF_trans_left_eq ren_out_Buff1'
    (cspF_Act_prefix_step (a := Event.midC)
      (P := Buff1P [[Event.outC <--> Event.midC]]))
  refine cspF_trans_left_eq
    (cspF_Hiding_cong rfl (cspF_Parallel_cong rfl hL hR)) ?_
  refine cspF_trans_left_eq (cspF_Hiding_cong rfl cspF_Parallel_step) ?_
  rw [show ((({Event.midC} : Set Event) ∩ ({Event.midC} : Set Event) ∩
        ({Event.outC} : Set Event)) ∪
      (({Event.midC} : Set Event) \ ({Event.midC} : Set Event))) ∪
      (({Event.outC} : Set Event) \ ({Event.midC} : Set Event))
      = ({Event.outC} : Set Event) from by ext e; cases e <;> simp]
  refine cspF_trans_left_eq cspF_Hiding_step ?_
  rw [procIte_pos (show ({Event.outC} : Set Event) ∩ ({Event.midC} : Set Event) = ∅ from by
    ext e; cases e <;> simp)]
  refine cspF_trans_left_eq
    (cspF_Ext_pre_choice_cong rfl (fun e he => ?_))
    (cspF_Act_prefix_step_sym (a := Event.outC) (P := Buff1'P <---> BuffP M (M - 1)))
  have hee : e = Event.outC := he
  subst hee
  rw [procIte_neg (show Event.outC ∉ ({Event.midC} : Set Event) from by rintro hc; cases hc),
    procIte_neg (fun hc => by cases hc.1),
    procIte_neg (show Event.outC ∉ ({Event.midC} : Set Event) from by rintro hc; cases hc)]
  exact cspF_Hiding_cong rfl (cspF_Parallel_cong rfl (cspF_sym hL) cspF_reflex_eq_P)

private theorem BtoL_out (M j : Nat) (h : ¬ (1 ≤ M ∧ j ≤ M)) :
    Buff_to_Link_Buff (PN.Buff M j) = proc.STOP := by
  have h1 : (Nat.blt 0 M && Nat.ble j M) = false := by
    rw [Bool.and_eq_false_iff]
    rcases Nat.lt_or_ge M 1 with hh | hh
    · exact Or.inl (by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega)
    · exact Or.inr (by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega)
  simp [Buff_to_Link_Buff, h1]

private theorem BtoL_one (j : Nat) (hj : j ≤ 1) :
    Buff_to_Link_Buff (PN.Buff 1 j) = (if Nat.blt j 1 then Buff1P else Buff1'P) := by
  have h1 : (Nat.blt 0 1 && Nat.ble j 1) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
    omega
  simp [Buff_to_Link_Buff, h1]

private theorem BtoL_lt (M j : Nat) (hM : 2 ≤ M) (_hjM : j ≤ M) (hj : Nat.succ j ≤ M) :
    Buff_to_Link_Buff (PN.Buff M j) = Buff1P <---> BuffP (M - 1) j := by
  have h1 : (Nat.blt 0 M && Nat.ble j M) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
    omega
  have h2 : ¬ (M = Nat.succ 0) := by omega
  have h3 : Nat.blt j M = true := by
    simp only [Nat.blt_eq]
    omega
  simp [Buff_to_Link_Buff, h1, h2, h3]

private theorem BtoL_ge (M j : Nat) (hM : 2 ≤ M) (_hjM : j ≤ M) (hj : M ≤ j) :
    Buff_to_Link_Buff (PN.Buff M j) = Buff1'P <---> BuffP (M - 1) (j - 1) := by
  have h1 : (Nat.blt 0 M && Nat.ble j M) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
    omega
  have h2 : ¬ (M = Nat.succ 0) := by omega
  have h3 : Nat.blt j M = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
    omega
  simp [Buff_to_Link_Buff, h1, h2, h3]

private theorem PNdef_Buff_out (M j : Nat) (h : ¬ (1 ≤ M ∧ j ≤ M)) :
    PNdef (PN.Buff M j) = proc.STOP := by
  have h1 : (Nat.blt 0 M && Nat.ble j M) = false := by
    rw [Bool.and_eq_false_iff]
    rcases Nat.lt_or_ge M 1 with hh | hh
    · exact Or.inl (by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; omega)
    · exact Or.inr (by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega)
  simp [PNdef, h1]

private theorem PNdef_Buff_mid (M j : Nat) (hM : 1 ≤ M) (_hjM : j ≤ M)
    (hlt : Nat.succ j ≤ M) (hj0 : 1 ≤ j) :
    PNdef (PN.Buff M j) =
      ((Event.inC ~> proc.Proc_name (PN.Buff M (Nat.succ j))) [+]
        (Event.outC ~> proc.Proc_name (PN.Buff M (j - 1)))) := by
  have h1 : (Nat.blt 0 M && Nat.ble j M) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
    omega
  have h2 : Nat.blt j M = true := by
    simp only [Nat.blt_eq]
    omega
  have h3 : Nat.blt 0 j = true := by
    simp only [Nat.blt_eq]
    omega
  simp [PNdef, h1, h2, h3]

private theorem PNdef_Buff_zero (M : Nat) (hM : 1 ≤ M) :
    PNdef (PN.Buff M 0) = ((Event.inC ~> proc.Proc_name (PN.Buff M 1)) [+] proc.STOP) := by
  have h1 : (Nat.blt 0 M && Nat.ble 0 M) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
    omega
  have h2 : Nat.blt 0 M = true := by
    simp only [Nat.blt_eq]
    omega
  simp [PNdef, h2]

private theorem PNdef_Buff_full (M : Nat) (hM : 1 ≤ M) :
    PNdef (PN.Buff M M) =
      (proc.STOP [+] (Event.outC ~> proc.Proc_name (PN.Buff M (M - 1)))) := by
  have h1 : (Nat.blt 0 M && Nat.ble M M) = true := by
    simp only [Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq]
    omega
  have h2 : Nat.blt M M = false := by
    rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]
    omega
  have h3 : Nat.blt 0 M = true := by
    simp only [Nat.blt_eq]
    omega
  simp [PNdef, h2, h3]

private theorem BtoL_10 : Buff_to_Link_Buff (PN.Buff 1 0) = Buff1P := by
  simp [Buff_to_Link_Buff]

private theorem BtoL_11 : Buff_to_Link_Buff (PN.Buff 1 1) = Buff1'P := by
  simp [Buff_to_Link_Buff]

theorem LinkBuff_eq_Buff_step_k {N k : Nat} :
    Nat.lt 0 N -> k <= Nat.succ N ->
      BuffP N k =F Buff_to_Link_Buff (PN.Buff N k) := by
  intro _h0 _hk
  refine cspF_fp_induct_cms_eq_left (Pf := PNdef) (f := Buff_to_Link_Buff)
    (p0 := PN.Buff N k) rfl guardedfun_PN FPmode_def cspF_reflex_eq_P ?_
  intro p
  cases p with
  | Buff1 => exact cspF_sym (unw PN.Buff1)
  | Buff1' => exact cspF_sym (unw PN.Buff1')
  | Buff M j =>
      by_cases hok : 1 ≤ M ∧ j ≤ M
      · obtain ⟨hM, hjM⟩ := hok
        by_cases hM2 : 2 ≤ M
        · by_cases hjlt : Nat.succ j ≤ M
          · rw [BtoL_lt M j hM2 hjM hjlt]
            by_cases hj0 : 1 ≤ j
            · rw [PNdef_Buff_mid M j hM hjM hjlt hj0]
              simp only [Subst_procfun]
              rw [BtoL_lt M (j - 1) hM2 (by omega) (by omega)]
              refine cspF_trans_left_eq ?_
                (cspF_sym (link_Buff1_hsf (M - 1) j hj0 (by omega)))
              refine cspF_Ext_choice_cong (cspF_Act_prefix_cong rfl ?_) cspF_reflex_eq_P
              by_cases hs : Nat.succ (Nat.succ j) ≤ M
              · rw [BtoL_lt M (Nat.succ j) hM2 (by omega) hs]
                exact cspF_sym
                  (internal_data_transfer (show Nat.succ j ≤ M - 1 by omega))
              · rw [BtoL_ge M (Nat.succ j) hM2 (by omega) (by omega)]
                exact cspF_reflex_eq_P
            · have hj : j = 0 := by omega
              rw [hj, PNdef_Buff_zero M hM]
              simp only [Subst_procfun]
              refine cspF_trans_left_eq cspF_Ext_choice_unit_r ?_
              refine cspF_trans_left_eq ?_
                (cspF_sym (link_Buff1_empty (M - 1) (show 1 ≤ M - 1 by omega)))
              refine cspF_Act_prefix_cong rfl ?_
              rw [BtoL_lt M 1 hM2 (by omega) (by omega)]
              exact cspF_sym
                (internal_data_transfer (show Nat.succ 0 ≤ M - 1 by omega))
          · have hjeq : j = M := by omega
            rw [hjeq, BtoL_ge M M hM2 (Nat.le_refl M) (Nat.le_refl M), PNdef_Buff_full M hM]
            simp only [Subst_procfun]
            refine cspF_trans_left_eq cspF_Ext_choice_unit_l ?_
            refine cspF_trans_left_eq ?_
              (cspF_sym (link_Buff1'_full (M - 1) (show 1 ≤ M - 1 by omega)))
            refine cspF_Act_prefix_cong rfl ?_
            rw [BtoL_lt M (M - 1) hM2 (by omega) (by omega)]
            have harith : Nat.succ (M - 1 - 1) = M - 1 := by omega
            refine cspF_sym (?_ : eqFfix (Buff1'P <---> BuffP (M - 1) (M - 1 - 1)) _)
            rw [← harith]
            exact internal_data_transfer (Nat.le_refl _)
        · have hM1 : M = 1 := by omega
          rw [hM1] at hjM ⊢
          interval_cases j
          · rw [BtoL_10, PNdef_Buff_zero 1 (Nat.le_refl 1)]
            simp only [Subst_procfun, BtoL_11]
            refine cspF_trans_left_eq cspF_Ext_choice_unit_r ?_
            exact cspF_sym (unw PN.Buff1)
          · rw [BtoL_11, PNdef_Buff_full 1 (Nat.le_refl 1)]
            simp only [Subst_procfun]
            refine cspF_trans_left_eq cspF_Ext_choice_unit_l ?_
            exact cspF_sym (unw PN.Buff1')
      · rw [PNdef_Buff_out M j hok, BtoL_out M j hok]
        exact cspF_reflex_eq_P

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
