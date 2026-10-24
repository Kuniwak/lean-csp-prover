           /- -------------------------------------------*
            |  The Dining Mathematicians in CSP-Prover  |
            |               August 2004                 |
            |             December 2004 (modified)      |
            |             November 2005 (modified)      |
            |                April 2006 (modified)      |
            |                  May 2016  (modified)     |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

open fpmode

noncomputable section

namespace DM1_Imp_def

/- *****************************************************************

         1. defines Imp
         2.
         3.
         4.

 ***************************************************************** -/

/- *********************************************************
                    ODD and EVEN
 ********************************************************* -/

def EVEN : Int → Bool
  | n => n % 2 == 0

def ODD : Int → Bool
  | n => n % 2 == 1

abbrev EVENs : Set Int := {n | EVEN n}

abbrev ODDs : Set Int := {n | ODD n}

/- *********************************************************
                         event
 ********************************************************* -/

inductive Event where
  | Eat0
  | Back0
  | End0
  | RD0 : Int → Event
  | WR0 : Int → Event
  | Eat1
  | Back1
  | End1
  | RD1 : Int → Event
  | WR1 : Int → Event
  | NUM : Int → Event
deriving DecidableEq, Inhabited

@[simp]
theorem expand_Event_fun (Ef Eg : Int → Event) : (Ef = Eg) ↔ ∀ n, Ef n = Eg n := by
  constructor
  · intro h n
    simp [h]
  · intro h
    exact funext h

abbrev CH0 : Set Event := Set.range Event.RD0 ∪ Set.range Event.WR0

abbrev CH1 : Set Event := Set.range Event.RD1 ∪ Set.range Event.WR1

abbrev OBS : Set Event :=
  {Event.Eat0, Event.Back0, Event.End0, Event.Eat1, Event.Back1, Event.End1}

/- *********************************************************
                     function
 ********************************************************* -/

def getInt : Event → Int
  | Event.Eat0 => 0
  | Event.Eat1 => 0
  | Event.Back0 => 0
  | Event.Back1 => 0
  | Event.End0 => 0
  | Event.End1 => 0
  | Event.RD0 n => n
  | Event.RD1 n => n
  | Event.WR0 n => n
  | Event.WR1 n => n
  | Event.NUM n => n

/- *********************************************************
                Parallel system definition
 ********************************************************* -/
/- Lean note:
   Isabelle's overloaded constant `FPmode` is represented by a typeclass
   instance. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

inductive ImpName where
  | VAR : Int → ImpName
  | TH0
  | EAT0 : Int → ImpName
  | TH1
  | EAT1 : Int → ImpName
deriving DecidableEq, Inhabited

def Impfun : ImpName → proc ImpName Event
  | ImpName.TH0 =>
      Rec_prefix Event.RD0 Set.univ fun n =>
        IF EVEN n THEN Event.Eat0 ~> proc.Proc_name (ImpName.EAT0 n)
        ELSE Event.Back0 ~> proc.Proc_name ImpName.TH0
  | ImpName.TH1 =>
      Rec_prefix Event.RD1 Set.univ fun n =>
        IF ODD n THEN Event.Eat1 ~> proc.Proc_name (ImpName.EAT1 n)
        ELSE Event.Back1 ~> proc.Proc_name ImpName.TH1
  | ImpName.EAT0 n =>
      Event.End0 ~> Event.WR0 (n / 2) ~> proc.Proc_name ImpName.TH0
  | ImpName.EAT1 n =>
      Event.End1 ~> Event.WR1 (3 * n + 1) ~> proc.Proc_name ImpName.TH1
  | ImpName.VAR n =>
      Rec_prefix Event.WR0 Set.univ (fun m => proc.Proc_name (ImpName.VAR m)) [+]
      Rec_prefix Event.WR1 Set.univ (fun m => proc.Proc_name (ImpName.VAR m)) [+]
      Event.RD0 n ~> proc.Proc_name (ImpName.VAR n) [+]
      Event.RD1 n ~> proc.Proc_name (ImpName.VAR n)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Impfun : HasPNfun ImpName Event where
  PNfun := Impfun

@[simp]
theorem Set_Impfun_def (pn : ImpName) :
    PNfun (p := ImpName) (α := Event) pn = Impfun pn :=
  rfl

def Imp : Int → proc ImpName Event :=
  fun n =>
    proc.Hiding
      (((proc.Proc_name ImpName.TH0) |[CH0]| (proc.Proc_name (ImpName.VAR n))) |[CH1]|
        (proc.Proc_name ImpName.TH1))
      (CH0 ∪ CH1)

theorem Imp_def :
    Imp =
      (fun n =>
        proc.Hiding
          (((proc.Proc_name ImpName.TH0) |[CH0]| (proc.Proc_name (ImpName.VAR n))) |[CH1]|
            (proc.Proc_name ImpName.TH1))
          (CH0 ∪ CH1)) :=
  rfl

/- *********************************************************
         To unfold "range" and "syntactic sugar", ...
 ********************************************************* -/

/- Lean note:
   Isabelle's `declare image_iff[in simp]`, `declare inj_on_def[simp]`, and
   `declare csp_prefix_ss_def[simp]` have no direct Lean analogue here. -/

/- *********************************************************
                gProc lemmas (routine work)
 ********************************************************* -/

@[simp]
theorem guarded_Imp :
    guardedfun (p := ImpName) (q := ImpName) (α := Event) Impfun := by
  intro pn
  cases pn <;> simp [Impfun, guarded, noHide]

/- *********************************************************
                        Lemmas
 ********************************************************* -/

/- (*** int lemmas ***) -/

theorem int_le_inc : ∀ (n : Int) m, n <= m → n = m ∨ n + 1 <= m := by
  intro n m hnm
  omega

theorem mod_2_not_le : ∀ n : Int, ¬ (2 <= n % 2) := by
  intro n
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1 <;> omega

theorem mod_2_or : ∀ n : Int, n % 2 = 0 ∨ n % 2 = 1 :=
  Int.emod_two_eq_zero_or_one

/- (*** ODD and EVEN lemmas ***) -/

@[simp]
theorem EVEN_not_ODD : ∀ n, EVEN n = !ODD n := by
  intro n
  rcases Int.emod_two_eq_zero_or_one n with h0 | h1
  · simp [EVEN, ODD, h0]
  · simp [EVEN, ODD, h1]

theorem ODD_add_1 : ∀ n : Int, n % 2 = 1 → (n + 1) % 2 = 0 := by
  intro n hn
  have hEven : Even (n + 1) := by
    exact (Int.even_add_one).2 ((Int.not_even_iff).2 hn)
  exact (Int.even_iff).1 hEven

theorem ODD_EX : ∀ m, ODD m → ∃ n, m = 2 * n + 1 := by
  intro m hm
  have hm' : m % 2 = 1 := by
    simpa [ODD] using hm
  refine ⟨m / 2, ?_⟩
  omega

@[simp]
theorem ODD_to_EVEN {n : Int} : ODD n → EVEN (3 * n + 1) := by
  intro hn
  rcases ODD_EX n hn with ⟨m, hm⟩
  subst hm
  simp [EVEN, Int.add_emod, Int.mul_emod]

@[simp]
theorem ODD_to_notODD {n : Int} : ODD n → ¬ ODD (3 * n + 1) := by
  intro hn
  have hEven : EVEN (3 * n + 1) := ODD_to_EVEN hn
  simpa [EVEN_not_ODD] using hEven

/- (*** range ***) -/

theorem fold_range : (∃ a, x = f a) ↔ x ∈ Set.range f := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

noncomputable def is_WR01 (x : Event) : Bool := by
  classical
  exact decide (x ∈ Set.range Event.WR0 ∨ x ∈ Set.range Event.WR1)

/- *********************************************************
           unfolding & folding process names
 ********************************************************* -/

/- computation lemmas for `is_WR01` and the `Rec_prefix` inverses -/

@[simp]
theorem is_WR01_WR0 (m : Int) : is_WR01 (Event.WR0 m) = true := by
  simp [is_WR01]

@[simp]
theorem is_WR01_WR1 (m : Int) : is_WR01 (Event.WR1 m) = true := by
  simp [is_WR01]

@[simp]
theorem is_WR01_RD0 (m : Int) : is_WR01 (Event.RD0 m) = false := by
  simp [is_WR01]

@[simp]
theorem is_WR01_RD1 (m : Int) : is_WR01 (Event.RD1 m) = false := by
  simp [is_WR01]

theorem WR0_inj : Function.Injective Event.WR0 := by
  intro a b h
  injection h

theorem WR1_inj : Function.Injective Event.WR1 := by
  intro a b h
  injection h

@[simp]
theorem invFun_WR0 (m : Int) : Function.invFun Event.WR0 (Event.WR0 m) = m :=
  Function.leftInverse_invFun WR0_inj m

@[simp]
theorem invFun_WR1 (m : Int) : Function.invFun Event.WR1 (Event.WR1 m) = m :=
  Function.leftInverse_invFun WR1_inj m

private theorem VAR_index_set (n : Int) :
    ((Set.range Event.WR0 ∪ Set.range Event.WR1) ∪ ({Event.RD0 n} : Set Event)) ∪
        ({Event.RD1 n} : Set Event) =
      Set.insert (Event.RD1 n)
        (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)) := by
  ext e
  simp [Set.insert, Set.mem_setOf_eq]

/- (*** unfold VAR ***) -/

theorem VAR (n : Int) :
    eqF (proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
      (proc.Ext_pre_choice
        (Set.insert (Event.RD1 n)
          (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)))
        (fun x =>
          IF is_WR01 x
          THEN proc.Proc_name (ImpName.VAR (getInt x))
          ELSE proc.Proc_name (ImpName.VAR n))) := by
  have h0 := «cspF_unwind» (Pf := Impfun) (p0 := ImpName.VAR n) rfl
    (Or.inr (Or.inl ⟨rfl, guarded_Imp⟩))
  simp only [Impfun, Rec_prefix, Set.image_univ] at h0
  refine cspF_trans_left_eq h0 ?_
  -- turn the two `Act_prefix`es into external prefix choices
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong
      (cspF_Ext_choice_cong cspF_reflex_eq_P cspF_Act_prefix_step)
      cspF_Act_prefix_step) ?_
  -- merge the four external prefix choices (left-associated)
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong
      (cspF_Ext_choice_cong cspF_Ext_choice_step cspF_reflex_eq_P)
      cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq
    (cspF_Ext_choice_cong cspF_Ext_choice_step cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq cspF_Ext_choice_step ?_
  rw [VAR_index_set n]
  refine cspF_Ext_pre_choice_cong rfl ?_
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · -- x = RD1 n
    rw [procIte_neg (by simp), procIte_neg (by simp), is_WR01_RD1]
    exact cspF_sym cspF_IF_split
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · -- x = RD0 n
    rw [procIte_neg (by simp), procIte_pos (by simp),
      procIte_neg (by simp), procIte_neg (by simp), is_WR01_RD0]
    exact cspF_sym cspF_IF_split
  rcases hx with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- x = WR0 m
    rw [procIte_neg (by simp), procIte_pos (by simp),
      procIte_neg (by simp), procIte_pos (by simp),
      procIte_neg (by simp), procIte_pos (Set.mem_range_self m),
      invFun_WR0, is_WR01_WR0]
    exact cspF_sym cspF_IF_split
  · -- x = WR1 m
    rw [procIte_neg (by simp), procIte_pos (by simp),
      procIte_neg (by simp), procIte_pos (by simp),
      procIte_neg (by simp), procIte_neg (by simp),
      invFun_WR1, is_WR01_WR1]
    exact cspF_sym cspF_IF_split

theorem VAR_simp (n : Int) :
    eqF (proc.Proc_name (ImpName.VAR n) : proc ImpName Event) MF MF
      (proc.Ext_pre_choice
        (Set.insert (Event.RD1 n)
          (Set.insert (Event.RD0 n) (Set.range Event.WR0 ∪ Set.range Event.WR1)))
        (fun x =>
          IF is_WR01 x
          THEN proc.Proc_name (ImpName.VAR (getInt x))
          ELSE proc.Proc_name (ImpName.VAR n))) :=
  VAR n

/- The Isabelle theorem bundles `unfold_Imp_rules` and `fold_Imp_rules` are
   represented by `VAR_simp` and its `cspF_sym` image. -/

/- (*** unfold TH0 ***) -/

theorem TH0 :
    eqF (proc.Proc_name ImpName.TH0 : proc ImpName Event) MF MF
      (Rec_prefix Event.RD0 Set.univ fun n =>
        IF EVEN n THEN Event.Eat0 ~> proc.Proc_name (ImpName.EAT0 n)
        ELSE Event.Back0 ~> proc.Proc_name ImpName.TH0) := by
  have h :
      eqF (proc.Proc_name ImpName.TH0 : proc ImpName Event) MF MF (Impfun ImpName.TH0) := by
    exact _root_.cspF_unwind (Pf := Impfun) (p0 := ImpName.TH0) rfl
      (Or.inr (Or.inl ⟨FPmode_def, guarded_Imp⟩))
  simpa only [Impfun] using h

theorem TH0_simp :
    eqF (proc.Proc_name ImpName.TH0 : proc ImpName Event) MF MF
      (Rec_prefix Event.RD0 Set.univ fun n =>
        IF EVEN n THEN Event.Eat0 ~> proc.Proc_name (ImpName.EAT0 n)
        ELSE Event.Back0 ~> proc.Proc_name ImpName.TH0) :=
  TH0

/- The Isabelle theorem bundles `unfold_Imp_rules0` and `fold_Imp_rules0` are
   represented by `VAR_simp`, `TH0_simp`, and their `cspF_sym` images. -/

/- (*** unfold TH1 ***) -/

theorem TH1 :
    eqF (proc.Proc_name ImpName.TH1 : proc ImpName Event) MF MF
      (Rec_prefix Event.RD1 Set.univ fun n =>
        IF ODD n THEN Event.Eat1 ~> proc.Proc_name (ImpName.EAT1 n)
        ELSE Event.Back1 ~> proc.Proc_name ImpName.TH1) := by
  have h :
      eqF (proc.Proc_name ImpName.TH1 : proc ImpName Event) MF MF (Impfun ImpName.TH1) := by
    exact _root_.cspF_unwind (Pf := Impfun) (p0 := ImpName.TH1) rfl
      (Or.inr (Or.inl ⟨FPmode_def, guarded_Imp⟩))
  simpa only [Impfun] using h

theorem TH1_simp :
    eqF (proc.Proc_name ImpName.TH1 : proc ImpName Event) MF MF
      (Rec_prefix Event.RD1 Set.univ fun n =>
        IF ODD n THEN Event.Eat1 ~> proc.Proc_name (ImpName.EAT1 n)
        ELSE Event.Back1 ~> proc.Proc_name ImpName.TH1) :=
  TH1

/- The Isabelle theorem bundles `unfold_Imp_rules1` and `fold_Imp_rules1` are
   represented by `VAR_simp`, `TH0_simp`, `TH1_simp`, and their `cspF_sym`
   images. -/

/- (*** unfold EAT0 ***) -/

/- Lean note:
   Isabelle's singleton receiving-prefix syntax is stated here as the
   equivalent direct action-prefix term. -/

theorem EAT0 (n : Int) :
    eqF (proc.Proc_name (ImpName.EAT0 n) : proc ImpName Event) MF MF
      (Event.End0 ~> Event.WR0 (n / 2) ~> proc.Proc_name ImpName.TH0) := by
  have h :
      eqF (proc.Proc_name (ImpName.EAT0 n) : proc ImpName Event) MF MF
        (Impfun (ImpName.EAT0 n)) := by
    exact _root_.cspF_unwind (Pf := Impfun) (p0 := ImpName.EAT0 n) rfl
      (Or.inr (Or.inl ⟨FPmode_def, guarded_Imp⟩))
  simpa only [Impfun] using h

theorem EAT0_simp (n : Int) :
    eqF (proc.Proc_name (ImpName.EAT0 n) : proc ImpName Event) MF MF
      (Event.End0 ~> Event.WR0 (n / 2) ~> proc.Proc_name ImpName.TH0) :=
  EAT0 n

/- The Isabelle theorem bundles `unfold_Imp_rules2` and `fold_Imp_rules2` are
   represented by `VAR_simp`, `TH0_simp`, `TH1_simp`, `EAT0_simp`, and their
   `cspF_sym` images. -/

/- (*** unfold EAT1 ***) -/

theorem EAT1 (n : Int) :
    eqF (proc.Proc_name (ImpName.EAT1 n) : proc ImpName Event) MF MF
      (Event.End1 ~> Event.WR1 (3 * n + 1) ~> proc.Proc_name ImpName.TH1) := by
  have h :
      eqF (proc.Proc_name (ImpName.EAT1 n) : proc ImpName Event) MF MF
        (Impfun (ImpName.EAT1 n)) := by
    exact _root_.cspF_unwind (Pf := Impfun) (p0 := ImpName.EAT1 n) rfl
      (Or.inr (Or.inl ⟨FPmode_def, guarded_Imp⟩))
  simpa only [Impfun] using h

theorem EAT1_simp (n : Int) :
    eqF (proc.Proc_name (ImpName.EAT1 n) : proc ImpName Event) MF MF
      (Event.End1 ~> Event.WR1 (3 * n + 1) ~> proc.Proc_name ImpName.TH1) :=
  EAT1 n

/- The Isabelle theorem bundles `unfold_Imp_rules3` and `fold_Imp_rules3` are
   represented by `VAR_simp`, `TH0_simp`, `TH1_simp`, `EAT0_simp`,
   `EAT1_simp`, and their `cspF_sym` images. -/

end DM1_Imp_def
