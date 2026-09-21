           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                January 2007  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2007         |
            |                January 2008  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra

open Function
open SumType

set_option autoImplicit true

noncomputable section

/- -----------------------------------------------------------*
 |                                                           |
 |    Process Type Definitions                               |
 |                                                           |
 |             'a proc : type of process expressions         |
 |                       'n : process name                   |
 |                       'a : event                          |
 |                                                           |
 *----------------------------------------------------------- -/

/- *********************************************************************
                       process expression
 ********************************************************************* -/

abbrev sets_nats (α : Type _) := sum (Set (Set α)) (Set Nat)
abbrev aset_anat (α : Type _) := sum (Set α) Nat

inductive proc (p : Type u) (α : Type v) where
  | STOP
  | SKIP
  | DIV
  | Act_prefix : α → proc p α → proc p α
  | Ext_pre_choice : Set α → (α → proc p α) → proc p α
  | Ext_choice : proc p α → proc p α → proc p α
  | Int_choice : proc p α → proc p α → proc p α
  | Rep_int_choice : sets_nats α → (aset_anat α → proc p α) → proc p α
  | IF : Bool → proc p α → proc p α → proc p α
  | Parallel : proc p α → Set α → proc p α → proc p α
  | Hiding : proc p α → Set α → proc p α
  | Renaming : proc p α → Set (α × α) → proc p α
  | Seq_compo : proc p α → proc p α → proc p α
  | Depth_rest : proc p α → Nat → proc p α
  | Proc_name : p → proc p α

open proc

instance : Inhabited (proc p α) := ⟨proc.STOP⟩

infixr:80 " ~> " => proc.Act_prefix
infixl:72 " [+] " => proc.Ext_choice
infixl:64 " |~| " => proc.Int_choice
syntax "IF " term " THEN " term " ELSE " term : term
macro_rules
  | `(IF $b THEN $P ELSE $Q) => `(proc.IF $b $P $Q)
notation:76 P " |[" X "]| " Q => proc.Parallel P X Q
notation:84 P " [[" r "]]" => proc.Renaming P r
infixr:78 " ;; " => proc.Seq_compo
notation:84 P " |. " n => proc.Depth_rest P n

/- Lean note:
   Isabelle's syntax/translations sections are represented here by plain
   definitions and a smaller set of custom notations. -/

/- (*** external prefix ***) -/

noncomputable def the_elem [Inhabited α] (X : Set α) : α :=
  THE fun x => x ∈ X

@[simp]
theorem the_elem_singleton [Inhabited α] {a : α} : the_elem ({a} : Set α) = a := by
  apply chooseOrDefault_eq
  · simp
  · intro x hx
    simpa using hx

/- (*** replicated internal choice (bound variable, UNIV) ***) -/

def Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) : proc p α :=
  proc.Rep_int_choice (type1 Xs) fun c => Pf (Function.invFun type1 c)

theorem Rep_int_choice_set_def (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    Rep_int_choice_set (p := p) Xs Pf =
      proc.Rep_int_choice (type1 Xs) (fun c => Pf (Function.invFun type1 c)) :=
  rfl

def Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) : proc p α :=
  proc.Rep_int_choice (type2 N) fun c => Pf (Function.invFun type2 c)

theorem Rep_int_choice_nat_def (N : Set Nat) (Pf : Nat → proc p α) :
    Rep_int_choice_nat (p := p) N Pf =
      proc.Rep_int_choice (type2 N) (fun c => Pf (Function.invFun type2 c)) :=
  rfl

def Rep_int_choice_com [Inhabited α] (A : Set α) (Pf : α → proc p α) : proc p α :=
  Rep_int_choice_set {X | ∃ a, a ∈ A ∧ X = ({a} : Set α)} fun X => Pf (the_elem X)

theorem Rep_int_choice_com_def [Inhabited α] (A : Set α) (Pf : α → proc p α) :
    Rep_int_choice_com (p := p) A Pf =
      Rep_int_choice_set {X | ∃ a, a ∈ A ∧ X = ({a} : Set α)} (fun X => Pf (the_elem X)) :=
  rfl

def Rep_int_choice_f [Inhabited α] [Inhabited β] (f : β → α) (X : Set β) (Pf : β → proc p α) :
    proc p α :=
  Rep_int_choice_com (f '' X) fun x => Pf (Function.invFun f x)

theorem Rep_int_choice_f_def [Inhabited α] [Inhabited β] (f : β → α) (X : Set β)
    (Pf : β → proc p α) :
    Rep_int_choice_f (p := p) f X Pf =
      Rep_int_choice_com (f '' X) (fun x => Pf (Function.invFun f x)) :=
  rfl

/- (*** internal prefix choice ***) -/

def Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) : proc p α :=
  Rep_int_choice_com X fun x => proc.Act_prefix x (Pf x)

theorem Int_pre_choice_def [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    Int_pre_choice (p := p) X Pf = Rep_int_choice_com X (fun x => proc.Act_prefix x (Pf x)) :=
  rfl

/- (*** sending and receiving prefixes ***) -/

def Send_prefix (a : x → α) (x : x) (P : proc p α) : proc p α :=
  a x ~> P

theorem Send_prefix_def (a : x → α) (x : x) (P : proc p α) :
    Send_prefix (p := p) a x P = a x ~> P :=
  rfl

def Nondet_send_prefix [Inhabited α] [Inhabited x] (f : x → α) (X : Set x) (Pf : x → proc p α) :
    proc p α :=
  Int_pre_choice (f '' X) fun x => Pf (Function.invFun f x)

theorem Nondet_send_prefix_def [Inhabited α] [Inhabited x] (f : x → α) (X : Set x)
    (Pf : x → proc p α) :
    Nondet_send_prefix (p := p) f X Pf =
      Int_pre_choice (f '' X) (fun x => Pf (Function.invFun f x)) :=
  rfl

def Rec_prefix [Inhabited x] (f : x → α) (X : Set x) (Pf : x → proc p α) : proc p α :=
  proc.Ext_pre_choice (f '' X) fun x => Pf (Function.invFun f x)

theorem Rec_prefix_def [Inhabited x] (f : x → α) (X : Set x) (Pf : x → proc p α) :
    Rec_prefix (p := p) f X Pf =
      proc.Ext_pre_choice (f '' X) (fun x => Pf (Function.invFun f x)) :=
  rfl

/- (*** parallel ***) -/

abbrev Interleave (P Q : proc p α) : proc p α := P |[{}]| Q
abbrev Synchro (P Q : proc p α) : proc p α := P |[Set.univ]| Q

def Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) : proc p α :=
  (P |[Xᶜ]| SKIP) |[X ∩ Y]| (Q |[Yᶜ]| SKIP)

theorem Alpha_parallel_def (P : proc p α) (X Y : Set α) (Q : proc p α) :
    Alpha_parallel P X Y Q = (P |[Xᶜ]| SKIP) |[X ∩ Y]| (Q |[Yᶜ]| SKIP) :=
  rfl

notation:76 P " |[" X "," Y "]| " Q => Alpha_parallel P X Y Q

def Inductive_parallel : List (proc p α × Set α) → proc p α
  | [] => SKIP
  | PX :: PXs =>
      (Prod.fst PX) |[Prod.snd PX, Set.sUnion (Prod.snd '' set PXs)]| Inductive_parallel PXs

def Rep_parallel (I : Set ι) (PXf : ι → proc p α × Set α) : proc p α :=
  Inductive_parallel (List.map PXf (SOME fun Is : List ι => isListOf Is I))

theorem Rep_parallel_def (I : Set ι) (PXf : ι → proc p α × Set α) :
    Rep_parallel (p := p) I PXf =
      Inductive_parallel (List.map PXf (SOME fun Is : List ι => isListOf Is I)) :=
  rfl

/- ************************************
 |           empty Index            |
 ************************************ -/

@[simp]
theorem Rep_parallel_empty (PXf : ι → proc p α × Set α) :
    Rep_parallel (p := p) ({} : Set ι) PXf = SKIP := by
  rw [Rep_parallel_def]
  have hset : _root_.set ([] : List ι) = (∅ : Set ι) := by
    ext x
    simp [_root_.set]
  have h : (SOME fun Is : List ι => isListOf Is ({} : Set ι)) = ([] : List ι) := by
    refine chooseOrDefault_eq ⟨hset.symm, by rw [hset]; simp⟩ ?_
    intro y hy
    obtain ⟨hy1, -⟩ := hy
    refine List.eq_nil_iff_forall_not_mem.mpr ?_
    intro x hx
    have hmem : x ∈ (∅ : Set ι) := by
      rw [hy1]
      exact hx
    exact hmem
  rw [h]
  rfl

/- ************************************
 |            one Index             |
 ************************************ -/

theorem Rep_parallel_one (PXf : ι → proc p α × Set α) {i : ι} :
    Rep_parallel (p := p) ({i} : Set ι) PXf =
      (Prod.fst (PXf i)) |[Prod.snd (PXf i), {}]| SKIP := by
  rw [Rep_parallel_def]
  have hset : _root_.set ([i] : List ι) = ({i} : Set ι) := by
    ext x
    simp [_root_.set]
  have h : (SOME fun Is : List ι => isListOf Is ({i} : Set ι)) = ([i] : List ι) := by
    refine chooseOrDefault_eq ⟨hset.symm, by rw [hset]; simp⟩ ?_
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [← hy1] at hy2
    have hlen : y.length = 1 := by
      rw [← hy2]
      simp
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hx : x = i := by
      have hmem : x ∈ ({i} : Set ι) := by
        rw [hy1]
        simp [_root_.set]
      simpa using hmem
    rw [hx]
  rw [h]
  simp [Inductive_parallel, _root_.set]

/- (*** timeout ***) -/

abbrev Timeout_abb (P Q : proc p α) : proc p α := (P |~| STOP) [+] Q

infixl:73 " [> " => Timeout_abb

def Timeout (P Q : proc p α) : proc p α := P [> Q

theorem Timeout_def (P Q : proc p α) : Timeout P Q = P [> Q := rfl

/- ************************************
 |       Renaming by lists          |
 ************************************ -/

def Renaming_List (P : proc p α) : List (Set (α × α)) → proc p α
  | [] => P
  | r :: rs => Renaming_List (P[[r]]) rs

/- --------------------------------------------------- *
             pipe operator (CSP-Prover 5)
 * --------------------------------------------------- -/

def Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) : proc p α :=
  proc.Hiding
    (Alpha_parallel (P[[right <==> mid]]) (Set.range left ∪ Set.range mid)
      (Set.range mid ∪ Set.range right) (Q[[left <==> mid]]))
    (Set.range mid)

theorem Pipe_def (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    Pipe P left mid right Q =
      proc.Hiding
        (Alpha_parallel (P[[right <==> mid]]) (Set.range left ∪ Set.range mid)
          (Set.range mid ∪ Set.range right) (Q[[left <==> mid]]))
        (Set.range mid) :=
  rfl

/- ===================================================================*

(1) We assume that a process-name-function PNfun is given for
    defining the meaning of each process-name.

    Lean note: Isabelle's overloaded constant is represented by a
    typeclass.

(2) There are two kinds of approahes for fixed points, i.e.
    cms and cpo approaches.

 *================================================================== -/

abbrev pnfun (p : Type u) (α : Type v) := p → proc p α

class HasPNfun (p : Type u) (α : Type v) where
  PNfun : pnfun p α

export HasPNfun (PNfun)

inductive fpmode where
  | CPOmode
  | CMSmode
  | MIXmode

open fpmode

class HasFPmode where
  FPmode : fpmode

export HasFPmode (FPmode)

theorem CPOmode_or_CMSmode_or_MIXmode_lm [HasFPmode] (m : fpmode) :
    m = FPmode → m = CPOmode ∨ m = CMSmode ∨ m = MIXmode := by
  intro hm
  subst hm
  cases FPmode <;> simp

theorem CPOmode_or_CMSmode_or_MIXmode [HasFPmode] :
    FPmode = CPOmode ∨ FPmode = CMSmode ∨ FPmode = MIXmode :=
  CPOmode_or_CMSmode_or_MIXmode_lm FPmode rfl

/- -------*
 | CHAOS |
 *------- -/

/- This CHAOS may cause some error on process definition ... ? -/

inductive ChaosName (α : Type _) where
  | Chaos : Set α → ChaosName α

open ChaosName

def Chaosfun [Inhabited α] : ChaosName α → proc (ChaosName α) α
  | Chaos A => Int_pre_choice A (fun _ => proc.Proc_name (Chaos A)) |~| STOP

instance Set_Chaosfun [Inhabited α] : HasPNfun (ChaosName α) α where
  PNfun := Chaosfun

@[simp]
theorem Set_Chaosfun_def [Inhabited α] (pn : ChaosName α) :
    PNfun pn = Chaosfun pn :=
  rfl

def CHAOS (A : Set α) : proc (ChaosName α) α := proc.Proc_name (Chaos A)

theorem CHAOS_def (A : Set α) : CHAOS A = proc.Proc_name (Chaos A) := rfl

/- *********************************************************************
            substitution by functions : 'p => ('a,'p) proc
 ********************************************************************* -/

def Subst_procfun (P : proc p α) (Pf : p → proc q α) : proc q α :=
  match P with
  | STOP => STOP
  | SKIP => SKIP
  | DIV => DIV
  | a ~> P => a ~> Subst_procfun P Pf
  | proc.Ext_pre_choice X Qf => proc.Ext_pre_choice X fun a => Subst_procfun (Qf a) Pf
  | P [+] Q => Subst_procfun P Pf [+] Subst_procfun Q Pf
  | P |~| Q => Subst_procfun P Pf |~| Subst_procfun Q Pf
  | proc.Rep_int_choice C Qf => proc.Rep_int_choice C fun c => Subst_procfun (Qf c) Pf
  | proc.IF b P Q => proc.IF b (Subst_procfun P Pf) (Subst_procfun Q Pf)
  | proc.Parallel P X Q => proc.Parallel (Subst_procfun P Pf) X (Subst_procfun Q Pf)
  | proc.Hiding P X => proc.Hiding (Subst_procfun P Pf) X
  | proc.Renaming P r => proc.Renaming (Subst_procfun P Pf) r
  | proc.Seq_compo P Q => proc.Seq_compo (Subst_procfun P Pf) (Subst_procfun Q Pf)
  | proc.Depth_rest P n => proc.Depth_rest (Subst_procfun P Pf) n
  | proc.Proc_name p => Pf p

infixl:1000 " << " => Subst_procfun

def Subst_procfun_prod (Pf : p → proc q α) (Qf : q → proc r α) : p → proc r α :=
  fun p => (Pf p) << Qf

infixr:1000 " <<< " => Subst_procfun_prod

theorem Subst_procfun_prod_p (Pf : p → proc q α) (Qf : q → proc r α) (p0 : p) :
    (Pf <<< Qf) p0 = (Pf p0) << Qf :=
  rfl

/- for sending and receiving -/

@[simp] theorem Subst_procfun_Rep_int_choice_set (Xs : Set (Set α)) (Qf : Set α → proc p α)
    (Pf : p → proc q α) :
    (Rep_int_choice_set Xs Qf) << Pf = Rep_int_choice_set Xs (fun X => (Qf X) << Pf) :=
  rfl
@[simp] theorem Subst_procfun_Rep_int_choice_nat (N : Set Nat) (Qf : Nat → proc p α)
    (Pf : p → proc q α) :
    (Rep_int_choice_nat N Qf) << Pf = Rep_int_choice_nat N (fun n => (Qf n) << Pf) :=
  rfl
@[simp] theorem Subst_procfun_Rep_int_choice_com [Inhabited α] (X : Set α) (Qf : α → proc p α)
    (Pf : p → proc q α) :
    (Rep_int_choice_com X Qf) << Pf = Rep_int_choice_com X (fun x => (Qf x) << Pf) :=
  rfl
@[simp] theorem Subst_procfun_Rep_int_choice_f [Inhabited α] [Inhabited β]
    (f : β → α) (X : Set β) (Qf : β → proc p α) (Pf : p → proc q α) :
    (Rep_int_choice_f f X Qf) << Pf = Rep_int_choice_f f X (fun x => (Qf x) << Pf) :=
  rfl
@[simp] theorem Subst_procfun_Send_prefix (a : x → α) (v : x) (P : proc p α) (Pf : p → proc q α) :
    (Send_prefix a v P) << Pf = Send_prefix a v (P << Pf) :=
  rfl
@[simp] theorem Subst_procfun_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α)
    (Qf : p → proc q α) :
    (Rec_prefix a X Pf) << Qf = Rec_prefix a X (fun x => (Pf x) << Qf) :=
  rfl
@[simp] theorem Subst_procfun_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α)
    (Qf : p → proc q α) :
    (Int_pre_choice X Pf) << Qf = Int_pre_choice X (fun x => (Pf x) << Qf) :=
  rfl
@[simp] theorem Subst_procfun_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) (Qf : p → proc q α) :
    (Nondet_send_prefix a X Pf) << Qf = Nondet_send_prefix a X (fun x => (Pf x) << Qf) :=
  rfl
@[simp] theorem Subst_procfun_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α)
    (Pf : p → proc q α) :
    (Alpha_parallel P X Y Q) << Pf = Alpha_parallel (P << Pf) X Y (Q << Pf) :=
  rfl
@[simp] theorem Subst_procfun_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α)
    (Pf : p → proc q α) :
    (Pipe P left mid right Q) << Pf = Pipe (P << Pf) left mid right (Q << Pf) :=
  rfl

/- *************************************************************
                   Syntactical functions
 ************************************************************* -/

/-- No process name occurs in `P` (Isabelle: `primrec noPN`). -/
def noPN : proc p α → Prop
  | STOP => True
  | SKIP => True
  | DIV => True
  | Act_prefix _ P => noPN P
  | proc.Ext_pre_choice _ Pf => ∀ a, noPN (Pf a)
  | Ext_choice P Q => noPN P ∧ noPN Q
  | Int_choice P Q => noPN P ∧ noPN Q
  | proc.Rep_int_choice _ Pf => ∀ c, noPN (Pf c)
  | proc.IF _ P Q => noPN P ∧ noPN Q
  | proc.Parallel P _ Q => noPN P ∧ noPN Q
  | proc.Hiding P _ => noPN P
  | proc.Renaming P _ => noPN P
  | proc.Seq_compo P Q => noPN P ∧ noPN Q
  | proc.Depth_rest P _ => noPN P
  | proc.Proc_name _ => False

/-- `P` cannot terminate immediately ("guarded SKIP"; Isabelle: `primrec gSKIP`). -/
def gSKIP : proc p α → Prop
  | STOP => True
  | SKIP => False
  | DIV => True
  | Act_prefix _ _ => True
  | proc.Ext_pre_choice _ _ => True
  | Ext_choice P Q => gSKIP P ∧ gSKIP Q
  | Int_choice P Q => gSKIP P ∧ gSKIP Q
  | proc.Rep_int_choice _ Pf => ∀ c, gSKIP (Pf c)
  | proc.IF _ P Q => gSKIP P ∧ gSKIP Q
  | proc.Parallel P _ Q => gSKIP P ∨ gSKIP Q
  | proc.Hiding _ _ => False
  | proc.Renaming P _ => gSKIP P
  | proc.Seq_compo P Q => gSKIP P ∨ gSKIP Q
  | proc.Depth_rest P n => gSKIP P ∨ n = 0
  | proc.Proc_name _ => False

/-- No hiding occurs in `P` outside a name-free part (Isabelle: `primrec noHide`). -/
def noHide : proc p α → Prop
  | STOP => True
  | SKIP => True
  | DIV => True
  | Act_prefix _ P => noHide P
  | proc.Ext_pre_choice _ Pf => ∀ a, noHide (Pf a)
  | Ext_choice P Q => noHide P ∧ noHide Q
  | Int_choice P Q => noHide P ∧ noHide Q
  | proc.Rep_int_choice _ Pf => ∀ c, noHide (Pf c)
  | proc.IF _ P Q => noHide P ∧ noHide Q
  | proc.Parallel P _ Q => noHide P ∧ noHide Q
  | proc.Hiding P _ => noPN P
  | proc.Renaming P _ => noHide P
  | proc.Seq_compo P Q => noHide P ∧ noHide Q
  | proc.Depth_rest P n => noHide P ∨ n = 0
  | proc.Proc_name _ => True

/-- Every process name in `P` is guarded (Isabelle: `primrec guarded`). -/
def guarded : proc p α → Prop
  | STOP => True
  | SKIP => True
  | DIV => True
  | Act_prefix _ P => noHide P
  | proc.Ext_pre_choice _ Pf => ∀ a, noHide (Pf a)
  | Ext_choice P Q => guarded P ∧ guarded Q
  | Int_choice P Q => guarded P ∧ guarded Q
  | proc.Rep_int_choice _ Pf => ∀ c, guarded (Pf c)
  | proc.IF _ P Q => guarded P ∧ guarded Q
  | proc.Parallel P _ Q => guarded P ∧ guarded Q
  | proc.Hiding P _ => noPN P
  | proc.Renaming P _ => guarded P
  | proc.Seq_compo P Q => (guarded P ∧ gSKIP P ∧ noHide Q) ∨ (guarded P ∧ guarded Q)
  | proc.Depth_rest P n => guarded P ∨ n = 0
  | proc.Proc_name _ => False

def noPNfun (Pf : p → proc q α) : Prop := ∀ p, noPN (Pf p)
def gSKIPfun (Pf : p → proc q α) : Prop := ∀ p, gSKIP (Pf p)
def noHidefun (Pf : p → proc q α) : Prop := ∀ p, noHide (Pf p)
def guardedfun (Pf : p → proc q α) : Prop := ∀ p, guarded (Pf p)

/- computation rules for the derived operators -/

private theorem type1_injective {α β : Type _} :
    Function.Injective (type1 : α → sum α β) := by
  intro a b h
  cases h
  rfl

private theorem type2_injective {α β : Type _} :
    Function.Injective (type2 : β → sum α β) := by
  intro a b h
  cases h
  rfl

private theorem invFun_type1 {α β : Type _} [Nonempty α] {X : α} :
    Function.invFun (type1 : α → sum α β) (type1 X) = X :=
  Function.leftInverse_invFun type1_injective X

private theorem invFun_type2 {α β : Type _} [Nonempty β] {n : β} :
    Function.invFun (type2 : β → sum α β) (type2 n) = n :=
  Function.leftInverse_invFun type2_injective n

/-- The `!! :C ..`-clause of the four predicates ranges over *all* indices,
    so on `Rep_int_choice_set` it is equivalent to ranging over all sets. -/
private theorem pred_Rep_int_choice_set_iff {Pf : Set α → proc p α}
    {pred : proc p α → Prop} :
    (∀ c : aset_anat α, pred (Pf (Function.invFun type1 c))) ↔
      (∀ X, pred (Pf X)) := by
  constructor
  · intro h X
    simpa [invFun_type1] using h (type1 X)
  · intro h c
    exact h _

private theorem pred_Rep_int_choice_nat_iff {Pf : Nat → proc p α}
    {pred : proc p α → Prop} :
    (∀ c : aset_anat α, pred (Pf (Function.invFun type2 c))) ↔
      (∀ n, pred (Pf n)) := by
  constructor
  · intro h n
    simpa [invFun_type2] using h (type2 n)
  · intro h c
    exact h _

@[simp] theorem noPN_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    noPN (Rep_int_choice_set Xs Pf) ↔ (∀ X, noPN (Pf X)) :=
  pred_Rep_int_choice_set_iff
@[simp] theorem noPN_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    noPN (Rep_int_choice_nat N Pf) ↔ (∀ n, noPN (Pf n)) :=
  pred_Rep_int_choice_nat_iff
@[simp] theorem noPN_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noPN (Rep_int_choice_com X Pf) ↔ (∀ a, noPN (Pf a)) := by
  rw [Rep_int_choice_com, noPN_Rep_int_choice_set]
  constructor
  · intro h a
    simpa using h {a}
  · intro h X
    exact h _
theorem noPN_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (_hf : Injective f) (hPf : ∀ a, noPN (Pf a)) :
    noPN (Rep_int_choice_f (p := p) f X Pf) := by
  rw [Rep_int_choice_f, noPN_Rep_int_choice_com]
  intro a
  exact hPf _
@[simp] theorem noPN_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    noPN (Alpha_parallel P X Y Q) ↔ (noPN P ∧ noPN Q) := by
  simp [Alpha_parallel, noPN]

@[simp] theorem gSKIP_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    gSKIP (Rep_int_choice_set Xs Pf) ↔ (∀ X, gSKIP (Pf X)) :=
  pred_Rep_int_choice_set_iff
@[simp] theorem gSKIP_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    gSKIP (Rep_int_choice_nat N Pf) ↔ (∀ n, gSKIP (Pf n)) :=
  pred_Rep_int_choice_nat_iff
@[simp] theorem gSKIP_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    gSKIP (Rep_int_choice_com X Pf) ↔ (∀ a, gSKIP (Pf a)) := by
  rw [Rep_int_choice_com, gSKIP_Rep_int_choice_set]
  constructor
  · intro h a
    simpa using h {a}
  · intro h X
    exact h _
theorem gSKIP_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (_hf : Injective f) (hPf : ∀ a, gSKIP (Pf a)) :
    gSKIP (Rep_int_choice_f (p := p) f X Pf) := by
  rw [Rep_int_choice_f, gSKIP_Rep_int_choice_com]
  intro a
  exact hPf _
@[simp] theorem gSKIP_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    gSKIP (Alpha_parallel P X Y Q) ↔ (gSKIP P ∨ gSKIP Q) := by
  simp [Alpha_parallel, gSKIP]

@[simp] theorem noHide_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    noHide (Rep_int_choice_set Xs Pf) ↔ (∀ X, noHide (Pf X)) :=
  pred_Rep_int_choice_set_iff
@[simp] theorem noHide_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    noHide (Rep_int_choice_nat N Pf) ↔ (∀ n, noHide (Pf n)) :=
  pred_Rep_int_choice_nat_iff
@[simp] theorem noHide_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noHide (Rep_int_choice_com X Pf) ↔ (∀ a, noHide (Pf a)) := by
  rw [Rep_int_choice_com, noHide_Rep_int_choice_set]
  constructor
  · intro h a
    simpa using h {a}
  · intro h X
    exact h _
theorem noHide_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (_hf : Injective f) (hPf : ∀ a, noHide (Pf a)) :
    noHide (Rep_int_choice_f (p := p) f X Pf) := by
  rw [Rep_int_choice_f, noHide_Rep_int_choice_com]
  intro a
  exact hPf _
@[simp] theorem noHide_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    noHide (Alpha_parallel P X Y Q) ↔ (noHide P ∧ noHide Q) := by
  simp [Alpha_parallel, noHide]

@[simp] theorem guarded_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    guarded (Rep_int_choice_set Xs Pf) ↔ (∀ X, guarded (Pf X)) :=
  pred_Rep_int_choice_set_iff
@[simp] theorem guarded_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    guarded (Rep_int_choice_nat N Pf) ↔ (∀ n, guarded (Pf n)) :=
  pred_Rep_int_choice_nat_iff
@[simp] theorem guarded_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    guarded (Rep_int_choice_com X Pf) ↔ (∀ a, guarded (Pf a)) := by
  rw [Rep_int_choice_com, guarded_Rep_int_choice_set]
  constructor
  · intro h a
    simpa using h {a}
  · intro h X
    exact h _
theorem guarded_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (_hf : Injective f) (hPf : ∀ a, guarded (Pf a)) :
    guarded (Rep_int_choice_f (p := p) f X Pf) := by
  rw [Rep_int_choice_f, guarded_Rep_int_choice_com]
  intro a
  exact hPf _
@[simp] theorem guarded_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    guarded (Alpha_parallel P X Y Q) ↔ (guarded P ∧ guarded Q) := by
  simp [Alpha_parallel, guarded]

@[simp] theorem noPN_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    noPN (Send_prefix a v P) ↔ noPN P :=
  Iff.rfl
@[simp] theorem noPN_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noPN (Rec_prefix a X Pf) ↔ (∀ x, noPN (Pf (Function.invFun a x))) :=
  Iff.rfl
@[simp] theorem noPN_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noPN (Int_pre_choice X Pf) ↔ (∀ x, noPN (Pf x)) := by
  rw [Int_pre_choice, noPN_Rep_int_choice_com]
  exact Iff.rfl
@[simp] theorem noPN_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noPN (Nondet_send_prefix a X Pf) ↔ (∀ x, noPN (Pf (Function.invFun a x))) := by
  rw [Nondet_send_prefix, noPN_Int_pre_choice]

@[simp] theorem gSKIP_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    gSKIP (Send_prefix a v P) :=
  trivial
@[simp] theorem gSKIP_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    gSKIP (Rec_prefix a X Pf) :=
  trivial
@[simp] theorem gSKIP_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    gSKIP (Int_pre_choice X Pf) := by
  rw [Int_pre_choice, gSKIP_Rep_int_choice_com]
  intro a
  trivial
@[simp] theorem gSKIP_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    gSKIP (Nondet_send_prefix a X Pf) :=
  gSKIP_Int_pre_choice _ _

@[simp] theorem noHide_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    noHide (Send_prefix a v P) ↔ noHide P :=
  Iff.rfl
@[simp] theorem noHide_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noHide (Rec_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x))) :=
  Iff.rfl
@[simp] theorem noHide_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noHide (Int_pre_choice X Pf) ↔ (∀ x, noHide (Pf x)) := by
  rw [Int_pre_choice, noHide_Rep_int_choice_com]
  exact Iff.rfl
@[simp] theorem noHide_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noHide (Nondet_send_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x))) := by
  rw [Nondet_send_prefix, noHide_Int_pre_choice]

@[simp] theorem guarded_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    guarded (Send_prefix a v P) ↔ noHide P :=
  Iff.rfl
@[simp] theorem guarded_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    guarded (Rec_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x))) :=
  Iff.rfl
@[simp] theorem guarded_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    guarded (Int_pre_choice X Pf) ↔ (∀ x, noHide (Pf x)) := by
  rw [Int_pre_choice, guarded_Rep_int_choice_com]
  exact forall_congr' fun x => Iff.rfl
@[simp] theorem guarded_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    guarded (Nondet_send_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x))) := by
  rw [Nondet_send_prefix, guarded_Int_pre_choice]

@[simp] theorem noPN_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    noPN (Pipe P left mid right Q) ↔ (noPN P ∧ noPN Q) := by
  simp [Pipe, noPN]
@[simp] theorem gSKIP_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    ¬ gSKIP (Pipe P left mid right Q) := by
  simp [Pipe, gSKIP]
@[simp] theorem noHide_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    noHide (Pipe P left mid right Q) ↔ (noPN P ∧ noPN Q) := by
  simp [Pipe, noHide, noPN]
@[simp] theorem guarded_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    guarded (Pipe P left mid right Q) ↔ (noPN P ∧ noPN Q) := by
  simp [Pipe, guarded, noPN]

/- substitution preserves the syntactical predicates -/

theorem noPN_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    noPN P → noPN (P << Pf) := by
  induction P with
  | STOP => intro _; trivial
  | SKIP => intro _; trivial
  | DIV => intro _; trivial
  | Act_prefix a P ih => exact ih
  | Ext_pre_choice X Qf ih => exact fun h a => ih a (h a)
  | Ext_choice P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Int_choice P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Rep_int_choice C Qf ih => exact fun h c => ih c (h c)
  | «IF» b P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Parallel P X Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Hiding P X ih => exact ih
  | Renaming P r ih => exact ih
  | Seq_compo P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Depth_rest P n ih => exact ih
  | Proc_name p => exact fun h => h.elim

theorem noPN_Subst (P : proc p α) (Pf : p → proc q α) :
    noPN P → noPN (P << Pf) :=
  noPN_Subst_lm P Pf

theorem noPN_Subst_Pf (P : proc p α) (Pf : p → proc q α) :
    noPNfun Pf → noPN (P << Pf) := by
  intro hPf
  induction P with
  | STOP => trivial
  | SKIP => trivial
  | DIV => trivial
  | Act_prefix a P ih => exact ih
  | Ext_pre_choice X Qf ih => exact fun a => ih a
  | Ext_choice P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | Int_choice P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | Rep_int_choice C Qf ih => exact fun c => ih c
  | «IF» b P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | Parallel P X Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | Hiding P X ih => exact ih
  | Renaming P r ih => exact ih
  | Seq_compo P Q ihP ihQ => exact ⟨ihP, ihQ⟩
  | Depth_rest P n ih => exact ih
  | Proc_name p => exact hPf p

theorem noHide_Subst (P : proc p α) (Pf : p → proc q α) :
    noHide P → noHidefun Pf → noHide (P << Pf) := by
  intro hP hPf
  induction P with
  | STOP => trivial
  | SKIP => trivial
  | DIV => trivial
  | Act_prefix a P ih => exact ih hP
  | Ext_pre_choice X Qf ih => exact fun a => ih a (hP a)
  | Ext_choice P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Int_choice P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Rep_int_choice C Qf ih => exact fun c => ih c (hP c)
  | «IF» b P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Parallel P X Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Hiding P X ih =>
      exact noPN_Subst_lm P Pf hP
  | Renaming P r ih => exact ih hP
  | Seq_compo P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Depth_rest P n ih =>
      rcases hP with hP | hn
      · exact Or.inl (ih hP)
      · exact Or.inr hn
  | Proc_name p => exact hPf p

theorem noHide_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    noHide P ∧ noHidefun Pf → noHide (P << Pf) :=
  fun h => noHide_Subst P Pf h.1 h.2

theorem gSKIP_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    gSKIP P → gSKIP (P << Pf) := by
  induction P with
  | STOP => intro _; trivial
  | SKIP => exact fun h => h.elim
  | DIV => intro _; trivial
  | Act_prefix a P ih => intro _; trivial
  | Ext_pre_choice X Qf ih => intro _; trivial
  | Ext_choice P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Int_choice P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Rep_int_choice C Qf ih => exact fun h c => ih c (h c)
  | «IF» b P Q ihP ihQ => exact fun h => ⟨ihP h.1, ihQ h.2⟩
  | Parallel P X Q ihP ihQ =>
      rintro (h | h)
      · exact Or.inl (ihP h)
      · exact Or.inr (ihQ h)
  | Hiding P X ih => exact fun h => h.elim
  | Renaming P r ih => exact ih
  | Seq_compo P Q ihP ihQ =>
      rintro (h | h)
      · exact Or.inl (ihP h)
      · exact Or.inr (ihQ h)
  | Depth_rest P n ih =>
      rintro (h | h)
      · exact Or.inl (ih h)
      · exact Or.inr h
  | Proc_name p => exact fun h => h.elim

theorem gSKIP_Subst (P : proc p α) (Pf : p → proc q α) :
    gSKIP P → gSKIP (P << Pf) :=
  gSKIP_Subst_lm P Pf

theorem guarded_Subst (P : proc p α) (Pf : p → proc q α) :
    guarded P → noHidefun Pf → guarded (P << Pf) := by
  intro hP hPf
  induction P with
  | STOP => trivial
  | SKIP => trivial
  | DIV => trivial
  | Act_prefix a P ih => exact noHide_Subst P Pf hP hPf
  | Ext_pre_choice X Qf ih => exact fun a => noHide_Subst (Qf a) Pf (hP a) hPf
  | Ext_choice P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Int_choice P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Rep_int_choice C Qf ih => exact fun c => ih c (hP c)
  | «IF» b P Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Parallel P X Q ihP ihQ => exact ⟨ihP hP.1, ihQ hP.2⟩
  | Hiding P X ih => exact noPN_Subst_lm P Pf hP
  | Renaming P r ih => exact ih hP
  | Seq_compo P Q ihP ihQ =>
      rcases hP with ⟨hgP, hsP, hnQ⟩ | ⟨hgP, hgQ⟩
      · exact Or.inl ⟨ihP hgP, gSKIP_Subst_lm P Pf hsP, noHide_Subst Q Pf hnQ hPf⟩
      · exact Or.inr ⟨ihP hgP, ihQ hgQ⟩
  | Depth_rest P n ih =>
      rcases hP with hP | hn
      · exact Or.inl (ih hP)
      · exact Or.inr hn
  | Proc_name p => exact hP.elim

theorem guarded_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    guarded P ∧ noHidefun Pf → guarded (P << Pf) :=
  fun h => guarded_Subst P Pf h.1 h.2

/- *********************************************************
             termination relation for proc
 ********************************************************* -/

inductive procterm : proc p α → proc p α → Prop where
  | Act_prefix (a : α) (P : proc p α) : procterm P (a ~> P)
  | Ext_pre_choice (Pf : α → proc p α) (X : Set α) (a : α) :
      procterm (Pf a) (proc.Ext_pre_choice X Pf)
  | Ext_choice_l (P Q : proc p α) : procterm P (P [+] Q)
  | Ext_choice_r (P Q : proc p α) : procterm Q (P [+] Q)
  | Int_choice_l (P Q : proc p α) : procterm P (P |~| Q)
  | Int_choice_r (P Q : proc p α) : procterm Q (P |~| Q)
  | Rep_int_choice (Pf : aset_anat α → proc p α) (C : sets_nats α) (c : aset_anat α) :
      procterm (Pf c) (proc.Rep_int_choice C Pf)
  | IF_l (b : Bool) (P Q : proc p α) : procterm P (IF b THEN P ELSE Q)
  | IF_r (b : Bool) (P Q : proc p α) : procterm Q (IF b THEN P ELSE Q)
  | Parallel_l (P Q : proc p α) (X : Set α) : procterm P (P |[X]| Q)
  | Parallel_r (P Q : proc p α) (X : Set α) : procterm Q (P |[X]| Q)
  | Hiding (P : proc p α) (X : Set α) : procterm P (proc.Hiding P X)
  | Renaming (P : proc p α) (r : Set (α × α)) : procterm P (P[[r]])
  | Seq_compo_l (P Q : proc p α) : procterm P (P ;; Q)
  | Seq_compo_r (P Q : proc p α) : procterm Q (P ;; Q)
  | Depth_rest (P : proc p α) (n : Nat) : procterm P (P |. n)

theorem wf_procterm : WellFounded (@procterm p α) := by
  constructor
  intro P
  induction P with
  | STOP =>
      constructor
      intro y h
      cases h
  | SKIP =>
      constructor
      intro y h
      cases h
  | DIV =>
      constructor
      intro y h
      cases h
  | Act_prefix a P ih =>
      constructor
      intro y h
      cases h
      exact ih
  | Ext_pre_choice X Pf ih =>
      constructor
      intro y h
      cases h
      exact ih _
  | Ext_choice P Q ihP ihQ =>
      constructor
      intro y h
      cases h
      · exact ihP
      · exact ihQ
  | Int_choice P Q ihP ihQ =>
      constructor
      intro y h
      cases h
      · exact ihP
      · exact ihQ
  | Rep_int_choice C Pf ih =>
      constructor
      intro y h
      cases h
      exact ih _
  | «IF» b P Q ihP ihQ =>
      constructor
      intro y h
      cases h
      · exact ihP
      · exact ihQ
  | Parallel P X Q ihP ihQ =>
      constructor
      intro y h
      cases h
      · exact ihP
      · exact ihQ
  | Hiding P X ih =>
      constructor
      intro y h
      cases h
      exact ih
  | Renaming P r ih =>
      constructor
      intro y h
      cases h
      exact ih
  | Seq_compo P Q ihP ihQ =>
      constructor
      intro y h
      cases h
      · exact ihP
      · exact ihQ
  | Depth_rest P n ih =>
      constructor
      intro y h
      cases h
      exact ih
  | Proc_name pn =>
      constructor
      intro y h
      cases h

/- -------------------------------------------------------*
 |                                                       |
 |      decompostion controlled by Not_Decompo_Flag      |
 |                                                       |
 *------------------------------------------------------- -/

def Not_Decompo_Flag : Prop := True

theorem Not_Decompo_Flag_def : Not_Decompo_Flag ↔ True := Iff.rfl

theorem on_Not_Decompo_Flag (R : Prop) : Not_Decompo_Flag ∧ R → R := by
  simp [Not_Decompo_Flag]

theorem off_Not_Decompo_Flag (R : Prop) : R → Not_Decompo_Flag ∧ R := by
  simp [Not_Decompo_Flag]

theorem off_Not_Decompo_Flag_True : Not_Decompo_Flag := by
  simp [Not_Decompo_Flag]

/- -------------------------------------------------------*
 |                                                       |
 |        rewriting controlled by Not_Rewrite_Flag       |
 |                      CSP-Prover 5                     |
 *------------------------------------------------------- -/

def Not_Rewrite_Flag : Prop := True

theorem Not_Rewrite_Flag_def : Not_Rewrite_Flag ↔ True := Iff.rfl

theorem on_Not_Rewrite_Flag (R : Prop) : Not_Rewrite_Flag ∧ R → R := by
  simp [Not_Rewrite_Flag]

theorem off_Not_Rewrite_Flag (R : Prop) : R → Not_Rewrite_Flag ∧ R := by
  simp [Not_Rewrite_Flag]

theorem off_Not_Rewrite_Flag_True : Not_Rewrite_Flag := by
  simp [Not_Rewrite_Flag]

theorem off_All_Flag_True : Not_Decompo_Flag ∧ Not_Rewrite_Flag := by
  simp [Not_Decompo_Flag, Not_Rewrite_Flag]

end
