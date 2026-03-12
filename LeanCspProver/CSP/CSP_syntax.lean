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
axiom Rep_parallel_empty (PXf : ι → proc p α × Set α) :
    Rep_parallel (p := p) ({} : Set ι) PXf = SKIP

/- ************************************
 |            one Index             |
 ************************************ -/

axiom Rep_parallel_one (PXf : ι → proc p α × Set α) {i : ι} :
    Rep_parallel (p := p) ({i} : Set ι) PXf =
      (Prod.fst (PXf i)) |[Prod.snd (PXf i), {}]| SKIP

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

@[simp] axiom Subst_procfun_Rep_int_choice_set (Xs : Set (Set α)) (Qf : Set α → proc p α)
    (Pf : p → proc q α) :
    (Rep_int_choice_set Xs Qf) << Pf = Rep_int_choice_set Xs (fun X => (Qf X) << Pf)
@[simp] axiom Subst_procfun_Rep_int_choice_nat (N : Set Nat) (Qf : Nat → proc p α)
    (Pf : p → proc q α) :
    (Rep_int_choice_nat N Qf) << Pf = Rep_int_choice_nat N (fun n => (Qf n) << Pf)
@[simp] axiom Subst_procfun_Rep_int_choice_com [Inhabited α] (X : Set α) (Qf : α → proc p α)
    (Pf : p → proc q α) :
    (Rep_int_choice_com X Qf) << Pf = Rep_int_choice_com X (fun x => (Qf x) << Pf)
@[simp] axiom Subst_procfun_Rep_int_choice_f [Inhabited α] [Inhabited β]
    (f : β → α) (X : Set β) (Qf : β → proc p α) (Pf : p → proc q α) :
    (Rep_int_choice_f f X Qf) << Pf = Rep_int_choice_f f X (fun x => (Qf x) << Pf)
@[simp] axiom Subst_procfun_Send_prefix (a : x → α) (v : x) (P : proc p α) (Pf : p → proc q α) :
    (Send_prefix a v P) << Pf = Send_prefix a v (P << Pf)
@[simp] axiom Subst_procfun_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α)
    (Qf : p → proc q α) :
    (Rec_prefix a X Pf) << Qf = Rec_prefix a X (fun x => (Pf x) << Qf)
@[simp] axiom Subst_procfun_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α)
    (Qf : p → proc q α) :
    (Int_pre_choice X Pf) << Qf = Int_pre_choice X (fun x => (Pf x) << Qf)
@[simp] axiom Subst_procfun_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) (Qf : p → proc q α) :
    (Nondet_send_prefix a X Pf) << Qf = Nondet_send_prefix a X (fun x => (Pf x) << Qf)
@[simp] axiom Subst_procfun_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α)
    (Pf : p → proc q α) :
    (Alpha_parallel P X Y Q) << Pf = Alpha_parallel (P << Pf) X Y (Q << Pf)
@[simp] axiom Subst_procfun_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α)
    (Pf : p → proc q α) :
    (Pipe P left mid right Q) << Pf = Pipe (P << Pf) left mid right (Q << Pf)

/- *************************************************************
                   Syntactical functions
 ************************************************************* -/

axiom noPN : proc p α → Prop
axiom gSKIP : proc p α → Prop
axiom noHide : proc p α → Prop
axiom guarded : proc p α → Prop

def noPNfun (Pf : p → proc q α) : Prop := ∀ p, noPN (Pf p)
def gSKIPfun (Pf : p → proc q α) : Prop := ∀ p, gSKIP (Pf p)
def noHidefun (Pf : p → proc q α) : Prop := ∀ p, noHide (Pf p)
def guardedfun (Pf : p → proc q α) : Prop := ∀ p, guarded (Pf p)

@[simp] axiom noPN_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    noPN (Rep_int_choice_set Xs Pf) ↔ (∀ X, noPN (Pf X))
@[simp] axiom noPN_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    noPN (Rep_int_choice_nat N Pf) ↔ (∀ n, noPN (Pf n))
@[simp] axiom noPN_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noPN (Rep_int_choice_com X Pf) ↔ (∀ a, noPN (Pf a))
axiom noPN_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (hf : Injective f) (hPf : ∀ a, noPN (Pf a)) :
    noPN (Rep_int_choice_f (p := p) f X Pf)
@[simp] axiom noPN_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    noPN (Alpha_parallel P X Y Q) ↔ (noPN P ∧ noPN Q)

@[simp] axiom gSKIP_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    gSKIP (Rep_int_choice_set Xs Pf) ↔ (∀ X, gSKIP (Pf X))
@[simp] axiom gSKIP_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    gSKIP (Rep_int_choice_nat N Pf) ↔ (∀ n, gSKIP (Pf n))
@[simp] axiom gSKIP_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    gSKIP (Rep_int_choice_com X Pf) ↔ (∀ a, gSKIP (Pf a))
axiom gSKIP_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (hf : Injective f) (hPf : ∀ a, gSKIP (Pf a)) :
    gSKIP (Rep_int_choice_f (p := p) f X Pf)
@[simp] axiom gSKIP_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    gSKIP (Alpha_parallel P X Y Q) ↔ (gSKIP P ∨ gSKIP Q)

@[simp] axiom noHide_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    noHide (Rep_int_choice_set Xs Pf) ↔ (∀ X, noHide (Pf X))
@[simp] axiom noHide_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    noHide (Rep_int_choice_nat N Pf) ↔ (∀ n, noHide (Pf n))
@[simp] axiom noHide_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noHide (Rep_int_choice_com X Pf) ↔ (∀ a, noHide (Pf a))
axiom noHide_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (hf : Injective f) (hPf : ∀ a, noHide (Pf a)) :
    noHide (Rep_int_choice_f (p := p) f X Pf)
@[simp] axiom noHide_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    noHide (Alpha_parallel P X Y Q) ↔ (noHide P ∧ noHide Q)

@[simp] axiom guarded_Rep_int_choice_set (Xs : Set (Set α)) (Pf : Set α → proc p α) :
    guarded (Rep_int_choice_set Xs Pf) ↔ (∀ X, guarded (Pf X))
@[simp] axiom guarded_Rep_int_choice_nat (N : Set Nat) (Pf : Nat → proc p α) :
    guarded (Rep_int_choice_nat N Pf) ↔ (∀ n, guarded (Pf n))
@[simp] axiom guarded_Rep_int_choice_com [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    guarded (Rep_int_choice_com X Pf) ↔ (∀ a, guarded (Pf a))
axiom guarded_Rep_int_choice_f [Inhabited α] [Inhabited β] {f : β → α} {X : Set β}
    {Pf : β → proc p α} (hf : Injective f) (hPf : ∀ a, guarded (Pf a)) :
    guarded (Rep_int_choice_f (p := p) f X Pf)
@[simp] axiom guarded_Alpha_parallel (P : proc p α) (X Y : Set α) (Q : proc p α) :
    guarded (Alpha_parallel P X Y Q) ↔ (guarded P ∧ guarded Q)

@[simp] axiom noPN_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    noPN (Send_prefix a v P) ↔ noPN P
@[simp] axiom noPN_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noPN (Rec_prefix a X Pf) ↔ (∀ x, noPN (Pf (Function.invFun a x)))
@[simp] axiom noPN_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noPN (Int_pre_choice X Pf) ↔ (∀ x, noPN (Pf x))
@[simp] axiom noPN_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noPN (Nondet_send_prefix a X Pf) ↔ (∀ x, noPN (Pf (Function.invFun a x)))

@[simp] axiom gSKIP_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    gSKIP (Send_prefix a v P)
@[simp] axiom gSKIP_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    gSKIP (Rec_prefix a X Pf)
@[simp] axiom gSKIP_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    gSKIP (Int_pre_choice X Pf)
@[simp] axiom gSKIP_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    gSKIP (Nondet_send_prefix a X Pf)

@[simp] axiom noHide_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    noHide (Send_prefix a v P) ↔ noHide P
@[simp] axiom noHide_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noHide (Rec_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x)))
@[simp] axiom noHide_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    noHide (Int_pre_choice X Pf) ↔ (∀ x, noHide (Pf x))
@[simp] axiom noHide_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    noHide (Nondet_send_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x)))

@[simp] axiom guarded_Send_prefix (a : x → α) (v : x) (P : proc p α) :
    guarded (Send_prefix a v P) ↔ noHide P
@[simp] axiom guarded_Rec_prefix [Inhabited x] (a : x → α) (X : Set x) (Pf : x → proc p α) :
    guarded (Rec_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x)))
@[simp] axiom guarded_Int_pre_choice [Inhabited α] (X : Set α) (Pf : α → proc p α) :
    guarded (Int_pre_choice X Pf) ↔ (∀ x, noHide (Pf x))
@[simp] axiom guarded_Nondet_send_prefix [Inhabited α] [Inhabited x]
    (a : x → α) (X : Set x) (Pf : x → proc p α) :
    guarded (Nondet_send_prefix a X Pf) ↔ (∀ x, noHide (Pf (Function.invFun a x)))

@[simp] axiom noPN_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    noPN (Pipe P left mid right Q) ↔ (noPN P ∧ noPN Q)
@[simp] axiom gSKIP_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    ¬ gSKIP (Pipe P left mid right Q)
@[simp] axiom noHide_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    noHide (Pipe P left mid right Q) ↔ (noPN P ∧ noPN Q)
@[simp] axiom guarded_Pipe (P : proc p α) (left mid right : x → α) (Q : proc p α) :
    guarded (Pipe P left mid right Q) ↔ (noPN P ∧ noPN Q)

axiom noPN_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    noPN P → noPN (P << Pf)
axiom noPN_Subst (P : proc p α) (Pf : p → proc q α) :
    noPN P → noPN (P << Pf)
axiom noPN_Subst_Pf (P : proc p α) (Pf : p → proc q α) :
    noPNfun Pf → noPN (P << Pf)
axiom noHide_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    noHide P ∧ noHidefun Pf → noHide (P << Pf)
axiom noHide_Subst (P : proc p α) (Pf : p → proc q α) :
    noHide P → noHidefun Pf → noHide (P << Pf)
axiom gSKIP_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    gSKIP P → gSKIP (P << Pf)
axiom gSKIP_Subst (P : proc p α) (Pf : p → proc q α) :
    gSKIP P → gSKIP (P << Pf)
axiom guarded_Subst_lm (P : proc p α) (Pf : p → proc q α) :
    guarded P ∧ noHidefun Pf → guarded (P << Pf)
axiom guarded_Subst (P : proc p α) (Pf : p → proc q α) :
    guarded P → noHidefun Pf → guarded (P << Pf)

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

axiom wf_procterm : WellFounded (@procterm p α)

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
