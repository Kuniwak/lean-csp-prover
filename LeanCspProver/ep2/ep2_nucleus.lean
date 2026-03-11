           /- -------------------------------------------*
            |                 (a part of) ep2            |
            |                  September 2004            |
            |                   December 2004 (modified) |
            |                   November 2005 (modified) |
            |                      April 2006 (modified) |
            |                      March 2007  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2009          |
            |                       June 2009  (modified)|
            |                                            |
            |        CSP-Prover on Isabelle2016          |
            |                        May 2016  (modified)|
            |                                            |
            |  Markus Roggenbach (Univ of Wales Swansea, |
            |  UK)                                       |
            |  Yoshinao Isobe    (AIST, Japan)           |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F

open fpmode

noncomputable section

namespace ep2_nucleus

local notation:50 P " =F " Q => eqF P MF MF Q

private noncomputable def decideMem {α : Type _} (x : α) (X : Set α) : Bool := by
  classical
  exact decide (x ∈ X)

/- (*** To automatically unfold syntactic sugar ***) -/

/- Lean note:
   Isabelle's `declare csp_prefix_ss_def [simp]` and `declare inj_on_def [simp]`
   have no direct Lean analogue here. -/

/- *********************************************************
              data type passed on channels
 ********************************************************* -/

axiom init_d : Type
axiom request_d : Type
axiom response_d : Type
axiom exit_d : Type

axiom default_init_d : init_d
axiom default_request_d : request_d
axiom default_response_d : response_d
axiom default_exit_d : exit_d

instance : Inhabited init_d where
  default := default_init_d

instance : Inhabited request_d where
  default := default_request_d

instance : Inhabited response_d where
  default := default_response_d

instance : Inhabited exit_d where
  default := default_exit_d

noncomputable instance : DecidableEq init_d := Classical.decEq _
noncomputable instance : DecidableEq request_d := Classical.decEq _
noncomputable instance : DecidableEq response_d := Classical.decEq _
noncomputable instance : DecidableEq exit_d := Classical.decEq _

inductive Data where
  | Init : init_d → Data
  | Exit : exit_d → Data
  | Request : request_d → Data
  | Response : response_d → Data

instance : Inhabited Data where
  default := Data.Init default

noncomputable instance : DecidableEq Data := Classical.decEq _

/- *********************************************************
                     event (channel)
 ********************************************************* -/

inductive Event where
  | c : Data → Event

instance : Inhabited Event where
  default := Event.c default

noncomputable instance : DecidableEq Event := Classical.decEq _

/- *********************************************************
         abstract component description level
 ********************************************************* -/

inductive ACName where
  | Acquirer
  | AcConfigManagement
  | Terminal
  | TerminalConfigManagement

instance : Inhabited ACName where
  default := ACName.Acquirer

noncomputable instance : DecidableEq ACName := Classical.decEq _

def ACfun : ACName → proc ACName Event
  | ACName.Acquirer =>
      Rec_prefix Event.c (Set.range Data.Init) fun _ =>
        proc.Proc_name ACName.AcConfigManagement
  | ACName.AcConfigManagement =>
      (Nondet_send_prefix Event.c (Set.range Data.Exit) fun _ =>
        proc.SKIP) |~|
        (Nondet_send_prefix Event.c (Set.range Data.Request) fun _ =>
          Rec_prefix Event.c (Set.range Data.Response) fun _ =>
            proc.Proc_name ACName.AcConfigManagement)
  | ACName.Terminal =>
      Nondet_send_prefix Event.c (Set.range Data.Init) fun _ =>
        proc.Proc_name ACName.TerminalConfigManagement
  | ACName.TerminalConfigManagement =>
      Rec_prefix Event.c Set.univ fun x =>
        IF decideMem x (Set.range Data.Request) THEN
          (Nondet_send_prefix Event.c (Set.range Data.Response) fun _ =>
            proc.Proc_name ACName.TerminalConfigManagement)
        ELSE IF decideMem x (Set.range Data.Exit) THEN
          proc.SKIP
        ELSE
          proc.STOP

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_ACfun : HasPNfun ACName Event where
  PNfun := ACfun

@[simp]
theorem Set_ACfun_def (pn : ACName) :
    PNfun pn = ACfun pn :=
  rfl

def AC : proc ACName Event :=
  (proc.Proc_name ACName.Acquirer) |[Set.range Event.c]| (proc.Proc_name ACName.Terminal)

theorem AC_def :
    AC = (proc.Proc_name ACName.Acquirer) |[Set.range Event.c]| (proc.Proc_name ACName.Terminal) :=
  rfl

/- ---------------------------------------------------------------*
 |                          NOTE                                 |
 |                                                               |
 | c ! v -> P       : sends a value v to c, then behaves like P. |
 |                                                               |
 | c ? x:X -> P(x)  : receives a value v from c if c in X,       |
 |                    then behaves like P(v).                    |
 |                                                               |
 | c !? x:X -> P(x) : sends a value v selected from X to c,      |
 |                    then behaves like P(v).                    |
 |                                                               |
 *--------------------------------------------------------------- -/

/- *********************************************************
              equivalent sequential behavior
 ********************************************************* -/

inductive SeqName where
  | SeqInit
  | Loop

instance : Inhabited SeqName where
  default := SeqName.SeqInit

noncomputable instance : DecidableEq SeqName := Classical.decEq _

def Seqfun : SeqName → proc SeqName Event
  | SeqName.SeqInit =>
      Nondet_send_prefix Event.c (Set.range Data.Init) fun _ =>
        proc.Proc_name SeqName.Loop
  | SeqName.Loop =>
      (Nondet_send_prefix Event.c (Set.range Data.Exit) fun _ =>
        proc.SKIP) |~|
        (Nondet_send_prefix Event.c (Set.range Data.Request) fun _ =>
          Nondet_send_prefix Event.c (Set.range Data.Response) fun _ =>
            proc.Proc_name SeqName.Loop)

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_Seqfun : HasPNfun SeqName Event where
  PNfun := Seqfun

@[simp]
theorem Set_Seqfun_def (pn : SeqName) :
    PNfun pn = Seqfun pn :=
  rfl

def Seq : proc SeqName Event :=
  proc.Proc_name SeqName.SeqInit

theorem Seq_def :
    Seq = proc.Proc_name SeqName.SeqInit :=
  rfl

/- *********************************************************
        relating function between ACName and SeqName
 ********************************************************* -/

def Seq_to_AC : SeqName → proc ACName Event
  | SeqName.SeqInit =>
      (proc.Proc_name ACName.Acquirer) |[Set.range Event.c]| (proc.Proc_name ACName.Terminal)
  | SeqName.Loop =>
      (proc.Proc_name ACName.AcConfigManagement) |[Set.range Event.c]|
        (proc.Proc_name ACName.TerminalConfigManagement)

/- *********************************************************
               gProc lemmas (routine work)
 ********************************************************* -/

@[simp]
axiom guardedfun_AC_Seq :
    guardedfun ACfun ∧ guardedfun Seqfun

/- *********************************************************
           a theorem for verifying Seq <=F AC
 ********************************************************* -/

/- Lean note:
   The original Isabelle proof uses fixed-point induction across
   `SeqName` and `ACName`. The current Lean port keeps this heterogeneous
   fixed-point argument as an axiom for now. -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

axiom ep2 : Seq =F AC

end ep2_nucleus
