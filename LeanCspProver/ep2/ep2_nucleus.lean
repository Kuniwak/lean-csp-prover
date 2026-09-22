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

/- Lean note:
   Isabelle's `typedecl` (an unspecified nonempty type) and its unspecified
   default elements were ported as `axiom`s. They are now `opaque`
   `NonemptyType`s — the same abstraction without extending the axiom
   base (cf. `diff_fun` in the core). -/

private opaque init_d_spec : NonemptyType.{0}
private opaque request_d_spec : NonemptyType.{0}
private opaque response_d_spec : NonemptyType.{0}
private opaque exit_d_spec : NonemptyType.{0}

def init_d : Type := init_d_spec.type
def request_d : Type := request_d_spec.type
def response_d : Type := response_d_spec.type
def exit_d : Type := exit_d_spec.type

noncomputable def default_init_d : init_d :=
  Classical.choice init_d_spec.property
noncomputable def default_request_d : request_d :=
  Classical.choice request_d_spec.property
noncomputable def default_response_d : response_d :=
  Classical.choice response_d_spec.property
noncomputable def default_exit_d : exit_d :=
  Classical.choice exit_d_spec.property

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
theorem guardedfun_AC_Seq :
    guardedfun ACfun ∧ guardedfun Seqfun := by
  constructor <;> intro pn <;> cases pn <;> simp [ACfun, Seqfun, guarded, noHide]

/- *********************************************************
           a theorem for verifying Seq <=F AC
 ********************************************************* -/

instance Set_FPmode : HasFPmode where
  FPmode := CMSmode

@[simp]
theorem FPmode_def : FPmode = CMSmode :=
  rfl

private theorem inj_c : Function.Injective Event.c := by
  intro a b h
  cases h
  rfl

private theorem unwAC (pn : ACName) :
    eqF (proc.Proc_name pn : proc ACName Event) MF MF (ACfun pn) :=
  «cspF_unwind» rfl (Or.inr (Or.inl ⟨rfl, guardedfun_AC_Seq.1⟩))

private theorem range_ne {γ : Type _} [Inhabited γ] (f : γ → Data) : Set.range f ≠ ∅ :=
  Set.nonempty_iff_ne_empty.mp ⟨f default, default, rfl⟩

/-- The body of `$TerminalConfigManagement` behaves like `SKIP` on an `Exit` value. -/
theorem TCM_body_Exit (e : exit_d) :
    eqF
      (IF decideMem (Data.Exit e) (Set.range Data.Request) THEN
          (Nondet_send_prefix Event.c (Set.range Data.Response) fun _ =>
            proc.Proc_name ACName.TerminalConfigManagement)
        ELSE IF decideMem (Data.Exit e) (Set.range Data.Exit) THEN
          proc.SKIP
        ELSE
          proc.STOP) MF MF (proc.SKIP : proc ACName Event) := by
  have h1 : decideMem (Data.Exit e) (Set.range Data.Request) = false := by simp [decideMem]
  have h2 : decideMem (Data.Exit e) (Set.range Data.Exit) = true := by simp [decideMem]
  rw [h1, h2]
  exact cspF_trans_left_eq cspF_IF_False cspF_IF_True

/-- The body of `$TerminalConfigManagement` on a `Request` value. -/
theorem TCM_body_Request (r : request_d) :
    eqF
      (IF decideMem (Data.Request r) (Set.range Data.Request) THEN
          (Nondet_send_prefix Event.c (Set.range Data.Response) fun _ =>
            proc.Proc_name ACName.TerminalConfigManagement)
        ELSE IF decideMem (Data.Request r) (Set.range Data.Exit) THEN
          proc.SKIP
        ELSE
          proc.STOP) MF MF
      (Nondet_send_prefix Event.c (Set.range Data.Response) fun _ =>
        proc.Proc_name ACName.TerminalConfigManagement) := by
  have h1 : decideMem (Data.Request r) (Set.range Data.Request) = true := by simp [decideMem]
  rw [h1]
  exact cspF_IF_True

theorem ep2 : Seq =F AC := by
  rw [Seq_def, AC_def]
  refine cspF_fp_induct_eq_left (Pf := Seqfun) (f := Seq_to_AC)
    rfl (Or.inl rfl) guardedfun_AC_Seq.2 cspF_reflex_eq_P ?_
  intro pn
  cases pn with
  | SeqInit =>
      have hRHS :
          eqF (Seq_to_AC SeqName.SeqInit) MF MF
            ((Rec_prefix Event.c (Set.range Data.Init)
                fun _ => proc.Proc_name ACName.AcConfigManagement) |[Set.range Event.c]|
              (Nondet_send_prefix Event.c (Set.range Data.Init)
                fun _ => proc.Proc_name ACName.TerminalConfigManagement)) :=
        cspF_Parallel_cong rfl (unwAC ACName.Acquirer) (unwAC ACName.Terminal)
      refine cspF_trans_left_eq ?_ (cspF_sym hRHS)
      simp only [Seqfun, Seq_to_AC, Subst_procfun_Nondet_send_prefix, Subst_procfun]
      exact cspF_sym
        (cspF_Parallel_Rec_Nondet_send_prefix (Set.image_subset_range _ _)
          (subset_refl _) (range_ne Data.Init))
  | Loop =>
      have hRHS :
          eqF (Seq_to_AC SeqName.Loop) MF MF
            ((ACfun ACName.AcConfigManagement) |[Set.range Event.c]|
              (ACfun ACName.TerminalConfigManagement)) :=
        cspF_Parallel_cong rfl (unwAC ACName.AcConfigManagement)
          (unwAC ACName.TerminalConfigManagement)
      refine cspF_trans_left_eq ?_ (cspF_sym hRHS)
      simp only [Seqfun, ACfun, Seq_to_AC, Subst_procfun_Nondet_send_prefix, Subst_procfun]
      refine cspF_trans_left_eq ?_ (cspF_sym cspF_Parallel_dist_l)
      refine cspF_Int_choice_cong ?_ ?_
      · -- the `Exit` branch: both sides terminate
        refine cspF_sym (cspF_trans_left_eq
          (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.c) (A := Set.univ)
            (B := Set.range Data.Exit) (Set.image_subset_range _ _) (Set.subset_univ _)
            (range_ne Data.Exit)) ?_)
        refine cspF_Nondet_send_prefix_cong inj_c rfl rfl (fun x hx => ?_)
        obtain ⟨e, rfl⟩ := hx
        exact cspF_trans_left_eq
          (cspF_Parallel_cong rfl cspF_reflex_eq_P (TCM_body_Exit e)) cspF_Parallel_term
      · -- the `Request` branch: one more synchronised `Response`
        refine cspF_sym (cspF_trans_left_eq
          (cspF_Parallel_Nondet_send_Rec_prefix (f := Event.c) (A := Set.univ)
            (B := Set.range Data.Request) (Set.image_subset_range _ _) (Set.subset_univ _)
            (range_ne Data.Request)) ?_)
        refine cspF_Nondet_send_prefix_cong inj_c rfl rfl (fun x hx => ?_)
        obtain ⟨r, rfl⟩ := hx
        refine cspF_trans_left_eq
          (cspF_Parallel_cong rfl cspF_reflex_eq_P (TCM_body_Request r)) ?_
        exact cspF_Parallel_Rec_Nondet_send_prefix (Set.image_subset_range _ _)
          (subset_refl _) (range_ne Data.Response)

end ep2_nucleus
