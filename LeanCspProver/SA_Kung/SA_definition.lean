           /- -------------------------------------------*
            |    Example 1 [Roscoe_Dathi_1987 P.10]     |
            |             WITH computation              |
            |  Self-timed version of a systolic array   |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.3.0            |
            |              September 2006  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.4.0            |
            |                  April 2007  (modified)   |
            |                   June 2008  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.5.0            |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.DFP.DFP_Main

open fpmode

noncomputable section

namespace SA_definition

local infix:50 " =F " => eqFfix

local instance instInhabitedOfZero (α : Type _) [Zero α] : Inhabited α where
  default := 0

/- *********************************************************
                         event
 ********************************************************* -/

inductive Event (r : Type _) where
  | vert : Nat × Nat → r → Event r
  | hori : Nat × Nat → r → Event r
deriving DecidableEq

/- *********************************************************
                  element process
 ********************************************************* -/

abbrev index_type := Nat × Nat

inductive ProcName (r : Type _) where
  | pe : index_type → r → ProcName r
  | pe' : index_type → r → r → r → ProcName r
deriving DecidableEq

def SAfun [Ring r] : ProcName r → proc (ProcName r) (Event r)
  | ProcName.pe (i, j) r0 =>
      (Rec_prefix (Event.vert (i, j)) Set.univ fun x =>
        Rec_prefix (Event.hori (i, j)) Set.univ fun y =>
          proc.Proc_name (ProcName.pe' (i, j) r0 x y)) [+]
      (Rec_prefix (Event.hori (i, j)) Set.univ fun y =>
        Rec_prefix (Event.vert (i, j)) Set.univ fun x =>
          proc.Proc_name (ProcName.pe' (i, j) r0 x y))
  | ProcName.pe' (i, j) r0 x y =>
      (Interleave
        (Send_prefix (Event.vert (i + 1, j)) x proc.SKIP)
        (Send_prefix (Event.hori (i, j + 1)) y proc.SKIP)) ;;
      proc.Proc_name (ProcName.pe (i, j) (r0 + x * y))

/- Lean note:
   Isabelle's overloaded constant `PNfun` is represented by a typeclass
   instance. -/

instance Set_SAfun [Ring r] : HasPNfun (ProcName r) (Event r) where
  PNfun := SAfun

@[simp]
theorem Set_SAfun_def [Ring r] (pn : ProcName r) :
    PNfun pn = SAfun pn :=
  rfl

/- Lean note:
   Isabelle's overloaded constant `FPmode` is represented by a typeclass
   instance. -/

instance Set_FPmode : HasFPmode where
  FPmode := CPOmode

@[simp]
theorem FPmode_def : FPmode = CPOmode :=
  rfl

/- (*** fixed point ***) -/

theorem pe_FIX [Ring r] (ij : index_type) (r0 : r) :
    (proc.Proc_name (ProcName.pe ij r0) : proc (ProcName r) (Event r)) =F
      FIX SAfun (ProcName.pe ij r0) := by
  exact cspF_FIX (Pf := SAfun) (p0 := ProcName.pe ij r0) (Or.inl rfl) rfl

/- (*** network ***) -/

def Alpha_pe {r : Type _} : index_type → Set (Event r)
  | (i, j) =>
      {a | ∃ x,
        a = Event.vert (i, j) x ∨
          a = Event.hori (i, j) x ∨
          a = Event.vert (i + 1, j) x ∨
          a = Event.hori (i, j + 1) x}

/- Lean note:
   Isabelle's `declare Alpha_pe.simps [simp del]` has no direct Lean analogue. -/

def Array_Index (N : Nat) : Set index_type :=
  {ij | ∃ i, ∃ j, ij = (i, j) ∧ (i < N) ∧ (j < N)}

theorem Array_Index_def (N : Nat) :
    Array_Index N = {ij | ∃ i, ∃ j, ij = (i, j) ∧ (i < N) ∧ (j < N)} :=
  rfl

def Systolic_Array [Ring r] (N : Nat) : Network index_type (ProcName r) (Event r) :=
  (Array_Index N, fun ij => (proc.Proc_name (ProcName.pe ij (0 : r)), Alpha_pe (r := r) ij))

theorem Systolic_Array_def [Ring r] (N : Nat) :
    Systolic_Array (r := r) N =
      (Array_Index N, fun ij => (proc.Proc_name (ProcName.pe ij (0 : r)), Alpha_pe (r := r) ij)) :=
  rfl

/- ---------------------------------*
 | Failures sets of Systolic_Array |
 *--------------------------------- -/

/- (*** out term ***) -/

def Faiures_out_hori {r : Type _} (y : r) :
    index_type → Set (failure (Event r)) → Set (failure (Event r)) :=
  fun (i, j) F =>
    {((<> : traceType (Event r)),
      {e | ∃ z,
        e = event.Ev (Event.vert (i, j) z) ∨
          e = event.Ev (Event.hori (i, j) z) ∨
          e = event.Ev (Event.vert (i + 1, j) z) ∨
          (e = event.Ev (Event.hori (i, j + 1) z) ∧ z ≠ y)})} ∪
      {u | ∃ s Y,
        u = (((Abs_trace [event.Ev (Event.hori (i, j + 1) y)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ F}

theorem Faiures_out_hori_def {r : Type _} (y : r) :
    Faiures_out_hori y =
      fun (i, j) F =>
        {((<> : traceType (Event r)),
          {e | ∃ z,
            e = event.Ev (Event.vert (i, j) z) ∨
              e = event.Ev (Event.hori (i, j) z) ∨
              e = event.Ev (Event.vert (i + 1, j) z) ∨
              (e = event.Ev (Event.hori (i, j + 1) z) ∧ z ≠ y)})} ∪
          {u | ∃ s Y,
            u =
              (((Abs_trace [event.Ev (Event.hori (i, j + 1) y)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ F} :=
  rfl

def Faiures_out_vert {r : Type _} (x : r) :
    index_type → Set (failure (Event r)) → Set (failure (Event r)) :=
  fun (i, j) F =>
    {((<> : traceType (Event r)),
      {e | ∃ z,
        e = event.Ev (Event.hori (i, j) z) ∨
          e = event.Ev (Event.vert (i, j) z) ∨
          e = event.Ev (Event.hori (i, j + 1) z) ∨
          (e = event.Ev (Event.vert (i + 1, j) z) ∧ z ≠ x)})} ∪
      {u | ∃ s Y,
        u = (((Abs_trace [event.Ev (Event.vert (i + 1, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ F}

theorem Faiures_out_vert_def {r : Type _} (x : r) :
    Faiures_out_vert x =
      fun (i, j) F =>
        {((<> : traceType (Event r)),
          {e | ∃ z,
            e = event.Ev (Event.hori (i, j) z) ∨
              e = event.Ev (Event.vert (i, j) z) ∨
              e = event.Ev (Event.hori (i, j + 1) z) ∨
              (e = event.Ev (Event.vert (i + 1, j) z) ∧ z ≠ x)})} ∪
          {u | ∃ s Y,
            u =
              (((Abs_trace [event.Ev (Event.vert (i + 1, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ F} :=
  rfl

def Faiures_out {r : Type _} (x y : r) :
    index_type → Set (failure (Event r)) → Set (failure (Event r)) :=
  fun (i, j) F =>
    {((<> : traceType (Event r)),
      {e | ∃ z,
        e = event.Ev (Event.hori (i, j) z) ∨
          e = event.Ev (Event.vert (i, j) z) ∨
          (e = event.Ev (Event.hori (i, j + 1) z) ∧ z ≠ y) ∨
          (e = event.Ev (Event.vert (i + 1, j) z) ∧ z ≠ x)})} ∪
      {u | ∃ s Y,
        u = (((Abs_trace [event.Ev (Event.vert (i + 1, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_out_hori y (i, j) F} ∪
      {u | ∃ s Y,
        u = (((Abs_trace [event.Ev (Event.hori (i, j + 1) y)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_out_vert x (i, j) F}

theorem Faiures_out_def {r : Type _} (x y : r) :
    Faiures_out x y =
      fun (i, j) F =>
        {((<> : traceType (Event r)),
          {e | ∃ z,
            e = event.Ev (Event.hori (i, j) z) ∨
              e = event.Ev (Event.vert (i, j) z) ∨
              (e = event.Ev (Event.hori (i, j + 1) z) ∧ z ≠ y) ∨
              (e = event.Ev (Event.vert (i + 1, j) z) ∧ z ≠ x)})} ∪
          {u | ∃ s Y,
            u =
              (((Abs_trace [event.Ev (Event.vert (i + 1, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ Faiures_out_hori y (i, j) F} ∪
          {u | ∃ s Y,
            u =
              (((Abs_trace [event.Ev (Event.hori (i, j + 1) y)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ Faiures_out_vert x (i, j) F} :=
  rfl

/- (*** in term ***) -/

def Faiures_in_hori {r : Type _} (x : r) :
    index_type → Set (failure (Event r)) → Set (failure (Event r)) :=
  fun (i, j) F =>
    {((<> : traceType (Event r)),
      {e | ∃ z,
        e = event.Ev (Event.vert (i, j) z) ∨
          e = event.Ev (Event.hori (i, j + 1) z) ∨
          e = event.Ev (Event.vert (i + 1, j) z)})} ∪
      {u | ∃ y s Y,
        u = (((Abs_trace [event.Ev (Event.hori (i, j) y)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_out x y (i, j) F}

theorem Faiures_in_hori_def {r : Type _} (x : r) :
    Faiures_in_hori x =
      fun (i, j) F =>
        {((<> : traceType (Event r)),
          {e | ∃ z,
            e = event.Ev (Event.vert (i, j) z) ∨
              e = event.Ev (Event.hori (i, j + 1) z) ∨
              e = event.Ev (Event.vert (i + 1, j) z)})} ∪
          {u | ∃ y s Y,
            u = (((Abs_trace [event.Ev (Event.hori (i, j) y)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ Faiures_out x y (i, j) F} :=
  rfl

def Faiures_in_vert {r : Type _} (y : r) :
    index_type → Set (failure (Event r)) → Set (failure (Event r)) :=
  fun (i, j) F =>
    {((<> : traceType (Event r)),
      {e | ∃ z,
        e = event.Ev (Event.hori (i, j) z) ∨
          e = event.Ev (Event.vert (i + 1, j) z) ∨
          e = event.Ev (Event.hori (i, j + 1) z)})} ∪
      {u | ∃ x s Y,
        u = (((Abs_trace [event.Ev (Event.vert (i, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_out x y (i, j) F}

theorem Faiures_in_vert_def {r : Type _} (y : r) :
    Faiures_in_vert y =
      fun (i, j) F =>
        {((<> : traceType (Event r)),
          {e | ∃ z,
            e = event.Ev (Event.hori (i, j) z) ∨
              e = event.Ev (Event.vert (i + 1, j) z) ∨
              e = event.Ev (Event.hori (i, j + 1) z)})} ∪
          {u | ∃ x s Y,
            u = (((Abs_trace [event.Ev (Event.vert (i, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ Faiures_out x y (i, j) F} :=
  rfl

def Faiures_in {r : Type _} :
    index_type → Set (failure (Event r)) → Set (failure (Event r)) :=
  fun (i, j) F =>
    {((<> : traceType (Event r)),
      {e | ∃ z,
        e = event.Ev (Event.vert (i + 1, j) z) ∨
          e = event.Ev (Event.hori (i, j + 1) z)})} ∪
      {u | ∃ x s Y,
        u = (((Abs_trace [event.Ev (Event.vert (i, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_in_hori x (i, j) F} ∪
      {u | ∃ y s Y,
        u = (((Abs_trace [event.Ev (Event.hori (i, j) y)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_in_vert y (i, j) F}

theorem Faiures_in_def {r : Type _} :
    Faiures_in =
      fun (i, j) F =>
        {((<> : traceType (Event r)),
          {e | ∃ z,
            e = event.Ev (Event.vert (i + 1, j) z) ∨
              e = event.Ev (Event.hori (i, j + 1) z)})} ∪
          {u | ∃ x s Y,
            u = (((Abs_trace [event.Ev (Event.vert (i, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ Faiures_in_hori x (i, j) F} ∪
          {u | ∃ y s Y,
            u = (((Abs_trace [event.Ev (Event.hori (i, j) y)] : traceType (Event r)) ^^^ s), Y) ∧
              (s, Y) ∈ Faiures_in_vert y (i, j) F} :=
  rfl

/- (*** induction ***) -/

def peF_rec {r : Type _} : Nat → index_type → Set (failure (Event r))
  | 0 => fun _ => ∅
  | Nat.succ n => fun ij => Faiures_in ij (peF_rec n ij)

def peF {r : Type _} (ij : index_type) : Set (failure (Event r)) :=
  ⋃ n : Nat, peF_rec n ij

theorem peF_def {r : Type _} (ij : index_type) :
    peF (r := r) ij = ⋃ n : Nat, peF_rec (r := r) n ij :=
  rfl

/- (*** NetworkF ***) -/

def Systolic_ArrayF {r : Type _} (N : Nat) : NetworkF index_type (Event r) :=
  (Array_Index N, fun ij => (peF ij, Alpha_pe ij))

theorem Systolic_ArrayF_def {r : Type _} :
    Systolic_ArrayF (r := r) =
      fun N => (Array_Index N, fun ij => (peF (r := r) ij, Alpha_pe (r := r) ij)) :=
  rfl

/- ******************************************************************
                        small lemmas
 ****************************************************************** -/

/- (*** index ***) -/

theorem Example1_index_mem {ij : index_type} {N : Nat} :
    ij ∈ Array_Index N ↔ ∃ i, ∃ j, ij = (i, j) ∧ (i < N) ∧ (j < N) :=
  Iff.rfl

/- (****************** to add it again ******************) -/

end SA_definition
