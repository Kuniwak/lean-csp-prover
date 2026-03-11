           /- -------------------------------------------*
            |    Example 1 [Roscoe_Dathi_1987 P.10]     |
            |  Self-timed version of a systolic array   |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.3.0            |
            |              September 2006  (modified)   |
            |                                           |
            |   on DFP on CSP-Prover ver.4.0            |
            |                  April 2007  (modified)   |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.SA_Kung.SA_definition

open event
open SA_definition

noncomputable section

namespace SA_expanding

local infix:50 " =F " => eqFfix

local instance instInhabitedOfZero (α : Type _) [Zero α] : Inhabited α where
  default := 0

attribute [local instance] Classical.propDecidable

/- Lean note:
   Isabelle's `declare inj_on_def [simp]` has no direct Lean analogue. -/

/- this is automatically used in simplifying (inv (vert (i, j)) (vert (i,j))) -/

/- *********************************************************
              Element process expanding
 ********************************************************* -/

/- in -/

axiom pe_expand_in {r : Type _} [Ring r] (n i j : Nat) (r0 : r) :
   (FIXn (Nat.succ (Nat.succ (n + n))) SAfun (ProcName.pe (i, j) r0))
   =F
   proc.Ext_pre_choice
     (Set.range (Event.vert (i, j)) ∪ Set.range (Event.hori (i, j)))
     (fun a =>
       IF a ∈ Set.range (Event.vert (i, j))
       THEN
         Rec_prefix (Event.hori (i, j)) Set.univ (fun b =>
           FIXn (Nat.succ (n + n)) SAfun
             (ProcName.pe' (i, j) r0
               (Function.invFun (Event.vert (i, j)) a) b))
       ELSE
         Rec_prefix (Event.vert (i, j)) Set.univ (fun b =>
           FIXn (Nat.succ (n + n)) SAfun
             (ProcName.pe' (i, j) r0
               b (Function.invFun (Event.hori (i, j)) a))))

/- out -/

axiom pe_expand_out {r : Type _} [Ring r] (n i j : Nat) (r0 x y : r) :
   (FIXn (Nat.succ (n + n)) SAfun (ProcName.pe' (i, j) r0 x y))
   =F
   proc.Ext_pre_choice
     ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r))
     (fun a =>
       if a = Event.vert (i + 1, j) x then
         proc.Ext_pre_choice ({Event.hori (i, j + 1) y} : Set (Event r)) (fun _ =>
           FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))
       else
         proc.Ext_pre_choice ({Event.vert (i + 1, j) x} : Set (Event r)) (fun _ =>
           FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y))))

/- *********************************************************
                  alphabet lemma
 ********************************************************* -/

axiom EX1_isFailureOf_in_alpha1 {r : Type _} (i j : Nat) :
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \
        (Ev '' (Set.range (Event.vert (i, j)) ∪ Set.range (Event.hori (i, j)))) ) =
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ (∃ x, a = Event.vert (i + 1, j) x ∨ a = Event.hori (i, j + 1) x)})

axiom EX1_isFailureOf_in_alpha2 {r : Type _} [Inhabited r] (i j : Nat) (F : Set (failure (Event r))) :
    ({u : failure (Event r) | ∃ x s Y,
        u = (((Abs_trace [Ev (Event.vert (i, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_in_hori x (i, j) F} ∪
      {u : failure (Event r) | ∃ y s Y,
        u = (((Abs_trace [Ev (Event.hori (i, j) y)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_in_vert y (i, j) F}) =
    {u : failure (Event r) | ∃ a s Y,
      u = (((Abs_trace [Ev a] : traceType (Event r)) ^^^ s), Y) ∧
        (s, Y) ∈
          (if a ∈ Set.range (Event.vert (i, j))
           then Faiures_in_hori (Function.invFun (Event.vert (i, j)) a) (i, j) F
           else Faiures_in_vert (Function.invFun (Event.hori (i, j)) a) (i, j) F) ∧
        a ∈ Set.range (Event.vert (i, j)) ∪ Set.range (Event.hori (i, j))}

axiom EX1_isFailureOf_in_hori_alpha1 {r : Type _} (i j : Nat) :
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ ∃ x,
        a = Event.vert (i, j) x ∨
          a = Event.hori (i, j + 1) x ∨
          a = Event.vert (i + 1, j) x}) =
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \ Ev '' Set.range (Event.hori (i, j)))

axiom EX1_isFailureOf_in_hori_alpha2 {r : Type _} [Inhabited r] (i j : Nat) (a : Event r)
    (F : Set (failure (Event r))) :
    {u : failure (Event r) | ∃ y s Y,
      u = (((Abs_trace [Ev (Event.hori (i, j) y)] : traceType (Event r)) ^^^ s), Y) ∧
        (s, Y) ∈ Faiures_out (Function.invFun (Event.vert (i, j)) a) y (i, j) F} =
    {u : failure (Event r) | ∃ aa s Y,
      u = (((Abs_trace [Ev aa] : traceType (Event r)) ^^^ s), Y) ∧
        (s, Y) ∈
          Faiures_out
            (Function.invFun (Event.vert (i, j)) a)
            (Function.invFun (Event.hori (i, j)) aa) (i, j) F ∧
        aa ∈ Set.range (Event.hori (i, j))}

axiom EX1_isFailureOf_in_vert_alpha1 {r : Type _} (i j : Nat) :
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ ∃ x,
        a = Event.hori (i, j) x ∨
          a = Event.vert (i + 1, j) x ∨
          a = Event.hori (i, j + 1) x}) =
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \ Ev '' Set.range (Event.vert (i, j)))

axiom EX1_isFailureOf_in_vert_alpha2 {r : Type _} [Inhabited r] (i j : Nat) (a : Event r)
    (F : Set (failure (Event r))) :
    {u : failure (Event r) | ∃ x s Y,
      u = (((Abs_trace [Ev (Event.vert (i, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
        (s, Y) ∈ Faiures_out x (Function.invFun (Event.hori (i, j)) a) (i, j) F} =
    {u : failure (Event r) | ∃ aa s Y,
      u = (((Abs_trace [Ev aa] : traceType (Event r)) ^^^ s), Y) ∧
        (s, Y) ∈
          Faiures_out
            (Function.invFun (Event.vert (i, j)) aa)
            (Function.invFun (Event.hori (i, j)) a) (i, j) F ∧
        aa ∈ Set.range (Event.vert (i, j))}

axiom EX1_isFailureOf_out_alpha1 {r : Type _} (i j : Nat) (x y : r) :
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ ∃ z,
        a = Event.hori (i, j) z ∨
          a = Event.vert (i, j) z ∨
          (a = Event.hori (i, j + 1) z ∧ z ≠ y) ∨
          (a = Event.vert (i + 1, j) z ∧ z ≠ x)}) =
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r)))

axiom EX1_isFailureOf_out_alpha2 {r : Type _} (i j : Nat) (x y : r)
    (F : Set (failure (Event r))) :
    ({u : failure (Event r) | ∃ s Y,
        u = (((Abs_trace [Ev (Event.vert (i + 1, j) x)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_out_hori y (i, j) F} ∪
      {u : failure (Event r) | ∃ s Y,
        u = (((Abs_trace [Ev (Event.hori (i, j + 1) y)] : traceType (Event r)) ^^^ s), Y) ∧
          (s, Y) ∈ Faiures_out_vert x (i, j) F}) =
    {u : failure (Event r) | ∃ a s Y,
      u = (((Abs_trace [Ev a] : traceType (Event r)) ^^^ s), Y) ∧
        (s, Y) ∈
          (if a ∈ Set.range (Event.vert (i + 1, j))
           then Faiures_out_hori y (i, j) F
           else Faiures_out_vert x (i, j) F) ∧
        a ∈ ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r))}

/- *********************************************************
                  isFailureOf
 ********************************************************* -/

/- out -/

axiom EX1_isFailureOf_out_hori {r : Type _} [Ring r]
    (n i j : Nat) (x y : r) :
    ∀ r0 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r0)) MF)
          (Ev '' Alpha_pe (r := r) (i, j)) →
    Faiures_out_hori y (i, j) (peF_rec (r := r) n (i, j)) <=EX
      restRefusal
        (failures
          (if true then
             proc.Ext_pre_choice ({Event.hori (i, j + 1) y} : Set (Event r)) (fun _ =>
               FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))
           else
             proc.Ext_pre_choice ({Event.vert (i + 1, j) x} : Set (Event r)) (fun _ =>
               FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))) MF)
        (Ev '' Alpha_pe (r := r) (i, j))

axiom EX1_isFailureOf_out_vert {r : Type _} [Ring r]
    (n i j : Nat) (x y : r) :
    ∀ r0 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r0)) MF)
          (Ev '' Alpha_pe (r := r) (i, j)) →
    Faiures_out_vert x (i, j) (peF_rec (r := r) n (i, j)) <=EX
      restRefusal
        (failures
          (if false then
             proc.Ext_pre_choice ({Event.hori (i, j + 1) y} : Set (Event r)) (fun _ =>
               FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))
           else
             proc.Ext_pre_choice ({Event.vert (i + 1, j) x} : Set (Event r)) (fun _ =>
               FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))) MF)
        (Ev '' Alpha_pe (r := r) (i, j))

axiom EX1_isFailureOf_out {r : Type _} [Ring r]
    (n i j : Nat) (x y r0 : r) :
    (∀ r1 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r1)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))) →
    Faiures_out x y (i, j) (peF_rec (r := r) n (i, j)) <=EX
      restRefusal
        (failures (FIXn (Nat.succ (n + n)) SAfun (ProcName.pe' (i, j) r0 x y)) MF)
        (Ev '' Alpha_pe (r := r) (i, j))

/- in -/

axiom EX1_isFailureOf_in_hori {r : Type _} [Ring r]
    (n i j : Nat) (r0 : r) (a : Event r) :
    (∀ r1 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r1)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))) →
    a ∈ Set.range (Event.vert (i, j)) →
    Faiures_in_hori (Function.invFun (Event.vert (i, j)) a) (i, j) (peF_rec (r := r) n (i, j))
      <=EX
      restRefusal
        (failures
          (if true then
             Rec_prefix (Event.hori (i, j)) Set.univ (fun b =>
               FIXn (Nat.succ (n + n)) SAfun
                 (ProcName.pe' (i, j) r0
                   (Function.invFun (Event.vert (i, j)) a) b))
           else
             Rec_prefix (Event.vert (i, j)) Set.univ (fun b =>
               FIXn (Nat.succ (n + n)) SAfun
                 (ProcName.pe' (i, j) r0
                   b (Function.invFun (Event.hori (i, j)) a)))) MF)
        (Ev '' Alpha_pe (r := r) (i, j))

axiom EX1_isFailureOf_in_vert {r : Type _} [Ring r]
    (n i j : Nat) (r0 : r) (a : Event r) :
    (∀ r1 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r1)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))) →
    a ∈ Set.range (Event.hori (i, j)) →
    a ∉ Set.range (Event.vert (i, j)) →
    Faiures_in_vert (Function.invFun (Event.hori (i, j)) a) (i, j) (peF_rec (r := r) n (i, j))
      <=EX
      restRefusal
        (failures
          (if false then
             Rec_prefix (Event.hori (i, j)) Set.univ (fun b =>
               FIXn (Nat.succ (n + n)) SAfun
                 (ProcName.pe' (i, j) r0
                   (Function.invFun (Event.vert (i, j)) a) b))
           else
             Rec_prefix (Event.vert (i, j)) Set.univ (fun b =>
               FIXn (Nat.succ (n + n)) SAfun
                 (ProcName.pe' (i, j) r0
                   b (Function.invFun (Event.hori (i, j)) a)))) MF)
        (Ev '' Alpha_pe (r := r) (i, j))

axiom EX1_isFailureOf_in {r : Type _} [Ring r]
    (n i j : Nat) (r0 : r) :
    (∀ r0 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r0)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))) →
    Faiures_in (r := r) (i, j) (peF_rec (r := r) n (i, j)) <=EX
      restRefusal
        (failures (FIXn (Nat.succ (Nat.succ (n + n))) SAfun (ProcName.pe (i, j) r0)) MF)
        (Ev '' Alpha_pe (r := r) (i, j))

axiom EX1_isFailureOf_in_ALL {r : Type _} [Ring r]
    (n i j : Nat) :
    ∀ r0 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r0)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))

/- main -/

axiom EX1_isFailureOf {r : Type _} [Ring r] (N : Nat) :
   isFailureOf (Systolic_ArrayF (r := r) N) (Systolic_Array (r := r) N)

/- Lean note:
   Isabelle's `declare inj_on_def [simp del]` has no direct Lean analogue. -/

end SA_expanding
