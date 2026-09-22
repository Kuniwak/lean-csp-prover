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

private theorem hori_notin_range_vert {r : Type _} {ij kl : Nat × Nat} {y : r} :
    Event.hori ij y ∉ Set.range (Event.vert (r := r) kl) := by
  rintro ⟨z, hz⟩
  exact absurd hz (by simp)

private theorem inj_hori {r : Type _} (ij : Nat × Nat) :
    Function.Injective (Event.hori (r := r) ij) := by
  intro a b h
  cases h
  rfl

private theorem inj_vert {r : Type _} (ij : Nat × Nat) :
    Function.Injective (Event.vert (r := r) ij) := by
  intro a b h
  cases h
  rfl

/- *********************************************************
                  alphabet lemma
 ********************************************************* -/

theorem EX1_isFailureOf_in_alpha1 {r : Type _} (i j : Nat) :
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \
        (Ev '' (Set.range (Event.vert (i, j)) ∪ Set.range (Event.hori (i, j)))) ) =
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧
        (∃ x, a = Event.vert (i + 1, j) x ∨ a = Event.hori (i, j + 1) x)}) := by
  congr 1
  ext e
  simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_range]
  constructor
  · rintro ⟨⟨a, ⟨x, ha⟩, rfl⟩, hnot⟩
    refine ⟨a, rfl, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl
    · exact absurd ⟨_, Or.inl ⟨x, rfl⟩, rfl⟩ hnot
    · exact absurd ⟨_, Or.inr ⟨x, rfl⟩, rfl⟩ hnot
    · exact ⟨x, Or.inl rfl⟩
    · exact ⟨x, Or.inr rfl⟩
  · rintro ⟨a, rfl, x, ha⟩
    rcases ha with rfl | rfl
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, (⟨y, rfl⟩ | ⟨y, rfl⟩), hb⟩ <;> (injection hb with hb; simp at hb)
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, (⟨y, rfl⟩ | ⟨y, rfl⟩), hb⟩ <;> (injection hb with hb; simp at hb)

theorem EX1_isFailureOf_in_alpha2
{r : Type _} [Inhabited r] (i j : Nat) (F : Set (failure (Event r))) :
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
        a ∈ Set.range (Event.vert (i, j)) ∪ Set.range (Event.hori (i, j))} := by
  ext u
  simp only [Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (⟨x, s, Y, rfl, hF⟩ | ⟨y, s, Y, rfl, hF⟩)
    · refine ⟨Event.vert (i, j) x, s, Y, rfl, ?_, Or.inl ⟨x, rfl⟩⟩
      rw [if_pos ⟨x, rfl⟩, Function.leftInverse_invFun (inj_vert (i, j)) x]
      exact hF
    · refine ⟨Event.hori (i, j) y, s, Y, rfl, ?_, Or.inr ⟨y, rfl⟩⟩
      rw [if_neg hori_notin_range_vert, Function.leftInverse_invFun (inj_hori (i, j)) y]
      exact hF
  · rintro ⟨a, s, Y, rfl, hF, hmem⟩
    by_cases ha : a ∈ Set.range (Event.vert (i, j))
    · obtain ⟨x, rfl⟩ := ha
      refine Or.inl ⟨x, s, Y, rfl, ?_⟩
      rw [if_pos ⟨x, rfl⟩, Function.leftInverse_invFun (inj_vert (i, j)) x] at hF
      exact hF
    · rcases hmem with h | ⟨y, rfl⟩
      · exact absurd h ha
      refine Or.inr ⟨y, s, Y, rfl, ?_⟩
      rw [if_neg ha, Function.leftInverse_invFun (inj_hori (i, j)) y] at hF
      exact hF

theorem EX1_isFailureOf_in_hori_alpha1 {r : Type _} (i j : Nat) :
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ ∃ x,
        a = Event.vert (i, j) x ∨
          a = Event.hori (i, j + 1) x ∨
          a = Event.vert (i + 1, j) x}) =
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \ Ev '' Set.range (Event.hori (i, j))) := by
  congr 1
  ext e
  simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨a, rfl, x, ha⟩
    rcases ha with rfl | rfl | rfl
    · refine ⟨⟨_, ⟨x, Or.inl rfl⟩, rfl⟩, ?_⟩
      rintro ⟨b, ⟨y, rfl⟩, hb⟩
      injection hb with hb
      simp at hb
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, ⟨y, rfl⟩, hb⟩
      injection hb with hb
      simp at hb
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, ⟨y, rfl⟩, hb⟩
      injection hb with hb
      simp at hb
  · rintro ⟨⟨a, ⟨x, ha⟩, rfl⟩, hnot⟩
    refine ⟨a, rfl, x, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact absurd ⟨_, ⟨x, rfl⟩, rfl⟩ hnot
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

theorem EX1_isFailureOf_in_hori_alpha2 {r : Type _} [Inhabited r] (i j : Nat) (a : Event r)
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
        aa ∈ Set.range (Event.hori (i, j))} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨y, s, Y, rfl, hF⟩
    refine ⟨Event.hori (i, j) y, s, Y, rfl, ?_, ⟨y, rfl⟩⟩
    rwa [Function.leftInverse_invFun (inj_hori (i, j)) y]
  · rintro ⟨aa, s, Y, rfl, hF, ⟨y, rfl⟩⟩
    refine ⟨y, s, Y, rfl, ?_⟩
    rwa [Function.leftInverse_invFun (inj_hori (i, j)) y] at hF

theorem EX1_isFailureOf_in_vert_alpha1 {r : Type _} (i j : Nat) :
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ ∃ x,
        a = Event.hori (i, j) x ∨
          a = Event.vert (i + 1, j) x ∨
          a = Event.hori (i, j + 1) x}) =
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \ Ev '' Set.range (Event.vert (i, j))) := by
  congr 1
  ext e
  simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨a, rfl, x, ha⟩
    rcases ha with rfl | rfl | rfl
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inl rfl)⟩, rfl⟩, ?_⟩
      rintro ⟨b, ⟨y, rfl⟩, hb⟩
      injection hb with hb
      simp at hb
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, ⟨y, rfl⟩, hb⟩
      injection hb with hb
      simp at hb
    · refine ⟨⟨_, ⟨x, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, ⟨y, rfl⟩, hb⟩
      injection hb with hb
      simp at hb
  · rintro ⟨⟨a, ⟨x, ha⟩, rfl⟩, hnot⟩
    refine ⟨a, rfl, x, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl
    · exact absurd ⟨_, ⟨x, rfl⟩, rfl⟩ hnot
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

theorem EX1_isFailureOf_in_vert_alpha2 {r : Type _} [Inhabited r] (i j : Nat) (a : Event r)
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
        aa ∈ Set.range (Event.vert (i, j))} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨x, s, Y, rfl, hF⟩
    refine ⟨Event.vert (i, j) x, s, Y, rfl, ?_, ⟨x, rfl⟩⟩
    rwa [Function.leftInverse_invFun (inj_vert (i, j)) x]
  · rintro ⟨aa, s, Y, rfl, hF, ⟨x, rfl⟩⟩
    refine ⟨x, s, Y, rfl, ?_⟩
    rwa [Function.leftInverse_invFun (inj_vert (i, j)) x] at hF

theorem EX1_isFailureOf_out_alpha1 {r : Type _} (i j : Nat) (x y : r) :
    ((<> : traceType (Event r)),
      {e | ∃ a, e = Ev a ∧ ∃ z,
        a = Event.hori (i, j) z ∨
          a = Event.vert (i, j) z ∨
          (a = Event.hori (i, j + 1) z ∧ z ≠ y) ∨
          (a = Event.vert (i + 1, j) z ∧ z ≠ x)}) =
    ((<> : traceType (Event r)),
      Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r))) := by
  congr 1
  ext e
  simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, z, ha⟩
    rcases ha with rfl | rfl | ⟨rfl, hz⟩ | ⟨rfl, hz⟩
    · refine ⟨⟨_, ⟨z, Or.inr (Or.inl rfl)⟩, rfl⟩, ?_⟩
      rintro ⟨b, (rfl | rfl), hb⟩ <;> (injection hb with hb; simp at hb)
    · refine ⟨⟨_, ⟨z, Or.inl rfl⟩, rfl⟩, ?_⟩
      rintro ⟨b, (rfl | rfl), hb⟩ <;> (injection hb with hb; simp at hb)
    · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, (rfl | rfl), hb⟩ <;> injection hb with hb <;> simp at hb
      exact hz hb.symm
    · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
      rintro ⟨b, (rfl | rfl), hb⟩ <;> injection hb with hb <;> simp at hb
      exact hz hb.symm
  · rintro ⟨⟨a, ⟨z, ha⟩, rfl⟩, hnot⟩
    refine ⟨a, rfl, z, ?_⟩
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
      rintro rfl
      exact hnot ⟨_, Or.inl rfl, rfl⟩
    · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
      rintro rfl
      exact hnot ⟨_, Or.inr rfl, rfl⟩

theorem EX1_isFailureOf_out_alpha2
{r : Type _} (i j : Nat) (x y : r) (F : Set (failure (Event r))) :
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
        a ∈ ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r))} := by
  ext u
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨s, Y, rfl, hF⟩ | ⟨s, Y, rfl, hF⟩)
    · exact ⟨_, s, Y, rfl, by rw [if_pos ⟨x, rfl⟩]; exact hF, Or.inl rfl⟩
    · exact ⟨_, s, Y, rfl, by rw [if_neg hori_notin_range_vert]; exact hF, Or.inr rfl⟩
  · rintro ⟨a, s, Y, rfl, hF, (rfl | rfl)⟩
    · refine Or.inl ⟨s, Y, rfl, ?_⟩
      rw [if_pos ⟨x, rfl⟩] at hF
      exact hF
    · refine Or.inr ⟨s, Y, rfl, ?_⟩
      rw [if_neg hori_notin_range_vert] at hF
      exact hF

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

theorem EX1_isFailureOf_in_ALL {r : Type _} [Ring r]
    (n i j : Nat) :
    ∀ r0 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r0)) MF)
          (Ev '' Alpha_pe (r := r) (i, j)) := by
  induction n with
  | zero =>
      intro r0
      have hDIV : FIXn 0 SAfun (ProcName.pe (i, j) r0) = (proc.DIV : proc (ProcName r) (Event r)) :=
        rfl
      constructor
      · intro f hf
        exact absurd hf (by simp [peF_rec])
      · rintro s Y ⟨hY, -⟩
        rw [hDIV] at hY
        exact absurd hY in_failures_DIV
  | succ n ih =>
      intro r0
      have h := EX1_isFailureOf_in n i j r0 ih
      have harith : Nat.succ n + Nat.succ n = Nat.succ (Nat.succ (n + n)) := by omega
      rw [harith]
      simpa [peF_rec] using h

/- main -/

theorem EX1_isFailureOf {r : Type _} [Ring r] (N : Nat) :
    isFailureOf (Systolic_ArrayF (r := r) N) (Systolic_Array (r := r) N) := by
  refine ⟨rfl, ?_⟩
  rintro ⟨i, j⟩ -
  refine ⟨?_, rfl⟩
  refine cspF_subseteqEX_Rep_int_choice_nat_UNIV
    (P := (proc.Proc_name (ProcName.pe (i, j) (0 : r)) : proc (ProcName r) (Event r)))
    (Pf := fun n => FIXn (n + n) SAfun (ProcName.pe (i, j) (0 : r)))
    (Ff := fun n => peF_rec (r := r) n (i, j))
    ?_ ?_ (fun n => EX1_isFailureOf_in_ALL n i j 0)
  · exact cspF_trans_left_eq (pe_FIX (i, j) 0) (cspF_FIX_plus_eq (fun n => n) _)
  · change peF (r := r) (i, j) = _
    rw [peF_def]
    ext f
    simp

/- Lean note:
   Isabelle's `declare inj_on_def [simp del]` has no direct Lean analogue. -/

end SA_expanding
