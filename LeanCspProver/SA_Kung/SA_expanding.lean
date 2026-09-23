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

attribute [local instance] Classical.propDecidable

/- Lean note:
   Isabelle's `declare inj_on_def [simp]` has no direct Lean analogue. -/

/- this is automatically used in simplifying (inv (vert (i, j)) (vert (i,j))) -/

/- *********************************************************
              Element process expanding
 ********************************************************* -/

/- in -/

private theorem vert_hori_disjoint {r : Type _} {i j : Nat} {a : Event r} :
    a ∈ Set.range (Event.vert (i, j)) → a ∉ Set.range (Event.hori (i, j)) := by
  rintro ⟨x, rfl⟩ ⟨y, hy⟩
  cases hy

private theorem vert_ne_hori {r : Type _} {ij kl : Nat × Nat} {u v : r} :
    (Event.vert ij u : Event r) ≠ Event.hori kl v := by
  intro h
  cases h

theorem pe_expand_in {r : Type _} [Ring r] (n i j : Nat) (r0 : r) :
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
               b (Function.invFun (Event.hori (i, j)) a)))) := by
  rw [FIXn_def, Function.iterate_succ_apply']
  simp only [Subst_procfun_prod, SAfun, Subst_procfun, Rec_prefix_def, Set.image_univ]
  refine cspF_trans_left_eq cspF_Ext_choice_step ?_
  refine cspF_Ext_pre_choice_cong rfl (fun a _ => ?_)
  refine cspF_trans_right_eq (cspF_sym cspF_IF_split) ?_
  by_cases hA : a ∈ Set.range (Event.vert (i, j) (r := r))
  · rw [procIte_neg (fun h => vert_hori_disjoint hA h.2), procIte_pos hA,
      if_pos (by simpa using hA)]
    exact cspF_reflex_eq_P
  · rw [procIte_neg (fun h => hA h.1), procIte_neg hA,
      if_neg (by simpa using hA)]
    exact cspF_reflex_eq_P

/- out -/

theorem pe_expand_out {r : Type _} [Ring r] (n i j : Nat) (r0 x y : r) :
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
           FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))) := by
  rw [FIXn_def, Function.iterate_succ_apply']
  simp only [Subst_procfun_prod, SAfun, Subst_procfun, Send_prefix_def]
  refine cspF_trans_left_eq
    (cspF_Seq_compo_cong
      (cspF_Parallel_cong rfl cspF_Act_prefix_step cspF_Act_prefix_step)
      cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq
    (cspF_Seq_compo_cong cspF_Parallel_step cspF_reflex_eq_P) ?_
  refine cspF_trans_left_eq cspF_Seq_compo_step ?_
  refine cspF_Ext_pre_choice_cong (by simp [Set.pair_comm]) (fun a ha => ?_)
  by_cases hA : a = Event.vert (i + 1, j) x
  · subst hA
    rw [procIte_neg (by simp), procIte_neg (by simp [vert_ne_hori]),
      procIte_pos (Set.mem_singleton _), if_pos rfl]
    refine cspF_trans_left_eq
      (cspF_Seq_compo_cong cspF_Parallel_preterm_l cspF_reflex_eq_P) ?_
    refine cspF_trans_left_eq cspF_Seq_compo_step ?_
    refine cspF_Ext_pre_choice_cong (by simp) (fun b hb => ?_)
    exact cspF_trans_left_eq
      (cspF_Seq_compo_cong cspF_Parallel_term cspF_reflex_eq_P) cspF_Seq_compo_unit_l
  · have hB : a = Event.hori (i, j + 1) y := by
      rcases ha with h | h
      · exact absurd h hA
      · exact h
    subst hB
    rw [procIte_neg (by simp),
      procIte_neg (show ¬ (Event.hori (i, j + 1) y ∈
          ({Event.vert (i + 1, j) x} : Set (Event r)) ∧ _) from fun h => vert_ne_hori h.1.symm),
      procIte_neg (show ¬ (Event.hori (i, j + 1) y ∈
          ({Event.vert (i + 1, j) x} : Set (Event r))) from fun h => vert_ne_hori h.symm),
      if_neg hA]
    refine cspF_trans_left_eq
      (cspF_Seq_compo_cong cspF_Parallel_preterm_r cspF_reflex_eq_P) ?_
    refine cspF_trans_left_eq cspF_Seq_compo_step ?_
    refine cspF_Ext_pre_choice_cong (by simp) (fun b hb => ?_)
    exact cspF_trans_left_eq
      (cspF_Seq_compo_cong cspF_Parallel_term cspF_reflex_eq_P) cspF_Seq_compo_unit_l

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
{r : Type _} [Nonempty r] (i j : Nat) (F : Set (failure (Event r))) :
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

theorem EX1_isFailureOf_in_hori_alpha2 {r : Type _} [Nonempty r] (i j : Nat) (a : Event r)
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

theorem EX1_isFailureOf_in_vert_alpha2 {r : Type _} [Nonempty r] (i j : Nat) (a : Event r)
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

private theorem FIXn_succ_app {p α : Type _} (m : Nat) (Pf : p → proc p α) (p0 : p) :
    FIXn (m + 1) Pf p0 = Subst_procfun (Pf p0) (FIXn m Pf) := by
  rw [FIXn_def, Function.iterate_succ_apply']
  rfl

/-- The accumulator of a processing element never reaches an event, so the
    finite unfoldings do not depend on it. -/
theorem FIXn_SAfun_acc {r : Type _} [Ring r] (i j : Nat) :
    ∀ m : Nat,
      (∀ r0 r1 : r,
        FIXn m SAfun (ProcName.pe (i, j) r0) = FIXn m SAfun (ProcName.pe (i, j) r1)) ∧
      (∀ r0 r1 x y : r,
        FIXn m SAfun (ProcName.pe' (i, j) r0 x y) =
          FIXn m SAfun (ProcName.pe' (i, j) r1 x y)) := by
  intro m
  induction m with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ m ih =>
      refine ⟨fun r0 r1 => ?_, fun r0 r1 x y => ?_⟩
      · simp only [FIXn_succ_app, SAfun, Subst_procfun, Rec_prefix_def]
        simp only [ih.2 r0 r1]
      · simp only [FIXn_succ_app, SAfun, Subst_procfun]
        simp only [ih.1 (r0 + x * y) (r1 + x * y)]

theorem EX1_isFailureOf_out_hori {r : Type _} [Ring r]
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
        (Ev '' Alpha_pe (r := r) (i, j)) := by
  intro r0 hyp
  have hS : (Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' ({Event.hori (i, j + 1) y} : Set (Event r)))
      = {e | ∃ z, e = Ev (Event.vert (i, j) z) ∨ e = Ev (Event.hori (i, j) z) ∨
          e = Ev (Event.vert (i + 1, j) z) ∨ (e = Ev (Event.hori (i, j + 1) z) ∧ z ≠ y)} := by
    ext e
    simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨a, ⟨z, ha⟩, rfl⟩, hnot⟩
      refine ⟨z, ?_⟩
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rintro rfl
        exact hnot ⟨_, rfl, rfl⟩
    · rintro ⟨z, (rfl | rfl | rfl | ⟨rfl, hz⟩)⟩
      · exact ⟨⟨_, ⟨z, Or.inl rfl⟩, rfl⟩, by rintro ⟨b, rfl, hb⟩; cases hb⟩
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inl rfl)⟩, rfl⟩, by rintro ⟨b, rfl, hb⟩; cases hb⟩
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩,
          by rintro ⟨b, rfl, hb⟩; cases hb⟩
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, rfl, hb⟩
        injection hb with hb
        injection hb with _ hb
        exact hz hb.symm
  refine cspF_subseteqEX_Ext_pre_choice
    (X := ({Event.hori (i, j + 1) y} : Set (Event r)))
    (Pf := fun _ => FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))
    (Ff := fun _ => peF_rec (r := r) n (i, j))
    cspF_reflex_eq_P ?_ ?_
  · ext f
    simp only [Faiures_out_hori, Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq,
      Set.mem_singleton_iff, hS]
    constructor
    · rintro (h0 | ⟨s, Y, rfl, hsY⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨_, s, Y, rfl, hsY, rfl⟩
    · rintro (h0 | ⟨a, s, Y, rfl, hsY, rfl⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨s, Y, rfl, hsY⟩
  · intro a _
    rw [(FIXn_SAfun_acc i j (n + n)).1 (r0 + x * y) r0]
    exact hyp

theorem EX1_isFailureOf_out_vert {r : Type _} [Ring r]
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
        (Ev '' Alpha_pe (r := r) (i, j)) := by
  intro r0 hyp
  have hS : (Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' ({Event.vert (i + 1, j) x} : Set (Event r)))
      = {e | ∃ z, e = Ev (Event.hori (i, j) z) ∨ e = Ev (Event.vert (i, j) z) ∨
          e = Ev (Event.hori (i, j + 1) z) ∨ (e = Ev (Event.vert (i + 1, j) z) ∧ z ≠ x)} := by
    ext e
    simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨a, ⟨z, ha⟩, rfl⟩, hnot⟩
      refine ⟨z, ?_⟩
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rintro rfl
        exact hnot ⟨_, rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl rfl))
    · rintro ⟨z, (rfl | rfl | rfl | ⟨rfl, hz⟩)⟩
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inl rfl)⟩, rfl⟩, by rintro ⟨b, rfl, hb⟩; cases hb⟩
      · exact ⟨⟨_, ⟨z, Or.inl rfl⟩, rfl⟩, by rintro ⟨b, rfl, hb⟩; cases hb⟩
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩,
          by rintro ⟨b, rfl, hb⟩; cases hb⟩
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, rfl, hb⟩
        injection hb with hb
        injection hb with _ hb
        exact hz hb.symm
  refine cspF_subseteqEX_Ext_pre_choice
    (X := ({Event.vert (i + 1, j) x} : Set (Event r)))
    (Pf := fun _ => FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))
    (Ff := fun _ => peF_rec (r := r) n (i, j))
    cspF_reflex_eq_P ?_ ?_
  · ext f
    simp only [Faiures_out_vert, Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq,
      Set.mem_singleton_iff, hS]
    constructor
    · rintro (h0 | ⟨s, Y, rfl, hsY⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨_, s, Y, rfl, hsY, rfl⟩
    · rintro (h0 | ⟨a, s, Y, rfl, hsY, rfl⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨s, Y, rfl, hsY⟩
  · intro a _
    rw [(FIXn_SAfun_acc i j (n + n)).1 (r0 + x * y) r0]
    exact hyp

theorem EX1_isFailureOf_out {r : Type _} [Ring r]
    (n i j : Nat) (x y r0 : r) :
    (∀ r1 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r1)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))) →
    Faiures_out x y (i, j) (peF_rec (r := r) n (i, j)) <=EX
      restRefusal
        (failures (FIXn (Nat.succ (n + n)) SAfun (ProcName.pe' (i, j) r0 x y)) MF)
        (Ev '' Alpha_pe (r := r) (i, j)) := by
  intro hyp
  have hS : (Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r)))
      = {e | ∃ z, e = Ev (Event.hori (i, j) z) ∨ e = Ev (Event.vert (i, j) z) ∨
          (e = Ev (Event.hori (i, j + 1) z) ∧ z ≠ y) ∨
          (e = Ev (Event.vert (i + 1, j) z) ∧ z ≠ x)} := by
    ext e
    simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨a, ⟨z, ha⟩, rfl⟩, hnot⟩
      refine ⟨z, ?_⟩
      rcases ha with rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · refine Or.inr (Or.inr (Or.inr ⟨rfl, ?_⟩))
        rintro rfl
        exact hnot ⟨_, Or.inl rfl, rfl⟩
      · refine Or.inr (Or.inr (Or.inl ⟨rfl, ?_⟩))
        rintro rfl
        exact hnot ⟨_, Or.inr rfl, rfl⟩
    · rintro ⟨z, (rfl | rfl | ⟨rfl, hz⟩ | ⟨rfl, hz⟩)⟩
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inl rfl)⟩, rfl⟩,
          by rintro ⟨b, (rfl | rfl), hb⟩ <;> cases hb⟩
      · exact ⟨⟨_, ⟨z, Or.inl rfl⟩, rfl⟩,
          by rintro ⟨b, (rfl | rfl), hb⟩ <;> cases hb⟩
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, (rfl | rfl), hb⟩
        · cases hb
        · injection hb with hb
          injection hb with _ hb
          exact hz hb.symm
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, (rfl | rfl), hb⟩
        · injection hb with hb
          injection hb with _ hb
          exact hz hb.symm
        · cases hb
  refine cspF_subseteqEX_Ext_pre_choice
    (X := ({Event.vert (i + 1, j) x, Event.hori (i, j + 1) y} : Set (Event r)))
    (Pf := fun a =>
      if a = Event.vert (i + 1, j) x then
        proc.Ext_pre_choice ({Event.hori (i, j + 1) y} : Set (Event r)) (fun _ =>
          FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y)))
      else
        proc.Ext_pre_choice ({Event.vert (i + 1, j) x} : Set (Event r)) (fun _ =>
          FIXn (n + n) SAfun (ProcName.pe (i, j) (r0 + x * y))))
    (Ff := fun a =>
      if a ∈ Set.range (Event.vert (i + 1, j) (r := r))
      then Faiures_out_hori y (i, j) (peF_rec (r := r) n (i, j))
      else Faiures_out_vert x (i, j) (peF_rec (r := r) n (i, j)))
    (pe_expand_out n i j r0 x y) ?_ ?_
  · ext f
    simp only [Faiures_out, Set.mem_union, Set.mem_insert_iff, Set.mem_setOf_eq,
      Set.mem_singleton_iff, hS]
    constructor
    · rintro ((h0 | ⟨s, Y, rfl, hF⟩) | ⟨s, Y, rfl, hF⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨_, s, Y, rfl, by rw [if_pos ⟨x, rfl⟩]; exact hF, Or.inl rfl⟩
      · exact Or.inr ⟨_, s, Y, rfl, by rw [if_neg hori_notin_range_vert]; exact hF, Or.inr rfl⟩
    · rintro (h0 | ⟨a, s, Y, rfl, hF, (rfl | rfl)⟩)
      · exact Or.inl (Or.inl h0)
      · rw [if_pos ⟨x, rfl⟩] at hF
        exact Or.inl (Or.inr ⟨s, Y, rfl, hF⟩)
      · rw [if_neg hori_notin_range_vert] at hF
        exact Or.inr ⟨s, Y, rfl, hF⟩
  · rintro a (rfl | rfl)
    · dsimp only
      rw [if_pos ⟨x, rfl⟩, if_pos rfl]
      exact EX1_isFailureOf_out_hori n i j x y r0 (hyp r0)
    · dsimp only
      rw [if_neg hori_notin_range_vert, if_neg (fun h => hori_notin_range_vert ⟨x, h.symm⟩)]
      exact EX1_isFailureOf_out_vert n i j x y r0 (hyp r0)

/- in -/

theorem EX1_isFailureOf_in_hori {r : Type _} [Ring r]
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
        (Ev '' Alpha_pe (r := r) (i, j)) := by
  intro hyp _ha
  have hS : (Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' Set.range (Event.hori (i, j) (r := r)))
      = {e | ∃ z, e = Ev (Event.vert (i, j) z) ∨ e = Ev (Event.hori (i, j + 1) z) ∨
          e = Ev (Event.vert (i + 1, j) z)} := by
    ext e
    simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨b, ⟨z, hb⟩, rfl⟩, hnot⟩
      refine ⟨z, ?_⟩
      rcases hb with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact absurd ⟨_, ⟨z, rfl⟩, rfl⟩ hnot
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
    · rintro ⟨z, (rfl | rfl | rfl)⟩
      · exact ⟨⟨_, ⟨z, Or.inl rfl⟩, rfl⟩, by rintro ⟨b, ⟨w, rfl⟩, hb⟩; cases hb⟩
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, ⟨w, rfl⟩, hb⟩
        injection hb with hb
        injection hb with hb
        simp at hb
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩,
          by rintro ⟨b, ⟨w, rfl⟩, hb⟩; cases hb⟩
  refine cspF_subseteqEX_Ext_pre_choice
    (X := Set.range (Event.hori (i, j) (r := r)))
    (Pf := fun b => FIXn (Nat.succ (n + n)) SAfun
      (ProcName.pe' (i, j) r0 (Function.invFun (Event.vert (i, j)) a)
        (Function.invFun (Event.hori (i, j)) b)))
    (Ff := fun b => Faiures_out (Function.invFun (Event.vert (i, j)) a)
      (Function.invFun (Event.hori (i, j)) b) (i, j) (peF_rec (r := r) n (i, j)))
    ?_ ?_ ?_
  · simp only [Rec_prefix_def, Set.image_univ]
    exact cspF_reflex_eq_P
  · rw [Faiures_in_hori, ← hS,
      EX1_isFailureOf_in_hori_alpha2 i j a (peF_rec (r := r) n (i, j))]
    exact (Set.insert_eq _ _).symm
  · intro b _
    exact EX1_isFailureOf_out n i j (Function.invFun (Event.vert (i, j)) a)
      (Function.invFun (Event.hori (i, j)) b) r0 hyp

theorem EX1_isFailureOf_in_vert {r : Type _} [Ring r]
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
        (Ev '' Alpha_pe (r := r) (i, j)) := by
  intro hyp _ha _ha2
  have hS : (Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' Set.range (Event.vert (i, j) (r := r)))
      = {e | ∃ z, e = Ev (Event.hori (i, j) z) ∨ e = Ev (Event.vert (i + 1, j) z) ∨
          e = Ev (Event.hori (i, j + 1) z)} := by
    ext e
    simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨⟨b, ⟨z, hb⟩, rfl⟩, hnot⟩
      refine ⟨z, ?_⟩
      rcases hb with rfl | rfl | rfl | rfl
      · exact absurd ⟨_, ⟨z, rfl⟩, rfl⟩ hnot
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    · rintro ⟨z, (rfl | rfl | rfl)⟩
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inl rfl)⟩, rfl⟩,
          by rintro ⟨b, ⟨w, rfl⟩, hb⟩; cases hb⟩
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, ⟨w, rfl⟩, hb⟩
        injection hb with hb
        injection hb with hb
        simp at hb
      · exact ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩,
          by rintro ⟨b, ⟨w, rfl⟩, hb⟩; cases hb⟩
  refine cspF_subseteqEX_Ext_pre_choice
    (X := Set.range (Event.vert (i, j) (r := r)))
    (Pf := fun b => FIXn (Nat.succ (n + n)) SAfun
      (ProcName.pe' (i, j) r0 (Function.invFun (Event.vert (i, j)) b)
        (Function.invFun (Event.hori (i, j)) a)))
    (Ff := fun b => Faiures_out (Function.invFun (Event.vert (i, j)) b)
      (Function.invFun (Event.hori (i, j)) a) (i, j) (peF_rec (r := r) n (i, j)))
    ?_ ?_ ?_
  · simp only [Rec_prefix_def, Set.image_univ]
    exact cspF_reflex_eq_P
  · rw [Faiures_in_vert, ← hS,
      EX1_isFailureOf_in_vert_alpha2 i j a (peF_rec (r := r) n (i, j))]
    exact (Set.insert_eq _ _).symm
  · intro b _
    exact EX1_isFailureOf_out n i j (Function.invFun (Event.vert (i, j)) b)
      (Function.invFun (Event.hori (i, j)) a) r0 hyp

theorem EX1_isFailureOf_in {r : Type _} [Ring r]
    (n i j : Nat) (r0 : r) :
    (∀ r0 : r,
      peF_rec (r := r) n (i, j) <=EX
        restRefusal
          (failures (FIXn (n + n) SAfun (ProcName.pe (i, j) r0)) MF)
          (Ev '' Alpha_pe (r := r) (i, j))) →
    Faiures_in (r := r) (i, j) (peF_rec (r := r) n (i, j)) <=EX
      restRefusal
        (failures (FIXn (Nat.succ (Nat.succ (n + n))) SAfun (ProcName.pe (i, j) r0)) MF)
        (Ev '' Alpha_pe (r := r) (i, j)) := by
  intro hyp
  have hS : (Ev '' Alpha_pe (r := r) (i, j) \
        Ev '' (Set.range (Event.vert (i, j) (r := r)) ∪ Set.range (Event.hori (i, j) (r := r))))
      = {e | ∃ z, e = Ev (Event.vert (i + 1, j) z) ∨ e = Ev (Event.hori (i, j + 1) z)} := by
    ext e
    simp only [Alpha_pe, Set.mem_diff, Set.mem_image, Set.mem_setOf_eq, Set.mem_union,
      Set.mem_range]
    constructor
    · rintro ⟨⟨b, ⟨z, hb⟩, rfl⟩, hnot⟩
      refine ⟨z, ?_⟩
      rcases hb with rfl | rfl | rfl | rfl
      · exact absurd ⟨_, Or.inl ⟨z, rfl⟩, rfl⟩ hnot
      · exact absurd ⟨_, Or.inr ⟨z, rfl⟩, rfl⟩ hnot
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro ⟨z, (rfl | rfl)⟩
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inl rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, (⟨w, rfl⟩ | ⟨w, rfl⟩), hb⟩
        · injection hb with hb
          injection hb with hb
          simp at hb
        · cases hb
      · refine ⟨⟨_, ⟨z, Or.inr (Or.inr (Or.inr rfl))⟩, rfl⟩, ?_⟩
        rintro ⟨b, (⟨w, rfl⟩ | ⟨w, rfl⟩), hb⟩
        · cases hb
        · injection hb with hb
          injection hb with hb
          simp at hb
  refine cspF_subseteqEX_Ext_pre_choice
    (X := Set.range (Event.vert (i, j) (r := r)) ∪ Set.range (Event.hori (i, j) (r := r)))
    (Pf := fun a =>
      IF a ∈ Set.range (Event.vert (i, j))
      THEN
        Rec_prefix (Event.hori (i, j)) Set.univ (fun b =>
          FIXn (Nat.succ (n + n)) SAfun
            (ProcName.pe' (i, j) r0 (Function.invFun (Event.vert (i, j)) a) b))
      ELSE
        Rec_prefix (Event.vert (i, j)) Set.univ (fun b =>
          FIXn (Nat.succ (n + n)) SAfun
            (ProcName.pe' (i, j) r0 b (Function.invFun (Event.hori (i, j)) a))))
    (Ff := fun a =>
      if a ∈ Set.range (Event.vert (i, j) (r := r))
      then Faiures_in_hori (Function.invFun (Event.vert (i, j)) a) (i, j)
        (peF_rec (r := r) n (i, j))
      else Faiures_in_vert (Function.invFun (Event.hori (i, j)) a) (i, j)
        (peF_rec (r := r) n (i, j)))
    (pe_expand_in n i j r0) ?_ ?_
  · rw [Faiures_in, ← hS, Set.union_assoc,
      EX1_isFailureOf_in_alpha2 i j (peF_rec (r := r) n (i, j))]
    exact (Set.insert_eq _ _).symm
  · rintro a ha
    dsimp only
    by_cases hv : a ∈ Set.range (Event.vert (i, j) (r := r))
    · rw [if_pos hv]
      refine cspF_subseteqEX_eqF
        (cspF_trans_left_eq cspF_IF_split
          (by rw [if_pos (show (decide (a ∈ Set.range (Event.vert (i, j) (r := r)))) = true
                    from by simpa using hv)]
              exact cspF_reflex_eq_P)) ?_
      exact EX1_isFailureOf_in_hori n i j r0 a hyp hv
    · rw [if_neg hv]
      refine cspF_subseteqEX_eqF
        (cspF_trans_left_eq cspF_IF_split
          (by rw [if_neg (show ¬ ((decide (a ∈ Set.range (Event.vert (i, j) (r := r)))) = true)
                    from by simpa using hv)]
              exact cspF_reflex_eq_P)) ?_
      refine EX1_isFailureOf_in_vert n i j r0 a hyp ?_ hv
      rcases ha with h | h
      · exact absurd h hv
      · exact h

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
