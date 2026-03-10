           /- -------------------------------------------*
            |                DFP package                |
            |                   June 2005               |
            |               December 2005  (modified)   |
            |                                           |
            |   DFP on CSP-Prover ver.3.0               |
            |              September 2006  (modified)   |
            |                  April 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                    May 2016  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_Main

open Classical

noncomputable section

inductive Event where
  | left : Real → Event
  | right : Real × Nat → Event
deriving DecidableEq, Inhabited

inductive Name where
  | Empty : Nat → Name
  | Full : Real → Nat → Name
deriving DecidableEq, Inhabited

inductive DFName where
  | DF
deriving DecidableEq, Inhabited

def Bufferfun : Name → proc Name Event
  | Name.Empty n => Rec_prefix Event.left Set.univ fun r => proc.Proc_name (Name.Full r n)
  | Name.Full r n => Event.right (r, n) ~> proc.Proc_name (Name.Empty (Nat.succ n))

instance Set_Bufferfun : HasPNfun Name Event where
  PNfun := Bufferfun

@[simp]
theorem Set_Bufferfun_def (pn : Name) :
    PNfun pn = Bufferfun pn :=
  rfl

/- *****************************************************************

  1. safe subsets of [[P]]F, used for deadlock-free verification.

 *****************************************************************) -/

/- *********************************************************
                    safe cut of [[_]]F
        This is used for deadlock-free verification.
 *********************************************************) -/

def restRefusal {α : Type _} (F : setFType α) (A : Set (event α)) : Set (failure α) :=
  {f | f :f F ∧ f.2 ⊆ A}

theorem restRefusal_def {α : Type _} (F : setFType α) (A : Set (event α)) :
    restRefusal F A = {f | f :f F ∧ f.2 ⊆ A} :=
  rfl

def subseteqEX {α : Type _} (F E : Set (failure α)) : Prop :=
  F ⊆ E ∧ ∀ s Y, (s, Y) ∈ E → ∃ Z, (s, Z) ∈ F ∧ Y ⊆ Z

infix:50 " <=EX " => subseteqEX

theorem subseteqEX_def {α : Type _} {F E : Set (failure α)} :
    (F <=EX E) ↔ F ⊆ E ∧ ∀ s Y, (s, Y) ∈ E → ∃ Z, (s, Z) ∈ F ∧ Y ⊆ Z :=
  Iff.rfl

/- *********************************************************
                subseteqEX &  restRefusal
 *********************************************************) -/

theorem subseteqEX_reflex {α : Type _} {F : Set (failure α)} : F <=EX F := by
  constructor
  · intro f hf
    exact hf
  · intro s Y hs
    exact ⟨Y, hs, Set.Subset.rfl⟩

theorem subseteqEX_Int {α : Type _} {F : setFType α} {A : Set (event α)} :
    restRefusal F A = {f : failure α | ∃ s Y, f = (s, Y ∩ A) ∧ (s, Y) :f F} := by
  ext f
  rcases f with ⟨s, X⟩
  constructor
  · intro h
    refine ⟨s, X, ?_, h.1⟩
    have hX : X = X ∩ A := by
      ext e
      constructor
      · intro he
        exact ⟨he, h.2 he⟩
      · intro he
        exact he.1
    exact congrArg (fun Y => (s, Y)) hX
  · rintro ⟨s', Y, hEq, hsY⟩
    rcases Prod.mk.inj hEq with ⟨hs, hX⟩
    subst hs
    subst hX
    exact ⟨memF_F2 hsY Set.inter_subset_left, Set.inter_subset_right⟩

theorem subseteqEX_restRefusal_iff {α : Type _} {F : Set (failure α)}
    {E : setFType α} {A : Set (event α)} :
    (F <=EX restRefusal E A) ↔
      ((∀ s Y, (s, Y) ∈ F → (s, Y) :f E ∧ Y ⊆ A) ∧
        (∀ s Y, (s, Y) :f E → ∃ Z, (s, Z) ∈ F ∧ Y ∩ A ⊆ Z)) := by
  constructor
  · intro h
    constructor
    · intro s Y hs
      exact h.1 hs
    · intro s Y hsE
      have hsRest : (s, Y ∩ A) ∈ restRefusal E A := by
        exact ⟨memF_F2 hsE Set.inter_subset_left, Set.inter_subset_right⟩
      exact h.2 s (Y ∩ A) hsRest
  · intro h
    constructor
    · intro f hf
      rcases f with ⟨s, Y⟩
      exact h.1 s Y hf
    · intro s Y hs
      rcases h.2 s Y hs.1 with ⟨Z, hZF, hYZ⟩
      refine ⟨Z, hZF, ?_⟩
      intro e he
      exact hYZ ⟨he, hs.2 he⟩

/- *********************************************************
        How to prove F <=EX ([[P]]F restRefusal A)
 *********************************************************) -/

/- --------------------*
 |        DIV         |
 *-------------------- -/

theorem subseteqEX_DIV {p α : Type _} [HasPNfun p α] [HasFPmode] {A : Set (event α)} :
    (∅ : Set (failure α)) <=EX restRefusal (failures (proc.DIV : proc p α) MF) A := by
  constructor
  · intro f hf
    exact False.elim hf
  · intro s Y hs
    exact False.elim ((in_failures_DIV (f := (s, Y)) (M := MF)) hs.1)

/- -----------*
 | csp rules |
 *----------- -/

theorem cspF_subseteqEX_DIV {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P : proc p α} {A : Set (event α)}
    (hP : eqFfix P (proc.DIV : proc p α)) :
    (∅ : Set (failure α)) <=EX restRefusal (failures P MF) A := by
  have hFail : failures P MF = failures (proc.DIV : proc p α) MF :=
    (cspF_eqF_semantics (P := P) (Q := (proc.DIV : proc p α)) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hFail] using (subseteqEX_DIV (p := p) (α := α) (A := A))

/- --------------------*
 |     Int_choice     |
 *-------------------- -/

/- eq -/

theorem subseteqEX_Int_choice {p α : Type _} [HasPNfun p α] [HasFPmode]
    {F1 F2 : Set (failure α)} {P1 P2 : proc p α} {A : Set (event α)}
    (h1 : F1 <=EX restRefusal (failures P1 MF) A)
    (h2 : F2 <=EX restRefusal (failures P2 MF) A) :
    F1 ∪ F2 <=EX restRefusal (failures (P1 |~| P2) MF) A := by
  rw [subseteqEX_restRefusal_iff] at h1 h2 ⊢
  constructor
  · intro s Y hs
    rcases hs with hs | hs
    · have hRest := h1.1 s Y hs
      exact ⟨(in_failures_Int_choice (f := (s, Y)) (P := P1) (Q := P2) (M := MF)).2 (Or.inl hRest.1), hRest.2⟩
    · have hRest := h2.1 s Y hs
      exact ⟨(in_failures_Int_choice (f := (s, Y)) (P := P1) (Q := P2) (M := MF)).2 (Or.inr hRest.1), hRest.2⟩
  · intro s Y hs
    rcases (in_failures_Int_choice (f := (s, Y)) (P := P1) (Q := P2) (M := MF)).1 hs with hsP1 | hsP2
    · rcases h1.2 s Y hsP1 with ⟨Z, hZF, hYZ⟩
      refine ⟨Z, Or.inl hZF, hYZ⟩
    · rcases h2.2 s Y hsP2 with ⟨Z, hZF, hYZ⟩
      refine ⟨Z, Or.inr hZF, hYZ⟩

/- -----------*
 | csp rules |
 *----------- -/

theorem cspF_subseteqEX_Int_choice {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P P1 P2 : proc p α} {F F1 F2 : Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (P1 |~| P2))
    (hF : F = F1 ∪ F2)
    (h1 : F1 <=EX restRefusal (failures P1 MF) A)
    (h2 : F2 <=EX restRefusal (failures P2 MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  have hFail : failures P MF = failures (P1 |~| P2) MF :=
    (cspF_eqF_semantics (P := P) (Q := P1 |~| P2) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hF, hFail] using
    (subseteqEX_Int_choice (p := p) (α := α) (P1 := P1) (P2 := P2) (A := A) h1 h2)

/- ------------------------*
 |   Rep_int_choice_nat   |
 *------------------------ -/

/- eq -/

theorem subseteqEX_Rep_int_choice_nat {p α : Type _} [HasPNfun p α] [HasFPmode]
    {N : Set Nat} {Pf : Nat → proc p α} {Ff : Nat → Set (failure α)} {A : Set (event α)}
    (hAll : ∀ n ∈ N, Ff n <=EX restRefusal (failures (Pf n) MF) A) :
    ⋃₀ (Ff '' N) <=EX restRefusal (failures (Rep_int_choice_nat N Pf) MF) A := by
  rw [subseteqEX_restRefusal_iff]
  constructor
  · intro s Y hs
    rcases Set.mem_sUnion.mp hs with ⟨G, hG, hsG⟩
    rcases hG with ⟨n, hnN, rfl⟩
    have hRest := (hAll n hnN).1 hsG
    exact ⟨(in_failures_Rep_int_choice_nat (f := (s, Y)) (N := N) (Pf := Pf) (M := MF)).2 ⟨n, hnN, hRest.1⟩, hRest.2⟩
  · intro s Y hs
    rcases (in_failures_Rep_int_choice_nat (f := (s, Y)) (N := N) (Pf := Pf) (M := MF)).1 hs with ⟨n, hnN, hsN⟩
    rcases (subseteqEX_restRefusal_iff.mp (hAll n hnN)).2 s Y hsN with ⟨Z, hZF, hYZ⟩
    refine ⟨Z, Set.mem_sUnion.mpr ⟨Ff n, ⟨n, hnN, rfl⟩, hZF⟩, hYZ⟩

/- -----------*
 | csp rules |
 *----------- -/

theorem cspF_subseteqEX_Rep_int_choice_nat {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P : proc p α} {N : Set Nat} {Pf : Nat → proc p α}
    {F : Set (failure α)} {Ff : Nat → Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (Rep_int_choice_nat N Pf))
    (hF : F = ⋃₀ (Ff '' N))
    (hAll : ∀ n ∈ N, Ff n <=EX restRefusal (failures (Pf n) MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  have hFail : failures P MF = failures (Rep_int_choice_nat N Pf) MF :=
    (cspF_eqF_semantics (P := P) (Q := Rep_int_choice_nat N Pf) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hF, hFail] using
    (subseteqEX_Rep_int_choice_nat (p := p) (α := α) (N := N) (Pf := Pf) (Ff := Ff) (A := A) hAll)

/- ------------------------*
 |   Rep_int_choice_set   |
 *------------------------ -/

/- eq -/

theorem subseteqEX_Rep_int_choice_set {p α : Type _} [HasPNfun p α] [HasFPmode]
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Ff : Set α → Set (failure α)} {A : Set (event α)}
    (hAll : ∀ X ∈ Xs, Ff X <=EX restRefusal (failures (Pf X) MF) A) :
    ⋃₀ (Ff '' Xs) <=EX restRefusal (failures (Rep_int_choice_set Xs Pf) MF) A := by
  rw [subseteqEX_restRefusal_iff]
  constructor
  · intro s Y hs
    rcases Set.mem_sUnion.mp hs with ⟨G, hG, hsG⟩
    rcases hG with ⟨X, hXXs, rfl⟩
    have hRest := (hAll X hXXs).1 hsG
    exact ⟨(in_failures_Rep_int_choice_set (f := (s, Y)) (Xs := Xs) (Pf := Pf) (M := MF)).2 ⟨X, hXXs, hRest.1⟩, hRest.2⟩
  · intro s Y hs
    rcases (in_failures_Rep_int_choice_set (f := (s, Y)) (Xs := Xs) (Pf := Pf) (M := MF)).1 hs with ⟨X, hXXs, hsX⟩
    rcases (subseteqEX_restRefusal_iff.mp (hAll X hXXs)).2 s Y hsX with ⟨Z, hZF, hYZ⟩
    refine ⟨Z, Set.mem_sUnion.mpr ⟨Ff X, ⟨X, hXXs, rfl⟩, hZF⟩, hYZ⟩

/- -----------*
 | csp rules |
 *----------- -/

theorem cspF_subseteqEX_Rep_int_choice_set {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P : proc p α} {Xs : Set (Set α)} {Pf : Set α → proc p α}
    {F : Set (failure α)} {Ff : Set α → Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (Rep_int_choice_set Xs Pf))
    (hF : F = ⋃₀ (Ff '' Xs))
    (hAll : ∀ X ∈ Xs, Ff X <=EX restRefusal (failures (Pf X) MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  have hFail : failures P MF = failures (Rep_int_choice_set Xs Pf) MF :=
    (cspF_eqF_semantics (P := P) (Q := Rep_int_choice_set Xs Pf) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hF, hFail] using
    (subseteqEX_Rep_int_choice_set (p := p) (α := α) (Xs := Xs) (Pf := Pf) (Ff := Ff) (A := A) hAll)

/- com -/

theorem cspF_subseteqEX_Rep_int_choice_com {p α : Type _} [Inhabited α] [HasPNfun p α] [HasFPmode]
    {P : proc p α} {X : Set α} {Pf : α → proc p α}
    {F : Set (failure α)} {Ff : α → Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (Rep_int_choice_com X Pf))
    (hF : F = ⋃₀ (Ff '' X))
    (hAll : ∀ a ∈ X, Ff a <=EX restRefusal (failures (Pf a) MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  have hBase : ⋃₀ (Ff '' X) <=EX restRefusal (failures (Rep_int_choice_com X Pf) MF) A := by
    rw [subseteqEX_restRefusal_iff]
    constructor
    · intro s Y hs
      rcases Set.mem_sUnion.mp hs with ⟨G, hG, hsG⟩
      rcases hG with ⟨a, haX, rfl⟩
      have hRest := (hAll a haX).1 hsG
      exact ⟨(in_failures_Rep_int_choice_com (f := (s, Y)) (X := X) (Pf := Pf) (M := MF)).2 ⟨a, haX, hRest.1⟩, hRest.2⟩
    · intro s Y hs
      rcases (in_failures_Rep_int_choice_com (f := (s, Y)) (X := X) (Pf := Pf) (M := MF)).1 hs with ⟨a, haX, hsA⟩
      rcases (subseteqEX_restRefusal_iff.mp (hAll a haX)).2 s Y hsA with ⟨Z, hZF, hYZ⟩
      refine ⟨Z, Set.mem_sUnion.mpr ⟨Ff a, ⟨a, haX, rfl⟩, hZF⟩, hYZ⟩
  have hFail : failures P MF = failures (Rep_int_choice_com X Pf) MF :=
    (cspF_eqF_semantics (P := P) (Q := Rep_int_choice_com X Pf) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hF, hFail] using hBase

/- f -/

theorem cspF_subseteqEX_Rep_int_choice_f {p α β : Type _} [Inhabited α] [Inhabited β]
    [HasPNfun p α] [HasFPmode]
    {f : β → α} (hf : Function.Injective f)
    {P : proc p α} {X : Set β} {Pf : β → proc p α}
    {F : Set (failure α)} {Ff : β → Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (Rep_int_choice_f f X Pf))
    (hF : F = ⋃₀ (Ff '' X))
    (hAll : ∀ a ∈ X, Ff a <=EX restRefusal (failures (Pf a) MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  have hBase : ⋃₀ (Ff '' X) <=EX restRefusal (failures (Rep_int_choice_f f X Pf) MF) A := by
    rw [subseteqEX_restRefusal_iff]
    constructor
    · intro s Y hs
      rcases Set.mem_sUnion.mp hs with ⟨G, hG, hsG⟩
      rcases hG with ⟨a, haX, rfl⟩
      have hRest := (hAll a haX).1 hsG
      exact ⟨(in_failures_Rep_int_choice_f (f := (s, Y)) (g := f) hf (X := X) (Pf := Pf) (M := MF)).2 ⟨a, haX, hRest.1⟩, hRest.2⟩
    · intro s Y hs
      rcases (in_failures_Rep_int_choice_f (f := (s, Y)) (g := f) hf (X := X) (Pf := Pf) (M := MF)).1 hs with ⟨a, haX, hsA⟩
      rcases (subseteqEX_restRefusal_iff.mp (hAll a haX)).2 s Y hsA with ⟨Z, hZF, hYZ⟩
      refine ⟨Z, Set.mem_sUnion.mpr ⟨Ff a, ⟨a, haX, rfl⟩, hZF⟩, hYZ⟩
  have hFail : failures P MF = failures (Rep_int_choice_f f X Pf) MF :=
    (cspF_eqF_semantics (P := P) (Q := Rep_int_choice_f f X Pf) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hF, hFail] using hBase

/- The Isabelle theorem bundle `cspF_subseteqEX_Rep_int_choice` is
   represented by `cspF_subseteqEX_Rep_int_choice_nat`,
   `cspF_subseteqEX_Rep_int_choice_set`,
   `cspF_subseteqEX_Rep_int_choice_com`, and
   `cspF_subseteqEX_Rep_int_choice_f`. -/

theorem cspF_subseteqEX_Rep_int_choice_nat_UNIV {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P : proc p α} {Pf : Nat → proc p α}
    {F : Set (failure α)} {Ff : Nat → Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (Rep_int_choice_nat Set.univ Pf))
    (hF : F = ⋃₀ (Ff '' (Set.univ : Set Nat)))
    (hAll : ∀ a, Ff a <=EX restRefusal (failures (Pf a) MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  apply cspF_subseteqEX_Rep_int_choice_nat (P := P) (N := Set.univ) (Pf := Pf) (F := F) (Ff := Ff) (A := A)
  · exact hP
  · exact hF
  · intro a _ha
    exact hAll a

/- --------------------*
 |   Ext_pre_choice   |
 *-------------------- -/

/- eq -/

theorem subseteqEX_Ext_pre_choice {p α : Type _} [HasPNfun p α] [HasFPmode]
    {X : Set α} {Pf : α → proc p α} {Ff : α → Set (failure α)} {A : Set (event α)}
    (hAll : ∀ a ∈ X, Ff a <=EX restRefusal (failures (Pf a) MF) A) :
    insert ((<> : traceType α), A \ (event.Ev '' X))
      {f : failure α |
        ∃ a s Y, f = (Abs_trace [event.Ev a] ^^^ s, Y) ∧ (s, Y) ∈ Ff a ∧ a ∈ X}
      <=EX restRefusal (failures (proc.Ext_pre_choice X Pf) MF) A := by
  rw [subseteqEX_restRefusal_iff]
  constructor
  · intro s Y hs
    rcases hs with hInit | hs
    · rcases Prod.mk.inj hInit with ⟨hsEq, hYEq⟩
      subst hsEq
      subst hYEq
      refine ⟨?_, Set.diff_subset⟩
      refine (in_failures_Ext_pre_choice
        (f := (((<> : traceType α), A \ (event.Ev '' X)) : failure α))
        (X := X) (Pf := Pf) (M := MF)).2 ?_
      left
      refine ⟨A \ (event.Ev '' X), rfl, ?_⟩
      ext e
      simp
    · rcases hs with ⟨a, t, Z, hEq, hsF, haX⟩
      rcases Prod.mk.inj hEq with ⟨hs, hY⟩
      subst hs
      subst hY
      have hRest := (hAll a haX).1 hsF
      have hMem : (((Abs_trace [event.Ev a] : traceType α) ^^^ t), Y) :f
          failures (proc.Ext_pre_choice X Pf) MF := by
        refine (in_failures_Ext_pre_choice
          (f := (((Abs_trace [event.Ev a] ^^^ t), Y) : failure α))
          (X := X) (Pf := Pf) (M := MF)).2 ?_
        right
        exact ⟨a, t, Y, rfl, hRest.1, haX⟩
      exact ⟨hMem, hRest.2⟩
  · intro s Y hs
    rcases (in_failures_Ext_pre_choice (f := (s, Y)) (X := X) (Pf := Pf) (M := MF)).1 hs with hInit | hStep
    · rcases hInit with ⟨Z, hEq, hEmpty⟩
      rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
      subst hsEq
      subst hYEq
      refine ⟨A \ (event.Ev '' X), Set.mem_insert _ _, ?_⟩
      intro e he
      refine ⟨he.2, ?_⟩
      intro heX
      have : e ∈ (event.Ev '' X) ∩ Y := ⟨heX, he.1⟩
      simp [hEmpty] at this
    · rcases hStep with ⟨a, t, Z, hEq, hsF, haX⟩
      rcases Prod.mk.inj hEq with ⟨hsEq, hYEq⟩
      subst hsEq
      subst hYEq
      rcases (subseteqEX_restRefusal_iff.mp (hAll a haX)).2 t Y hsF with ⟨W, hWF, hYW⟩
      refine ⟨W, Set.mem_insert_of_mem _ ⟨a, t, W, rfl, hWF, haX⟩, ?_⟩
      intro e he
      exact hYW he

/- -----------*
 | csp rules |
 *----------- -/

theorem cspF_subseteqEX_Ext_pre_choice {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P : proc p α} {X : Set α} {Pf : α → proc p α}
    {F : Set (failure α)} {Ff : α → Set (failure α)} {A : Set (event α)}
    (hP : eqFfix P (proc.Ext_pre_choice X Pf))
    (hF : F =
      insert ((<> : traceType α), A \ (event.Ev '' X))
        {f : failure α |
          ∃ a s Y, f = (Abs_trace [event.Ev a] ^^^ s, Y) ∧ (s, Y) ∈ Ff a ∧ a ∈ X})
    (hAll : ∀ a ∈ X, Ff a <=EX restRefusal (failures (Pf a) MF) A) :
    F <=EX restRefusal (failures P MF) A := by
  have hFail : failures P MF = failures (proc.Ext_pre_choice X Pf) MF :=
    (cspF_eqF_semantics (P := P) (Q := proc.Ext_pre_choice X Pf) (M1 := MF) (M2 := MF)).1 hP |>.2
  simpa [hF, hFail] using
    (subseteqEX_Ext_pre_choice (p := p) (α := α) (X := X) (Pf := Pf) (Ff := Ff) (A := A) hAll)

/- -----------*
 | csp rules |
 *----------- -/

theorem cspF_subseteqEX_eqF {p α : Type _} [HasPNfun p α] [HasFPmode]
    {P Q : proc p α} {FS : Set (failure α)} {A : Set (event α)}
    (hPQ : eqFfix P Q)
    (hFS : FS <=EX restRefusal (failures Q MF) A) :
    FS <=EX restRefusal (failures P MF) A := by
  have hFail : failures P MF = failures Q MF :=
    (cspF_eqF_semantics (P := P) (Q := Q) (M1 := MF) (M2 := MF)).1 hPQ |>.2
  simpa [hFail] using hFS

/- (****************** to add them again ******************) -/

end
