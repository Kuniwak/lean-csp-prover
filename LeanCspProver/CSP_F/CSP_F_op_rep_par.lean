           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                    May 2005               |
            |                   June 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |               November 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2017         |
            |                  April 2018  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_op_alpha_par
import LeanCspProver.CSP_T.CSP_T_op_rep_par

open event

noncomputable section

/-  The following simplification rules are deleted in this theory file. -/
/-  Lean has no direct analogue of Isabelle's `Sup_image_eq`,           -/
/-  `Inf_image_eq`, or `disj_not1`, so there is nothing to disable.     -/

/-============================================================*
 |                                                            |
 |            replicated alphabetized parallel                |
 |                                                            |
 *============================================================-/

/- (*** Inductive_parallel ***) -/

private theorem set_cons'' {β : Type _} (a : β) (s : List β) :
    _root_.set (a :: s) = insert a (_root_.set s) := by
  rw [set_cons]
  rfl
private theorem set_map' {β γ : Type _} (f : β → γ) (l : List β) :
    _root_.set (l.map f) = f '' _root_.set l := by
  ext x
  simp [_root_.set]
private theorem nth_map_lt {β γ : Type _} [Inhabited β] [Inhabited γ] {f : β → γ}
    {l : List β} {i : Nat} (hi : i < l.length) : nth (l.map f) i = f (nth l i) := by
  have hi' : i < (l.map f).length := by simpa using hi
  rw [nth, nth, List.getD_eq_getElem (l := l.map f) (d := default) hi',
    List.getD_eq_getElem (l := l) (d := default) hi, List.getElem_map]

private theorem nth_zip_lt {β γ : Type _} [Inhabited β] [Inhabited γ] {s : List β} {t : List γ}
    {i : Nat} (hi : i < s.length) (hlen : s.length = t.length) :
    nth (List.zip s t) i = (nth s i, nth t i) := by
  have hz : i < (List.zip s t).length := by
    simpa [List.length_zip, hlen] using hi
  rw [nth, nth, nth, List.getD_eq_getElem (l := List.zip s t) (d := default) hz,
    List.getD_eq_getElem (l := s) (d := default) hi,
    List.getD_eq_getElem (l := t) (d := default) (by omega)]
  simp

/- local copies of the file-private definitions -/

private theorem sUnion_snd_cons' {PX : proc p α × Set α} {PXs : List (proc p α × Set α)} :
    Set.sUnion (Prod.snd '' _root_.set (PX :: PXs)) =
      Prod.snd PX ∪ Set.sUnion (Prod.snd '' _root_.set PXs) := by
  rw [set_cons'', Set.image_insert_eq, Set.sUnion_insert]
private theorem in_failures_SKIP_iff {s : traceType α} {W : Set (event α)}
    {M : p → domFType α} :
    ((s, W) :f failures (proc.SKIP : proc p α) M) ↔
      ((s = <> ∧ W ⊆ Evset) ∨ s = (Abs_trace [event.Tick] : traceType α)) := by
  rw [in_failures_SKIP]
  constructor
  · rintro (⟨V, hEq, hV⟩ | ⟨V, hEq⟩)
    · exact Or.inl ⟨(Prod.mk.inj hEq).1, by rw [(Prod.mk.inj hEq).2]; exact hV⟩
    · exact Or.inr (Prod.mk.inj hEq).1
  · rintro (⟨rfl, hW⟩ | rfl)
    · exact Or.inl ⟨W, rfl, hW⟩
    · exact Or.inr ⟨W, rfl⟩
private theorem sUnion_single {PX : proc p α × Set α} {W : Set (event α)} :
    Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set [(PX, W)] ∧
        S = Set.inter Y (Set.insert Tick (Ev '' X))} =
      Set.inter W (Set.insert Tick (Ev '' Prod.snd PX)) := by
  ext e
  constructor
  · rintro ⟨S, ⟨P, X, Y, hmem, rfl⟩, he⟩
    have hmem' : ((P, X), Y) = (PX, W) := by simpa [_root_.set] using hmem
    rw [← (Prod.mk.inj hmem').1, ← (Prod.mk.inj hmem').2]
    exact he
  · intro he
    exact ⟨Set.inter W (Set.insert Tick (Ev '' Prod.snd PX)),
      ⟨Prod.fst PX, Prod.snd PX, W, by simp [_root_.set], rfl⟩, he⟩
private theorem map_fst_eq_singleton {PX : proc p α × Set α}
    {PXYs : List ((proc p α × Set α) × Set (event α))} :
    List.map Prod.fst PXYs = [PX] → ∃ W, PXYs = [(PX, W)] := by
  cases PXYs with
  | nil => intro h; simp at h
  | cons a t =>
      intro h
      simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at h
      obtain ⟨h1, h2⟩ := h
      subst h2
      exact ⟨a.2, by rw [← h1]⟩
private theorem map_fst_eq_cons {PX : proc p α × Set α} {PXs : List (proc p α × Set α)}
    {PXYs : List ((proc p α × Set α) × Set (event α))} :
    List.map Prod.fst PXYs = PX :: PXs →
      ∃ W zs, PXYs = (PX, W) :: zs ∧ List.map Prod.fst zs = PXs := by
  cases PXYs with
  | nil => intro h; simp at h
  | cons a t =>
      intro h
      simp only [List.map_cons, List.cons.injEq] at h
      exact ⟨a.2, t, by rw [← h.1], h.2⟩
private theorem mem_Set_insert' {β : Type _} {a b : β} {s : Set β} :
    a ∈ Set.insert b s ↔ (a = b ∨ a ∈ s) :=
  Iff.rfl
private theorem pair_pair_inj {P : proc p α} {X' : Set α} {Y' : Set (event α)}
    {PX : proc p α × Set α} {W : Set (event α)} :
    ((P, X'), Y') = (PX, W) → P = Prod.fst PX ∧ X' = Prod.snd PX ∧ Y' = W := fun h =>
  ⟨congrArg Prod.fst (Prod.mk.inj h).1, congrArg Prod.snd (Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
private theorem sUnion_cons {PX : proc p α × Set α} {Y : Set (event α)}
    {PXYs : List ((proc p α × Set α) × Set (event α))} :
    Set.sUnion {S | ∃ P X Y', ((P, X), Y') ∈ _root_.set ((PX, Y) :: PXYs) ∧
        S = Set.inter Y' (Set.insert Tick (Ev '' X))} =
      Set.inter Y (Set.insert Tick (Ev '' Prod.snd PX)) ∪
        Set.sUnion {S | ∃ P X Y', ((P, X), Y') ∈ _root_.set PXYs ∧
          S = Set.inter Y' (Set.insert Tick (Ev '' X))} := by
  ext e
  constructor
  · rintro ⟨S, ⟨P, X, Y', hmem, rfl⟩, he⟩
    rw [set_cons'', Set.mem_insert_iff] at hmem
    rcases hmem with hmem | hmem
    · refine Or.inl ?_
      rw [← (Prod.mk.inj hmem).1, ← (Prod.mk.inj hmem).2]
      exact he
    · exact Or.inr ⟨Set.inter Y' (Set.insert Tick (Ev '' X)), ⟨P, X, Y', hmem, rfl⟩, he⟩
  · rintro (he | ⟨S, ⟨P, X, Y', hmem, rfl⟩, he⟩)
    · exact ⟨Set.inter Y (Set.insert Tick (Ev '' Prod.snd PX)),
        ⟨Prod.fst PX, Prod.snd PX, Y, by rw [set_cons'']; simp, rfl⟩, he⟩
    · exact ⟨Set.inter Y' (Set.insert Tick (Ev '' X)),
        ⟨P, X, Y', by rw [set_cons'']; exact Or.inr hmem, rfl⟩, he⟩

theorem in_failures_Inductive_parallel_lm1
    {a : proc p α × Set α} {Y : Set (event α)}
    {PXYs : List ((proc p α × Set α) × Set (event α))} :
    Set.inter Y (Set.insert Tick (Ev '' Prod.snd a)) ∪
        Set.sUnion {S | ∃ P X Ya, ((P, X), Ya) ∈ _root_.set PXYs ∧
          S = Set.inter Ya (Set.insert Tick (Ev '' X))} =
      Set.sUnion {S | ∃ P X Ya,
        ((P = Prod.fst a ∧ X = Prod.snd a ∧ Ya = Y) ∨ ((P, X), Ya) ∈ _root_.set PXYs) ∧
          S = Set.inter Ya (Set.insert Tick (Ev '' X))} := by
  ext e
  constructor
  · rintro (he | ⟨S, ⟨P, X, Ya, hmem, rfl⟩, he⟩)
    · exact ⟨Set.inter Y (Set.insert Tick (Ev '' Prod.snd a)),
        ⟨Prod.fst a, Prod.snd a, Y, Or.inl ⟨rfl, rfl, rfl⟩, rfl⟩, he⟩
    · exact ⟨Set.inter Ya (Set.insert Tick (Ev '' X)), ⟨P, X, Ya, Or.inr hmem, rfl⟩, he⟩
  · rintro ⟨S, ⟨P, X, Ya, (⟨rfl, rfl, rfl⟩ | hmem), rfl⟩, he⟩
    · exact Or.inl he
    · exact Or.inr ⟨Set.inter Ya (Set.insert Tick (Ev '' X)), ⟨P, X, Ya, hmem, rfl⟩, he⟩

theorem in_failures_Inductive_parallel_lm2
    {s : List ((proc p α × Set α) × Set (event α))} {P : proc p α} {X : Set α}
    {Y : Set (event α)} :
    ((P, X), Y) ∈ _root_.set s → X ⊆ Set.sUnion (Prod.snd '' (Prod.fst '' _root_.set s)) := by
  intro h a ha
  exact ⟨X, ⟨(P, X), ⟨((P, X), Y), h, rfl⟩, rfl⟩, ha⟩

theorem in_failures_Inductive_parallel_lm3
    {zs : List ((proc p α × Set α) × Set (event α))} :
    Set.sUnion
        {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set zs ∧ S = Set.inter Y (Set.insert Tick (Ev '' X))} ⊆
      Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (Prod.fst '' _root_.set zs)))) := by
  rintro e ⟨S, ⟨P, X, Y, hmem, rfl⟩, he⟩
  rcases he.2 with hT | ⟨b, hb, rfl⟩
  · exact Or.inl hT
  · exact Or.inr ⟨b, in_failures_Inductive_parallel_lm2 hmem hb, rfl⟩

theorem in_failures_Inductive_parallel_lm4
    {zs : List ((proc p α × Set α) × Set (event α))} :
    Set.sUnion
        {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set zs ∧ S = Set.inter Y (Set.insert Tick (Ev '' X))} ∩
        Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (Prod.fst '' _root_.set zs)))) =
      Set.sUnion
        {S | ∃ P X Y,
          ((P, X), Y) ∈ _root_.set zs ∧
            S = Set.inter Y (Set.insert Tick (Ev '' X))} :=
  Set.inter_eq_left.mpr in_failures_Inductive_parallel_lm3

theorem in_failures_Inductive_parallel_lm
    {PXs : List (proc p α × Set α)} {f : failure α} {M : p → domFType α} :
    PXs ≠ [] →
      ((f :f failures (Inductive_parallel PXs) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                  List.map Prod.fst PXYs = PXs ∧
                    Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                        S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                    ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs →
                      ((u rest-tr X), Y) :f failures P M) := by
  have key : ∀ (PXs : List (proc p α × Set α)), PXs ≠ [] → ∀ g : failure α,
      ((g :f failures (Inductive_parallel PXs) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∃ Z,
              g = (u, Z) ∧
                ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                  List.map Prod.fst PXYs = PXs ∧
                    Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                        S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                    ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs →
                      ((u rest-tr X), Y) :f failures P M) := by
    intro PXs
    induction PXs with
    | nil => intro h; exact absurd rfl h
    | cons PX PXs ih =>
        intro _ g
        have h0 : Set.sUnion (Prod.snd '' _root_.set ([] : List (proc p α × Set α)))
            = (∅ : Set α) := by simp
        by_cases hPXs : PXs = []
        · subst hPXs
          have hU : Set.sUnion (Prod.snd '' _root_.set [PX]) = Prod.snd PX := by
            rw [sUnion_snd_cons', h0, Set.union_empty]
          simp only [Inductive_parallel, h0]
          rw [in_failures_Alpha_parallel, hU, Set.union_empty, Set.image_empty]
          constructor
          · rintro ⟨u, X, hEq, Y, Z, hX, hP, hS, hsu⟩
            rw [in_failures_SKIP_iff] at hS
            by_cases hT : (Tick : event α) ∈ Z
            · have hTick : (u rest-tr (∅ : Set α)) = (Abs_trace [Tick] : traceType α) := by
                rcases hS with ⟨-, hZE⟩ | hTk
                · exact absurd (hZE hT) (by simp [Evset])
                · exact hTk
              obtain ⟨s', rfl, -, hno⟩ := rest_tr_Tick_sett.mp hTick
              have hPrest :
                  ((s' rest-tr Prod.snd PX) ^^^ (Abs_trace [Tick] : traceType α), Y) :f
                    failures (Prod.fst PX) M := by
                rwa [rest_tr_appt (Or.inl hno), rest_tr_Tick] at hP
              have hP2 :
                  ((s' rest-tr Prod.snd PX) ^^^ (Abs_trace [Tick] : traceType α),
                    Set.insert Tick Y) :f failures (Prod.fst PX) M :=
                proc_T2_T3 hPrest (rest_tr_noTick.mpr hno)
              refine ⟨s' ^^^ Abs_trace [Tick], hsu, X, hEq, [(PX, Set.insert Tick Y)], rfl, ?_, ?_⟩
              · rw [sUnion_single, hX]
                ext e
                simp only [Set.mem_union, Set.mem_inter_iff, mem_Set_insert',
                  Set.mem_empty_iff_false, or_false]
                constructor
                · rintro (⟨hY, hA⟩ | ⟨-, rfl⟩)
                  · exact ⟨Or.inr hY, hA⟩
                  · exact ⟨Or.inl rfl, Or.inl rfl⟩
                · rintro ⟨hc, hA⟩
                  rcases hc with rfl | hY
                  · exact Or.inr ⟨hT, rfl⟩
                  · exact Or.inl ⟨hY, hA⟩
              · intro P X' Y' hmem
                have hmem' : ((P, X'), Y') = (PX, Set.insert Tick Y) := by
                  simpa [_root_.set] using hmem
                obtain ⟨rfl, rfl, rfl⟩ := pair_pair_inj hmem'
                rw [rest_tr_appt (Or.inl hno), rest_tr_Tick]
                exact hP2
            · have hZE : Z ∩ Set.insert Tick (∅ : Set (event α)) = ∅ := by
                rw [Set.eq_empty_iff_forall_notMem]
                rintro e ⟨he, hc⟩
                rcases hc with rfl | hf
                · exact hT he
                · exact hf
              refine ⟨u, hsu, X, hEq, [(PX, Y)], rfl, ?_, ?_⟩
              · rw [sUnion_single, hX, hZE, Set.union_empty]
                rfl
              · intro P X' Y' hmem
                have hmem' : ((P, X'), Y') = (PX, Y) := by simpa [_root_.set] using hmem
                obtain ⟨rfl, rfl, rfl⟩ := pair_pair_inj hmem'
                exact hP
          · rintro ⟨u, hsu, Z, hEq, PXYs, hmap, hZ, hall⟩
            obtain ⟨W, rfl⟩ := map_fst_eq_singleton hmap
            rw [sUnion_single] at hZ
            refine ⟨u, Z, hEq, W, ∅, ?_, ?_, ?_, hsu⟩
            · rw [hZ, Set.empty_inter, Set.union_empty]
              rfl
            · exact hall (Prod.fst PX) (Prod.snd PX) W (by simp [_root_.set])
            · rw [in_failures_SKIP_iff]
              rcases rest_tr_empty (u := u) with h | h
              · exact Or.inl ⟨h, Set.empty_subset _⟩
              · exact Or.inr h
        · have hU : Set.sUnion (Prod.snd '' _root_.set (PX :: PXs)) =
              Prod.snd PX ∪ Set.sUnion (Prod.snd '' _root_.set PXs) := sUnion_snd_cons'
          simp only [Inductive_parallel]
          rw [in_failures_Alpha_parallel, hU]
          constructor
          · rintro ⟨u, X, hEq, Y, Z, hX, hP, hQ, hsu⟩
            rw [ih hPXs] at hQ
            obtain ⟨u2, hsu2, Z2, hEq2, PXYs, hmap, hZ2, hall2⟩ := hQ
            have hu2 : u2 = u rest-tr (Set.sUnion (Prod.snd '' _root_.set PXs)) :=
              (Prod.mk.inj hEq2).1.symm
            have hZ2' : Z2 = Z := (Prod.mk.inj hEq2).2.symm
            rw [hu2] at hall2
            rw [hZ2'] at hZ2
            have hfst : Prod.fst '' _root_.set PXYs = _root_.set PXs := by
              rw [← set_map', hmap]
            refine ⟨u, hsu, X, hEq, (PX, Y) :: PXYs, by rw [List.map_cons, hmap], ?_, ?_⟩
            · rw [sUnion_cons, ← hZ2]
              exact hX
            · intro P X' Y' hmem
              rw [set_cons'', Set.mem_insert_iff] at hmem
              rcases hmem with hmem | hmem
              · obtain ⟨rfl, rfl, rfl⟩ := pair_pair_inj hmem
                exact hP
              · have hsub : X' ⊆ Set.sUnion (Prod.snd '' _root_.set PXs) := by
                  rw [← hfst]
                  exact in_failures_Inductive_parallel_lm2 hmem
                have hval := hall2 P X' Y' hmem
                rwa [(rest_tr_of_rest_tr_subset hsub).2] at hval
          · rintro ⟨u, hsu, Z, hEq, PXYs, hmap, hZ, hall⟩
            obtain ⟨W, zs, rfl, hmapzs⟩ := map_fst_eq_cons hmap
            have hfst : Prod.fst '' _root_.set zs = _root_.set PXs := by
              rw [← set_map', hmapzs]
            rw [sUnion_cons] at hZ
            refine ⟨u, Z, hEq, W,
              Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set zs ∧
                S = Set.inter Y (Set.insert Tick (Ev '' X))}, ?_, ?_, ?_, hsu⟩
            · rw [hZ]
              congr 1
              rw [← hfst]
              exact in_failures_Inductive_parallel_lm4.symm
            · exact hall (Prod.fst PX) (Prod.snd PX) W (by rw [set_cons'']; simp)
            · rw [ih hPXs]
              refine ⟨u rest-tr (Set.sUnion (Prod.snd '' _root_.set PXs)),
                rest_tr_subset_event, _, rfl, zs, hmapzs, ?_, ?_⟩
              · rw [← hfst]
                exact in_failures_Inductive_parallel_lm4
              · intro P X' Y' hmem
                have hsub : X' ⊆ Set.sUnion (Prod.snd '' _root_.set PXs) := by
                  rw [← hfst]
                  exact in_failures_Inductive_parallel_lm2 hmem
                rw [(rest_tr_of_rest_tr_subset hsub).2]
                exact hall P X' Y' (by rw [set_cons'']; exact Or.inr hmem)
  intro h
  exact key PXs h f

/- (*** remove ALL ***) -/

theorem in_failures_Inductive_parallel
    {PXs : List (proc p α × Set α)} {f : failure α} {M : p → domFType α} :
    PXs ≠ [] →
      ((f :f failures (Inductive_parallel PXs) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                  List.map Prod.fst PXYs = PXs ∧
                    Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                        S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                    ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs →
                      ((u rest-tr X), Y) :f failures P M) :=
  in_failures_Inductive_parallel_lm

/- (*** Semantics for replicated alphabetized parallel on F ***) -/

theorem failures_Inductive_parallel
    {PXs : List (proc p α × Set α)} {M : p → domFType α} :
    PXs ≠ [] →
      failures (Inductive_parallel PXs) M =
        CollectF (fun f : failure α =>
          ∃ u,
            sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
              ∃ Z,
                f = (u, Z) ∧
                  ∃ PXYs : List ((proc p α × Set α) × Set (event α)),
                    List.map Prod.fst PXYs = PXs ∧
                      Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                        Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
                          S = Set.inter Y (Set.insert Tick (Ev '' X))} ∧
                      ∀ P X Y, ((P, X), Y) ∈ _root_.set PXYs →
                        ((u rest-tr X), Y) :f failures P M) := by
  intro h
  rw [← CollectF_open (F := failures (Inductive_parallel PXs) M)]
  apply CollectF_eq
  intro f
  exact propext (in_failures_Inductive_parallel (f := f) h)

/-************************************
 |              traces              |
 ************************************-/

theorem sett_in_failures_Inductive_parallel
    {PXs : List (proc p α × Set α)} {t : traceType α} {X : Set (event α)}
    {M : p → domFType α} :
    PXs ≠ [] → (t, X) :f failures (Inductive_parallel PXs) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) := by
  intro h hf
  obtain ⟨u, hsu, Z, hEq, -⟩ := (in_failures_Inductive_parallel h).1 hf
  rw [(Prod.mk.inj hEq).1]
  exact hsu

/- ---------------------------------------------------------*
 |        another expression of Inductive_parallel_eval    |
 *--------------------------------------------------------- -/

private def inductive_parallel_nth_union
    (PXs : List (proc p α × Set α)) (Ys : List (Set (event α))) : Set (Set (event α)) :=
  fun S => ∃ i : Nat,
    And
      (i < PXs.length)
      (S = Set.inter (nth Ys i) (Set.insert Tick (Ev '' (Prod.snd (nth PXs i)))))

private def nth_inductive_parallel_failure_cond
    (PXs : List (proc p α × Set α)) (Ys : List (Set (event α)))
    (u : traceType α) (M : p → domFType α) (i : Nat) : Prop :=
  let PX := nth PXs i
  memF ((u rest-tr PX.2), nth Ys i) (failures PX.1 M)

private def in_failures_Inductive_parallel_nth_stmt
    (PXs : List (proc p α × Set α)) (f : failure α) (M : p → domFType α) : Prop :=
  PXs ≠ [] →
    ((f :f failures (Inductive_parallel PXs) M) ↔
      ∃ u,
        sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) ∧
          ∃ Z,
            f = (u, Z) ∧
              ∃ Ys : List (Set (event α)),
                And
                  (PXs.length = Ys.length)
                  (And
                    (Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' _root_.set PXs))) =
                      Set.sUnion (inductive_parallel_nth_union PXs Ys))
                    (∀ i : Nat, (i < PXs.length) →
                      nth_inductive_parallel_failure_cond PXs Ys u M i)))

private theorem union_PXYs_eq_nth {PXYs : List ((proc p α × Set α) × Set (event α))} :
    Set.sUnion {S | ∃ P X Y, ((P, X), Y) ∈ _root_.set PXYs ∧
        S = Set.inter Y (Set.insert Tick (Ev '' X))} =
      Set.sUnion
        (inductive_parallel_nth_union (List.map Prod.fst PXYs) (List.map Prod.snd PXYs)) := by
  ext e
  constructor
  · rintro ⟨S, ⟨P, X, Y, hmem, rfl⟩, he⟩
    obtain ⟨i, hi, hnth⟩ := set_nth.mp hmem
    refine ⟨Set.inter (nth (List.map Prod.snd PXYs) i)
      (Set.insert Tick (Ev '' (Prod.snd (nth (List.map Prod.fst PXYs) i)))),
      ⟨i, by simpa using hi, rfl⟩, ?_⟩
    rw [nth_map_lt hi, nth_map_lt hi, ← hnth]
    exact he
  · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
    have hi' : i < PXYs.length := by simpa using hi
    refine ⟨Set.inter (nth PXYs i).2 (Set.insert Tick (Ev '' (Prod.snd (nth PXYs i).1))),
      ⟨(nth PXYs i).1.1, (nth PXYs i).1.2, (nth PXYs i).2, set_nth.mpr ⟨i, hi', rfl⟩, rfl⟩, ?_⟩
    rw [nth_map_lt hi', nth_map_lt hi'] at he
    exact he

theorem in_failures_Inductive_parallel_nth
    {PXs : List (proc p α × Set α)} {f : failure α} {M : p → domFType α} :
    in_failures_Inductive_parallel_nth_stmt PXs f M := by
  intro h
  rw [in_failures_Inductive_parallel h]
  constructor
  · rintro ⟨u, hsu, Z, hEq, PXYs, hmap, hZ, hall⟩
    subst hmap
    refine ⟨u, hsu, Z, hEq, List.map Prod.snd PXYs, by simp, ?_, ?_⟩
    · rw [hZ, union_PXYs_eq_nth]
    · intro i hi
      have hi' : i < PXYs.length := by simpa using hi
      have hval := hall (nth PXYs i).1.1 (nth PXYs i).1.2 (nth PXYs i).2
        (set_nth.mpr ⟨i, hi', rfl⟩)
      simp only [nth_inductive_parallel_failure_cond]
      rw [nth_map_lt hi', nth_map_lt hi']
      exact hval
  · rintro ⟨u, hsu, Z, hEq, Ys, hlen, hZ, hall⟩
    refine ⟨u, hsu, Z, hEq, List.zip PXs Ys, map_fst_zip_eq (le_of_eq hlen), ?_, ?_⟩
    · rw [hZ, union_PXYs_eq_nth, map_fst_zip_eq (le_of_eq hlen),
        List.map_snd_zip (le_of_eq hlen.symm)]
    · intro P X Y hmem
      obtain ⟨i, hi, hnth⟩ := set_nth.mp hmem
      have hiP : i < PXs.length := by
        rw [List.length_zip] at hi
        omega
      have hval := hall i hiP
      simp only [nth_inductive_parallel_failure_cond] at hval
      rw [nth_zip_lt hiP hlen] at hnth
      obtain ⟨h1, h2⟩ := Prod.mk.inj hnth
      have hP : P = (nth PXs i).1 := congrArg Prod.fst h1
      have hX : X = (nth PXs i).2 := congrArg Prod.snd h1
      subst hP
      subst hX
      subst h2
      exact hval

/-============================================================*
 |                                                            |
 |              indexed alphabetized parallel                 |
 |                                                            |
 *============================================================-/

/- (*** failures Inductive_parallel ***) -/

private def rep_parallel_lm1_left
    (Is : List ι) (Ys : List (Set (event α))) (PXf : ι → proc p α × Set α) : Set (Set (event α)) :=
  fun S => ∃ i : Nat,
    And
      (i < Ys.length)
      (S = Set.inter (nth Ys i) (Set.insert Tick (Ev '' (Prod.snd (nth (List.map PXf Is) i)))))

private def rep_parallel_lm1_right
    [Inhabited ι] (I : Set ι) (Is : List ι) (Ys : List (Set (event α)))
    (PXf : ι → proc p α × Set α) :
    Set (Set (event α)) :=
  fun S => ∃ i : ι,
    And
      (i ∈ I)
      (S =
        Set.inter
          (nth Ys (THE (fun n : Nat => nth Is n = i ∧ n < Is.length)))
          (Set.insert Tick (Ev '' (Prod.snd (PXf i)))))

private def rep_parallel_lm2_left
    (I : Set ι) (PXf : ι → proc p α × Set α) (Yf : ι → Set (event α)) : Set (Set (event α)) :=
  fun S => ∃ i : ι,
    And
      (i ∈ I)
      (S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i)))))

private def rep_parallel_lm2_right
    (Is : List ι) (PXf : ι → proc p α × Set α) (Yf : ι → Set (event α)) : Set (Set (event α)) :=
  fun S => ∃ i : Nat,
    And
      (i < Is.length)
      (S =
        Set.inter
          (nth (List.map Yf Is) i)
          (Set.insert Tick (Ev '' (Prod.snd (nth (List.map PXf Is) i)))))

theorem in_failures_Rep_parallel_lm1
    [Inhabited ι] {I : Set ι} {Is : List ι} {Ys : List (Set (event α))}
    {PXf : ι → proc p α × Set α} :
    isListOf Is I → Ys.length = Is.length →
      Set.sUnion (rep_parallel_lm1_left Is Ys PXf) =
        Set.sUnion (rep_parallel_lm1_right I Is Ys PXf) := by
  intro hIs hlen
  ext e
  constructor
  · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
    have hiIs : i < Is.length := by omega
    refine ⟨Set.inter (nth Ys (THE (fun n : Nat => nth Is n = nth Is i ∧ n < Is.length)))
        (Set.insert Tick (Ev '' (Prod.snd (PXf (nth Is i))))),
      ⟨nth Is i, isListOf_nth_in_index hIs hiIs, rfl⟩, ?_⟩
    rw [isListOf_THE_nth hIs hiIs, ← nth_map_lt (f := PXf) hiIs]
    exact he
  · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
    obtain ⟨n, hn, hin⟩ := isListOf_index_to_nth hIs i hi
    refine ⟨Set.inter (nth Ys n)
        (Set.insert Tick (Ev '' (Prod.snd (nth (List.map PXf Is) n)))),
      ⟨n, by omega, rfl⟩, ?_⟩
    rw [nth_map_lt hn]
    rw [hin, isListOf_THE_nth hIs hn] at he
    exact he

theorem in_failures_Rep_parallel_lm2
    {I : Set ι} {Is : List ι} {PXf : ι → proc p α × Set α} {Yf : ι → Set (event α)} :
    isListOf Is I →
      Set.sUnion (rep_parallel_lm2_left I PXf Yf) =
        Set.sUnion (rep_parallel_lm2_right Is PXf Yf) := by
  cases Is with
  | nil =>
      intro hIs
      have hI : I = {} := isListOf_nil_to_emptyset.mp hIs
      subst hI
      ext e
      constructor
      · rintro ⟨S, ⟨i, hi, rfl⟩, -⟩
        simp at hi
      · rintro ⟨S, ⟨i, hi, rfl⟩, -⟩
        simp at hi
  | cons a t =>
      intro hIs
      haveI : Inhabited ι := ⟨a⟩
      ext e
      constructor
      · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
        obtain ⟨n, hn, hin⟩ := isListOf_index_to_nth hIs i hi
        refine ⟨Set.inter (nth (List.map Yf (a :: t)) n)
            (Set.insert Tick (Ev '' (Prod.snd (nth (List.map PXf (a :: t)) n)))),
          ⟨n, hn, rfl⟩, ?_⟩
        rw [nth_map_lt hn, nth_map_lt hn, ← hin]
        exact he
      · rintro ⟨S, ⟨i, hi, rfl⟩, he⟩
        refine ⟨Set.inter (Yf (nth (a :: t) i))
            (Set.insert Tick (Ev '' (Prod.snd (PXf (nth (a :: t) i))))),
          ⟨nth (a :: t) i, isListOf_nth_in_index hIs hi, rfl⟩, ?_⟩
        rw [nth_map_lt hi, nth_map_lt hi] at he
        exact he

/-- The `Rep_parallel` characterisation for an *arbitrary* enumeration `Is` of `I`,
    not just the one picked by `Rep_parallel_def`. -/
theorem in_failures_Inductive_parallel_isListOf [Inhabited ι]
    {I : Set ι} {Is : List ι} {PXf : ι → proc p α × Set α} {f : failure α}
    {M : p → domFType α} :
    I ≠ ∅ → isListOf Is I →
      ((f :f failures (Inductive_parallel (List.map PXf Is)) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ Yf : ι → Set (event α),
                  Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) =
                    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
                      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∧
                  ∀ i : ι, i ∈ I →
                    ((u rest-tr (Prod.snd (PXf i))), Yf i) :f failures (Prod.fst (PXf i)) M) := by
  intro hI hIs
  have hne : Is ≠ [] := isListOf_nonemptyset hI hIs
  have hmapne : List.map PXf Is ≠ [] := by
    simpa using hne
  have hset : _root_.set (List.map PXf Is) = PXf '' I := by
    rw [set_map', isListOf_set_eq hIs]
  rw [in_failures_Inductive_parallel_nth hmapne, hset]
  constructor
  · rintro ⟨u, hsu, Z, hEq, Ys, hlen, hZ, hall⟩
    have hlen' : Ys.length = Is.length := by
      simpa using hlen.symm
    have hnu :
        inductive_parallel_nth_union (List.map PXf Is) Ys =
          rep_parallel_lm1_left Is Ys PXf := by
      ext S
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by rw [← hlen]; exact hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by rw [hlen]; exact hi, rfl⟩
    refine ⟨u, hsu, Z, hEq,
      fun i => nth Ys (THE (fun n : Nat =>
        nth Is n = i ∧
          n < Is.length)), ?_, ?_⟩
    · rw [hZ, hnu, in_failures_Rep_parallel_lm1 hIs hlen']
      rfl
    · intro i hi
      obtain ⟨n, hn, hin⟩ := isListOf_index_to_nth hIs i hi
      have hval := hall n (by simpa using hn)
      simp only [nth_inductive_parallel_failure_cond] at hval
      rw [nth_map_lt hn] at hval
      subst hin
      dsimp only
      rw [isListOf_THE_nth hIs hn]
      exact hval
  · rintro ⟨u, hsu, Z, hEq, Yf, hZ, hall⟩
    have hnu :
        inductive_parallel_nth_union (List.map PXf Is)
            (List.map Yf Is) =
          rep_parallel_lm2_right Is PXf Yf := by
      ext S
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by simpa using hi, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨i, by simpa using hi, rfl⟩
    refine ⟨u, hsu, Z, hEq, List.map Yf Is, by simp, ?_, ?_⟩
    · rw [hZ, hnu, ← in_failures_Rep_parallel_lm2 hIs]
      rfl
    · intro i hi
      have hi' : i < Is.length := by simpa using hi
      have hval := hall (nth Is i)
        (isListOf_nth_in_index hIs hi')
      simp only [nth_inductive_parallel_failure_cond]
      rw [nth_map_lt hi', nth_map_lt hi']
      exact hval

theorem in_failures_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {f : failure α} {M : p → domFType α} :
    I ≠ ∅ → I.Finite →
      ((f :f failures (Rep_parallel I PXf) M) ↔
        ∃ u,
          sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
            ∃ Z,
              f = (u, Z) ∧
                ∃ Yf : ι → Set (event α),
                  Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) =
                    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
                      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∧
                  ∀ i : ι, i ∈ I →
                    ((u rest-tr (Prod.snd (PXf i))), Yf i) :f failures (Prod.fst (PXf i)) M) := by
  intro hI hfin
  obtain ⟨i0, -⟩ := Set.nonempty_iff_ne_empty.2 hI
  haveI : Inhabited ι := ⟨i0⟩
  rw [Rep_parallel_def]
  exact in_failures_Inductive_parallel_isListOf hI (chooseOrDefault_spec (isListOf_EX hfin))


/- The Isabelle theorem bundle `in_failures_par` is represented by
   `in_failures_Alpha_parallel`, `in_failures_Inductive_parallel`, and
   `in_failures_Rep_parallel`. -/

/- (*** Semantics for indexed alphabetized parallel on F ***) -/

theorem failures_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {M : p → domFType α} :
    I ≠ ∅ → I.Finite →
      failures (Rep_parallel I PXf) M =
        CollectF (fun f : failure α =>
          ∃ u,
            sett u ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) ∧
              ∃ Z,
                f = (u, Z) ∧
                ∃ Yf : ι → Set (event α),
                  Z ∩ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) =
                    Set.sUnion {S | ∃ i : ι, i ∈ I ∧
                      S = Set.inter (Yf i) (Set.insert Tick (Ev '' (Prod.snd (PXf i))))} ∧
                  ∀ i : ι, i ∈ I →
                      ((u rest-tr (Prod.snd (PXf i))), Yf i) :f
                        failures (Prod.fst (PXf i)) M) := by
  intro hI hfin
  rw [← CollectF_open (F := failures (Rep_parallel I PXf) M)]
  apply CollectF_eq
  intro f
  exact propext (in_failures_Rep_parallel (f := f) hI hfin)

/-************************************
 |              traces              |
 ************************************-/

theorem sett_in_failures_Rep_parallel
    {I : Set ι} {PXf : ι → proc p α × Set α} {t : traceType α}
    {X : Set (event α)} {M : p → domFType α} :
    I ≠ ∅ → I.Finite → (t, X) :f failures (Rep_parallel I PXf) M →
      sett t ⊆ Set.insert Tick (Ev '' (Set.sUnion (Prod.snd '' (PXf '' I)))) := by
  intro hI hfin hf
  obtain ⟨u, hsu, Z, hEq, -⟩ := (in_failures_Rep_parallel hI hfin).1 hf
  rw [(Prod.mk.inj hEq).1]
  exact hsu

end
