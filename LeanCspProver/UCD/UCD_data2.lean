           /- -------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.UCD.UCD_data1

/- 
(*****************************************************************

         1. 

 *****************************************************************)
-/

/- *********************************************************
          preliminary (functions for updates)
 ********************************************************* -/

inductive Att where
  | AttL : Nat × Nat → Att
  | AttC : Nat → Att
  | AttR : Nat → Att
deriving DecidableEq, Inhabited

theorem inj_Att :
    Function.Injective Att.AttL ∧ Function.Injective Att.AttC ∧ Function.Injective Att.AttR := by
  constructor
  · intro a b h
    cases h
    rfl
  constructor
  · intro a b h
    cases h
    rfl
  · intro a b h
    cases h
    rfl

theorem Att_or : ∀ a : Att,
    (∃ n x, a = Att.AttL (n, x)) ∨ (∃ n, a = Att.AttC n) ∨ ∃ n, a = Att.AttR n := by
  intro a
  cases a with
  | AttL nx =>
      rcases nx with ⟨n, x⟩
      exact Or.inl ⟨n, x, rfl⟩
  | AttC n =>
      exact Or.inr <| Or.inl ⟨n, rfl⟩
  | AttR n =>
      exact Or.inr <| Or.inr ⟨n, rfl⟩

@[simp]
theorem AttR_EX {a : Att} :
    ((∀ n x, a ≠ Att.AttL (n, x)) ∧ (∀ n, a ≠ Att.AttC n)) ↔ ∃ n, a = Att.AttR n := by
  cases a with
  | AttL nx =>
      rcases nx with ⟨n, x⟩
      simp
  | AttC n =>
      simp
  | AttR n =>
      simp

/- functions -/

def getNat : Att → Nat
  | Att.AttL nx => nx.1
  | Att.AttC n => n
  | Att.AttR n => n

def updateR : List Att × Nat → List Att
  | ([], _) => []
  | (Att.AttL _ :: _, _) => [Att.AttR 0, Att.AttC 0]
  | (Att.AttC _ :: _, _) => [Att.AttR 0, Att.AttC 0]
  | ([Att.AttR n], x) => [Att.AttR (fill (n + x) / 2)]
  | (Att.AttR n :: s, x) =>
      Att.AttR (fill (n + getNat (hd (updateR (s, x)))) / 2) :: updateR (s, x)
termination_by sx => sx.1.length
decreasing_by
  simp_wf

def nextR : List Att × Nat → List Att
  | ([], _) => []
  | ([Att.AttL _], _) => [Att.AttR 0, Att.AttC 0]
  | (Att.AttL nx :: s, x) => Att.AttL nx :: nextR (s, x)
  | ([Att.AttC n], x) => [Att.AttL (n, x)]
  | (Att.AttC n :: s, x) => Att.AttL (n, getNat (hd (updateR (s, x)))) :: updateR (s, x)
  | ([Att.AttR n], x) => [Att.AttC (fill (n + x))]
  | (Att.AttR n :: s, x) => Att.AttC (fill (n + getNat (hd (updateR (s, x))))) :: updateR (s, x)
termination_by sx => sx.1.length
decreasing_by
  simp_wf

def nextLhd : Nat × List Att → Att
  | (nz, []) => Att.AttC nz
  | (nz, Att.AttR _ :: _) => Att.AttC nz
  | (nz, Att.AttC m :: _) => Att.AttL (nz, m / 2)
  | (nz, Att.AttL (m, _) :: _) => Att.AttL (nz, m / 2)

def nextL : List Att → List Att
  | [] => []
  | Att.AttR _ :: _ => [Att.AttR 0, Att.AttC 0]
  | Att.AttC n :: s => Att.AttR (n / 2) :: s
  | [Att.AttL (n, z)] => [Att.AttC (fill (n / 2 + z))]
  | Att.AttL (n, z) :: Att.AttL (m, y) :: s =>
      Att.AttL (fill (n / 2 + z), m / 2) :: nextL (Att.AttL (m, y) :: s)
  | Att.AttL (n, z) :: Att.AttC m :: s =>
      Att.AttL (fill (n / 2 + z), m / 2) :: Att.AttR (m / 2) :: s
  | Att.AttL (n, z) :: Att.AttR m :: s =>
      Att.AttC (fill (n / 2 + z)) :: Att.AttR m :: s
termination_by s => s.length
decreasing_by
  simp_wf

def guardL : List Att → Prop
  | [] => False
  | a :: _ => (∃ n x, a = Att.AttL (n, x)) ∨ ∃ n, a = Att.AttC n

def guardR : List Att → Prop
  | [] => False
  | [a] => (∃ n, a = Att.AttC n) ∨ ∃ n, a = Att.AttR n
  | _ :: s => guardR s

def nextLR (s : List Att) : List Att :=
  nextL (nextR (s, getNat (hd s) / 2))

def toStbOne : List Att → List Att
  | [] => []
  | [a] => [a]
  | Att.AttL nx :: s => Att.AttL nx :: s
  | Att.AttC n :: Att.AttL (m, z) :: s => Att.AttL (n, m / 2) :: nextL (Att.AttL (m, z) :: s)
  | Att.AttC n :: Att.AttC m :: s => Att.AttL (n, m / 2) :: nextL (Att.AttC m :: s)
  | Att.AttC n :: Att.AttR m :: s => Att.AttC n :: Att.AttR m :: s
  | [Att.AttR n, Att.AttL (m, z)] =>
      [Att.AttL (fill (n + m / 2), fill (m / 2 + z) / 2), Att.AttR (fill (m / 2 + z) / 2)]
  | Att.AttR n :: Att.AttL (m, z) :: Att.AttL (na, x) :: sa =>
      Att.AttL (fill (n + m / 2), fill (m / 2 + z) / 2) ::
        nextL (Att.AttL (fill (m / 2 + z), na / 2) :: nextL (Att.AttL (na, x) :: sa))
  | Att.AttR n :: Att.AttL (m, z) :: Att.AttC na :: sa =>
      Att.AttL (fill (n + m / 2), fill (m / 2 + z) / 2) ::
        Att.AttC (fill (fill (m / 2 + z) / 2 + na / 2)) :: Att.AttR (na / 2) :: sa
  | Att.AttR n :: Att.AttL (m, z) :: Att.AttR na :: sa =>
      Att.AttL (fill (n + m / 2), fill (m / 2 + z) / 2) ::
        Att.AttR (fill (m / 2 + z) / 2) :: Att.AttR na :: sa
  | Att.AttR n :: Att.AttC m :: s => Att.AttC (fill (n + m / 2)) :: nextL (Att.AttC m :: s)
  | Att.AttR n :: Att.AttR m :: s => Att.AttR n :: Att.AttR m :: s

def toStb : List Att → List Att
  | [] => []
  | a :: s => toStbOne (a :: toStb s)
termination_by s => s.length
decreasing_by
  simp_wf

/- --- test --- -/

theorem test_updateR :
    updateR ([Att.AttR 2, Att.AttR 4, Att.AttR 0], 8) =
      [Att.AttR 3, Att.AttR 4, Att.AttR 4] := by
  simp [updateR, fill, Nat.even_iff, getNat]

theorem test_toStbOne :
    toStbOne [Att.AttR 2, Att.AttL (4, 2), Att.AttC 0, Att.AttR 6] =
      [Att.AttL (4, 2), Att.AttC 2, Att.AttR 0, Att.AttR 6] := by
  simp [toStbOne, fill, Nat.even_iff]

/-   lemmas    -/

theorem guardR_last {s : List Att} :
    guardR s ↔ s ≠ [] ∧ ((∃ n, last s = Att.AttC n) ∨ ∃ n, last s = Att.AttR n) := by
  induction s with
  | nil =>
      simp [guardR]
  | cons a s ih =>
      cases s with
      | nil =>
          cases a <;> simp [guardR, last]
      | cons b t =>
          simpa [guardR, last] using ih

theorem guardL_hd {s : List Att} :
    guardL s ↔ s ≠ [] ∧ ((∃ n x, hd s = Att.AttL (n, x)) ∨ ∃ n, hd s = Att.AttC n) := by
  cases s with
  | nil =>
      simp [guardL, hd]
  | cons a t =>
      cases a <;> simp [guardL, hd]

@[simp] theorem guardR_AttL {sx : Nat × Nat} {t : List Att} :
    guardR (Att.AttL sx :: t) ↔ guardR t := by
  cases t <;> simp [guardR]

/- *********************************************************
                       L C R
 ********************************************************* -/

def ChkL : List Att → Prop
  | [] => True
  | c :: t => (∃ x, c = Att.AttL x) ∧ ChkL t

def ChkC : List Att → Prop
  | [] => True
  | c :: t => (∃ x, c = Att.AttC x) ∧ ChkC t

def ChkR : List Att → Prop
  | [] => True
  | c :: t => (∃ x, c = Att.AttR x) ∧ ChkR t

def ChkCR : List Att → Prop
  | [] => True
  | c :: t => ((∃ x, c = Att.AttC x) ∧ ChkR t) ∨ ChkR (c :: t)

def ChkLCR : List Att → Prop
  | [] => True
  | c :: t => ((∃ x, c = Att.AttL x) ∧ ChkLCR t) ∨ ChkCR (c :: t)

/- ---------- sub 1 ---------- -/

@[simp] theorem nextL_one_not_nil {a : Att} :
    nextL [a] ≠ [] := by
  cases a with
  | AttL nx =>
      rcases nx with ⟨n, z⟩
      simp [nextL]
  | AttC n =>
      simp [nextL]
  | AttR n =>
      simp [nextL]

@[simp] theorem nextL_not_nil {a : Att} {s : List Att} :
    nextL (a :: s) ≠ [] := by
  cases s with
  | nil =>
      exact nextL_one_not_nil (a := a)
  | cons b t =>
      cases a with
      | AttL nx =>
          rcases nx with ⟨n, z⟩
          cases b with
          | AttL mz =>
              rcases mz with ⟨m, y⟩
              simp [nextL]
          | AttC m =>
              simp [nextL]
          | AttR m =>
              simp [nextL]
      | AttC n =>
          simp [nextL]
      | AttR n =>
          simp [nextL]

@[simp] theorem nextR_not_nil {a : Att} {s : List Att} {x : Nat} :
    nextR (a :: s, x) ≠ [] := by
  cases s with
  | nil =>
      cases a with
      | AttL nx =>
          rcases nx with ⟨n, y⟩
          simp [nextR]
      | AttC n =>
          simp [nextR]
      | AttR n =>
          simp [nextR]
  | cons b t =>
      cases a with
      | AttL nx =>
          rcases nx with ⟨n, y⟩
          simp [nextR]
      | AttC n =>
          simp [nextR]
      | AttR n =>
          simp [nextR]

/- private helpers (house lemmas used repeatedly below) -/

private theorem ChkLCR_AttL_cons {nx : Nat × Nat} {t : List Att} :
    ChkLCR (Att.AttL nx :: t) ↔ ChkLCR t := by
  simp [ChkLCR, ChkCR, ChkR]

private theorem ChkLCR_AttC_cons {n : Nat} {t : List Att} :
    ChkLCR (Att.AttC n :: t) ↔ ChkR t := by
  simp [ChkLCR, ChkCR, ChkR]

private theorem ChkLCR_AttR_cons {n : Nat} {t : List Att} :
    ChkLCR (Att.AttR n :: t) ↔ ChkR t := by
  simp [ChkLCR, ChkCR, ChkR]

private theorem ChkR_AttL_cons {nx : Nat × Nat} {t : List Att} :
    ¬ ChkR (Att.AttL nx :: t) := by
  simp [ChkR]

private theorem ChkR_AttC_cons {n : Nat} {t : List Att} :
    ¬ ChkR (Att.AttC n :: t) := by
  simp [ChkR]

private theorem ChkR_AttR_cons {n : Nat} {t : List Att} :
    ChkR (Att.AttR n :: t) ↔ ChkR t := by
  simp [ChkR]

private theorem updateR_not_nil {a : Att} {s : List Att} {x : Nat} :
    updateR (a :: s, x) ≠ [] := by
  cases a <;> cases s <;> simp [updateR]

private theorem updateR_AttR_EX {a : Att} {s : List Att} {x : Nat} :
    ∃ m u, updateR (a :: s, x) = Att.AttR m :: u := by
  cases a with
  | AttL nx => exact ⟨0, [Att.AttC 0], by simp [updateR]⟩
  | AttC n => exact ⟨0, [Att.AttC 0], by simp [updateR]⟩
  | AttR n =>
      cases s with
      | nil => exact ⟨fill (n + x) / 2, [], by simp [updateR]⟩
      | cons b u =>
          exact ⟨fill (n + getNat (hd (updateR (b :: u, x)))) / 2, updateR (b :: u, x),
            by simp [updateR]⟩

private theorem guardR_cons2 {a b : Att} {u : List Att} :
    guardR (a :: b :: u) ↔ guardR (b :: u) := by
  simp [guardR]

private theorem nextL_AttL_cons_EX {n x : Nat} {t : List Att} :
    ∃ a s, nextL (Att.AttL (n, x) :: t) = a :: s := by
  cases t with
  | nil => exact ⟨Att.AttC (fill (n / 2 + x)), [], by simp [nextL]⟩
  | cons b u =>
      cases b with
      | AttL my =>
          rcases my with ⟨m, y⟩
          exact ⟨Att.AttL (fill (n / 2 + x), m / 2), nextL (Att.AttL (m, y) :: u),
            by simp [nextL]⟩
      | AttC m =>
          exact ⟨Att.AttL (fill (n / 2 + x), m / 2), Att.AttR (m / 2) :: u, by simp [nextL]⟩
      | AttR m =>
          exact ⟨Att.AttC (fill (n / 2 + x)), Att.AttR m :: u, by simp [nextL]⟩

private theorem guardR_updateR {s : List Att} {x : Nat} :
    s ≠ [] → guardR (updateR (s, x)) := by
  induction s with
  | nil => simp
  | cons a t ih =>
      intro _
      cases a with
      | AttL nx => simp [updateR, guardR]
      | AttC n => simp [updateR, guardR]
      | AttR n =>
          cases t with
          | nil => simp [updateR, guardR]
          | cons b u =>
              have h := ih (by simp)
              rcases updateR_AttR_EX (a := b) (s := u) (x := x) with ⟨m, v, hv⟩
              rw [hv] at h
              simp only [updateR, hv, List.head!_cons, guardR_cons2]
              exact h

private theorem ChkR_updateR_iff {s : List Att} {x : Nat} :
    ChkR (updateR (s, x)) ↔ ChkR s := by
  induction s with
  | nil => simp [updateR]
  | cons a t ih =>
      cases a with
      | AttL nx => simp [updateR, ChkR]
      | AttC n => simp [updateR, ChkR]
      | AttR n =>
          cases t with
          | nil => simp [updateR, ChkR]
          | cons b u => simp [updateR, ChkR_AttR_cons, ih]

private theorem ChkLCR_updateR_iff {s : List Att} {x : Nat} :
    ChkLCR (updateR (s, x)) ↔ ChkR s := by
  cases s with
  | nil => simp [updateR, ChkR, ChkLCR]
  | cons a t =>
      cases a with
      | AttL nx => simp [updateR, ChkLCR, ChkCR, ChkR]
      | AttC n => simp [updateR, ChkLCR, ChkCR, ChkR]
      | AttR n =>
          cases t with
          | nil => simp [updateR, ChkLCR, ChkCR, ChkR]
          | cons b u =>
              simp [updateR, ChkLCR_AttR_cons, ChkR_updateR_iff, ChkR_AttR_cons]

theorem tl_toStbOne_not_nil {s : List Att} :
    (tl (toStbOne s) ≠ []) ↔ ∃ a1 a2 t, s = a1 :: a2 :: t := by
  match s with
  | [] => simp [toStbOne]
  | [a] => simp [toStbOne]
  | a :: b :: t =>
      have h : tl (toStbOne (a :: b :: t)) ≠ [] := by
        cases a with
        | AttL nx => simp [toStbOne]
        | AttC n =>
            cases b with
            | AttL mz =>
                rcases mz with ⟨m, z⟩
                simp [toStbOne]
            | AttC m => simp [toStbOne]
            | AttR m => simp [toStbOne]
        | AttR n =>
            cases b with
            | AttL mz =>
                rcases mz with ⟨m, z⟩
                cases t with
                | nil => simp [toStbOne]
                | cons c u => cases c <;> simp [toStbOne]
            | AttC m => simp [toStbOne]
            | AttR m => simp [toStbOne]
      exact iff_of_true h ⟨a, b, t, rfl⟩

@[simp] theorem ChkLCR_nextL {s : List Att} :
    guardL s → (ChkLCR (nextL s) ↔ ChkLCR s) := by
  induction s with
  | nil => simp [guardL]
  | cons a t ih =>
      intro hg
      cases a with
      | AttL nx =>
          rcases nx with ⟨n, z⟩
          cases t with
          | nil => simp [nextL, ChkLCR, ChkCR, ChkR]
          | cons b u =>
              cases b with
              | AttL my =>
                  rcases my with ⟨m, y⟩
                  have h := ih (by simp [guardL])
                  simpa [nextL, ChkLCR_AttL_cons] using h
              | AttC m =>
                  simp [nextL, ChkLCR_AttL_cons, ChkLCR_AttC_cons, ChkLCR_AttR_cons]
              | AttR m =>
                  simp [nextL, ChkLCR_AttL_cons, ChkLCR_AttC_cons, ChkLCR_AttR_cons,
                    ChkR_AttR_cons]
      | AttC n =>
          simp [nextL, ChkLCR_AttC_cons, ChkLCR_AttR_cons]
      | AttR n =>
          simp [guardL] at hg

@[simp] theorem ChkLCR_nextR {s : List Att} {x : Nat} :
    guardR s → (ChkLCR (nextR (s, x)) ↔ ChkLCR s) := by
  induction s with
  | nil => simp [guardR]
  | cons a t ih =>
      intro hg
      cases t with
      | nil =>
          cases a with
          | AttL nx => simp [guardR] at hg
          | AttC n => simp [nextR, ChkLCR, ChkCR, ChkR]
          | AttR n => simp [nextR, ChkLCR, ChkCR, ChkR]
      | cons b u =>
          have hgt : guardR (b :: u) := by simpa [guardR_cons2] using hg
          cases a with
          | AttL nx =>
              rcases nx with ⟨n, z⟩
              have h := ih hgt
              simpa [nextR, ChkLCR_AttL_cons] using h
          | AttC n =>
              simp [nextR, ChkLCR_AttL_cons, ChkLCR_AttC_cons, ChkLCR_updateR_iff]
          | AttR n =>
              simp [nextR, ChkLCR_AttC_cons, ChkLCR_AttR_cons, ChkR_updateR_iff]

@[simp] theorem ChkLCR_AttL {n x : Nat} {s : List Att} :
    ChkLCR (Att.AttL (n, x) :: s) ↔ ChkLCR s := by
  simp [ChkLCR, ChkCR, ChkR]

@[simp] theorem toStbOne_AttL {n x : Nat} {s : List Att} :
    toStbOne (Att.AttL (n, x) :: s) = Att.AttL (n, x) :: s := by
  cases s <;> simp [toStbOne]

theorem nextL_nextR_order {t : List Att} {x : Nat} :
    (t = [] ∨ guardL t ∧ guardR t ∧ ChkLCR t) →
      nextL (nextR (t, x)) = nextR (nextL t, x) := by
  induction t with
  | nil =>
      intro _
      simp [nextR, nextL]
  | cons a s ih =>
      rintro (h | ⟨hL, hR, hC⟩)
      · simp at h
      cases s with
      | nil =>
          cases a with
          | AttL nx => simp [guardR] at hR
          | AttC n => simp [nextR, nextL]
          | AttR n => simp [guardL] at hL
      | cons b u =>
          have hRs : guardR (b :: u) := by simpa [guardR_cons2] using hR
          cases a with
          | AttR n => simp [guardL] at hL
          | AttC n =>
              rcases updateR_AttR_EX (a := b) (s := u) (x := x) with ⟨m, v, hv⟩
              simp [nextR, nextL, hv, getNat]
          | AttL nx =>
              rcases nx with ⟨n, z⟩
              have hCs : ChkLCR (b :: u) := by simpa using hC
              cases b with
              | AttL my =>
                  rcases my with ⟨m, y⟩
                  cases u with
                  | nil => simp [guardR] at hRs
                  | cons c w =>
                      have hIH := ih (Or.inr ⟨by simp [guardL], hRs, hCs⟩)
                      rcases nextL_AttL_cons_EX (n := m) (x := y) (t := c :: w) with ⟨a', s', hs'⟩
                      simp only [nextR, hs', nextL, List.cons.injEq, true_and] at hIH ⊢
                      exact hIH
              | AttC m =>
                  cases u with
                  | nil => simp [nextR, nextL]
                  | cons c w =>
                      rcases updateR_AttR_EX (a := c) (s := w) (x := x) with ⟨mv, v, hv⟩
                      simp [nextR, nextL, hv, getNat]
              | AttR m =>
                  cases u with
                  | nil => simp [nextR, nextL, updateR, getNat]
                  | cons c w =>
                      rcases updateR_AttR_EX (a := c) (s := w) (x := x) with ⟨mv, v, hv⟩
                      simp [nextR, nextL, updateR, hv, getNat]

theorem ChkR_ChkCR {t : List Att} :
    ChkR t → ChkLCR t := by
  intro h
  induction t with
  | nil =>
      simp [ChkLCR]
  | cons a t ih =>
      cases a with
      | AttL nx =>
          simp [ChkR] at h
      | AttC n =>
          simp [ChkR] at h
      | AttR n =>
          simpa [ChkLCR, ChkCR] using h

theorem guardR_hd {a : Att} {t : List Att} :
    guardR t → guardR (a :: t) := by
  intro h
  cases t with
  | nil =>
      simp [guardR] at h
  | cons b s =>
      cases s <;> simpa [guardR] using h

@[simp] theorem ChkR_guardR_AttR {s : List Att} :
    ∀ n, ChkR s → guardR (Att.AttR n :: s) := by
  induction s with
  | nil =>
      intro n h
      simp [guardR]
  | cons a t ih =>
      intro n h
      cases a with
      | AttL nx =>
          simp [ChkR] at h
      | AttC m =>
          simp [ChkR] at h
      | AttR m =>
          cases t with
          | nil =>
              simp [ChkR, guardR] at h ⊢
          | cons b u =>
              simp only [guardR]
              exact ih m (by simpa [ChkR] using h.2)

@[simp] theorem ChkR_guardR_AttC {s : List Att} :
    ∀ n, ChkR s → guardR (Att.AttC n :: s) := by
  induction s with
  | nil =>
      intro n h
      simp [guardR]
  | cons a t ih =>
      intro n h
      cases a with
      | AttL nx =>
          simp [ChkR] at h
      | AttC m =>
          simp [ChkR] at h
      | AttR m =>
          cases t with
          | nil =>
              simp [ChkR, guardR] at h ⊢
          | cons b u =>
              simp only [guardR]
              exact ih m (by simpa [ChkR] using h.2)

@[simp] theorem ChkLCR_guardR_next {t : List Att} :
    ChkLCR t ∧ t ≠ [] → guardR (nextL t) := by
  induction t with
  | nil =>
      rintro ⟨-, h⟩
      simp at h
  | cons a s ih =>
      rintro ⟨hC, -⟩
      cases a with
      | AttR n => simp [nextL, guardR]
      | AttC n =>
          have hR : ChkR s := ChkLCR_AttC_cons.mp hC
          have h := ChkR_guardR_AttR (s := s) (n / 2) hR
          simpa [nextL] using h
      | AttL nx =>
          rcases nx with ⟨n, z⟩
          have hC' : ChkLCR s := ChkLCR_AttL_cons.mp hC
          cases s with
          | nil => simp [nextL, guardR]
          | cons b u =>
              cases b with
              | AttL my =>
                  rcases my with ⟨m, y⟩
                  have h := ih ⟨hC', by simp⟩
                  simpa [nextL] using h
              | AttC m =>
                  have hR : ChkR u := ChkLCR_AttC_cons.mp hC'
                  have h := ChkR_guardR_AttR (s := u) (m / 2) hR
                  simpa [nextL] using h
              | AttR m =>
                  have hR : ChkR u := ChkLCR_AttR_cons.mp hC'
                  have h := ChkR_guardR_AttR (s := u) m hR
                  simpa [nextL, guardR_cons2] using h

@[simp] theorem guardR_nextR_AttL {n x : Nat} {t : List Att} {z : Nat} :
    guardR t → nextR (Att.AttL (n, x) :: t, z) = Att.AttL (n, x) :: nextR (t, z) := by
  intro h
  cases t with
  | nil =>
      simp [guardR] at h
  | cons a s =>
      simp [nextR]

@[simp] theorem nextL_AttL_nextR_AttC {n x m y : Nat} {t : List Att} :
    nextL (Att.AttL (n, x) :: nextR (Att.AttC m :: t, y)) =
      Att.AttL (fill (n / 2 + x), m / 2) :: nextL (nextR (Att.AttC m :: t, y)) := by
  cases t <;> simp [nextL, nextR]

@[simp] theorem nextL_AttL_nextR_AttR {n x m y : Nat} {t : List Att} :
    nextL (Att.AttL (n, x) :: nextR (Att.AttR m :: t, y)) =
      Att.AttL (fill (n / 2 + x), getNat (hd (updateR (Att.AttR m :: t, y)))) ::
        updateR (Att.AttR m :: t, y) := by
  cases t <;> simp [nextL, nextR, updateR, getNat]

@[simp] theorem nextL_AttL_updateR {n x m y : Nat} {t : List Att} :
    nextL (Att.AttL (n, x) :: updateR (Att.AttR m :: t, y)) =
      Att.AttC (fill (n / 2 + x)) :: updateR (Att.AttR m :: t, y) := by
  cases t <;> simp [nextL, updateR]

/- --------------------lemma ------------------ -/

@[simp] theorem guardL_nextL_AttL {n x : Nat} {t : List Att} :
    guardL (nextL (Att.AttL (n, x) :: t)) := by
  cases t with
  | nil =>
      simp [guardL, nextL]
  | cons b u =>
      cases b with
      | AttL mz =>
          rcases mz with ⟨m, y⟩
          simp [guardL, nextL]
      | AttC m =>
          simp [guardL, nextL]
      | AttR m =>
          simp [guardL, nextL]

@[simp] theorem nextL_AttL_nextL_AttL {n x m y : Nat} {t : List Att} :
    nextL (Att.AttL (n, x) :: nextL (Att.AttL (m, y) :: t)) =
      Att.AttL (fill (n / 2 + x), fill (m / 2 + y) / 2) ::
        nextL (nextL (Att.AttL (m, y) :: t)) := by
  cases t with
  | nil =>
      simp [nextL]
  | cons b u =>
      cases b with
      | AttL mz =>
          rcases mz with ⟨na, z⟩
          simp [nextL]
      | AttC na =>
          simp [nextL]
      | AttR na =>
          simp [nextL]

@[simp] theorem ChkLCR_guardL_guardR_nextL {t : List Att} :
    ChkLCR t → guardL t → guardR (nextL t) := by
  intro hC hL
  refine ChkLCR_guardR_next ⟨hC, ?_⟩
  cases t with
  | nil => simp [guardL] at hL
  | cons a s => simp

@[simp] theorem ChkLCR_guardR_guardL_nextR {t : List Att} {x : Nat} :
    ChkLCR t → guardR t → guardL (nextR (t, x)) := by
  intro _ hR
  cases t with
  | nil => simp [guardR] at hR
  | cons a s =>
      cases s with
      | nil =>
          cases a with
          | AttL nx => simp [guardR] at hR
          | AttC n => simp [nextR, guardL]
          | AttR n => simp [nextR, guardL]
      | cons b u =>
          cases a with
          | AttL nx =>
              rcases nx with ⟨n, z⟩
              simp [nextR, guardL]
          | AttC n => simp [nextR, guardL]
          | AttR n => simp [nextR, guardL]

theorem nextR_nextL_nextL_order_AttL {n x y : Nat} {t : List Att} :
    ChkLCR t → guardR t →
      nextR (nextL (nextL (Att.AttL (n, x) :: t)), y) =
        nextL (nextR (nextL (Att.AttL (n, x) :: t), y)) := by
  intro hC _
  have hCt : ChkLCR (Att.AttL (n, x) :: t) := ChkLCR_AttL_cons.mpr hC
  have hC' : ChkLCR (nextL (Att.AttL (n, x) :: t)) := by
    rw [ChkLCR_nextL (by simp [guardL])]
    exact hCt
  have hL' : guardL (nextL (Att.AttL (n, x) :: t)) := guardL_nextL_AttL
  have hR' : guardR (nextL (Att.AttL (n, x) :: t)) :=
    ChkLCR_guardR_next ⟨hCt, by simp⟩
  exact (nextL_nextR_order (Or.inr ⟨hL', hR', hC'⟩)).symm

@[simp] theorem nextL_AttL_nextR_guardR {n x y : Nat} {t : List Att} :
    ChkLCR t → guardR t →
      nextL (Att.AttL (n, x) :: nextR (t, y)) =
        Att.AttL (fill (n / 2 + x), getNat (hd (nextR (t, y))) / 2) :: nextL (nextR (t, y)) := by
  intro _ hR
  cases t with
  | nil => simp [guardR] at hR
  | cons a s =>
      cases s with
      | nil =>
          cases a with
          | AttL nx => simp [guardR] at hR
          | AttC m => simp [nextR, nextL, getNat]
          | AttR m => simp [nextR, nextL, getNat]
      | cons b u =>
          cases a with
          | AttL mz =>
              rcases mz with ⟨m, z⟩
              simp [nextR, nextL, getNat]
          | AttC m => simp [nextR, nextL, getNat]
          | AttR m => simp [nextR, nextL, getNat]

@[simp] theorem ChkR_ChkLCR_updateR {s : List Att} {x : Nat} :
    ChkR s → (ChkLCR (updateR (s, x)) ↔ ChkLCR s) := by
  intro h
  rw [ChkLCR_updateR_iff]
  exact iff_of_true h (ChkR_ChkCR h)

@[simp] theorem ChkR_ChkR_updateR {s : List Att} {x : Nat} :
    ChkR s → (ChkR (updateR (s, x)) ↔ ChkR s) := by
  intro _
  exact ChkR_updateR_iff

/- ---- basic ---- -/

theorem ChkLCR_toStbOne_id {t : List Att} :
    ChkLCR t → toStbOne t = t := by
  intro h
  cases t with
  | nil => rfl
  | cons a s =>
      cases s with
      | nil => simp [toStbOne]
      | cons b u =>
          cases a with
          | AttL nx => simp [toStbOne]
          | AttC n =>
              have hR : ChkR (b :: u) := ChkLCR_AttC_cons.mp h
              cases b with
              | AttL my => exact absurd hR (by simp [ChkR])
              | AttC m => exact absurd hR (by simp [ChkR])
              | AttR m => simp [toStbOne]
          | AttR n =>
              have hR : ChkR (b :: u) := ChkLCR_AttR_cons.mp h
              cases b with
              | AttL my => exact absurd hR (by simp [ChkR])
              | AttC m => exact absurd hR (by simp [ChkR])
              | AttR m => simp [toStbOne]

theorem ChkLCR_toStbOne {a : Att} {t : List Att} :
    ChkLCR t → ChkLCR (toStbOne (a :: t)) := by
  intro h
  cases t with
  | nil =>
      cases a <;> simp [toStbOne, ChkLCR, ChkCR, ChkR]
  | cons b u =>
      cases a with
      | AttL nx =>
          simpa [toStbOne, ChkLCR_AttL_cons] using h
      | AttC n =>
          cases b with
          | AttL my =>
              rcases my with ⟨m, y⟩
              have hL := ChkLCR_nextL (s := Att.AttL (m, y) :: u) (by simp [guardL])
              simp only [toStbOne, ChkLCR_AttL_cons, hL]
              exact ChkLCR_AttL_cons.mp h
          | AttC m =>
              simp only [toStbOne, nextL, ChkLCR_AttL_cons, ChkLCR_AttR_cons]
              exact ChkLCR_AttC_cons.mp h
          | AttR m =>
              simp only [toStbOne, ChkLCR_AttC_cons, ChkR_AttR_cons]
              exact ChkLCR_AttR_cons.mp h
      | AttR n =>
          cases b with
          | AttL my =>
              rcases my with ⟨m, y⟩
              cases u with
              | nil => simp [toStbOne, ChkLCR, ChkCR, ChkR]
              | cons c w =>
                  cases c with
                  | AttL ny =>
                      rcases ny with ⟨na, xx⟩
                      have h1 := ChkLCR_nextL (s := Att.AttL (na, xx) :: w) (by simp [guardL])
                      simp only [toStbOne, nextL_AttL_nextL_AttL, ChkLCR_AttL_cons,
                        guardL_nextL_AttL, ChkLCR_nextL, h1]
                      exact ChkLCR_AttL_cons.mp (ChkLCR_AttL_cons.mp h)
                  | AttC na =>
                      simp only [toStbOne, ChkLCR_AttL_cons, ChkLCR_AttC_cons, ChkR_AttR_cons]
                      exact ChkLCR_AttC_cons.mp (ChkLCR_AttL_cons.mp h)
                  | AttR na =>
                      simp only [toStbOne, ChkLCR_AttL_cons, ChkLCR_AttR_cons, ChkR_AttR_cons]
                      exact ChkLCR_AttR_cons.mp (ChkLCR_AttL_cons.mp h)
          | AttC m =>
              simp only [toStbOne, nextL, ChkLCR_AttC_cons, ChkR_AttR_cons]
              exact ChkLCR_AttC_cons.mp h
          | AttR m =>
              simp only [toStbOne, ChkLCR_AttR_cons, ChkR_AttR_cons]
              exact ChkLCR_AttR_cons.mp h

theorem ChkLCR_tl {a : Att} {t : List Att} :
    ChkLCR (a :: t) → ChkLCR t := by
  intro h
  cases a with
  | AttL nx => exact ChkLCR_AttL_cons.mp h
  | AttC n => exact ChkR_ChkCR (ChkLCR_AttC_cons.mp h)
  | AttR n => exact ChkR_ChkCR (ChkLCR_AttR_cons.mp h)

theorem ChkLCR_toStb {t : List Att} :
    ChkLCR (toStb t) := by
  induction t with
  | nil => simp [toStb, ChkLCR]
  | cons a s ih =>
      rw [show toStb (a :: s) = toStbOne (a :: toStb s) from by simp [toStb]]
      exact ChkLCR_toStbOne ih

theorem ChkLCR_toStb_id {t : List Att} :
    ChkLCR t → toStb t = t := by
  induction t with
  | nil =>
      intro _
      simp [toStb]
  | cons a s ih =>
      intro h
      rw [show toStb (a :: s) = toStbOne (a :: toStb s) from by simp [toStb],
        ih (ChkLCR_tl h)]
      exact ChkLCR_toStbOne_id h

theorem nextL_one_EX {t : List Att} {a : Att} :
    ChkLCR t → nextL t = [a] → ∃ a0 : Att, t = [a0] := by
  intro _ h
  cases t with
  | nil => simp [nextL] at h
  | cons a1 s =>
      cases s with
      | nil => exact ⟨a1, rfl⟩
      | cons a2 u =>
          exfalso
          cases a1 with
          | AttL nx =>
              rcases nx with ⟨n, z⟩
              cases a2 with
              | AttL my =>
                  rcases my with ⟨m, y⟩
                  rcases nextL_AttL_cons_EX (n := m) (x := y) (t := u) with ⟨a', s', hs⟩
                  simp [nextL, hs] at h
              | AttC m => simp [nextL] at h
              | AttR m => simp [nextL] at h
          | AttC n => simp [nextL] at h
          | AttR n => simp [nextL] at h

theorem nextR_one_EX {t : List Att} {x : Nat} {a : Att} :
    ChkLCR t → nextR (t, x) = [a] → ∃ a0 : Att, t = [a0] := by
  intro _ h
  cases t with
  | nil => simp [nextR] at h
  | cons a1 s =>
      cases s with
      | nil => exact ⟨a1, rfl⟩
      | cons a2 u =>
          exfalso
          cases a1 with
          | AttL nx =>
              rcases nx with ⟨n, z⟩
              rcases not_nil_EX.mp (nextR_not_nil (a := a2) (s := u) (x := x)) with ⟨b, v, hv⟩
              simp [nextR, hv] at h
          | AttC n =>
              rcases updateR_AttR_EX (a := a2) (s := u) (x := x) with ⟨m, v, hv⟩
              simp [nextR, hv] at h
          | AttR n =>
              rcases updateR_AttR_EX (a := a2) (s := u) (x := x) with ⟨m, v, hv⟩
              simp [nextR, hv] at h

@[simp] theorem toStbOne_nil {t : List Att} :
    (toStbOne t = []) ↔ (t = []) := by
  cases t with
  | nil => simp [toStbOne]
  | cons a s =>
      have h : toStbOne (a :: s) ≠ [] := by
        cases s with
        | nil => simp [toStbOne]
        | cons b u =>
            cases a with
            | AttL nx => simp [toStbOne]
            | AttC n =>
                cases b with
                | AttL my =>
                    rcases my with ⟨m, y⟩
                    simp [toStbOne]
                | AttC m => simp [toStbOne]
                | AttR m => simp [toStbOne]
            | AttR n =>
                cases b with
                | AttL my =>
                    rcases my with ⟨m, y⟩
                    cases u with
                    | nil => simp [toStbOne]
                    | cons c w => cases c <;> simp [toStbOne]
                | AttC m => simp [toStbOne]
                | AttR m => simp [toStbOne]
      simp [h]

@[simp] theorem toStb_nil {t : List Att} :
    (toStb t = []) ↔ (t = []) := by
  cases t with
  | nil => simp [toStb]
  | cons a s =>
      rw [show toStb (a :: s) = toStbOne (a :: toStb s) from by simp [toStb]]
      simp

@[simp] theorem toStbOne_one {t : List Att} {a : Att} :
    (toStbOne t = [a]) ↔ (t = [a]) := by
  cases t with
  | nil => simp [toStbOne]
  | cons a1 s =>
      cases s with
      | nil => simp [toStbOne]
      | cons b u =>
          have h : tl (toStbOne (a1 :: b :: u)) ≠ [] :=
            tl_toStbOne_not_nil.mpr ⟨a1, b, u, rfl⟩
          have h2 : toStbOne (a1 :: b :: u) ≠ [a] := by
            intro he
            rw [he] at h
            simp at h
          simp [h2]

@[simp] theorem toStb_one {t : List Att} {a : Att} :
    (toStb t = [a]) ↔ (t = [a]) := by
  cases t with
  | nil => simp [toStb]
  | cons a1 s =>
      rw [show toStb (a1 :: s) = toStbOne (a1 :: toStb s) from by simp [toStb]]
      simp

theorem length_nextL {t : List Att} :
    guardL t ∧ ChkLCR t → (nextL t).length = t.length := by
  induction t with
  | nil =>
      rintro ⟨h, -⟩
      simp [guardL] at h
  | cons a s ih =>
      rintro ⟨hL, hC⟩
      cases a with
      | AttR n => simp [guardL] at hL
      | AttC n => simp [nextL]
      | AttL nx =>
          rcases nx with ⟨n, z⟩
          cases s with
          | nil => simp [nextL]
          | cons b u =>
              cases b with
              | AttL my =>
                  rcases my with ⟨m, y⟩
                  have h := ih ⟨by simp [guardL], ChkLCR_AttL_cons.mp hC⟩
                  simp [nextL, h]
              | AttC m => simp [nextL]
              | AttR m => simp [nextL]

theorem toStbOne_length {t : List Att} :
    ∀ a, ChkLCR t → (toStbOne (a :: t)).length = Nat.succ t.length := by
  intro a h
  cases t with
  | nil => cases a <;> simp [toStbOne]
  | cons b u =>
      cases a with
      | AttL nx => simp [toStbOne]
      | AttC n =>
          cases b with
          | AttL my =>
              rcases my with ⟨m, y⟩
              have hl := length_nextL (t := Att.AttL (m, y) :: u) ⟨by simp [guardL], h⟩
              simp [toStbOne, hl]
          | AttC m => simp [toStbOne, nextL]
          | AttR m => simp [toStbOne]
      | AttR n =>
          cases b with
          | AttL my =>
              rcases my with ⟨m, y⟩
              cases u with
              | nil => simp [toStbOne]
              | cons c w =>
                  cases c with
                  | AttL ny =>
                      rcases ny with ⟨na, xx⟩
                      have h1 : ChkLCR (Att.AttL (na, xx) :: w) :=
                        ChkLCR_AttL_cons.mp h
                      have hl1 := length_nextL (t := Att.AttL (na, xx) :: w)
                        ⟨by simp [guardL], h1⟩
                      have h3 : ChkLCR (nextL (Att.AttL (na, xx) :: w)) := by
                        rw [ChkLCR_nextL (by simp [guardL])]
                        exact h1
                      have hl3 := length_nextL (t := nextL (Att.AttL (na, xx) :: w))
                        ⟨guardL_nextL_AttL, h3⟩
                      simp [toStbOne, hl3, hl1]
                  | AttC na => simp [toStbOne]
                  | AttR na => simp [toStbOne]
          | AttC m => simp [toStbOne, nextL]
          | AttR m => simp [toStbOne]

theorem ChkLCR_toStbOne_if {a : Att} {s : List Att} :
    ChkLCR (toStbOne (a :: s)) → ChkLCR s := by
  intro h
  cases s with
  | nil => simp [ChkLCR]
  | cons b u =>
      cases a with
      | AttL nx =>
          simp only [toStbOne] at h
          exact ChkLCR_AttL_cons.mp h
      | AttC n =>
          cases b with
          | AttL my =>
              rcases my with ⟨m, y⟩
              simp only [toStbOne] at h
              rw [ChkLCR_AttL_cons, ChkLCR_nextL (by simp [guardL])] at h
              exact h
          | AttC m =>
              simp only [toStbOne, nextL] at h
              rw [ChkLCR_AttL_cons, ChkLCR_AttR_cons] at h
              exact ChkLCR_AttC_cons.mpr h
          | AttR m =>
              simp only [toStbOne] at h
              rw [ChkLCR_AttC_cons, ChkR_AttR_cons] at h
              exact ChkLCR_AttR_cons.mpr h
      | AttR n =>
          cases b with
          | AttL my =>
              rcases my with ⟨m, y⟩
              cases u with
              | nil => simp [ChkLCR, ChkCR, ChkR]
              | cons c w =>
                  cases c with
                  | AttL ny =>
                      rcases ny with ⟨na, xx⟩
                      simp only [toStbOne] at h
                      rw [ChkLCR_AttL_cons, ChkLCR_nextL (by simp [guardL]),
                        ChkLCR_AttL_cons, ChkLCR_nextL (by simp [guardL]),
                        ChkLCR_AttL_cons] at h
                      simpa [ChkLCR_AttL_cons] using h
                  | AttC na =>
                      simp only [toStbOne] at h
                      rw [ChkLCR_AttL_cons, ChkLCR_AttC_cons, ChkR_AttR_cons] at h
                      simpa [ChkLCR_AttL_cons, ChkLCR_AttC_cons] using h
                  | AttR na =>
                      simp only [toStbOne] at h
                      rw [ChkLCR_AttL_cons, ChkLCR_AttR_cons, ChkR_AttR_cons] at h
                      simpa [ChkLCR_AttL_cons, ChkLCR_AttR_cons] using h
          | AttC m =>
              simp only [toStbOne, nextL] at h
              rw [ChkLCR_AttC_cons, ChkR_AttR_cons] at h
              exact ChkLCR_AttC_cons.mpr h
          | AttR m =>
              simp only [toStbOne] at h
              rw [ChkLCR_AttR_cons, ChkR_AttR_cons] at h
              exact ChkLCR_AttR_cons.mpr h

theorem ChkLCR_toStbOne_iff {a : Att} {s : List Att} :
    ChkLCR (toStbOne (a :: s)) ↔ ChkLCR s :=
  ⟨ChkLCR_toStbOne_if, ChkLCR_toStbOne⟩

theorem EX_toStbOne_toStb {s : List Att} :
    ∃ t, toStbOne t = toStb s := by
  cases s with
  | nil => exact ⟨[], by simp [toStb]⟩
  | cons a u => exact ⟨a :: toStb u, by simp [toStb]⟩

/- -------------------------------------------------------------------- -/

theorem nextL_AttL_EX {n x : Nat} {t : List Att} :
    ∃ a s, nextL (Att.AttL (n, x) :: t) = a :: s := by
  cases t with
  | nil =>
      exact ⟨Att.AttC (fill (n / 2 + x)), [], by simp [nextL]⟩
  | cons b u =>
      cases b with
      | AttL my =>
          rcases my with ⟨m, y⟩
          exact ⟨Att.AttL (fill (n / 2 + x), m / 2), nextL (Att.AttL (m, y) :: u), by simp [nextL]⟩
      | AttC m =>
          exact ⟨Att.AttL (fill (n / 2 + x), m / 2), Att.AttR (m / 2) :: u, by simp [nextL]⟩
      | AttR m =>
          exact ⟨Att.AttC (fill (n / 2 + x)), Att.AttR m :: u, by simp [nextL]⟩

theorem nextR_AttC_EX {n x : Nat} {t : List Att} :
    ∃ a s, nextR (Att.AttC n :: t, x) = a :: s := by
  cases t with
  | nil =>
      exact ⟨Att.AttL (n, x), [], by simp [nextR]⟩
  | cons b u =>
      exact ⟨Att.AttL (n, getNat (hd (updateR (b :: u, x)))), updateR (b :: u, x), by simp [nextR]⟩

theorem nextR_AttR_EX {n x : Nat} {t : List Att} :
    ∃ a s, nextR (Att.AttR n :: t, x) = a :: s := by
  cases t with
  | nil =>
      exact ⟨Att.AttC (fill (n + x)), [], by simp [nextR]⟩
  | cons b u =>
      exact ⟨Att.AttC (fill (n + getNat (hd (updateR (b :: u, x))))), updateR (b :: u, x),
        by simp [nextR]⟩

theorem hd_nextR_AttC_EX {n y : Nat} {t : List Att} :
    ∃ x s, nextR (Att.AttC n :: t, y) = Att.AttL (n, x) :: s := by
  cases t with
  | nil =>
      exact ⟨y, [], by simp [nextR]⟩
  | cons b u =>
      exact ⟨getNat (hd (updateR (b :: u, y))), updateR (b :: u, y), by simp [nextR]⟩

theorem getNat_hd_nextR_AttC {n y : Nat} {t : List Att} :
    getNat (hd (nextR (Att.AttC n :: t, y))) = n := by
  rcases hd_nextR_AttC_EX (n := n) (y := y) (t := t) with ⟨x, s, hs⟩
  simp [hs, getNat]

private theorem guardR_nextR_nextL_aux :
    ∀ t : List Att, ∀ z : Nat, ChkLCR t → guardL t → guardR t →
      guardR (nextR (nextL t, z)) := by
  intro t
  induction t with
  | nil =>
      intro z _ hL _
      simp [guardL] at hL
  | cons a s ih =>
      intro z hC hL hR
      cases a with
      | AttR n => simp [guardL] at hL
      | AttC n =>
          cases s with
          | nil => simp [nextL, nextR, guardR]
          | cons b u =>
              rcases updateR_AttR_EX (a := b) (s := u) (x := z) with ⟨m, v, hv⟩
              have hg := guardR_updateR (s := b :: u) (x := z) (by simp)
              rw [hv] at hg
              simp only [nextL, nextR, hv, List.head!_cons, guardR_cons2]
              exact hg
      | AttL nx =>
          rcases nx with ⟨n, x⟩
          cases s with
          | nil => simp [guardR] at hR
          | cons b u =>
              have hRs : guardR (b :: u) := by simpa [guardR_cons2] using hR
              cases b with
              | AttL my =>
                  rcases my with ⟨m, y⟩
                  have hIH := ih z (ChkLCR_AttL_cons.mp hC) (by simp [guardL]) hRs
                  rcases nextL_AttL_cons_EX (n := m) (x := y) (t := u) with ⟨a', s', hs⟩
                  rw [hs] at hIH
                  simp only [nextL, hs, nextR, guardR_AttL]
                  exact hIH
              | AttC m =>
                  cases u with
                  | nil => simp [nextL, nextR, guardR]
                  | cons c w =>
                      rcases updateR_AttR_EX (a := c) (s := w) (x := z) with ⟨mv, v, hv⟩
                      have hg := guardR_updateR (s := c :: w) (x := z) (by simp)
                      rw [hv] at hg
                      simp only [nextL, nextR, hv, List.head!_cons, guardR_cons2]
                      exact hg
              | AttR m =>
                  rcases updateR_AttR_EX (a := Att.AttR m) (s := u) (x := z) with ⟨mv, v, hv⟩
                  have hg := guardR_updateR (s := Att.AttR m :: u) (x := z) (by simp)
                  rw [hv] at hg
                  simp only [nextL, nextR, hv, List.head!_cons, guardR_cons2]
                  exact hg

theorem guardR_nextR_nextL_lm {n : Nat} :
    ∀ t z, (t.length = n ∧ ChkLCR t ∧ guardL t ∧ guardR t) →
      guardR (nextR (nextL t, z)) := by
  intro t z h
  exact guardR_nextR_nextL_aux t z h.2.1 h.2.2.1 h.2.2.2

theorem guardR_nextR_nextL {t : List Att} {z : Nat} :
    ChkLCR t → guardL t → guardR t → guardR (nextR (nextL t, z)) :=
  fun h1 h2 h3 => guardR_nextR_nextL_aux t z h1 h2 h3

private theorem guardL_nextL_nextR_aux {t : List Att} {z : Nat} :
    guardL t → guardR t → guardL (nextL (nextR (t, z))) := by
  intro hL hR
  cases t with
  | nil => simp [guardL] at hL
  | cons a s =>
      cases a with
      | AttR n => simp [guardL] at hL
      | AttC n =>
          cases s with
          | nil => simp [nextR, nextL, guardL]
          | cons b u =>
              rcases updateR_AttR_EX (a := b) (s := u) (x := z) with ⟨m, v, hv⟩
              simp [nextR, hv, nextL, guardL]
      | AttL nx =>
          rcases nx with ⟨n, x⟩
          cases s with
          | nil => simp [guardR] at hR
          | cons b u =>
              rcases not_nil_EX.mp (nextR_not_nil (a := b) (s := u) (x := z)) with ⟨b', v', hv'⟩
              simp [nextR, hv']

theorem guardL_nextL_nextR_lm {n : Nat} :
    ∀ t z, (t.length = n ∧ ChkLCR t ∧ guardL t ∧ guardR t) →
      guardL (nextL (nextR (t, z))) := by
  intro t z h
  exact guardL_nextL_nextR_aux h.2.2.1 h.2.2.2

theorem guardL_nextL_nextR {t : List Att} {z : Nat} :
    ChkLCR t → guardL t → guardR t → guardL (nextL (nextR (t, z))) :=
  fun _ h2 h3 => guardL_nextL_nextR_aux h2 h3

private theorem guardR_nextR_AttR_aux {t : List Att} {m x : Nat} :
    guardR (nextR (Att.AttR m :: t, x)) := by
  cases t with
  | nil => simp [nextR, guardR]
  | cons b u =>
      rcases updateR_AttR_EX (a := b) (s := u) (x := x) with ⟨mv, v, hv⟩
      have hg := guardR_updateR (s := b :: u) (x := x) (by simp)
      rw [hv] at hg
      simp only [nextR, hv, List.head!_cons, guardR_cons2]
      exact hg

theorem guardR_nextR_AttR_lm {n : Nat} :
    ∀ t m x, (t.length = n ∧ ChkLCR t) → guardR (nextR (Att.AttR m :: t, x)) := by
  intro t m x _
  exact guardR_nextR_AttR_aux

theorem guardR_nextR_AttR {t : List Att} {m x : Nat} :
    ChkLCR t → guardR (nextR (Att.AttR m :: t, x)) := by
  intro _
  exact guardR_nextR_AttR_aux

@[simp] theorem not_nil_nextL_not_nil {t : List Att} :
    t ≠ [] → nextL t ≠ [] := by
  intro h
  rcases not_nil_EX.mp h with ⟨a, s, rfl⟩
  exact nextL_not_nil

@[simp] theorem not_nil_nextR_not_nil {t : List Att} {x : Nat} :
    t ≠ [] → nextR (t, x) ≠ [] := by
  intro h
  rcases not_nil_EX.mp h with ⟨a, s, rfl⟩
  exact nextR_not_nil

/- --------------------------------- *
               lemmas
 * --------------------------------- -/

theorem toStbOne_AttC_hd :
    ∀ n s,
      (∃ m t, toStbOne (Att.AttC n :: s) = Att.AttC m :: t) ∨
        (∃ m t, toStbOne (Att.AttC n :: s) = Att.AttL m :: t) := by
  intro n s
  cases s with
  | nil => exact Or.inl ⟨n, [], by simp [toStbOne]⟩
  | cons b u =>
      cases b with
      | AttL my =>
          rcases my with ⟨m, y⟩
          exact Or.inr ⟨(n, m / 2), nextL (Att.AttL (m, y) :: u), by simp [toStbOne]⟩
      | AttC m =>
          exact Or.inr ⟨(n, m / 2), nextL (Att.AttC m :: u), by simp [toStbOne]⟩
      | AttR m =>
          exact Or.inl ⟨n, Att.AttR m :: u, by simp [toStbOne]⟩

theorem guardL_toStb_AttC {s : List Nat} :
    s ≠ [] → guardL (toStb (List.map Att.AttC s)) := by
  intro h
  cases s with
  | nil => simp at h
  | cons a u =>
      rw [List.map_cons, show toStb (Att.AttC a :: List.map Att.AttC u) =
        toStbOne (Att.AttC a :: toStb (List.map Att.AttC u)) from by simp [toStb]]
      rcases toStbOne_AttC_hd a (toStb (List.map Att.AttC u)) with ⟨m, t', ht⟩ | ⟨m, t', ht⟩
      · simp [ht, guardL]
      · simp only [guardL, ht, Att.AttL.injEq, reduceCtorEq, exists_const, or_false]
        exact ⟨m.1, m.2, rfl⟩

private theorem guardR_cons_map_AttC {c : Att} {u : List Nat} :
    ((∃ n, c = Att.AttC n) ∨ ∃ n, c = Att.AttR n) → guardR (c :: List.map Att.AttC u) := by
  induction u generalizing c with
  | nil =>
      intro h
      simpa [guardR] using h
  | cons a w ih =>
      intro _
      simp only [List.map_cons, guardR_cons2]
      exact ih (Or.inl ⟨a, rfl⟩)

theorem guardR_toStbOne_map_AttC_lm {n : Nat} :
    ∀ s, (s.length = n ∧ s ≠ []) → guardR (toStbOne (List.map Att.AttC s)) := by
  intro s h
  rcases h with ⟨-, hne⟩
  cases s with
  | nil => simp at hne
  | cons a u =>
      cases u with
      | nil => simp [toStbOne, guardR]
      | cons b w =>
          simp only [List.map_cons]
          simp only [toStbOne, nextL, guardR_AttL]
          exact guardR_cons_map_AttC (Or.inr ⟨b / 2, rfl⟩)

theorem guardR_toStbOne_AttC {t : List Att} {a : Nat} :
    ChkLCR t → guardR (toStbOne (Att.AttC a :: t)) := by
  intro h
  cases t with
  | nil => simp [toStbOne, guardR]
  | cons b u =>
      cases b with
      | AttL my =>
          rcases my with ⟨m, y⟩
          have hg : guardR (nextL (Att.AttL (m, y) :: u)) :=
            ChkLCR_guardR_next ⟨h, by simp⟩
          simpa [toStbOne] using hg
      | AttC m =>
          have hR : ChkR u := ChkLCR_AttC_cons.mp h
          have hg := ChkR_guardR_AttR (s := u) (m / 2) hR
          simpa [toStbOne, nextL] using hg
      | AttR m =>
          have hR : ChkR u := ChkLCR_AttR_cons.mp h
          have hg := ChkR_guardR_AttR (s := u) m hR
          simpa [toStbOne, guardR_cons2] using hg

theorem guardR_toStb_AttC {s : List Nat} :
    s ≠ [] → guardR (toStb (List.map Att.AttC s)) := by
  intro h
  cases s with
  | nil => simp at h
  | cons a u =>
      rw [List.map_cons, show toStb (Att.AttC a :: List.map Att.AttC u) =
        toStbOne (Att.AttC a :: toStb (List.map Att.AttC u)) from by simp [toStb]]
      exact guardR_toStbOne_AttC ChkLCR_toStb

/- *********************************************************
              preliminary (stabilization)
 ********************************************************* -/

theorem toStbOne_AttC_hd2 :
    ∀ n s,
      (∃ t, toStbOne (Att.AttC n :: s) = Att.AttC n :: t) ∨
        (∃ m t, toStbOne (Att.AttC n :: s) = Att.AttL (n, m) :: t) := by
  intro n s
  cases s with
  | nil => exact Or.inl ⟨[], by simp [toStbOne]⟩
  | cons b u =>
      cases b with
      | AttL my =>
          rcases my with ⟨m, y⟩
          exact Or.inr ⟨m / 2, nextL (Att.AttL (m, y) :: u), by simp [toStbOne]⟩
      | AttC m =>
          exact Or.inr ⟨m / 2, nextL (Att.AttC m :: u), by simp [toStbOne]⟩
      | AttR m =>
          exact Or.inl ⟨Att.AttR m :: u, by simp [toStbOne]⟩

@[simp] theorem getNat_hd_toStbOne_AttC {n : Nat} {s : List Att} :
    getNat (hd (toStbOne (Att.AttC n :: s))) = n := by
  rcases toStbOne_AttC_hd2 n s with ⟨t', ht⟩ | ⟨m, t', ht⟩ <;> simp [ht, getNat]

theorem nextR_nextL_AttL_EX :
    ∀ n x a s y,
      ∃ z t,
        nextR (nextL (Att.AttL (n, x) :: a :: s), y) =
          Att.AttL (fill (n / 2 + x), z) :: t := by
  intro n x a s y
  cases a with
  | AttL my =>
      rcases my with ⟨m, y'⟩
      rcases nextL_AttL_cons_EX (n := m) (x := y') (t := s) with ⟨a', s', hs⟩
      exact ⟨m / 2, nextR (a' :: s', y), by simp [nextL, hs, nextR]⟩
  | AttC m =>
      exact ⟨m / 2, nextR (Att.AttR (m / 2) :: s, y), by simp [nextL, nextR]⟩
  | AttR m =>
      exact ⟨getNat (hd (updateR (Att.AttR m :: s, y))), updateR (Att.AttR m :: s, y),
        by simp [nextL, nextR]⟩

@[simp] theorem getNat_hd_nextR_nextL_AttL {n x y : Nat} {a : Att} {s : List Att} :
    getNat (hd (nextR (nextL (Att.AttL (n, x) :: a :: s), y))) = fill (n / 2 + x) := by
  rcases nextR_nextL_AttL_EX n x a s y with ⟨z, t', ht⟩
  simp [ht, getNat]

/- ---------------------------------- *
      async version <--> lineNext
 * ---------------------------------- -/

theorem nextL_nextR_toStb_lineNext {s : List Nat} {x : Nat} :
    nextL (nextR (toStb (List.map Att.AttC s), x)) =
      toStb (List.map Att.AttC (lineNext s x)) := by
  induction s with
  | nil => simp [toStb, nextR, nextL, lineNext]
  | cons a u ih =>
      cases u with
      | nil => simp [lineNext, toStb, toStbOne, nextR, nextL]
      | cons b w =>
          have hC : ChkLCR (toStb (List.map Att.AttC (b :: w))) := ChkLCR_toStb
          have hL : guardL (toStb (List.map Att.AttC (b :: w))) :=
            guardL_toStb_AttC (by simp)
          have hR : guardR (toStb (List.map Att.AttC (b :: w))) :=
            guardR_toStb_AttC (by simp)
          have hOrd := nextL_nextR_order (t := toStb (List.map Att.AttC (b :: w))) (x := x)
            (Or.inr ⟨hL, hR, hC⟩)
          have hstep : toStb (List.map Att.AttC (a :: b :: w)) =
              toStbOne (Att.AttC a :: toStb (List.map Att.AttC (b :: w))) := by
            simp [toStb]
          have hline : lineNext (a :: b :: w) x =
              fill (a / 2 + b / 2) :: lineNext (b :: w) x := by
            simp [lineNext, hd]
          have hrhs : toStb (List.map Att.AttC (lineNext (a :: b :: w) x)) =
              toStbOne (Att.AttC (fill (a / 2 + b / 2)) ::
                nextL (nextR (toStb (List.map Att.AttC (b :: w)), x))) := by
            rw [hline]
            simp only [List.map_cons]
            rw [show toStb (Att.AttC (fill (a / 2 + b / 2)) ::
                  List.map Att.AttC (lineNext (b :: w) x)) =
                toStbOne (Att.AttC (fill (a / 2 + b / 2)) ::
                  toStb (List.map Att.AttC (lineNext (b :: w) x))) from by simp [toStb],
              ← ih, List.map_cons]
          rw [hstep, hrhs]
          have hWdef : toStb (List.map Att.AttC (b :: w)) =
              toStbOne (Att.AttC b :: toStb (List.map Att.AttC w)) := by
            simp [toStb]
          rcases toStbOne_AttC_hd2 b (toStb (List.map Att.AttC w)) with ⟨tb, hT⟩ | ⟨q, tb, hT⟩
          · -- head of the stabilized tail is (AttC b)
            have hT2 : toStb (List.map Att.AttC (b :: w)) = Att.AttC b :: tb := by
              rw [hWdef]; exact hT
            rw [hT2] at hOrd ⊢
            cases tb with
            | nil => simp [toStbOne, nextR, nextL]
            | cons c v =>
                rcases updateR_AttR_EX (a := c) (s := v) (x := x) with ⟨gm, gv, hv⟩
                simp [toStbOne, nextR, nextL, hv, getNat]
          · -- head of the stabilized tail is (AttL (b, q))
            have hT2 : toStb (List.map Att.AttC (b :: w)) = Att.AttL (b, q) :: tb := by
              rw [hWdef]; exact hT
            cases tb with
            | nil =>
                exfalso
                have h2 := toStb_one.mp hT2
                simp at h2
            | cons c2 tb' =>
                rw [hT2] at hOrd ⊢
                rcases nextL_AttL_cons_EX (n := b) (x := q) (t := c2 :: tb') with ⟨a', s', ha'⟩
                rcases nextR_nextL_AttL_EX b q c2 tb' x with ⟨z, t', hzt⟩
                rw [ha'] at hzt hOrd
                conv_rhs => rw [hOrd, hzt]
                rw [show toStbOne (Att.AttC a :: Att.AttL (b, q) :: c2 :: tb') =
                    Att.AttL (a, b / 2) :: nextL (Att.AttL (b, q) :: c2 :: tb') from by
                  simp [toStbOne], ha']
                simp [nextR, nextL, toStbOne, hzt]

theorem nextR_nextL_toStb_nextR_nextL_toStb {s : List Nat} {x : Nat} :
    s ≠ [] →
      nextR (nextL (toStb (List.map Att.AttC s)), x) =
        nextL (nextR (toStb (List.map Att.AttC s), x)) := by
  intro h
  exact (nextL_nextR_order
    (Or.inr ⟨guardL_toStb_AttC h, guardR_toStb_AttC h, ChkLCR_toStb⟩)).symm

theorem nextR_nextL_toStb_lineNext {s : List Nat} {x : Nat} :
    s ≠ [] →
      nextR (nextL (toStb (List.map Att.AttC s)), x) =
        toStb (List.map Att.AttC (lineNext s x)) := by
  intro h
  rw [nextR_nextL_toStb_nextR_nextL_toStb h, nextL_nextR_toStb_lineNext]

/- ----------- guard lemma ----------- -/

theorem guardL_nextL_toStb_AttC {s : List Nat} :
    tl s ≠ [] → guardL (nextL (toStb (List.map Att.AttC s))) := by
  intro h
  cases s with
  | nil => simp [tl] at h
  | cons a u =>
      cases u with
      | nil => simp [tl] at h
      | cons b w =>
          rw [show toStb (List.map Att.AttC (a :: b :: w)) =
            toStbOne (Att.AttC a :: toStb (List.map Att.AttC (b :: w))) from by simp [toStb]]
          have hWdef : toStb (List.map Att.AttC (b :: w)) =
              toStbOne (Att.AttC b :: toStb (List.map Att.AttC w)) := by
            simp [toStb]
          rcases toStbOne_AttC_hd2 b (toStb (List.map Att.AttC w)) with ⟨tb, hT⟩ | ⟨q, tb, hT⟩
          · rw [hWdef, hT]
            simp [toStbOne, nextL, guardL]
          · rw [hWdef, hT]
            rcases nextL_AttL_cons_EX (n := b) (x := q) (t := tb) with ⟨a', s', ha'⟩
            simp [toStbOne, ha']

theorem toStbOne_AttC_AttC {n m : Nat} {s : List Att} :
    toStbOne (Att.AttC n :: toStbOne (Att.AttC m :: s)) =
      Att.AttL (n, m / 2) :: nextL (toStbOne (Att.AttC m :: s)) := by
  cases s with
  | nil => simp [toStbOne, nextL]
  | cons b u =>
      cases b with
      | AttL my =>
          rcases my with ⟨p, q⟩
          rcases nextL_AttL_cons_EX (n := p) (x := q) (t := u) with ⟨a', s', ha'⟩
          simp [toStbOne, ha']
      | AttC p => simp [toStbOne, nextL]
      | AttR p => simp [toStbOne, nextL]

private theorem guardR_nextR_toStb_AttC_aux {s : List Nat} {x : Nat} :
    tl s ≠ [] → guardR (nextR (toStb (List.map Att.AttC s), x)) := by
  intro h
  cases s with
  | nil => simp [tl] at h
  | cons a u =>
      cases u with
      | nil => simp [tl] at h
      | cons b w =>
          rw [show toStb (List.map Att.AttC (a :: b :: w)) =
            toStbOne (Att.AttC a :: toStbOne (Att.AttC b :: toStb (List.map Att.AttC w)))
            from by simp [toStb]]
          rw [toStbOne_AttC_AttC]
          have hWdef : toStb (List.map Att.AttC (b :: w)) =
              toStbOne (Att.AttC b :: toStb (List.map Att.AttC w)) := by
            simp [toStb]
          have hg := guardR_nextR_nextL (t := toStb (List.map Att.AttC (b :: w))) (z := x)
            ChkLCR_toStb (guardL_toStb_AttC (by simp)) (guardR_toStb_AttC (by simp))
          rw [hWdef] at hg
          rcases not_nil_EX.mp (not_nil_nextL_not_nil
            (t := toStbOne (Att.AttC b :: toStb (List.map Att.AttC w))) (by simp))
            with ⟨w1, w2, hw⟩
          rw [hw] at hg ⊢
          simp only [nextR, guardR_AttL]
          exact hg

theorem guardR_nextR_toStb_AttC_lm {n : Nat} :
    ∀ s x, (s.length = n ∧ tl s ≠ []) →
      guardR (nextR (toStb (List.map Att.AttC s), x)) := by
  intro s x h
  exact guardR_nextR_toStb_AttC_aux h.2

theorem guardR_nextR_toStb_AttC {s : List Nat} {x : Nat} :
    tl s ≠ [] → guardR (nextR (toStb (List.map Att.AttC s), x)) :=
  guardR_nextR_toStb_AttC_aux

/- ---------------------------------- *
                nextLR
 * ---------------------------------- -/

theorem nextLR_toStb_circNext {s : List Nat} :
    nextLR (toStb (List.map Att.AttC s)) =
      toStb (List.map Att.AttC (circNext s)) := by
  cases s with
  | nil => simp [nextLR, toStb, nextR, nextL, circNext]
  | cons a u =>
      have hhd : getNat (hd (toStb (List.map Att.AttC (a :: u)))) = a := by
        rw [show toStb (List.map Att.AttC (a :: u)) =
          toStbOne (Att.AttC a :: toStb (List.map Att.AttC u)) from by simp [toStb]]
        exact getNat_hd_toStbOne_AttC
      simp only [nextLR]
      rw [hhd, nextL_nextR_toStb_lineNext]
      simp [circNext, hd]

/- ------------- lemma ------------- -/

theorem tl_lineNext {t : List Nat} {x : Nat} :
    tl t ≠ [] → lineNext (tl t) x = tl (lineNext t x) := by
  intro h
  cases t with
  | nil => simp [tl] at h
  | cons a u =>
      cases u with
      | nil => simp [tl] at h
      | cons b w => simp [lineNext, tl]

theorem hd_lineNext {t : List Nat} {x : Nat} :
    tl t ≠ [] → hd (lineNext t x) = fill (hd t / 2 + hd (tl t) / 2) := by
  intro h
  cases t with
  | nil => simp [tl] at h
  | cons a u =>
      cases u with
      | nil => simp [tl] at h
      | cons b w => simp [lineNext, hd, tl]

theorem hd_circNext {t : List Nat} :
    tl t ≠ [] → hd (circNext t) = fill (hd t / 2 + hd (tl t) / 2) := by
  intro h
  have ht : t ≠ [] := by
    intro he
    rw [he] at h
    simp [tl] at h
  rw [show circNext t = lineNext t (hd t / 2) from by simp [circNext, ht]]
  exact hd_lineNext h

theorem getNat_hd_toStb_map_AttC {t : List Nat} :
    t ≠ [] → getNat (hd (toStb (List.map Att.AttC t))) = hd t := by
  intro h
  cases t with
  | nil => simp at h
  | cons a u =>
      rw [show toStb (List.map Att.AttC (a :: u)) =
        toStbOne (Att.AttC a :: toStb (List.map Att.AttC u)) from by simp [toStb]]
      simp [hd]
