           /- -------------------------------------------*
            |       Uniform Candy Distribution          |
            |                                           |
            |           November 2007 for Isabelle 2005 |
            |           November 2008 for Isabelle 2008 |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.UCD.UCD_data1

open Classical

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
  native_decide

theorem test_toStbOne :
    toStbOne [Att.AttR 2, Att.AttL (4, 2), Att.AttC 0, Att.AttR 6] =
      [Att.AttL (4, 2), Att.AttC 2, Att.AttR 0, Att.AttR 6] := by
  native_decide

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
      simpa using (nextL_one_not_nil (a := a))
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

axiom tl_toStbOne_not_nil {s : List Att} :
  (tl (toStbOne s) ≠ []) ↔ ∃ a1 a2 t, s = a1 :: a2 :: t

@[simp] axiom ChkLCR_nextL {s : List Att} :
  guardL s → (ChkLCR (nextL s) ↔ ChkLCR s)

@[simp] axiom ChkLCR_nextR {s : List Att} {x : Nat} :
  guardR s → (ChkLCR (nextR (s, x)) ↔ ChkLCR s)

@[simp] theorem ChkLCR_AttL {n x : Nat} {s : List Att} :
    ChkLCR (Att.AttL (n, x) :: s) ↔ ChkLCR s := by
  simp [ChkLCR, ChkCR, ChkR]

@[simp] theorem toStbOne_AttL {n x : Nat} {s : List Att} :
    toStbOne (Att.AttL (n, x) :: s) = Att.AttL (n, x) :: s := by
  cases s <;> simp [toStbOne]

axiom nextL_nextR_order {t : List Att} {x : Nat} :
  (t = [] ∨ guardL t ∧ guardR t ∧ ChkLCR t) →
    nextL (nextR (t, x)) = nextR (nextL t, x)

theorem ChkR_ChkCR {t : List Att} :
    ChkR t → ChkLCR t := by
  intro h
  induction t with
  | nil =>
      simp [ChkR, ChkLCR]
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
              simp [guardR]
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
              simp [guardR]
              exact ih m (by simpa [ChkR] using h.2)

@[simp] axiom ChkLCR_guardR_next {t : List Att} :
  ChkLCR t ∧ t ≠ [] → guardR (nextL t)

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
  cases t <;> simp [nextL, nextR, updateR]

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
      Att.AttL (fill (n / 2 + x), fill (m / 2 + y) / 2) :: nextL (nextL (Att.AttL (m, y) :: t)) := by
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

@[simp] axiom ChkLCR_guardL_guardR_nextL {t : List Att} :
  ChkLCR t → guardL t → guardR (nextL t)

@[simp] axiom ChkLCR_guardR_guardL_nextR {t : List Att} {x : Nat} :
  ChkLCR t → guardR t → guardL (nextR (t, x))

axiom nextR_nextL_nextL_order_AttL {n x y : Nat} {t : List Att} :
  ChkLCR t → guardR t →
    nextR (nextL (nextL (Att.AttL (n, x) :: t)), y) =
      nextL (nextR (nextL (Att.AttL (n, x) :: t), y))

@[simp] axiom nextL_AttL_nextR_guardR {n x y : Nat} {t : List Att} :
  ChkLCR t → guardR t →
    nextL (Att.AttL (n, x) :: nextR (t, y)) =
      Att.AttL (fill (n / 2 + x), getNat (hd (nextR (t, y))) / 2) :: nextL (nextR (t, y))

@[simp] axiom ChkR_ChkLCR_updateR {s : List Att} {x : Nat} :
  ChkR s → (ChkLCR (updateR (s, x)) ↔ ChkLCR s)

@[simp] axiom ChkR_ChkR_updateR {s : List Att} {x : Nat} :
  ChkR s → (ChkR (updateR (s, x)) ↔ ChkR s)

/- ---- basic ---- -/

axiom ChkLCR_toStbOne_id {t : List Att} :
  ChkLCR t → toStbOne t = t

axiom ChkLCR_toStbOne {a : Att} {t : List Att} :
  ChkLCR t → ChkLCR (toStbOne (a :: t))

axiom ChkLCR_tl {a : Att} {t : List Att} :
  ChkLCR (a :: t) → ChkLCR t

axiom ChkLCR_toStb {t : List Att} :
  ChkLCR (toStb t)

axiom ChkLCR_toStb_id {t : List Att} :
  ChkLCR t → toStb t = t

axiom nextL_one_EX {t : List Att} {a : Att} :
  ChkLCR t → nextL t = [a] → ∃ a0 : Att, t = [a0]

axiom nextR_one_EX {t : List Att} {x : Nat} {a : Att} :
  ChkLCR t → nextR (t, x) = [a] → ∃ a0 : Att, t = [a0]

@[simp] axiom toStbOne_nil {t : List Att} :
  (toStbOne t = []) ↔ (t = [])

@[simp] axiom toStb_nil {t : List Att} :
  (toStb t = []) ↔ (t = [])

@[simp] axiom toStbOne_one {t : List Att} {a : Att} :
  (toStbOne t = [a]) ↔ (t = [a])

@[simp] axiom toStb_one {t : List Att} {a : Att} :
  (toStb t = [a]) ↔ (t = [a])

axiom length_nextL {t : List Att} :
  guardL t ∧ ChkLCR t → (nextL t).length = t.length

axiom toStbOne_length {t : List Att} :
  ∀ a, ChkLCR t → (toStbOne (a :: t)).length = Nat.succ t.length

axiom ChkLCR_toStbOne_if {a : Att} {s : List Att} :
  ChkLCR (toStbOne (a :: s)) → ChkLCR s

axiom ChkLCR_toStbOne_iff {a : Att} {s : List Att} :
  ChkLCR (toStbOne (a :: s)) ↔ ChkLCR s

axiom EX_toStbOne_toStb {s : List Att} :
  ∃ t, toStbOne t = toStb s

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
      exact ⟨Att.AttC (fill (n + getNat (hd (updateR (b :: u, x))))), updateR (b :: u, x), by simp [nextR]⟩

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

axiom guardR_nextR_nextL_lm {n : Nat} :
  ∀ t z, (t.length = n ∧ ChkLCR t ∧ guardL t ∧ guardR t) →
    guardR (nextR (nextL t, z))

axiom guardR_nextR_nextL {t : List Att} {z : Nat} :
  ChkLCR t → guardL t → guardR t → guardR (nextR (nextL t, z))

axiom guardL_nextL_nextR_lm {n : Nat} :
  ∀ t z, (t.length = n ∧ ChkLCR t ∧ guardL t ∧ guardR t) →
    guardL (nextL (nextR (t, z)))

axiom guardL_nextL_nextR {t : List Att} {z : Nat} :
  ChkLCR t → guardL t → guardR t → guardL (nextL (nextR (t, z)))

axiom guardR_nextR_AttR_lm {n : Nat} :
  ∀ t m x, (t.length = n ∧ ChkLCR t) → guardR (nextR (Att.AttR m :: t, x))

axiom guardR_nextR_AttR {t : List Att} {m x : Nat} :
  ChkLCR t → guardR (nextR (Att.AttR m :: t, x))

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

axiom toStbOne_AttC_hd :
  ∀ n s,
    (∃ m t, toStbOne (Att.AttC n :: s) = Att.AttC m :: t) ∨
      (∃ m t, toStbOne (Att.AttC n :: s) = Att.AttL m :: t)

axiom guardL_toStb_AttC {s : List Nat} :
  s ≠ [] → guardL (toStb (List.map Att.AttC s))

axiom guardR_toStbOne_map_AttC_lm {n : Nat} :
  ∀ s, (s.length = n ∧ s ≠ []) → guardR (toStbOne (List.map Att.AttC s))

axiom guardR_toStbOne_AttC {t : List Att} {a : Nat} :
  ChkLCR t → guardR (toStbOne (Att.AttC a :: t))

axiom guardR_toStb_AttC {s : List Nat} :
  s ≠ [] → guardR (toStb (List.map Att.AttC s))

/- *********************************************************
              preliminary (stabilization)
 ********************************************************* -/

axiom toStbOne_AttC_hd2 :
  ∀ n s,
    (∃ t, toStbOne (Att.AttC n :: s) = Att.AttC n :: t) ∨
      (∃ m t, toStbOne (Att.AttC n :: s) = Att.AttL (n, m) :: t)

@[simp] axiom getNat_hd_toStbOne_AttC {n : Nat} {s : List Att} :
  getNat (hd (toStbOne (Att.AttC n :: s))) = n

axiom nextR_nextL_AttL_EX :
  ∀ n x a s y,
    ∃ z t,
      nextR (nextL (Att.AttL (n, x) :: a :: s), y) =
        Att.AttL (fill (n / 2 + x), z) :: t

@[simp] axiom getNat_hd_nextR_nextL_AttL {n x y : Nat} {a : Att} {s : List Att} :
  getNat (hd (nextR (nextL (Att.AttL (n, x) :: a :: s), y))) = fill (n / 2 + x)

/- ---------------------------------- *
      async version <--> lineNext
 * ---------------------------------- -/

axiom nextL_nextR_toStb_lineNext {s : List Nat} {x : Nat} :
  nextL (nextR (toStb (List.map Att.AttC s), x)) =
    toStb (List.map Att.AttC (lineNext s x))

axiom nextR_nextL_toStb_nextR_nextL_toStb {s : List Nat} {x : Nat} :
  s ≠ [] →
    nextR (nextL (toStb (List.map Att.AttC s)), x) =
      nextL (nextR (toStb (List.map Att.AttC s), x))

axiom nextR_nextL_toStb_lineNext {s : List Nat} {x : Nat} :
  s ≠ [] →
    nextR (nextL (toStb (List.map Att.AttC s)), x) =
      toStb (List.map Att.AttC (lineNext s x))

/- ----------- guard lemma ----------- -/

axiom guardL_nextL_toStb_AttC {s : List Nat} :
  tl s ≠ [] → guardL (nextL (toStb (List.map Att.AttC s)))

axiom toStbOne_AttC_AttC {n m : Nat} {s : List Att} :
  toStbOne (Att.AttC n :: toStbOne (Att.AttC m :: s)) =
    Att.AttL (n, m / 2) :: nextL (toStbOne (Att.AttC m :: s))

axiom guardR_nextR_toStb_AttC_lm {n : Nat} :
  ∀ s x, (s.length = n ∧ tl s ≠ []) →
    guardR (nextR (toStb (List.map Att.AttC s), x))

axiom guardR_nextR_toStb_AttC {s : List Nat} {x : Nat} :
  tl s ≠ [] → guardR (nextR (toStb (List.map Att.AttC s), x))

/- ---------------------------------- *
                nextLR
 * ---------------------------------- -/

axiom nextLR_toStb_circNext {s : List Nat} :
  nextLR (toStb (List.map Att.AttC s)) =
    toStb (List.map Att.AttC (circNext s))

/- ------------- lemma ------------- -/

axiom tl_lineNext {t : List Nat} {x : Nat} :
  tl t ≠ [] → lineNext (tl t) x = tl (lineNext t x)

axiom hd_lineNext {t : List Nat} {x : Nat} :
  tl t ≠ [] → hd (lineNext t x) = fill (hd t / 2 + hd (tl t) / 2)

axiom hd_circNext {t : List Nat} :
  tl t ≠ [] → hd (circNext t) = fill (hd t / 2 + hd (tl t) / 2)

axiom getNat_hd_toStb_map_AttC {t : List Nat} :
  t ≠ [] → getNat (hd (toStb (List.map Att.AttC t))) = hd t
