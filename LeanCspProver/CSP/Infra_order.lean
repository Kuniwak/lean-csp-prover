           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               November 2004               |
            |                   June 2005  (modified)   |
            |                   July 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2016         |
            |                  April 2016  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2018         |
            |               February 2019  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Compat
import LeanCspProver.CSP.Infra_common

/-
(*****************************************************
                    order
 *****************************************************)
-/

theorem order_antisymE {α : Type _} [PartialOrder α] {a b : α} {P : Prop}
    (hEq : a = b) (hP : a <= b → b <= a → P) : P := by
  subst hEq
  exact hP le_rfl le_rfl

/-
(*****************************************************
            Upper Bound and Lower Bound
 *****************************************************)
-/

def isUB {α : Type _} [LE α] (x : α) (X : Set α) : Prop :=
  ∀ y, y ∈ X → y <= x

def isLUB {α : Type _} [PartialOrder α] (x : α) (X : Set α) : Prop :=
  isUB x X ∧ ∀ y, isUB y X → x <= y

def isLB {α : Type _} [LE α] (x : α) (X : Set α) : Prop :=
  ∀ y, y ∈ X → x <= y

def isGLB {α : Type _} [PartialOrder α] (x : α) (X : Set α) : Prop :=
  isLB x X ∧ ∀ y, isLB y X → y <= x

def hasLUB {α : Type _} [PartialOrder α] (X : Set α) : Prop :=
  ∃ x, isLUB x X

def hasGLB {α : Type _} [PartialOrder α] (X : Set α) : Prop :=
  ∃ x, isGLB x X

noncomputable def LUB {α : Type _} [PartialOrder α] [Inhabited α] (X : Set α) : α :=
  chooseOrDefault (fun x : α => isLUB x X)

noncomputable def GLB {α : Type _} [PartialOrder α] [Inhabited α] (X : Set α) : α :=
  chooseOrDefault (fun x : α => isGLB x X)

/- *** LUB is unique *** -/

theorem LUB_unique {α : Type _} [PartialOrder α] {x y : α} {X : Set α}
    (hx : isLUB x X) (hy : isLUB y X) : x = y := by
  exact le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/- *** GLB is unique *** -/

theorem GLB_unique {α : Type _} [PartialOrder α] {x y : α} {X : Set α}
    (hx : isGLB x X) (hy : isGLB y X) : x = y := by
  exact le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

private theorem isUB_of_subset {α : Type _} [LE α] {x : α} {X Y : Set α}
    (hx : isUB x Y) (hXY : X ⊆ Y) : isUB x X := by
  intro y hy
  exact hx y (hXY hy)

private theorem isLB_of_subset {α : Type _} [LE α] {x : α} {X Y : Set α}
    (hx : isLB x Y) (hXY : X ⊆ Y) : isLB x X := by
  intro y hy
  exact hx y (hXY hy)

/- -----------------------*
 |       the LUB         |
 *----------------------- -/

theorem isLUB_to_LUB {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasLUB X) : isLUB x X ↔ x = LUB X := by
  constructor
  · intro hx
    exact LUB_unique hx (by
      simpa [LUB] using chooseOrDefault_spec (p := fun z : α => isLUB z X) hX)
  · intro hx
    simpa [hx] using (show isLUB (LUB X) X from by
      simpa [LUB] using chooseOrDefault_spec (p := fun z : α => isLUB z X) hX)

theorem LUB_to_isLUB {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasLUB X) : x = LUB X ↔ isLUB x X := by
  exact (isLUB_to_LUB (X := X) (x := x) hX).symm

theorem LUB_to_isLUB_sym {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasLUB X) : LUB X = x ↔ isLUB x X := by
  simpa [eq_comm] using (LUB_to_isLUB (X := X) (x := x) hX)

theorem LUB_iff {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasLUB X) : (x = LUB X ↔ isLUB x X) ∧ (LUB X = x ↔ isLUB x X) :=
  ⟨LUB_to_isLUB hX, LUB_to_isLUB_sym hX⟩

theorem LUB_is {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α}
    (hX : hasLUB X) : isLUB (LUB X) X := by
  simpa [LUB] using chooseOrDefault_spec (p := fun z : α => isLUB z X) hX

theorem isLUB_LUB {α : Type _} [PartialOrder α] [Inhabited α] {x : α} {X : Set α}
    (hx : isLUB x X) : LUB X = x := by
  exact LUB_unique (LUB_is ⟨x, hx⟩) hx

/- -----------------------*
 |       the GLB         |
 *----------------------- -/

theorem isGLB_to_GLB {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasGLB X) : isGLB x X ↔ x = GLB X := by
  constructor
  · intro hx
    exact GLB_unique hx (by
      simpa [GLB] using chooseOrDefault_spec (p := fun z : α => isGLB z X) hX)
  · intro hx
    simpa [hx] using (show isGLB (GLB X) X from by
      simpa [GLB] using chooseOrDefault_spec (p := fun z : α => isGLB z X) hX)

theorem GLB_to_isGLB {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasGLB X) : x = GLB X ↔ isGLB x X := by
  exact (isGLB_to_GLB (X := X) (x := x) hX).symm

theorem GLB_to_isGLB_sym {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasGLB X) : GLB X = x ↔ isGLB x X := by
  simpa [eq_comm] using (GLB_to_isGLB (X := X) (x := x) hX)

theorem GLB_iff {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasGLB X) : (x = GLB X ↔ isGLB x X) ∧ (GLB X = x ↔ isGLB x X) :=
  ⟨GLB_to_isGLB hX, GLB_to_isGLB_sym hX⟩

theorem GLB_is {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α}
    (hX : hasGLB X) : isGLB (GLB X) X := by
  simpa [GLB] using chooseOrDefault_spec (p := fun z : α => isGLB z X) hX

theorem isGLB_GLB {α : Type _} [PartialOrder α] [Inhabited α] {x : α} {X : Set α}
    (hx : isGLB x X) : GLB X = x := by
  exact GLB_unique (GLB_is ⟨x, hx⟩) hx

/- -----------------------*
 |     LUB subset        |
 *----------------------- -/

theorem isLUB_subset {α : Type _} [PartialOrder α] {x y : α} {X Y : Set α}
    (hx : isLUB x X) (hy : isLUB y Y) (hXY : X ⊆ Y) : x <= y :=
  hx.2 y (isUB_of_subset hy.1 hXY)

/- -----------------------*
 |     GLB subset        |
 *----------------------- -/

theorem isGLB_subset {α : Type _} [PartialOrder α] {x y : α} {X Y : Set α}
    (hx : isGLB x X) (hy : isGLB y Y) (hXY : X ⊆ Y) : y <= x :=
  hx.2 y (isLB_of_subset hy.1 hXY)

/- --------------------------*
 |  GLB exists for nat set  |
 *-------------------------- -/

theorem EX_GLB_nat_lm {X : Set Nat} :
    ∀ m m', m' <= m ∧ m' ∈ X → ∃ n, isGLB n X ∧ n ∈ X := by
  classical
  intro m m' hm
  let hX : ∃ n, n ∈ X := ⟨m', hm.2⟩
  refine ⟨Nat.find hX, ?_, Nat.find_spec hX⟩
  constructor
  · intro y hy
    exact Nat.find_min' hX hy
  · intro y hy
    exact hy _ (Nat.find_spec hX)

/- *** EX *** -/

theorem EX_GLB_nat {X : Set Nat} : X ≠ ∅ → ∃ n, isGLB n X ∧ n ∈ X := by
  intro hX
  rcases Set.nonempty_iff_ne_empty.mpr hX with ⟨m, hm⟩
  exact EX_GLB_nat_lm m m ⟨le_rfl, hm⟩

/- --------------------------*
 |       LUB is least       |
 *-------------------------- -/

theorem LUB_least {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {Y : α}
    (hXY : ∀ x ∈ X, x <= Y) (hX : hasLUB X) : LUB X <= Y :=
  (LUB_is hX).2 Y hXY

/- --------------------------*
 |       GLB is great       |
 *-------------------------- -/

theorem GLB_great {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {Y : α}
    (hXY : ∀ x ∈ X, Y <= x) (hX : hasGLB X) : Y <= GLB X :=
  (GLB_is hX).2 Y hXY

/- --------------------------*
 |       Union isLUB        |
 *-------------------------- -/

theorem Union_isUB {α : Type _} {X : Set (Set α)} : isUB (Set.sUnion X) X := by
  intro Y hY y hy
  exact Set.mem_sUnion.mpr ⟨Y, hY, hy⟩

theorem Union_isLUB {α : Type _} {X : Set (Set α)} : isLUB (Set.sUnion X) X := by
  constructor
  · exact Union_isUB
  · intro Y hY y hy
    rcases Set.mem_sUnion.mp hy with ⟨Z, hZX, hyZ⟩
    exact hY Z hZX hyZ

theorem isLUB_Union_only_if {α : Type _} {x : Set α} {X : Set (Set α)}
    (hx : isLUB x X) : x = Set.sUnion X := by
  exact LUB_unique hx Union_isLUB

theorem isLUB_Union {α : Type _} {x : Set α} {X : Set (Set α)} :
    isLUB x X ↔ x = Set.sUnion X := by
  constructor
  · exact isLUB_Union_only_if
  · intro hx
    simpa [hx] using (Union_isLUB (X := X))

theorem LUB_Union {α : Type _} {X : Set (Set α)} :
    LUB (α := Set α) X = Set.sUnion X :=
  isLUB_LUB (Union_isLUB (X := X))

/-
(*****************************************************
                   MIN and MAX
 *****************************************************)
-/

def isMAX {α : Type _} [LE α] (x : α) (X : Set α) : Prop :=
  isUB x X ∧ x ∈ X

def isMIN {α : Type _} [LE α] (x : α) (X : Set α) : Prop :=
  isLB x X ∧ x ∈ X

def hasMAX {α : Type _} [PartialOrder α] (X : Set α) : Prop :=
  ∃ x, isMAX x X

def hasMIN {α : Type _} [PartialOrder α] (X : Set α) : Prop :=
  ∃ x, isMIN x X

noncomputable def CSPMax {α : Type _} [PartialOrder α] [Inhabited α] (X : Set α) : α :=
  chooseOrDefault (fun x : α => isMAX x X)

noncomputable def CSPMin {α : Type _} [PartialOrder α] [Inhabited α] (X : Set α) : α :=
  chooseOrDefault (fun x : α => isMIN x X)

notation "Max" => CSPMax
notation "Min" => CSPMin

/- *** MAX is unique *** -/

theorem MAX_unique {α : Type _} [PartialOrder α] {x y : α} {X : Set α}
    (hx : isMAX x X) (hy : isMAX y X) : x = y := by
  exact le_antisymm (hy.1 x hx.2) (hx.1 y hy.2)

/- *** MIN is unique *** -/

theorem MIN_unique {α : Type _} [PartialOrder α] {x y : α} {X : Set α}
    (hx : isMIN x X) (hy : isMIN y X) : x = y := by
  exact le_antisymm (hx.1 y hy.2) (hy.1 x hx.2)

/- -----------------------*
 |       the MAX         |
 *----------------------- -/

theorem isMAX_to_MAX {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMAX X) : isMAX x X ↔ x = Max X := by
  constructor
  · intro hx
    exact MAX_unique hx (by
      simpa [CSPMax] using chooseOrDefault_spec (p := fun z : α => isMAX z X) hX)
  · intro hx
    simpa [hx] using (show isMAX (Max X) X from by
      simpa [CSPMax] using chooseOrDefault_spec (p := fun z : α => isMAX z X) hX)

theorem MAX_to_isMAX {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMAX X) : x = Max X ↔ isMAX x X := by
  exact (isMAX_to_MAX (X := X) (x := x) hX).symm

theorem MAX_to_isMAX_sym {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMAX X) : Max X = x ↔ isMAX x X := by
  simpa [eq_comm] using (MAX_to_isMAX (X := X) (x := x) hX)

theorem MAX_iff {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMAX X) : (x = Max X ↔ isMAX x X) ∧ (Max X = x ↔ isMAX x X) :=
  ⟨MAX_to_isMAX hX, MAX_to_isMAX_sym hX⟩

/- -----------------------*
 |       the MIN         |
 *----------------------- -/

theorem isMIN_to_MIN {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMIN X) : isMIN x X ↔ x = Min X := by
  constructor
  · intro hx
    exact MIN_unique hx (by
      simpa [CSPMin] using chooseOrDefault_spec (p := fun z : α => isMIN z X) hX)
  · intro hx
    simpa [hx] using (show isMIN (Min X) X from by
      simpa [CSPMin] using chooseOrDefault_spec (p := fun z : α => isMIN z X) hX)

theorem MIN_to_isMIN {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMIN X) : x = Min X ↔ isMIN x X := by
  exact (isMIN_to_MIN (X := X) (x := x) hX).symm

theorem MIN_to_isMIN_sym {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMIN X) : Min X = x ↔ isMIN x X := by
  simpa [eq_comm] using (MIN_to_isMIN (X := X) (x := x) hX)

theorem MIN_iff {α : Type _} [PartialOrder α] [Inhabited α] {X : Set α} {x : α}
    (hX : hasMIN X) : (x = Min X ↔ isMIN x X) ∧ (Min X = x ↔ isMIN x X) :=
  ⟨MIN_to_isMIN hX, MIN_to_isMIN_sym hX⟩

/- -----------------------*
 |     MAX subset        |
 *----------------------- -/

theorem isMAX_subset {α : Type _} [PartialOrder α] {x y : α} {X Y : Set α}
    (hx : isMAX x X) (hy : isMAX y Y) (hXY : X ⊆ Y) : x <= y :=
  hy.1 x (hXY hx.2)

/- -----------------------*
 |     MIN subset        |
 *----------------------- -/

theorem isMIN_subset {α : Type _} [PartialOrder α] {x y : α} {X Y : Set α}
    (hx : isMIN x X) (hy : isMIN y Y) (hXY : X ⊆ Y) : y <= x :=
  hy.1 x (hXY hx.2)

/- --------------------------*
 |  MIN exists for nat set  |
 *-------------------------- -/

theorem EX_MIN_nat_lm {X : Set Nat} :
    ∀ m m', m' <= m ∧ m' ∈ X → ∃ n, isMIN n X := by
  classical
  intro m m' hm
  let hX : ∃ n, n ∈ X := ⟨m', hm.2⟩
  refine ⟨Nat.find hX, ?_⟩
  constructor
  · intro y hy
    exact Nat.find_min' hX hy
  · exact Nat.find_spec hX

/- *** EX *** -/

theorem EX_MIN_nat {X : Set Nat} : X ≠ ∅ → ∃ n, isMIN n X := by
  intro hX
  rcases Set.nonempty_iff_ne_empty.mpr hX with ⟨m, hm⟩
  exact EX_MIN_nat_lm m m ⟨le_rfl, hm⟩

/-
(*****************************************************
                   Fixed Point
 *****************************************************)
-/

def isUFP {α : Type _} (x : α) (f : α → α) : Prop :=
  x = f x ∧ ∀ y, y = f y → x = y

def isLFP {α : Type _} [PartialOrder α] (x : α) (f : α → α) : Prop :=
  x = f x ∧ ∀ y, y = f y → x <= y

def isGFP {α : Type _} [PartialOrder α] (x : α) (f : α → α) : Prop :=
  x = f x ∧ ∀ y, y = f y → y <= x

def hasUFP {α : Type _} (f : α → α) : Prop :=
  ∃ x, isUFP x f

def hasLFP {α : Type _} [PartialOrder α] (f : α → α) : Prop :=
  ∃ x, isLFP x f

def hasGFP {α : Type _} [PartialOrder α] (f : α → α) : Prop :=
  ∃ x, isGFP x f

noncomputable def UFP {α : Type _} [Inhabited α] (f : α → α) : α :=
  chooseOrDefault (fun x : α => isUFP x f)

noncomputable def LFP {α : Type _} [PartialOrder α] [Inhabited α] (f : α → α) : α :=
  chooseOrDefault (fun x : α => isLFP x f)

noncomputable def GFP {α : Type _} [PartialOrder α] [Inhabited α] (f : α → α) : α :=
  chooseOrDefault (fun x : α => isGFP x f)

/- *******************************
            lemmas
 *******************************) -/

/- *** UFP is unique *** -/

theorem UFP_unique {α : Type _} {x y : α} {f : α → α}
    (hx : isUFP x f) (hy : isUFP y f) : x = y := by
  exact hx.2 y hy.1

/- *** LFP is unique *** -/

theorem LFP_unique {α : Type _} [PartialOrder α] {x y : α} {f : α → α}
    (hx : isLFP x f) (hy : isLFP y f) : x = y := by
  exact le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/- *** GFP is unique *** -/

theorem GFP_unique {α : Type _} [PartialOrder α] {x y : α} {f : α → α}
    (hx : isGFP x f) (hy : isGFP y f) : x = y := by
  exact le_antisymm (hy.2 x hx.1) (hx.2 y hy.1)

/- -----------------------*
 |       the UFP         |
 *----------------------- -/

theorem isUFP_to_UFP {α : Type _} [Inhabited α] {f : α → α} {x : α}
    (hf : hasUFP f) : isUFP x f ↔ x = UFP f := by
  constructor
  · intro hx
    exact by
      have hU : isUFP (UFP f) f := by
        simpa [UFP] using chooseOrDefault_spec (p := fun z : α => isUFP z f) hf
      exact UFP_unique hx hU
  · intro hx
    simpa [hx] using (show isUFP (UFP f) f from by
      simpa [UFP] using chooseOrDefault_spec (p := fun z : α => isUFP z f) hf)

theorem UFP_to_isUFP {α : Type _} [Inhabited α] {f : α → α} {x : α}
    (hf : hasUFP f) : x = UFP f ↔ isUFP x f := by
  exact (isUFP_to_UFP (f := f) (x := x) hf).symm

theorem UFP_to_isUFP_sym {α : Type _} [Inhabited α] {f : α → α} {x : α}
    (hf : hasUFP f) : UFP f = x ↔ isUFP x f := by
  simpa [eq_comm] using (UFP_to_isUFP (f := f) (x := x) hf)

theorem UFP_iff {α : Type _} [Inhabited α] {f : α → α} {x : α}
    (hf : hasUFP f) : (x = UFP f ↔ isUFP x f) ∧ (UFP f = x ↔ isUFP x f) :=
  ⟨UFP_to_isUFP hf, UFP_to_isUFP_sym hf⟩

/- *** UFP is *** -/

theorem UFP_is {α : Type _} [Inhabited α] {f : α → α} (hf : hasUFP f) : isUFP (UFP f) f := by
  simpa [UFP] using chooseOrDefault_spec (p := fun z : α => isUFP z f) hf

theorem isUFP_UFP {α : Type _} [Inhabited α] {f : α → α} {x : α}
    (hx : isUFP x f) : UFP f = x := by
  exact UFP_unique (UFP_is ⟨x, hx⟩) hx

/- *** UFP is fixed point *** -/

theorem UFP_fp_lm {α : Type _} [Inhabited α] {f : α → α} {x : α}
    (hf : hasUFP f) (hx : x = UFP f) : f x = x := by
  subst hx
  exact (UFP_is hf).1.symm

theorem UFP_fp {α : Type _} [Inhabited α] {f : α → α} (hf : hasUFP f) : f (UFP f) = UFP f := by
  exact UFP_fp_lm hf rfl

/- *** unique solution *** -/

theorem hasUFP_unique_solution {α : Type _} {f : α → α} {x y : α}
    (hf : hasUFP f) (hx : f x = x) (hy : f y = y) : x = y := by
  rcases hf with ⟨z, hz⟩
  have hzx : z = x := hz.2 x hx.symm
  have hzy : z = y := hz.2 y hy.symm
  exact hzx.symm.trans hzy

/- -----------------------*
 |       the LFP         |
 *----------------------- -/

theorem isLFP_to_LFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasLFP f) : isLFP x f ↔ x = LFP f := by
  constructor
  · intro hx
    exact LFP_unique hx (by
      simpa [LFP] using chooseOrDefault_spec (p := fun z : α => isLFP z f) hf)
  · intro hx
    simpa [hx] using (show isLFP (LFP f) f from by
      simpa [LFP] using chooseOrDefault_spec (p := fun z : α => isLFP z f) hf)

theorem LFP_to_isLFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasLFP f) : x = LFP f ↔ isLFP x f := by
  exact (isLFP_to_LFP (f := f) (x := x) hf).symm

theorem LFP_to_isLFP_sym {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasLFP f) : LFP f = x ↔ isLFP x f := by
  simpa [eq_comm] using (LFP_to_isLFP (f := f) (x := x) hf)

theorem LFP_iff {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasLFP f) : (x = LFP f ↔ isLFP x f) ∧ (LFP f = x ↔ isLFP x f) :=
  ⟨LFP_to_isLFP hf, LFP_to_isLFP_sym hf⟩

/- *** LFP is *** -/

theorem LFP_is {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α}
    (hf : hasLFP f) : isLFP (LFP f) f := by
  simpa [LFP] using chooseOrDefault_spec (p := fun z : α => isLFP z f) hf

theorem isLFP_LFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hx : isLFP x f) : LFP f = x := by
  exact LFP_unique (LFP_is ⟨x, hx⟩) hx

/- *** LFP is fixed point *** -/

theorem LFP_fp_lm {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasLFP f) (hx : x = LFP f) : f x = x := by
  subst hx
  exact (LFP_is hf).1.symm

theorem LFP_fp {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α}
    (hf : hasLFP f) : f (LFP f) = LFP f := by
  exact LFP_fp_lm hf rfl

/- *** LFP is least *** -/

theorem LFP_least {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasLFP f) (hx : f x = x) : LFP f <= x :=
  (LFP_is hf).2 x hx.symm

/- -----------------------*
 |       the GFP         |
 *----------------------- -/

theorem isGFP_to_GFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasGFP f) : isGFP x f ↔ x = GFP f := by
  constructor
  · intro hx
    exact GFP_unique hx (by
      simpa [GFP] using chooseOrDefault_spec (p := fun z : α => isGFP z f) hf)
  · intro hx
    simpa [hx] using (show isGFP (GFP f) f from by
      simpa [GFP] using chooseOrDefault_spec (p := fun z : α => isGFP z f) hf)

theorem GFP_to_isGFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasGFP f) : x = GFP f ↔ isGFP x f := by
  exact (isGFP_to_GFP (f := f) (x := x) hf).symm

theorem GFP_to_isGFP_sym {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasGFP f) : GFP f = x ↔ isGFP x f := by
  simpa [eq_comm] using (GFP_to_isGFP (f := f) (x := x) hf)

theorem GFP_iff {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasGFP f) : (x = GFP f ↔ isGFP x f) ∧ (GFP f = x ↔ isGFP x f) :=
  ⟨GFP_to_isGFP hf, GFP_to_isGFP_sym hf⟩

/- *** GFP is *** -/

theorem GFP_is {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α}
    (hf : hasGFP f) : isGFP (GFP f) f := by
  simpa [GFP] using chooseOrDefault_spec (p := fun z : α => isGFP z f) hf

theorem isGFP_GFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hx : isGFP x f) : GFP f = x := by
  exact GFP_unique (GFP_is ⟨x, hx⟩) hx

/- *** GFP is fixed point *** -/

theorem GFP_fp_lm {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasGFP f) (hx : x = GFP f) : f x = x := by
  subst hx
  exact (GFP_is hf).1.symm

theorem GFP_fp {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α}
    (hf : hasGFP f) : f (GFP f) = GFP f := by
  exact GFP_fp_lm hf rfl

/- *** GFP is greatest *** -/

theorem GFP_greatest {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} {x : α}
    (hf : hasGFP f) (hx : f x = x) : x <= GFP f :=
  (GFP_is hf).2 x hx.symm

/- -----------------------*
 |     UFP --> LFP       |
 *----------------------- -/

theorem hasUFP_hasLFP {α : Type _} [PartialOrder α] {f : α → α} :
    hasUFP f → hasLFP f := by
  rintro ⟨x, hx⟩
  refine ⟨x, hx.1, ?_⟩
  intro y hy
  simp [hx.2 y hy]

theorem hasUFP_LFP_UFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} :
    hasUFP f → LFP f = UFP f := by
  intro hf
  refine isLFP_LFP ?_
  rcases UFP_is hf with ⟨hfp, huniq⟩
  refine ⟨hfp, ?_⟩
  intro y hy
  simp [huniq y hy]

/- -----------------------*
 |     UFP --> GFP       |
 *----------------------- -/

theorem hasUFP_hasGFP {α : Type _} [PartialOrder α] {f : α → α} :
    hasUFP f → hasGFP f := by
  rintro ⟨x, hx⟩
  refine ⟨x, hx.1, ?_⟩
  intro y hy
  simp [hx.2 y hy]

theorem hasUFP_GFP_UFP {α : Type _} [PartialOrder α] [Inhabited α] {f : α → α} :
    hasUFP f → GFP f = UFP f := by
  intro hf
  refine isGFP_GFP ?_
  rcases UFP_is hf with ⟨hfp, huniq⟩
  refine ⟨hfp, ?_⟩
  intro y hy
  simp [huniq y hy]
