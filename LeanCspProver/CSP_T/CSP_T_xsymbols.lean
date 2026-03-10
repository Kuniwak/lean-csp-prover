           /- -------------------------------------------*
            |        X symbols for CSP-Prover           |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_T.Domain_T
import LeanCspProver.CSP_T.CSP_T_semantics

noncomputable section

/- ------------------------------------*
 |                                    |
 |             Domain_T               |
 |                                    |
 *------------------------------------ -/

syntax:50 term:50 " ∈t " term:51 : term
syntax "⋃t " term:90 : term
syntax "⋂t " term:90 : term

syntax:50 term:50 " ∉t " term:51 : term
syntax:65 term:65 " ∪t " term:66 : term
syntax:70 term:70 " ∩t " term:71 : term

macro_rules
  | `($x ∈t $T) => `(memT $x $T)
  | `(⋃t $Ts) => `(UnionT $Ts)
  | `(⋂t $Ts) => `(InterT $Ts)
  | `($x ∉t $T) => `(¬ memT $x $T)
  | `($T ∪t $S) => `(_root_.UnT $T $S)
  | `($T ∩t $S) => `(_root_.IntT $T $S)

/- ------------------------------------*
 |                                    |
 |           CSP_T_semantics          |
 |                                    |
 *------------------------------------ -/

syntax "⟦" term "⟧Tf" : term
syntax "⟦" term "⟧Tfun" : term

syntax "⟦" term "⟧Tfix" : term
syntax "⟦" term "⟧T" : term

syntax:50 term:51 " ⊑T[" term "," term "] " term:50 : term
syntax:50 term:51 " ⊑T " term:50 : term

macro_rules
  | `(⟦$p⟧Tf) => `(semTf $p)
  | `(⟦$p⟧Tfun) => `(semTfun $p)
  | `(⟦$p⟧Tfix) => `(semTfix $p)
  | `(⟦$p⟧T) => `(semT $p)
  | `($p ⊑T[$m1,$m2] $q) => `(refT $p $m1 $m2 $q)
  | `($p ⊑T $q) => `(refTfix $p $q)
