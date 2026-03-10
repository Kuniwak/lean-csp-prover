           /- -------------------------------------------*
            |        X symbols for CSP-Prover           |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.Set_F
import LeanCspProver.CSP_F.CSP_F_semantics

noncomputable section

/- ------------------------------------*
 |                                    |
 |               Set_F                |
 |                                    |
 *------------------------------------ -/

syntax:50 term:50 " ∈f " term:51 : term
syntax "⋃f " term:90 : term
syntax "⋂f " term:90 : term

syntax:50 term:50 " ∉f " term:51 : term
syntax:65 term:65 " ∪f " term:66 : term
syntax:70 term:70 " ∩f " term:71 : term

macro_rules
  | `($x ∈f $f) => `(memF $x $f)
  | `(⋃f $f) => `(UnionF $f)
  | `(⋂f $f) => `(InterF $f)
  | `($x ∉f $f) => `(¬ memF $x $f)
  | `($f ∪f $e) => `(_root_.UnF $f $e)
  | `($f ∩f $e) => `(_root_.IntF $f $e)

/- ------------------------------------*
 |                                    |
 |        CSP_F_semantics             |
 |                                    |
 *------------------------------------ -/

syntax "⟦" term "⟧Ff" : term
syntax "⟦" term "⟧Ffun" : term

syntax "⟦" term "⟧Ffix" : term
syntax "⟦" term "⟧F" : term

syntax:50 term:51 " ⊑F[" term "," term "] " term:50 : term
syntax:50 term:51 " ⊑F " term:50 : term

macro_rules
  | `(⟦$p⟧Ff) => `(semFf $p)
  | `(⟦$p⟧Ffun) => `(semFfun $p)
  | `(⟦$p⟧Ffix) => `(semFfix $p)
  | `(⟦$p⟧F) => `(semF $p)
  | `($p ⊑F[$m1,$m2] $q) => `(refF $p $m1 $m2 $q)
  | `($p ⊑F $q) => `(refFfix $p $q)
