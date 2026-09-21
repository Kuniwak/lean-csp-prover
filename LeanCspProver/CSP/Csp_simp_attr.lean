           /- -------------------------------------------*
            |        lean-csp-prover                    |
            |   simp sets for the semantic unfolding    |
            |   of CSP processes (traces / failures)    |
            *------------------------------------------- -/

import Mathlib.Tactic

/-- Simp set that rewrites `t :t traces P M` into a formula over the
    traces of the immediate subprocesses (`in_traces_*`), together with the
    small logical helpers needed to normalise the result. -/
register_simp_attr csp_T

/-- Simp set that rewrites `(s, X) :f failures P M` into a formula over the
    failures / traces of the immediate subprocesses (`in_failures_*`). -/
register_simp_attr csp_F
