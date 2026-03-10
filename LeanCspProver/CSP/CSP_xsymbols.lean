           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2008         |
            |                   June 2008  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Infra_type
import LeanCspProver.CSP.CSP_syntax
import LeanCspProver.CSP.Trace
import LeanCspProver.CSP.RS

noncomputable section

/- ------------------------------------*
 |                                    |
 |              X-Symbols             |
 |                                    |
 *------------------------------------ -/

/- ------------------------------------*
 |                                    |
 |             Infra_type             |
 |                                    |
 *------------------------------------ -/

abbrev sum_cup_mix := @sum_cup
abbrev sum_cap_mix := @sum_cap

infixl:65 " ∪s " => sum_cup_mix
infixl:70 " ∩s " => sum_cap_mix

/- ------------------------------------*
 |                                    |
 |                Trace               |
 |                                    |
 *------------------------------------ -/

notation "⟨⟩" => nilt
infixr:65 " ⌢ " => appt

/- Lean note:
   Isabelle's xsymbol trace syntax `⟨...⟩` is represented by a macro over
   `Abs_trace`. The empty trace remains the dedicated notation `⟨⟩`. -/
syntax "⟨" term,* "⟩" : term

macro_rules (kind := «term⟨_⟩»)
  | `(⟨$xs,*⟩) => `(Abs_trace [$xs,*])

notation "√" => event.Tick

/- ------------------------------------*
 |                                    |
 |                  RS                |
 |                                    |
 *------------------------------------ -/

infixl:84 " ↓ " => restriction

/- ------------------------------------*
 |                                    |
 |             CSP_syntax             |
 |                                    |
 *------------------------------------ -/

/- Lean note:
   Isabelle's xsymbol forms that overload the reserved token `→` keep their
   existing Lean encodings (`~>`, `Int_pre_choice`, `Send_prefix`,
   `Nondet_send_prefix`, and `Rec_prefix`). Non-conflicting xsymbol operators
   are introduced below. -/

infixl:72 " □ " => proc.Ext_choice
infixl:64 " ⊓ " => proc.Int_choice
notation:73 P " ⊳ " Q => P [> Q
notation:73 P " ⊵ " Q => Timeout P Q
notation:84 P " ─ " X => proc.Hiding P X
notation:84 P " ⟦" r "⟧" => proc.Renaming P r
notation:84 P " ⌊ " n => proc.Depth_rest P n
