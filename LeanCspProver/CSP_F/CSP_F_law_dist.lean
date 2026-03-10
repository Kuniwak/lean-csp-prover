           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |               December 2004               |
            |                   July 2005  (modified)   |
            |              September 2005  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2005         |
            |                October 2005  (modified)   |
            |                  April 2006  (modified)   |
            |                  March 2007  (modified)   |
            |                 August 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_basic
import LeanCspProver.CSP_F.CSP_F_law_decompo
import LeanCspProver.CSP_T.CSP_T_law_dist
import LeanCspProver.CSP_F.CSP_F_law_alpha_par

open Function
open SumType

noncomputable section

/-
(*****************************************************************

      distribution over internal choice

         1. (P1 |~| P2) [+] Q
         2. Q [+] (P1 |~| P2)
         3. (P1 |~| P2) |[X]| Q
         4. Q |[X]| (P1 |~| P2)
         5. (P1 |~| P2) -- X
         6. (P1 |~| P2) [[r]]
         7. (P1 |~| P2) ;; Q
         8. (P1 |~| P2) |. n
         9. !! x:X .. (P1 |~| P2)

 *****************************************************************)
-/

axiom cspF_Ext_choice_dist_l {P1 P2 Q : proc p α} {M : p → domFType α} :
    eqF ((P1 |~| P2) [+] Q) M M ((P1 [+] Q) |~| (P2 [+] Q))

axiom cspF_Ext_choice_dist_r {P Q1 Q2 : proc p α} {M : p → domFType α} :
    eqF (P [+] (Q1 |~| Q2)) M M ((P [+] Q1) |~| (P [+] Q2))

axiom cspF_Parallel_dist_l {P1 P2 Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF ((P1 |~| P2) |[X]| Q) M M ((P1 |[X]| Q) |~| (P2 |[X]| Q))

axiom cspF_Parallel_dist_r {P Q1 Q2 : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| (Q1 |~| Q2)) M M ((P |[X]| Q1) |~| (P |[X]| Q2))

axiom cspF_Hiding_dist {P1 P2 : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (P1 |~| P2) X) M M ((proc.Hiding P1 X) |~| (proc.Hiding P2 X))

axiom cspF_Renaming_dist {P1 P2 : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((P1 |~| P2)[[r]]) M M ((P1[[r]]) |~| (P2[[r]]))

axiom cspF_Seq_compo_dist {P1 P2 Q : proc p α} {M : p → domFType α} :
    eqF ((P1 |~| P2) ;; Q) M M ((P1 ;; Q) |~| (P2 ;; Q))

axiom cspF_Depth_rest_dist {P1 P2 : proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((P1 |~| P2) |. n) M M ((P1 |. n) |~| (P2 |. n))

axiom cspF_Rep_int_choice_sum_dist
    {C : sets_nats α} {Pf Qf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C (fun c => Pf c |~| Qf c)) M M
      ((proc.Rep_int_choice C Pf) |~| (proc.Rep_int_choice C Qf))

axiom cspF_Rep_int_choice_nat_dist
    {N : Set Nat} {Pf Qf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N (fun n => Pf n |~| Qf n)) M M
      ((Rep_int_choice_nat N Pf) |~| (Rep_int_choice_nat N Qf))

axiom cspF_Rep_int_choice_set_dist
    {Xs : Set (Set α)} {Pf Qf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs (fun X => Pf X |~| Qf X)) M M
      ((Rep_int_choice_set Xs Pf) |~| (Rep_int_choice_set Xs Qf))

axiom cspF_Rep_int_choice_com_dist [Inhabited α]
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X (fun a => Pf a |~| Qf a)) M M
      ((Rep_int_choice_com X Pf) |~| (Rep_int_choice_com X Qf))

axiom cspF_Rep_int_choice_f_dist [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf Qf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f X (fun a => Pf a |~| Qf a)) M M
      ((Rep_int_choice_f f X Pf) |~| (Rep_int_choice_f f X Qf))

/- The Isabelle theorem bundle `cspF_Rep_int_choice_dist` is represented by
   `cspF_Rep_int_choice_sum_dist`, `cspF_Rep_int_choice_nat_dist`,
   `cspF_Rep_int_choice_set_dist`, `cspF_Rep_int_choice_com_dist`, and
   `cspF_Rep_int_choice_f_dist`. -/

/- The Isabelle theorem bundle `cspF_dist` is represented by
   `cspF_Ext_choice_dist_l`, `cspF_Ext_choice_dist_r`,
   `cspF_Parallel_dist_l`, `cspF_Parallel_dist_r`, `cspF_Hiding_dist`,
   `cspF_Renaming_dist`, `cspF_Seq_compo_dist`, `cspF_Depth_rest_dist`,
   and `cspF_Rep_int_choice_dist`. -/

/-
(*****************************************************************

      distribution over replicated internal choice

         1. (!! :C .. Pf) [+] Q
         2. Q [+] (!! :C .. Pf)
         3. (!! :C .. Pf) |[X]| Q
         4. Q |[X]| (!! :C .. Pf)
         5. (!! :C .. Pf) -- X
         6. (!! :C .. Pf) [[r]]
         7. (!! :C .. Pf) |. n

 *****************************************************************)
-/

axiom cspF_Ext_choice_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF ((proc.Rep_int_choice C Pf) [+] Q) M M
        (proc.Rep_int_choice C fun c => Pf c [+] Q)

axiom cspF_Ext_choice_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf) [+] Q) M M
      (procIte (sumset C = ∅) ((proc.DIV : proc p α) [+] Q)
        (proc.Rep_int_choice C fun c => Pf c [+] Q))

axiom cspF_Ext_choice_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (P [+] proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P [+] Qf c)

axiom cspF_Ext_choice_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P [+] (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P [+] Qf c))

axiom cspF_Parallel_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (proc.Rep_int_choice C Pf |[X]| Q) M M
        (proc.Rep_int_choice C fun c => Pf c |[X]| Q)

axiom cspF_Parallel_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C Pf |[X]| Q) M M
      (procIte (sumset C = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (proc.Rep_int_choice C fun c => Pf c |[X]| Q))

axiom cspF_Parallel_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (P |[X]| proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P |[X]| Qf c)

axiom cspF_Parallel_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P |[X]| (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P |[X]| Qf c))

axiom cspF_Hiding_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (proc.Rep_int_choice C Pf) X) M M
      (proc.Rep_int_choice C fun c => proc.Hiding (Pf c) X)

axiom cspF_Renaming_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf)[[r]]) M M
      (proc.Rep_int_choice C fun c => (Pf c)[[r]])

axiom cspF_Seq_compo_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf) ;; Q) M M
      (proc.Rep_int_choice C fun c => Pf c ;; Q)

axiom cspF_Depth_rest_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {m : Nat} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf) |. m) M M
      (proc.Rep_int_choice C fun c => Pf c |. m)

/- The Isabelle theorem bundle `cspF_Dist_sum` is represented by
   `cspF_Ext_choice_Dist_sum_l`, `cspF_Ext_choice_Dist_sum_r`,
   `cspF_Parallel_Dist_sum_l`, `cspF_Parallel_Dist_sum_r`,
   `cspF_Hiding_Dist_sum`, `cspF_Renaming_Dist_sum`,
   `cspF_Seq_compo_Dist_sum`, and `cspF_Depth_rest_Dist_sum`. -/

/- The Isabelle theorem bundle `cspF_Dist_sum_nonempty` is represented by
   `cspF_Ext_choice_Dist_sum_l_nonempty`,
   `cspF_Ext_choice_Dist_sum_r_nonempty`,
   `cspF_Parallel_Dist_sum_l_nonempty`,
   `cspF_Parallel_Dist_sum_r_nonempty`, `cspF_Hiding_Dist_sum`,
   `cspF_Renaming_Dist_sum`, `cspF_Seq_compo_Dist_sum`, and
   `cspF_Depth_rest_Dist_sum`. -/

/-
(*****************************************************************

      distribution over replicated internal choice

         1. (!nat :C .. Pf) [+] Q
         2. Q [+] (!nat :C .. Pf)
         3. (!nat :C .. Pf) |[X]| Q
         4. Q |[X]| (!nat :C .. Pf)
         5. (!nat :C .. Pf) -- X
         6. (!nat :C .. Pf) [[r]]
         7. (!nat :C .. Pf) |. n

 *****************************************************************)
-/

axiom cspF_Ext_choice_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domFType α} :
    N ≠ ∅ → eqF ((Rep_int_choice_nat N Pf) [+] Q) M M
      (Rep_int_choice_nat N fun n => Pf n [+] Q)

axiom cspF_Ext_choice_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf) [+] Q) M M
      (procIte (N = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_nat N fun n => Pf n [+] Q))

axiom cspF_Ext_choice_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {M : p → domFType α} :
    N ≠ ∅ → eqF (P [+] Rep_int_choice_nat N Qf) M M
      (Rep_int_choice_nat N fun n => P [+] Qf n)

axiom cspF_Ext_choice_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P [+] Qf n))

axiom cspF_Parallel_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    N ≠ ∅ → eqF (Rep_int_choice_nat N Pf |[X]| Q) M M
      (Rep_int_choice_nat N fun n => Pf n |[X]| Q)

axiom cspF_Parallel_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N Pf |[X]| Q) M M
      (procIte (N = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_nat N fun n => Pf n |[X]| Q))

axiom cspF_Parallel_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    N ≠ ∅ → eqF (P |[X]| Rep_int_choice_nat N Qf) M M
      (Rep_int_choice_nat N fun n => P |[X]| Qf n)

axiom cspF_Parallel_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P |[X]| Qf n))

axiom cspF_Hiding_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_nat N Pf) X) M M
      (Rep_int_choice_nat N fun n => proc.Hiding (Pf n) X)

axiom cspF_Renaming_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf)[[r]]) M M
      (Rep_int_choice_nat N fun n => (Pf n)[[r]])

axiom cspF_Seq_compo_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf) ;; Q) M M
      (Rep_int_choice_nat N fun n => Pf n ;; Q)

axiom cspF_Depth_rest_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {m : Nat} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf) |. m) M M
      (Rep_int_choice_nat N fun n => Pf n |. m)

/- The Isabelle theorem bundle `cspF_Dist_nat` is represented by
   `cspF_Ext_choice_Dist_nat_l`, `cspF_Ext_choice_Dist_nat_r`,
   `cspF_Parallel_Dist_nat_l`, `cspF_Parallel_Dist_nat_r`,
   `cspF_Hiding_Dist_nat`, `cspF_Renaming_Dist_nat`,
   `cspF_Seq_compo_Dist_nat`, and `cspF_Depth_rest_Dist_nat`. -/

/- The Isabelle theorem bundle `cspF_Dist_nat_nonempty` is represented by
   `cspF_Ext_choice_Dist_nat_l_nonempty`,
   `cspF_Ext_choice_Dist_nat_r_nonempty`,
   `cspF_Parallel_Dist_nat_l_nonempty`,
   `cspF_Parallel_Dist_nat_r_nonempty`, `cspF_Hiding_Dist_nat`,
   `cspF_Renaming_Dist_nat`, `cspF_Seq_compo_Dist_nat`, and
   `cspF_Depth_rest_Dist_nat`. -/

/-
(*****************************************************************

      distribution over replicated internal choice

         1. (!set :C .. Pf) [+] Q
         2. Q [+] (!set :C .. Pf)
         3. (!set :C .. Pf) |[X]| Q
         4. Q |[X]| (!set :C .. Pf)
         5. (!set :C .. Pf) -- X
         6. (!set :C .. Pf) [[r]]
         7. (!set :C .. Pf) |. n

 *****************************************************************)
-/

axiom cspF_Ext_choice_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF ((Rep_int_choice_set Xs Pf) [+] Q) M M
      (Rep_int_choice_set Xs fun X => Pf X [+] Q)

axiom cspF_Ext_choice_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf) [+] Q) M M
      (procIte (Xs = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_set Xs fun X => Pf X [+] Q))

axiom cspF_Ext_choice_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (P [+] Rep_int_choice_set Xs Qf) M M
      (Rep_int_choice_set Xs fun X => P [+] Qf X)

axiom cspF_Ext_choice_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P [+] Qf X))

axiom cspF_Parallel_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {Y : Set α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (Rep_int_choice_set Xs Pf |[Y]| Q) M M
      (Rep_int_choice_set Xs fun X => Pf X |[Y]| Q)

axiom cspF_Parallel_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs Pf |[Y]| Q) M M
      (procIte (Xs = ∅) (((proc.DIV : proc p α) |[Y]| Q))
        (Rep_int_choice_set Xs fun X => Pf X |[Y]| Q))

axiom cspF_Parallel_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {Y : Set α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (P |[Y]| Rep_int_choice_set Xs Qf) M M
      (Rep_int_choice_set Xs fun X => P |[Y]| Qf X)

axiom cspF_Parallel_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {Y : Set α} {M : p → domFType α} :
    eqF (P |[Y]| Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P |[Y]| (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P |[Y]| Qf X))

axiom cspF_Hiding_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Y : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_set Xs Pf) Y) M M
      (Rep_int_choice_set Xs fun X => proc.Hiding (Pf X) Y)

axiom cspF_Renaming_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf)[[r]]) M M
      (Rep_int_choice_set Xs fun X => (Pf X)[[r]])

axiom cspF_Seq_compo_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf) ;; Q) M M
      (Rep_int_choice_set Xs fun X => Pf X ;; Q)

axiom cspF_Depth_rest_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {m : Nat} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf) |. m) M M
      (Rep_int_choice_set Xs fun X => Pf X |. m)

/- The Isabelle theorem bundle `cspF_Dist_set` is represented by
   `cspF_Ext_choice_Dist_set_l`, `cspF_Ext_choice_Dist_set_r`,
   `cspF_Parallel_Dist_set_l`, `cspF_Parallel_Dist_set_r`,
   `cspF_Hiding_Dist_set`, `cspF_Renaming_Dist_set`,
   `cspF_Seq_compo_Dist_set`, and `cspF_Depth_rest_Dist_set`. -/

/- The Isabelle theorem bundle `cspF_Dist_set_nonempty` is represented by
   `cspF_Ext_choice_Dist_set_l_nonempty`,
   `cspF_Ext_choice_Dist_set_r_nonempty`,
   `cspF_Parallel_Dist_set_l_nonempty`,
   `cspF_Parallel_Dist_set_r_nonempty`, `cspF_Hiding_Dist_set`,
   `cspF_Renaming_Dist_set`, `cspF_Seq_compo_Dist_set`, and
   `cspF_Depth_rest_Dist_set`. -/

/-
(*****************************************************************

      for convenience

         1. (! :X .. Pf) [+] Q
         2. Q [+] (! :X .. Pf)
         3. (! :X .. Pf) |[X]| Q
         4. Q |[X]| (! :X .. Pf)
         5. (! :X .. Pf) -- X
         6. (! :X .. Pf) [[r]]
         7. (! :X .. Pf) |. n

 *****************************************************************)
-/

axiom cspF_Ext_choice_Dist_com_l_nonempty [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF ((Rep_int_choice_com X Pf) [+] Q) M M
      (Rep_int_choice_com X fun x => Pf x [+] Q)

axiom cspF_Ext_choice_Dist_com_r_nonempty [Inhabited α]
    {X : Set α} {Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF (P [+] Rep_int_choice_com X Qf) M M
      (Rep_int_choice_com X fun x => P [+] Qf x)

axiom cspF_Parallel_Dist_com_l_nonempty [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (Rep_int_choice_com Y Pf |[X]| Q) M M
      (Rep_int_choice_com Y fun x => Pf x |[X]| Q)

axiom cspF_Parallel_Dist_com_r_nonempty [Inhabited α]
    {Y : Set α} {Qf : α → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (P |[X]| Rep_int_choice_com Y Qf) M M
      (Rep_int_choice_com Y fun x => P |[X]| Qf x)

axiom cspF_Ext_choice_Dist_com_l [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf) [+] Q) M M
      (procIte (X = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_com X fun x => Pf x [+] Q))

axiom cspF_Ext_choice_Dist_com_r [Inhabited α]
    {X : Set α} {Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_com X Qf) M M
      (procIte (X = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_com X fun x => P [+] Qf x))

axiom cspF_Parallel_Dist_com_l [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_com Y Pf |[X]| Q) M M
      (procIte (Y = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_com Y fun x => Pf x |[X]| Q))

axiom cspF_Parallel_Dist_com_r [Inhabited α]
    {Y : Set α} {Qf : α → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Rep_int_choice_com Y Qf) M M
      (procIte (Y = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_com Y fun x => P |[X]| Qf x))

axiom cspF_Hiding_Dist_com [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_com Y Pf) X) M M
      (Rep_int_choice_com Y fun x => proc.Hiding (Pf x) X)

axiom cspF_Renaming_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf)[[r]]) M M
      (Rep_int_choice_com X fun x => (Pf x)[[r]])

axiom cspF_Seq_compo_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf) ;; Q) M M
      (Rep_int_choice_com X fun x => Pf x ;; Q)

axiom cspF_Depth_rest_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf) |. n) M M
      (Rep_int_choice_com X fun x => Pf x |. n)

/- The Isabelle theorem bundle `cspF_Dist_com` is represented by
   `cspF_Ext_choice_Dist_com_l`, `cspF_Ext_choice_Dist_com_r`,
   `cspF_Parallel_Dist_com_l`, `cspF_Parallel_Dist_com_r`,
   `cspF_Hiding_Dist_com`, `cspF_Renaming_Dist_com`,
   `cspF_Seq_compo_Dist_com`, and `cspF_Depth_rest_Dist_com`. -/

/- The Isabelle theorem bundle `cspF_Dist_com_nonempty` is represented by
   `cspF_Ext_choice_Dist_com_l_nonempty`,
   `cspF_Ext_choice_Dist_com_r_nonempty`,
   `cspF_Parallel_Dist_com_l_nonempty`,
   `cspF_Parallel_Dist_com_r_nonempty`, `cspF_Hiding_Dist_com`,
   `cspF_Renaming_Dist_com`, `cspF_Seq_compo_Dist_com`, and
   `cspF_Depth_rest_Dist_com`. -/

/-
(*****************************************************************

      for convenience

         1. (!<f> :X .. Pf) [+] Q
         2. Q [+] (!<f> :X .. Pf)
         3. (!<f> :X .. Pf) |[X]| Q
         4. Q |[X]| (!<f> :X .. Pf)
         5. (!<f> :X .. Pf) -- X
         6. (!<f> :X .. Pf) [[r]]
         7. (!<f> :X .. Pf) |. n

 *****************************************************************)
-/

axiom cspF_Ext_choice_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domFType α} :
    X ≠ ∅ → eqF ((Rep_int_choice_f f X Pf) [+] Q) M M
      (Rep_int_choice_f f X fun x => Pf x [+] Q)

axiom cspF_Ext_choice_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Qf : β → proc p α} {P : proc p α}
    {M : p → domFType α} :
    X ≠ ∅ → eqF (P [+] Rep_int_choice_f f X Qf) M M
      (Rep_int_choice_f f X fun x => P [+] Qf x)

axiom cspF_Parallel_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (Rep_int_choice_f f Y Pf |[X]| Q) M M
      (Rep_int_choice_f f Y fun x => Pf x |[X]| Q)

axiom cspF_Parallel_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Qf : β → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (P |[X]| Rep_int_choice_f f Y Qf) M M
      (Rep_int_choice_f f Y fun x => P |[X]| Qf x)

axiom cspF_Ext_choice_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf) [+] Q) M M
      (procIte (X = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_f f X fun x => Pf x [+] Q))

axiom cspF_Ext_choice_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Qf : β → proc p α} {P : proc p α}
    {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_f f X Qf) M M
      (procIte (X = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_f f X fun x => P [+] Qf x))

axiom cspF_Parallel_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f Y Pf |[X]| Q) M M
      (procIte (Y = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_f f Y fun x => Pf x |[X]| Q))

axiom cspF_Parallel_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Qf : β → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Rep_int_choice_f f Y Qf) M M
      (procIte (Y = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_f f Y fun x => P |[X]| Qf x))

axiom cspF_Hiding_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {X : Set α}
    {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_f f Y Pf) X) M M
      (Rep_int_choice_f f Y fun x => proc.Hiding (Pf x) X)

axiom cspF_Renaming_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {r : Set (α × α)}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf)[[r]]) M M
      (Rep_int_choice_f f X fun x => (Pf x)[[r]])

axiom cspF_Seq_compo_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf) ;; Q) M M
      (Rep_int_choice_f f X fun x => Pf x ;; Q)

axiom cspF_Depth_rest_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {n : Nat}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf) |. n) M M
      (Rep_int_choice_f f X fun x => Pf x |. n)

/- The Isabelle theorem bundle `cspF_Dist_f` is represented by
   `cspF_Ext_choice_Dist_f_l`, `cspF_Ext_choice_Dist_f_r`,
   `cspF_Parallel_Dist_f_l`, `cspF_Parallel_Dist_f_r`,
   `cspF_Hiding_Dist_f`, `cspF_Renaming_Dist_f`,
   `cspF_Seq_compo_Dist_f`, and `cspF_Depth_rest_Dist_f`. -/

/- The Isabelle theorem bundle `cspF_Dist_f_nonempty` is represented by
   `cspF_Ext_choice_Dist_f_l_nonempty`,
   `cspF_Ext_choice_Dist_f_r_nonempty`,
   `cspF_Parallel_Dist_f_l_nonempty`,
   `cspF_Parallel_Dist_f_r_nonempty`, `cspF_Hiding_Dist_f`,
   `cspF_Renaming_Dist_f`, `cspF_Seq_compo_Dist_f`, and
   `cspF_Depth_rest_Dist_f`. -/

/- The Isabelle theorem bundle `cspF_Dist` is represented by
   `cspF_Dist_sum`, `cspF_Dist_nat`, `cspF_Dist_set`, `cspF_Dist_com`,
   and `cspF_Dist_f`. -/

/- The Isabelle theorem bundle `cspF_Dist_nonempty` is represented by
   `cspF_Dist_sum_nonempty`, `cspF_Dist_nat_nonempty`,
   `cspF_Dist_set_nonempty`, `cspF_Dist_com_nonempty`, and
   `cspF_Dist_f_nonempty`. -/

/-
(*****************************************************************

      additional distribution over replicated internal choice

         1. (!! :X .. (a -> P))
         2. (!! :Y .. (? :X -> P))

 *****************************************************************)
-/

axiom cspF_Act_prefix_Dist_sum
    {C : sets_nats α} {a : α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (a ~> proc.Rep_int_choice C Pf) M M
        (proc.Rep_int_choice C fun c => a ~> Pf c)

axiom cspF_Ext_pre_choice_Dist_sum
    {C : sets_nats α} {X : Set α} {Pf : aset_anat α → α → proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => proc.Rep_int_choice C fun c => Pf c x) M M
        (proc.Rep_int_choice C fun c => proc.Ext_pre_choice X (Pf c))

axiom cspF_Act_prefix_Dist_nat
    {N : Set Nat} {a : α} {Pf : Nat → proc p α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (a ~> Rep_int_choice_nat N Pf) M M
        (Rep_int_choice_nat N fun n => a ~> Pf n)

axiom cspF_Ext_pre_choice_Dist_nat
    {N : Set Nat} {X : Set α} {Pf : Nat → α → proc p α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_nat N fun n => Pf n x) M M
        (Rep_int_choice_nat N fun n => proc.Ext_pre_choice X (Pf n))

axiom cspF_Act_prefix_Dist_set
    {Xs : Set (Set α)} {a : α} {Pf : Set α → proc p α} {M : p → domFType α} :
    Xs ≠ ∅ →
      eqF (a ~> Rep_int_choice_set Xs Pf) M M
        (Rep_int_choice_set Xs fun X => a ~> Pf X)

axiom cspF_Ext_pre_choice_Dist_set
    {X : Set α} {Ys : Set (Set α)} {Pf : Set α → α → proc p α} {M : p → domFType α} :
    Ys ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_set Ys fun Y => Pf Y x) M M
        (Rep_int_choice_set Ys fun Y => proc.Ext_pre_choice X (Pf Y))

axiom cspF_Act_prefix_Dist_com [Inhabited α]
    {X : Set α} {a : α} {Pf : α → proc p α} {M : p → domFType α} :
    X ≠ ∅ →
      eqF (a ~> Rep_int_choice_com X Pf) M M
        (Rep_int_choice_com X fun x => a ~> Pf x)

axiom cspF_Ext_pre_choice_Dist_com [Inhabited α]
    {X Y : Set α} {Pf : α → α → proc p α} {M : p → domFType α} :
    Y ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_com Y fun y => Pf y x) M M
        (Rep_int_choice_com Y fun y => proc.Ext_pre_choice X (Pf y))

axiom cspF_Act_prefix_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {a : α} {Pf : β → proc p α}
    {M : p → domFType α} :
    X ≠ ∅ →
      eqF (a ~> Rep_int_choice_f f X Pf) M M
        (Rep_int_choice_f f X fun x => a ~> Pf x)

axiom cspF_Ext_pre_choice_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set α} {Y : Set β} {Pf : β → α → proc p α}
    {M : p → domFType α} :
    Y ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_f f Y fun y => Pf y x) M M
        (Rep_int_choice_f f Y fun y => proc.Ext_pre_choice X (Pf y))

/- The Isabelle theorem bundle `cspF_Act_prefix_Dist` is represented by
   `cspF_Act_prefix_Dist_sum`, `cspF_Act_prefix_Dist_nat`,
   `cspF_Act_prefix_Dist_set`, `cspF_Act_prefix_Dist_com`, and
   `cspF_Act_prefix_Dist_f`. -/

/- The Isabelle theorem bundle `cspF_Ext_pre_choice_Dist` is represented by
   `cspF_Ext_pre_choice_Dist_sum`, `cspF_Ext_pre_choice_Dist_nat`,
   `cspF_Ext_pre_choice_Dist_set`, `cspF_Ext_pre_choice_Dist_com`, and
   `cspF_Ext_pre_choice_Dist_f`. -/

/-
(*****************************************************************
      distribution over external choice
         1. (P1 [+] P2) [[r]]
         2. (P1 [+] P2) |. n
 *****************************************************************)
-/

axiom cspF_Renaming_Ext_dist
    {P1 P2 : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((P1 [+] P2)[[r]]) M M ((P1[[r]]) [+] (P2[[r]]))

axiom cspF_Depth_rest_Ext_dist
    {P1 P2 : proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((P1 [+] P2) |. n) M M ((P1 |. n) [+] (P2 |. n))

/- The Isabelle theorem bundle `cspF_Ext_dist` is represented by
   `cspF_Renaming_Ext_dist` and `cspF_Depth_rest_Ext_dist`. -/

/-
(*---------------------------------------------------------*
 |                   complex distribution                  |
 *---------------------------------------------------------*)
-/

axiom cspF_Rep_int_choice_sum_input_set
    {C : sets_nats α} {Yf : aset_anat α → Set α} {Rff : aset_anat α → α → proc p α}
    {M : p → domFType α} :
    eqF (proc.Rep_int_choice C fun c => proc.Ext_pre_choice (Yf c) (Rff c)) M M
      (Rep_int_choice_set (Yf '' sumset C) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          proc.Rep_int_choice (sub_sumset C fun c => a ∈ Yf c) fun c => Rff c a)

axiom cspF_Rep_int_choice_nat_input_set
    {N : Set Nat} {Yf : Nat → Set α} {Rff : Nat → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N fun n => proc.Ext_pre_choice (Yf n) (Rff n)) M M
      (Rep_int_choice_set (Yf '' N) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ a ∈ Yf n} fun n => Rff n a)

axiom cspF_Rep_int_choice_set_input_set
    {Xs : Set (Set α)} {Yf : Set α → Set α} {Rff : Set α → α → proc p α}
    {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs fun X => proc.Ext_pre_choice (Yf X) (Rff X)) M M
      (Rep_int_choice_set (Yf '' Xs) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          Rep_int_choice_set {X | X ∈ Xs ∧ a ∈ Yf X} fun X => Rff X a)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_input_set` is
   represented by `cspF_Rep_int_choice_sum_input_set`,
   `cspF_Rep_int_choice_nat_input_set`, and
   `cspF_Rep_int_choice_set_input_set`. -/

axiom cspF_Rep_int_choice_Ext_Dist_sum
    {C : sets_nats α} {Pf Qf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, c ∈ sumset C → Qf c = proc.SKIP ∨ Qf c = proc.DIV) →
      eqF (proc.Rep_int_choice C fun c => Pf c [+] Qf c) M M
        ((proc.Rep_int_choice C Pf) [+] (proc.Rep_int_choice C Qf))

axiom cspF_Rep_int_choice_Ext_Dist_nat
    {N : Set Nat} {Pf Qf : Nat → proc p α} {M : p → domFType α} :
    (∀ n, n ∈ N → Qf n = proc.SKIP ∨ Qf n = proc.DIV) →
      eqF (Rep_int_choice_nat N fun n => Pf n [+] Qf n) M M
        ((Rep_int_choice_nat N Pf) [+] (Rep_int_choice_nat N Qf))

axiom cspF_Rep_int_choice_Ext_Dist_set
    {Xs : Set (Set α)} {Pf Qf : Set α → proc p α} {M : p → domFType α} :
    (∀ X, X ∈ Xs → Qf X = proc.SKIP ∨ Qf X = proc.DIV) →
      eqF (Rep_int_choice_set Xs fun X => Pf X [+] Qf X) M M
        ((Rep_int_choice_set Xs Pf) [+] (Rep_int_choice_set Xs Qf))

axiom cspF_Rep_int_choice_Ext_Dist_com [Inhabited α]
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (∀ a, a ∈ X → Qf a = proc.SKIP ∨ Qf a = proc.DIV) →
      eqF (Rep_int_choice_com X fun a => Pf a [+] Qf a) M M
        ((Rep_int_choice_com X Pf) [+] (Rep_int_choice_com X Qf))

axiom cspF_Rep_int_choice_Ext_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf Qf : β → proc p α} {M : p → domFType α} :
    (∀ a, a ∈ X → Qf a = proc.SKIP ∨ Qf a = proc.DIV) →
      eqF (Rep_int_choice_f f X fun a => Pf a [+] Qf a) M M
        ((Rep_int_choice_f f X Pf) [+] (Rep_int_choice_f f X Qf))

/- The Isabelle theorem bundle `cspF_Rep_int_choice_Ext_Dist` is
   represented by `cspF_Rep_int_choice_Ext_Dist_sum`,
   `cspF_Rep_int_choice_Ext_Dist_nat`,
   `cspF_Rep_int_choice_Ext_Dist_set`,
   `cspF_Rep_int_choice_Ext_Dist_com`, and
   `cspF_Rep_int_choice_Ext_Dist_f`. -/

axiom cspF_Rep_int_choice_input_Dist_SKIP
    {Xs : Set (Set α)} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] proc.SKIP) M M
      ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] proc.SKIP)

axiom cspF_Rep_int_choice_input_Dist_DIV
    {Xs : Set (Set α)} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] proc.DIV) M M
      ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] proc.DIV)

axiom cspF_Rep_int_choice_input_Dist
    {Xs : Set (Set α)} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    Q = proc.SKIP ∨ Q = proc.DIV →
      eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] Q) M M
        ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] Q)

axiom cspF_Rep_int_choice_sum_Ext_choice
    {C : sets_nats α} {Xf : aset_anat α → Set α} {Pf : aset_anat α → α → proc p α}
    {Q : proc p α} {M : p → domFType α} :
    Q = proc.SKIP ∨ Q = proc.DIV →
      eqF ((proc.Rep_int_choice C fun c => proc.Ext_pre_choice (Xf c) (Pf c)) [+] Q) M M
        ((proc.Ext_pre_choice (Set.sUnion (Xf '' sumset C)) fun x =>
            proc.Rep_int_choice (sub_sumset C fun c => x ∈ Xf c) fun c => Pf c x) [+] Q)

axiom cspF_Rep_int_choice_nat_Ext_choice
    {N : Set Nat} {Xf : Nat → Set α} {Pf : Nat → α → proc p α}
    {Q : proc p α} {M : p → domFType α} :
    Q = proc.SKIP ∨ Q = proc.DIV →
      eqF ((Rep_int_choice_nat N fun n => proc.Ext_pre_choice (Xf n) (Pf n)) [+] Q) M M
        ((proc.Ext_pre_choice (Set.sUnion (Xf '' N)) fun x =>
            Rep_int_choice_nat {n | n ∈ N ∧ x ∈ Xf n} fun n => Pf n x) [+] Q)

axiom cspF_Rep_int_choice_set_Ext_choice
    {Xs : Set (Set α)} {Xf : Set α → Set α} {Pf : Set α → α → proc p α}
    {Q : proc p α} {M : p → domFType α} :
    Q = proc.SKIP ∨ Q = proc.DIV →
      eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice (Xf X) (Pf X)) [+] Q) M M
        ((proc.Ext_pre_choice (Set.sUnion (Xf '' Xs)) fun x =>
            Rep_int_choice_set {X | X ∈ Xs ∧ x ∈ Xf X} fun X => Pf X x) [+] Q)

/- The Isabelle theorem bundle `cspF_Rep_int_choice_Ext_choice` is
   represented by `cspF_Rep_int_choice_sum_Ext_choice`,
   `cspF_Rep_int_choice_nat_Ext_choice`, and
   `cspF_Rep_int_choice_set_Ext_choice`. -/

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)
-/

axiom cspF_Seq_compo_hide_dist
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (P ;; Q) X) M M ((proc.Hiding P X) ;; proc.Hiding Q X)

axiom cspF_Interleave_hide_dist
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (P |[(∅ : Set α)]| Q) X) M M
      ((proc.Hiding P X) |[(∅ : Set α)]| proc.Hiding Q X)

axiom cspF_Seq_compo_renaming_dist
    {P Q : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((P ;; Q)[[r]]) M M ((P[[r]]) ;; (Q[[r]]))

axiom cspF_Interleave_renaming_dist
    {P Q : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF (((P |[(∅ : Set α)]| Q))[[r]]) M M
      ((P[[r]]) |[(∅ : Set α)]| (Q[[r]]))

axiom cspF_Act_prefix_dist {a : α} {P Q : proc p α} {M : p → domFType α} :
    eqF (a ~> (P |~| Q)) M M ((a ~> P) |~| (a ~> Q))

axiom cspF_Int_choice_Act_prefix_delay {a : α} {P Q : proc p α} {M : p → domFType α} :
    eqF ((a ~> P) |~| (a ~> Q)) M M (a ~> (P |~| Q))

axiom cspF_Int_choice_Act_prefix_delay_eq
    {a b : α} {P Q : proc p α} {M : p → domFType α} :
    a = b → eqF ((a ~> P) |~| (b ~> Q)) M M (a ~> (P |~| Q))

axiom cspF_Ext_pre_choice_dist
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) M M
      ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice X Qf))

axiom cspF_Int_choice_Ext_pre_choice_delay
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice X Qf)) M M
      (proc.Ext_pre_choice X fun x => Pf x |~| Qf x)

axiom cspF_Int_choice_Ext_pre_choice_delay_eq
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    X = Y →
      eqF ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice Y Qf)) M M
        (proc.Ext_pre_choice X fun x => Pf x |~| Qf x)

axiom cspF_Act_prefix_delay_sum
    {C : sets_nats α} {a : α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C fun c => a ~> Pf c) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α) (a ~> proc.Rep_int_choice C Pf))

axiom cspF_Ext_pre_choice_delay_sum
    {C : sets_nats α} {X : Set α} {Pf : aset_anat α → α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C fun c => proc.Ext_pre_choice X (Pf c)) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => proc.Rep_int_choice C fun c => Pf c x))

axiom cspF_Act_prefix_delay_nat
    {N : Set Nat} {a : α} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N fun n => a ~> Pf n) M M
      (procIte (N = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_nat N Pf))

axiom cspF_Ext_pre_choice_delay_nat
    {N : Set Nat} {X : Set α} {Pf : Nat → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N fun n => proc.Ext_pre_choice X (Pf n)) M M
      (procIte (N = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_nat N fun n => Pf n x))

axiom cspF_Act_prefix_delay_set
    {Xs : Set (Set α)} {a : α} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs fun X => a ~> Pf X) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_set Xs Pf))

axiom cspF_Ext_pre_choice_delay_set
    {Xs : Set (Set α)} {X : Set α} {Pf : Set α → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs fun Y => proc.Ext_pre_choice X (Pf Y)) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_set Xs fun Y => Pf Y x))

axiom cspF_Act_prefix_delay_com [Inhabited α]
    {X : Set α} {a : α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X fun x => a ~> Pf x) M M
      (procIte (X = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_com X Pf))

axiom cspF_Ext_pre_choice_delay_com [Inhabited α]
    {X Y : Set α} {Pf : α → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com Y fun y => proc.Ext_pre_choice X (Pf y)) M M
      (procIte (Y = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_com Y fun y => Pf y x))

axiom cspF_Act_prefix_delay_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {a : α} {Pf : β → proc p α}
    {M : p → domFType α} :
    eqF (Rep_int_choice_f f X fun x => a ~> Pf x) M M
      (procIte (X = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_f f X Pf))

axiom cspF_Ext_pre_choice_delay_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set α} {Y : Set β} {Pf : β → α → proc p α}
    {M : p → domFType α} :
    eqF (Rep_int_choice_f f Y fun y => proc.Ext_pre_choice X (Pf y)) M M
      (procIte (Y = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_f f Y fun y => Pf y x))

/- The Isabelle theorem bundle `cspF_choice_delay` is represented by
   `cspF_Int_choice_Act_prefix_delay`,
   `cspF_Int_choice_Ext_pre_choice_delay`, `cspF_Act_prefix_delay_sum`,
   `cspF_Ext_pre_choice_delay_sum`, `cspF_Act_prefix_delay_nat`,
   `cspF_Ext_pre_choice_delay_nat`, `cspF_Act_prefix_delay_set`,
   `cspF_Ext_pre_choice_delay_set`, `cspF_Act_prefix_delay_com`,
   `cspF_Ext_pre_choice_delay_com`, `cspF_Act_prefix_delay_f`, and
   `cspF_Ext_pre_choice_delay_f`. -/

/- The Isabelle theorem bundle `cspF_choice_delay_eq` is represented by
   `cspF_Int_choice_Act_prefix_delay_eq` and
   `cspF_Int_choice_Ext_pre_choice_delay_eq`. -/

/-
(*********************************************************
                       P |[X,Y]| Q
 *********************************************************)
-/

axiom cspF_Alpha_Parallel_dist_l
    {P1 P2 Q : proc p α} {X Y : Set α} {M : p → domFType α} :
    eqF ((P1 |~| P2) |[X,Y]| Q) M M (((P1 |[X,Y]| Q)) |~| ((P2 |[X,Y]| Q)))

axiom cspF_Alpha_Parallel_dist_r
    {P Q1 Q2 : proc p α} {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| (Q1 |~| Q2)) M M (((P |[X,Y]| Q1)) |~| ((P |[X,Y]| Q2)))

axiom cspF_Alpha_Parallel_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (proc.Rep_int_choice C Pf |[X,Y]| Q) M M
        (proc.Rep_int_choice C fun c => Pf c |[X,Y]| Q)

axiom cspF_Alpha_Parallel_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C Pf |[X,Y]| Q) M M
      (procIte (sumset C = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (proc.Rep_int_choice C fun c => Pf c |[X,Y]| Q))

axiom cspF_Alpha_Parallel_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (P |[X,Y]| proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P |[X,Y]| Qf c)

axiom cspF_Alpha_Parallel_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P |[X,Y]| Qf c))

axiom cspF_Alpha_Parallel_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (Rep_int_choice_nat N Pf |[X,Y]| Q) M M
        (Rep_int_choice_nat N fun n => Pf n |[X,Y]| Q)

axiom cspF_Alpha_Parallel_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N Pf |[X,Y]| Q) M M
      (procIte (N = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_nat N fun n => Pf n |[X,Y]| Q))

axiom cspF_Alpha_Parallel_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (P |[X,Y]| Rep_int_choice_nat N Qf) M M
        (Rep_int_choice_nat N fun n => P |[X,Y]| Qf n)

axiom cspF_Alpha_Parallel_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P |[X,Y]| Qf n))

axiom cspF_Alpha_Parallel_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    Xs ≠ ∅ →
      eqF (Rep_int_choice_set Xs Pf |[Y,Z]| Q) M M
        (Rep_int_choice_set Xs fun X => Pf X |[Y,Z]| Q)

axiom cspF_Alpha_Parallel_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs Pf |[Y,Z]| Q) M M
      (procIte (Xs = ∅) (((proc.DIV : proc p α) |[Y,Z]| Q))
        (Rep_int_choice_set Xs fun X => Pf X |[Y,Z]| Q))

axiom cspF_Alpha_Parallel_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    Xs ≠ ∅ →
      eqF (P |[Y,Z]| Rep_int_choice_set Xs Qf) M M
        (Rep_int_choice_set Xs fun X => P |[Y,Z]| Qf X)

axiom cspF_Alpha_Parallel_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    eqF (P |[Y,Z]| Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P |[Y,Z]| (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P |[Y,Z]| Qf X))

axiom cspF_Alpha_Parallel_Dist_com_l_nonempty [Inhabited α]
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (Rep_int_choice_com A Pf |[X,Y]| Q) M M
        (Rep_int_choice_com A fun x => Pf x |[X,Y]| Q)

axiom cspF_Alpha_Parallel_Dist_com_l [Inhabited α]
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_com A Pf |[X,Y]| Q) M M
      (procIte (A = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_com A fun x => Pf x |[X,Y]| Q))

axiom cspF_Alpha_Parallel_Dist_com_r_nonempty [Inhabited α]
    {A : Set α} {Qf : α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (P |[X,Y]| Rep_int_choice_com A Qf) M M
        (Rep_int_choice_com A fun x => P |[X,Y]| Qf x)

axiom cspF_Alpha_Parallel_Dist_com_r [Inhabited α]
    {A : Set α} {Qf : α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| Rep_int_choice_com A Qf) M M
      (procIte (A = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_com A fun x => P |[X,Y]| Qf x))

axiom cspF_Alpha_Parallel_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (Rep_int_choice_f f A Pf |[X,Y]| Q) M M
        (Rep_int_choice_f f A fun x => Pf x |[X,Y]| Q)

axiom cspF_Alpha_Parallel_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f A Pf |[X,Y]| Q) M M
      (procIte (A = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_f f A fun x => Pf x |[X,Y]| Q))

axiom cspF_Alpha_Parallel_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Qf : β → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (P |[X,Y]| Rep_int_choice_f f A Qf) M M
        (Rep_int_choice_f f A fun x => P |[X,Y]| Qf x)

axiom cspF_Alpha_Parallel_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Qf : β → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| Rep_int_choice_f f A Qf) M M
      (procIte (A = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_f f A fun x => P |[X,Y]| Qf x))

/- The Isabelle theorem bundle `cspF_dist_Alpha_Parallel` is represented by
   `cspF_Alpha_Parallel_dist_l` and `cspF_Alpha_Parallel_dist_r`. -/

/- The Isabelle theorem bundle `cspF_Dist_Alpha_Parallel` is represented by
   `cspF_Alpha_Parallel_Dist_sum_l`, `cspF_Alpha_Parallel_Dist_sum_r`,
   `cspF_Alpha_Parallel_Dist_nat_l`, `cspF_Alpha_Parallel_Dist_nat_r`,
   `cspF_Alpha_Parallel_Dist_set_l`, `cspF_Alpha_Parallel_Dist_set_r`,
   `cspF_Alpha_Parallel_Dist_com_l`, `cspF_Alpha_Parallel_Dist_com_r`,
   `cspF_Alpha_Parallel_Dist_f_l`, and `cspF_Alpha_Parallel_Dist_f_r`. -/

/- The Isabelle theorem bundle `cspF_Dist_Alpha_Parallel_nonempty` is
   represented by `cspF_Alpha_Parallel_Dist_sum_l_nonempty`,
   `cspF_Alpha_Parallel_Dist_sum_r_nonempty`,
   `cspF_Alpha_Parallel_Dist_nat_l_nonempty`,
   `cspF_Alpha_Parallel_Dist_nat_r_nonempty`,
   `cspF_Alpha_Parallel_Dist_set_l_nonempty`,
   `cspF_Alpha_Parallel_Dist_set_r_nonempty`,
   `cspF_Alpha_Parallel_Dist_com_l_nonempty`,
   `cspF_Alpha_Parallel_Dist_com_r_nonempty`,
   `cspF_Alpha_Parallel_Dist_f_l_nonempty`, and
   `cspF_Alpha_Parallel_Dist_f_r_nonempty`. -/

end
