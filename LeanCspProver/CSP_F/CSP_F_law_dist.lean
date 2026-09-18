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
import LeanCspProver.CSP_F.CSP_F_simp

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

theorem cspF_Ext_choice_dist_l {P1 P2 Q : proc p α} {M : p → domFType α} :
    eqF ((P1 |~| P2) [+] Q) M M ((P1 [+] Q) |~| (P2 [+] Q)) := by
  cspF_auto

theorem cspF_Ext_choice_dist_r {P Q1 Q2 : proc p α} {M : p → domFType α} :
    eqF (P [+] (Q1 |~| Q2)) M M ((P [+] Q1) |~| (P [+] Q2)) := by
  cspF_auto

theorem cspF_Parallel_dist_l {P1 P2 Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF ((P1 |~| P2) |[X]| Q) M M ((P1 |[X]| Q) |~| (P2 |[X]| Q)) := by
  cspF_auto

theorem cspF_Parallel_dist_r {P Q1 Q2 : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| (Q1 |~| Q2)) M M ((P |[X]| Q1) |~| (P |[X]| Q2)) := by
  cspF_auto

theorem cspF_Hiding_dist {P1 P2 : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (P1 |~| P2) X) M M ((proc.Hiding P1 X) |~| (proc.Hiding P2 X)) := by
  cspF_auto

theorem cspF_Renaming_dist {P1 P2 : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((P1 |~| P2)[[r]]) M M ((P1[[r]]) |~| (P2[[r]])) := by
  cspF_auto

theorem cspF_Seq_compo_dist {P1 P2 Q : proc p α} {M : p → domFType α} :
    eqF ((P1 |~| P2) ;; Q) M M ((P1 ;; Q) |~| (P2 ;; Q)) := by
  cspF_auto

theorem cspF_Depth_rest_dist {P1 P2 : proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((P1 |~| P2) |. n) M M ((P1 |. n) |~| (P2 |. n)) := by
  cspF_auto

theorem cspF_Rep_int_choice_sum_dist
    {C : sets_nats α} {Pf Qf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C (fun c => Pf c |~| Qf c)) M M
      ((proc.Rep_int_choice C Pf) |~| (proc.Rep_int_choice C Qf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_nat_dist
    {N : Set Nat} {Pf Qf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N (fun n => Pf n |~| Qf n)) M M
      ((Rep_int_choice_nat N Pf) |~| (Rep_int_choice_nat N Qf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_dist
    {Xs : Set (Set α)} {Pf Qf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs (fun X => Pf X |~| Qf X)) M M
      ((Rep_int_choice_set Xs Pf) |~| (Rep_int_choice_set Xs Qf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_com_dist [Inhabited α]
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X (fun a => Pf a |~| Qf a)) M M
      ((Rep_int_choice_com X Pf) |~| (Rep_int_choice_com X Qf)) := by
  cspF_auto

theorem cspF_Rep_int_choice_f_dist [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf Qf : β → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f X (fun a => Pf a |~| Qf a)) M M
      ((Rep_int_choice_f f X Pf) |~| (Rep_int_choice_f f X Qf)) := by
  cspF_auto

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

theorem cspF_Ext_choice_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF ((proc.Rep_int_choice C Pf) [+] Q) M M
        (proc.Rep_int_choice C fun c => Pf c [+] Q) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf) [+] Q) M M
      (procIte (sumset C = ∅) ((proc.DIV : proc p α) [+] Q)
        (proc.Rep_int_choice C fun c => Pf c [+] Q)) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (P [+] proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P [+] Qf c) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P [+] (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P [+] Qf c)) := by
  cspF_auto

theorem cspF_Parallel_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (proc.Rep_int_choice C Pf |[X]| Q) M M
        (proc.Rep_int_choice C fun c => Pf c |[X]| Q) := by
  cspF_auto

theorem cspF_Parallel_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C Pf |[X]| Q) M M
      (procIte (sumset C = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (proc.Rep_int_choice C fun c => Pf c |[X]| Q)) := by
  cspF_auto

theorem cspF_Parallel_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (P |[X]| proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P |[X]| Qf c) := by
  cspF_auto

theorem cspF_Parallel_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P |[X]| (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P |[X]| Qf c)) := by
  cspF_auto

theorem cspF_Hiding_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (proc.Rep_int_choice C Pf) X) M M
      (proc.Rep_int_choice C fun c => proc.Hiding (Pf c) X) := by
  cspF_auto

theorem cspF_Renaming_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf)[[r]]) M M
      (proc.Rep_int_choice C fun c => (Pf c)[[r]]) := by
  cspF_auto

theorem cspF_Seq_compo_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf) ;; Q) M M
      (proc.Rep_int_choice C fun c => Pf c ;; Q) := by
  cspF_auto

theorem cspF_Depth_rest_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {m : Nat} {M : p → domFType α} :
    eqF ((proc.Rep_int_choice C Pf) |. m) M M
      (proc.Rep_int_choice C fun c => Pf c |. m) := by
  cspF_auto

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

theorem cspF_Ext_choice_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domFType α} :
    N ≠ ∅ → eqF ((Rep_int_choice_nat N Pf) [+] Q) M M
      (Rep_int_choice_nat N fun n => Pf n [+] Q) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf) [+] Q) M M
      (procIte (N = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_nat N fun n => Pf n [+] Q)) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {M : p → domFType α} :
    N ≠ ∅ → eqF (P [+] Rep_int_choice_nat N Qf) M M
      (Rep_int_choice_nat N fun n => P [+] Qf n) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P [+] Qf n)) := by
  cspF_auto

theorem cspF_Parallel_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    N ≠ ∅ → eqF (Rep_int_choice_nat N Pf |[X]| Q) M M
      (Rep_int_choice_nat N fun n => Pf n |[X]| Q) := by
  cspF_auto

theorem cspF_Parallel_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N Pf |[X]| Q) M M
      (procIte (N = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_nat N fun n => Pf n |[X]| Q)) := by
  cspF_auto

theorem cspF_Parallel_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    N ≠ ∅ → eqF (P |[X]| Rep_int_choice_nat N Qf) M M
      (Rep_int_choice_nat N fun n => P |[X]| Qf n) := by
  cspF_auto

theorem cspF_Parallel_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P |[X]| Qf n)) := by
  cspF_auto

theorem cspF_Hiding_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_nat N Pf) X) M M
      (Rep_int_choice_nat N fun n => proc.Hiding (Pf n) X) := by
  cspF_auto

theorem cspF_Renaming_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf)[[r]]) M M
      (Rep_int_choice_nat N fun n => (Pf n)[[r]]) := by
  cspF_auto

theorem cspF_Seq_compo_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf) ;; Q) M M
      (Rep_int_choice_nat N fun n => Pf n ;; Q) := by
  cspF_auto

theorem cspF_Depth_rest_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {m : Nat} {M : p → domFType α} :
    eqF ((Rep_int_choice_nat N Pf) |. m) M M
      (Rep_int_choice_nat N fun n => Pf n |. m) := by
  cspF_auto

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

theorem cspF_Ext_choice_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF ((Rep_int_choice_set Xs Pf) [+] Q) M M
      (Rep_int_choice_set Xs fun X => Pf X [+] Q) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf) [+] Q) M M
      (procIte (Xs = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_set Xs fun X => Pf X [+] Q)) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (P [+] Rep_int_choice_set Xs Qf) M M
      (Rep_int_choice_set Xs fun X => P [+] Qf X) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P [+] Qf X)) := by
  cspF_auto

theorem cspF_Parallel_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {Y : Set α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (Rep_int_choice_set Xs Pf |[Y]| Q) M M
      (Rep_int_choice_set Xs fun X => Pf X |[Y]| Q) := by
  cspF_auto

theorem cspF_Parallel_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs Pf |[Y]| Q) M M
      (procIte (Xs = ∅) (((proc.DIV : proc p α) |[Y]| Q))
        (Rep_int_choice_set Xs fun X => Pf X |[Y]| Q)) := by
  cspF_auto

theorem cspF_Parallel_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {Y : Set α} {M : p → domFType α} :
    Xs ≠ ∅ → eqF (P |[Y]| Rep_int_choice_set Xs Qf) M M
      (Rep_int_choice_set Xs fun X => P |[Y]| Qf X) := by
  cspF_auto

theorem cspF_Parallel_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {Y : Set α} {M : p → domFType α} :
    eqF (P |[Y]| Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P |[Y]| (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P |[Y]| Qf X)) := by
  cspF_auto

theorem cspF_Hiding_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Y : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_set Xs Pf) Y) M M
      (Rep_int_choice_set Xs fun X => proc.Hiding (Pf X) Y) := by
  cspF_auto

theorem cspF_Renaming_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf)[[r]]) M M
      (Rep_int_choice_set Xs fun X => (Pf X)[[r]]) := by
  cspF_auto

theorem cspF_Seq_compo_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf) ;; Q) M M
      (Rep_int_choice_set Xs fun X => Pf X ;; Q) := by
  cspF_auto

theorem cspF_Depth_rest_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {m : Nat} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs Pf) |. m) M M
      (Rep_int_choice_set Xs fun X => Pf X |. m) := by
  cspF_auto

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

theorem cspF_Ext_choice_Dist_com_l_nonempty [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF ((Rep_int_choice_com X Pf) [+] Q) M M
      (Rep_int_choice_com X fun x => Pf x [+] Q) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_com_r_nonempty [Inhabited α]
    {X : Set α} {Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    X ≠ ∅ → eqF (P [+] Rep_int_choice_com X Qf) M M
      (Rep_int_choice_com X fun x => P [+] Qf x) := by
  cspF_auto

theorem cspF_Parallel_Dist_com_l_nonempty [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (Rep_int_choice_com Y Pf |[X]| Q) M M
      (Rep_int_choice_com Y fun x => Pf x |[X]| Q) := by
  cspF_auto

theorem cspF_Parallel_Dist_com_r_nonempty [Inhabited α]
    {Y : Set α} {Qf : α → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (P |[X]| Rep_int_choice_com Y Qf) M M
      (Rep_int_choice_com Y fun x => P |[X]| Qf x) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_com_l [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf) [+] Q) M M
      (procIte (X = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_com X fun x => Pf x [+] Q)) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_com_r [Inhabited α]
    {X : Set α} {Qf : α → proc p α} {P : proc p α} {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_com X Qf) M M
      (procIte (X = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_com X fun x => P [+] Qf x)) := by
  cspF_auto

theorem cspF_Parallel_Dist_com_l [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_com Y Pf |[X]| Q) M M
      (procIte (Y = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_com Y fun x => Pf x |[X]| Q)) := by
  cspF_auto

theorem cspF_Parallel_Dist_com_r [Inhabited α]
    {Y : Set α} {Qf : α → proc p α} {P : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Rep_int_choice_com Y Qf) M M
      (procIte (Y = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_com Y fun x => P |[X]| Qf x)) := by
  cspF_auto

theorem cspF_Hiding_Dist_com [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_com Y Pf) X) M M
      (Rep_int_choice_com Y fun x => proc.Hiding (Pf x) X) := by
  cspF_auto

theorem cspF_Renaming_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf)[[r]]) M M
      (Rep_int_choice_com X fun x => (Pf x)[[r]]) := by
  cspF_auto

theorem cspF_Seq_compo_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf) ;; Q) M M
      (Rep_int_choice_com X fun x => Pf x ;; Q) := by
  cspF_auto

theorem cspF_Depth_rest_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((Rep_int_choice_com X Pf) |. n) M M
      (Rep_int_choice_com X fun x => Pf x |. n) := by
  cspF_auto

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

theorem cspF_Ext_choice_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domFType α} :
    X ≠ ∅ → eqF ((Rep_int_choice_f f X Pf) [+] Q) M M
      (Rep_int_choice_f f X fun x => Pf x [+] Q) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Qf : β → proc p α} {P : proc p α}
    {M : p → domFType α} :
    X ≠ ∅ → eqF (P [+] Rep_int_choice_f f X Qf) M M
      (Rep_int_choice_f f X fun x => P [+] Qf x) := by
  cspF_auto

theorem cspF_Parallel_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (Rep_int_choice_f f Y Pf |[X]| Q) M M
      (Rep_int_choice_f f Y fun x => Pf x |[X]| Q) := by
  cspF_auto

theorem cspF_Parallel_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Qf : β → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    Y ≠ ∅ → eqF (P |[X]| Rep_int_choice_f f Y Qf) M M
      (Rep_int_choice_f f Y fun x => P |[X]| Qf x) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf) [+] Q) M M
      (procIte (X = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_f f X fun x => Pf x [+] Q)) := by
  cspF_auto

theorem cspF_Ext_choice_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Qf : β → proc p α} {P : proc p α}
    {M : p → domFType α} :
    eqF (P [+] Rep_int_choice_f f X Qf) M M
      (procIte (X = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_f f X fun x => P [+] Qf x)) := by
  cspF_auto

theorem cspF_Parallel_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f Y Pf |[X]| Q) M M
      (procIte (Y = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_f f Y fun x => Pf x |[X]| Q)) := by
  cspF_auto

theorem cspF_Parallel_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Qf : β → proc p α} {P : proc p α}
    {X : Set α} {M : p → domFType α} :
    eqF (P |[X]| Rep_int_choice_f f Y Qf) M M
      (procIte (Y = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_f f Y fun x => P |[X]| Qf x)) := by
  cspF_auto

theorem cspF_Hiding_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {X : Set α}
    {M : p → domFType α} :
    eqF (proc.Hiding (Rep_int_choice_f f Y Pf) X) M M
      (Rep_int_choice_f f Y fun x => proc.Hiding (Pf x) X) := by
  cspF_auto

theorem cspF_Renaming_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {r : Set (α × α)}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf)[[r]]) M M
      (Rep_int_choice_f f X fun x => (Pf x)[[r]]) := by
  cspF_auto

theorem cspF_Seq_compo_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf) ;; Q) M M
      (Rep_int_choice_f f X fun x => Pf x ;; Q) := by
  cspF_auto

theorem cspF_Depth_rest_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {n : Nat}
    {M : p → domFType α} :
    eqF ((Rep_int_choice_f f X Pf) |. n) M M
      (Rep_int_choice_f f X fun x => Pf x |. n) := by
  cspF_auto

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

theorem cspF_Act_prefix_Dist_sum
    {C : sets_nats α} {a : α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (a ~> proc.Rep_int_choice C Pf) M M
        (proc.Rep_int_choice C fun c => a ~> Pf c) := by
  cspF_auto

theorem cspF_Ext_pre_choice_Dist_sum
    {C : sets_nats α} {X : Set α} {Pf : aset_anat α → α → proc p α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => proc.Rep_int_choice C fun c => Pf c x) M M
        (proc.Rep_int_choice C fun c => proc.Ext_pre_choice X (Pf c)) := by
  cspF_auto

theorem cspF_Act_prefix_Dist_nat
    {N : Set Nat} {a : α} {Pf : Nat → proc p α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (a ~> Rep_int_choice_nat N Pf) M M
        (Rep_int_choice_nat N fun n => a ~> Pf n) := by
  cspF_auto

theorem cspF_Ext_pre_choice_Dist_nat
    {N : Set Nat} {X : Set α} {Pf : Nat → α → proc p α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_nat N fun n => Pf n x) M M
        (Rep_int_choice_nat N fun n => proc.Ext_pre_choice X (Pf n)) := by
  cspF_auto

theorem cspF_Act_prefix_Dist_set
    {Xs : Set (Set α)} {a : α} {Pf : Set α → proc p α} {M : p → domFType α} :
    Xs ≠ ∅ →
      eqF (a ~> Rep_int_choice_set Xs Pf) M M
        (Rep_int_choice_set Xs fun X => a ~> Pf X) := by
  cspF_auto

theorem cspF_Ext_pre_choice_Dist_set
    {X : Set α} {Ys : Set (Set α)} {Pf : Set α → α → proc p α} {M : p → domFType α} :
    Ys ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_set Ys fun Y => Pf Y x) M M
        (Rep_int_choice_set Ys fun Y => proc.Ext_pre_choice X (Pf Y)) := by
  cspF_auto

theorem cspF_Act_prefix_Dist_com [Inhabited α]
    {X : Set α} {a : α} {Pf : α → proc p α} {M : p → domFType α} :
    X ≠ ∅ →
      eqF (a ~> Rep_int_choice_com X Pf) M M
        (Rep_int_choice_com X fun x => a ~> Pf x) := by
  cspF_auto

theorem cspF_Ext_pre_choice_Dist_com [Inhabited α]
    {X Y : Set α} {Pf : α → α → proc p α} {M : p → domFType α} :
    Y ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_com Y fun y => Pf y x) M M
        (Rep_int_choice_com Y fun y => proc.Ext_pre_choice X (Pf y)) := by
  cspF_auto

theorem cspF_Act_prefix_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {a : α} {Pf : β → proc p α}
    {M : p → domFType α} :
    X ≠ ∅ →
      eqF (a ~> Rep_int_choice_f f X Pf) M M
        (Rep_int_choice_f f X fun x => a ~> Pf x) := by
  cspF_auto

theorem cspF_Ext_pre_choice_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set α} {Y : Set β} {Pf : β → α → proc p α}
    {M : p → domFType α} :
    Y ≠ ∅ →
      eqF (proc.Ext_pre_choice X fun x => Rep_int_choice_f f Y fun y => Pf y x) M M
        (Rep_int_choice_f f Y fun y => proc.Ext_pre_choice X (Pf y)) := by
  cspF_auto

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

theorem cspF_Renaming_Ext_dist
    {P1 P2 : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((P1 [+] P2)[[r]]) M M ((P1[[r]]) [+] (P2[[r]])) := by
  cspF_auto

theorem cspF_Depth_rest_Ext_dist
    {P1 P2 : proc p α} {n : Nat} {M : p → domFType α} :
    eqF ((P1 [+] P2) |. n) M M ((P1 |. n) [+] (P2 |. n)) := by
  apply cspF_eqF_of_eqT cspT_Depth_rest_Ext_dist
  intro s X
  simp only [in_failures_Depth_rest, in_failures_Ext_choice, in_traces_Depth_rest,
    Prod.mk.injEq, tickTrace_eq, lengtht_one_event]
  grind [lengtht_zero, lengtht_one_event, event_app_not_nil_right, noTick_nil, appt_nil_left]

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

theorem cspF_Rep_int_choice_nat_input_set
    {N : Set Nat} {Yf : Nat → Set α} {Rff : Nat → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N fun n => proc.Ext_pre_choice (Yf n) (Rff n)) M M
      (Rep_int_choice_set (Yf '' N) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ a ∈ Yf n} fun n => Rff n a) := by
  cspF_auto

theorem cspF_Rep_int_choice_set_input_set
    {Xs : Set (Set α)} {Yf : Set α → Set α} {Rff : Set α → α → proc p α}
    {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs fun X => proc.Ext_pre_choice (Yf X) (Rff X)) M M
      (Rep_int_choice_set (Yf '' Xs) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          Rep_int_choice_set {X | X ∈ Xs ∧ a ∈ Yf X} fun X => Rff X a) := by
  cspF_auto

/- The Isabelle theorem bundle `cspF_Rep_int_choice_input_set` is
   represented by `cspF_Rep_int_choice_sum_input_set`,
   `cspF_Rep_int_choice_nat_input_set`, and
   `cspF_Rep_int_choice_set_input_set`. -/

/-- Failures of `SKIP`, split by the trace. -/
theorem in_failures_SKIP' {s : traceType α} {W : Set (event α)} {M : p → domFType α} :
    ((s, W) :f failures (proc.SKIP : proc p α) M) ↔
      ((s = <> ∧ W ⊆ Evset) ∨ s = (Abs_trace [event.Tick] : traceType α)) := by
  rw [in_failures_SKIP]
  constructor
  · rintro (⟨X, hEq, hX⟩ | ⟨X, hEq⟩)
    · exact Or.inl ⟨(Prod.mk.inj hEq).1, by rw [(Prod.mk.inj hEq).2]; exact hX⟩
    · exact Or.inr (Prod.mk.inj hEq).1
  · rintro (⟨rfl, hW⟩ | rfl)
    · exact Or.inl ⟨W, rfl, hW⟩
    · exact Or.inr ⟨W, rfl⟩

/-- Failures of `P [+] Q` when `Q` is `SKIP` or `DIV`. -/
theorem in_failures_Ext_choice_SKIP_or_DIV
    {P Q : proc p α} {s : traceType α} {W : Set (event α)} {M : p → domFType α}
    (hQ : Q = proc.SKIP ∨ Q = proc.DIV) :
    ((s, W) :f failures (P [+] Q) M) ↔
      ((s ≠ <> ∧ ((s, W) :f failures P M ∨
          (Q = proc.SKIP ∧ s = (Abs_trace [event.Tick] : traceType α)))) ∨
        (s = <> ∧ W ⊆ Evset ∧
          ((Abs_trace [event.Tick] : traceType α) :t traces P (fstF ∘ M) ∨
            Q = proc.SKIP))) := by
  rw [in_failures_Ext_choice]
  rcases hQ with rfl | rfl
  · constructor
    · rintro (⟨⟨W1, hEq⟩, -, hS⟩ | ⟨s1, ⟨W1, hEq⟩, hor, hne⟩ | ⟨W1, hEq, hTick, hsub⟩)
      · have hs : s = <> := (Prod.mk.inj hEq).1
        rw [in_failures_SKIP'] at hS
        rcases hS with ⟨-, hW⟩ | hT
        · exact Or.inr ⟨hs, hW, Or.inr rfl⟩
        · rw [hs] at hT
          simp at hT
      · have hs : s = s1 := (Prod.mk.inj hEq).1
        refine Or.inl ⟨by rw [hs]; exact hne, ?_⟩
        rcases hor with hP | hS
        · exact Or.inl hP
        · rw [in_failures_SKIP'] at hS
          rcases hS with ⟨h0, -⟩ | hT
          · exact absurd (hs.trans (hs ▸ h0)) (by rw [hs]; exact hne)
          · exact Or.inr ⟨rfl, hT⟩
      · refine Or.inr ⟨(Prod.mk.inj hEq).1, by rw [(Prod.mk.inj hEq).2]; exact hsub, ?_⟩
        rcases hTick with h | -
        · exact Or.inl h
        · exact Or.inr rfl
    · rintro (⟨hne, hor⟩ | ⟨rfl, hW, -⟩)
      · refine Or.inr (Or.inl ⟨s, ⟨W, rfl⟩, ?_, hne⟩)
        rcases hor with hP | ⟨-, rfl⟩
        · exact Or.inl hP
        · exact Or.inr (in_failures_SKIP'.mpr (Or.inr rfl))
      · exact Or.inr (Or.inr ⟨W, rfl, Or.inr (in_traces_SKIP.mpr (Or.inr rfl)), hW⟩)
  · constructor
    · rintro (⟨-, -, hD⟩ | ⟨s1, ⟨W1, hEq⟩, hor, hne⟩ | ⟨W1, hEq, hTick, hsub⟩)
      · exact absurd hD in_failures_DIV
      · have hs : s = s1 := (Prod.mk.inj hEq).1
        exact Or.inl ⟨by rw [hs]; exact hne,
          Or.inl (hor.resolve_right in_failures_DIV)⟩
      · refine Or.inr ⟨(Prod.mk.inj hEq).1, by rw [(Prod.mk.inj hEq).2]; exact hsub, ?_⟩
        rcases hTick with h | h
        · exact Or.inl h
        · rw [in_traces_DIV] at h
          simp at h
    · rintro (⟨hne, hor⟩ | ⟨rfl, hW, hor⟩)
      · refine Or.inr (Or.inl ⟨s, ⟨W, rfl⟩, ?_, hne⟩)
        rcases hor with hP | ⟨hS, -⟩
        · exact Or.inl hP
        · exact absurd hS (by simp)
      · refine Or.inr (Or.inr ⟨W, rfl, ?_, hW⟩)
        rcases hor with h | h
        · exact Or.inl h
        · exact absurd h (by simp)

theorem cspF_Rep_int_choice_Ext_Dist_sum
    {C : sets_nats α} {Pf Qf : aset_anat α → proc p α} {M : p → domFType α} :
    (∀ c, c ∈ sumset C → Qf c = proc.SKIP ∨ Qf c = proc.DIV) →
      eqF (proc.Rep_int_choice C fun c => Pf c [+] Qf c) M M
        ((proc.Rep_int_choice C Pf) [+] (proc.Rep_int_choice C Qf)) := by
  intro hQ
  refine cspF_eqF_of_eqT (cspT_Rep_int_choice_Ext_Dist_sum hQ) ?_
  intro s W
  rw [in_failures_Rep_int_choice_sum, in_failures_Ext_choice]
  constructor
  · rintro ⟨c, hc, hf⟩
    rw [in_failures_Ext_choice_SKIP_or_DIV (hQ c hc)] at hf
    rcases hf with ⟨hne, hor⟩ | ⟨rfl, hW, hor⟩
    · refine Or.inr (Or.inl ⟨s, ⟨W, rfl⟩, ?_, hne⟩)
      rcases hor with hP | ⟨hS, rfl⟩
      · exact Or.inl (in_failures_Rep_int_choice_sum.mpr ⟨c, hc, hP⟩)
      · refine Or.inr (in_failures_Rep_int_choice_sum.mpr ⟨c, hc, ?_⟩)
        rw [hS]
        exact in_failures_SKIP'.mpr (Or.inr rfl)
    · refine Or.inr (Or.inr ⟨W, rfl, ?_, hW⟩)
      rcases hor with hT | hS
      · exact Or.inl (in_traces_Rep_int_choice_sum.mpr (Or.inr ⟨c, hc, hT⟩))
      · refine Or.inr (in_traces_Rep_int_choice_sum.mpr (Or.inr ⟨c, hc, ?_⟩))
        rw [hS]
        exact in_traces_SKIP.mpr (Or.inr rfl)
  · rintro (⟨⟨W1, hEq⟩, -, hQm⟩ | ⟨s1, ⟨W1, hEq⟩, hor, hne⟩ | ⟨W1, hEq, hTick, hsub⟩)
    · have hs : s = <> := (Prod.mk.inj hEq).1
      obtain ⟨c, hc, hfc⟩ := in_failures_Rep_int_choice_sum.mp hQm
      rcases hQ c hc with hS | hD
      · rw [hS, in_failures_SKIP'] at hfc
        rcases hfc with ⟨-, hW⟩ | hT
        · exact ⟨c, hc, (in_failures_Ext_choice_SKIP_or_DIV (hQ c hc)).mpr
            (Or.inr ⟨hs, hW, Or.inr hS⟩)⟩
        · rw [hs] at hT
          simp at hT
      · rw [hD] at hfc
        exact absurd hfc in_failures_DIV
    · have hs : s = s1 := (Prod.mk.inj hEq).1
      have hne' : s ≠ <> := by rw [hs]; exact hne
      rcases hor with hP | hQm
      · obtain ⟨c, hc, hfc⟩ := in_failures_Rep_int_choice_sum.mp hP
        exact ⟨c, hc, (in_failures_Ext_choice_SKIP_or_DIV (hQ c hc)).mpr
          (Or.inl ⟨hne', Or.inl hfc⟩)⟩
      · obtain ⟨c, hc, hfc⟩ := in_failures_Rep_int_choice_sum.mp hQm
        rcases hQ c hc with hS | hD
        · rw [hS, in_failures_SKIP'] at hfc
          rcases hfc with ⟨h0, -⟩ | hT
          · exact absurd h0 hne'
          · exact ⟨c, hc, (in_failures_Ext_choice_SKIP_or_DIV (hQ c hc)).mpr
              (Or.inl ⟨hne', Or.inr ⟨hS, hT⟩⟩)⟩
        · rw [hD] at hfc
          exact absurd hfc in_failures_DIV
    · have hs : s = <> := (Prod.mk.inj hEq).1
      have hW : W ⊆ Evset := by rw [(Prod.mk.inj hEq).2]; exact hsub
      rcases hTick with hT | hT
      · rcases in_traces_Rep_int_choice_sum.mp hT with hnil | ⟨c, hc, htc⟩
        · simp at hnil
        · exact ⟨c, hc, (in_failures_Ext_choice_SKIP_or_DIV (hQ c hc)).mpr
            (Or.inr ⟨hs, hW, Or.inl htc⟩)⟩
      · rcases in_traces_Rep_int_choice_sum.mp hT with hnil | ⟨c, hc, htc⟩
        · simp at hnil
        · rcases hQ c hc with hS | hD
          · exact ⟨c, hc, (in_failures_Ext_choice_SKIP_or_DIV (hQ c hc)).mpr
              (Or.inr ⟨hs, hW, Or.inr hS⟩)⟩
          · rw [hD, in_traces_DIV] at htc
            simp at htc

theorem cspF_Rep_int_choice_Ext_Dist_nat
    {N : Set Nat} {Pf Qf : Nat → proc p α} {M : p → domFType α} :
    (∀ n, n ∈ N → Qf n = proc.SKIP ∨ Qf n = proc.DIV) →
      eqF (Rep_int_choice_nat N fun n => Pf n [+] Qf n) M M
        ((Rep_int_choice_nat N Pf) [+] (Rep_int_choice_nat N Qf)) := by
  intro hQ
  exact cspF_Rep_int_choice_Ext_Dist_sum
    (C := type2 N) (Pf := fun c => Pf (Function.invFun type2 c))
    (Qf := fun c => Qf (Function.invFun type2 c))
    (fun c hc => P_inv_type2 hQ hc)

theorem cspF_Rep_int_choice_Ext_Dist_set
    {Xs : Set (Set α)} {Pf Qf : Set α → proc p α} {M : p → domFType α} :
    (∀ X, X ∈ Xs → Qf X = proc.SKIP ∨ Qf X = proc.DIV) →
      eqF (Rep_int_choice_set Xs fun X => Pf X [+] Qf X) M M
        ((Rep_int_choice_set Xs Pf) [+] (Rep_int_choice_set Xs Qf)) := by
  intro hQ
  exact cspF_Rep_int_choice_Ext_Dist_sum
    (C := type1 Xs) (Pf := fun c => Pf (Function.invFun type1 c))
    (Qf := fun c => Qf (Function.invFun type1 c))
    (fun c hc => P_inv_type1 hQ hc)

theorem cspF_Rep_int_choice_Ext_Dist_com [Inhabited α]
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    (∀ a, a ∈ X → Qf a = proc.SKIP ∨ Qf a = proc.DIV) →
      eqF (Rep_int_choice_com X fun a => Pf a [+] Qf a) M M
        ((Rep_int_choice_com X Pf) [+] (Rep_int_choice_com X Qf)) := by
  intro hQ
  refine cspF_Rep_int_choice_Ext_Dist_set
    (Xs := {S : Set α | ∃ a, a ∈ X ∧ S = ({a} : Set α)})
    (Pf := fun S => Pf (the_elem S)) (Qf := fun S => Qf (the_elem S)) ?_
  rintro S ⟨a, ha, rfl⟩
  dsimp only
  rw [the_elem_singleton]
  exact hQ a ha

theorem cspF_Rep_int_choice_Ext_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf Qf : β → proc p α} {M : p → domFType α} :
    (∀ a, a ∈ X → Qf a = proc.SKIP ∨ Qf a = proc.DIV) →
      eqF (Rep_int_choice_f f X fun a => Pf a [+] Qf a) M M
        ((Rep_int_choice_f f X Pf) [+] (Rep_int_choice_f f X Qf)) := by
  intro hQ
  refine cspF_Rep_int_choice_Ext_Dist_com
    (X := f '' X) (Pf := fun y => Pf (Function.invFun f y))
    (Qf := fun y => Qf (Function.invFun f y)) ?_
  rintro y ⟨a, ha, rfl⟩
  dsimp only
  rw [Function.leftInverse_invFun hf a]
  exact hQ a ha

/- The Isabelle theorem bundle `cspF_Rep_int_choice_Ext_Dist` is
   represented by `cspF_Rep_int_choice_Ext_Dist_sum`,
   `cspF_Rep_int_choice_Ext_Dist_nat`,
   `cspF_Rep_int_choice_Ext_Dist_set`,
   `cspF_Rep_int_choice_Ext_Dist_com`, and
   `cspF_Rep_int_choice_Ext_Dist_f`. -/

theorem cspF_Rep_int_choice_input_Dist_SKIP
    {Xs : Set (Set α)} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] proc.SKIP) M M
      ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] proc.SKIP) := by
  refine cspF_eqF_of_eqT cspT_Rep_int_choice_input_Dist ?_
  intro s W
  rw [in_failures_Ext_choice_SKIP_or_DIV (Or.inl rfl),
    in_failures_Ext_choice_SKIP_or_DIV (Or.inl rfl)]
  constructor
  · rintro (⟨hne, hor⟩ | ⟨hs, hW, -⟩)
    · refine Or.inl ⟨hne, ?_⟩
      rcases hor with hA | hT
      · rw [in_failures_Rep_int_choice_set] at hA
        obtain ⟨X, hX, hf⟩ := hA
        rw [in_failures_Ext_pre_choice] at hf
        rcases hf with ⟨Y, hEq, -⟩ | ⟨a, t, Y, hEq, hft, ha⟩
        · exact absurd (Prod.mk.inj hEq).1 hne
        · exact Or.inl (in_failures_Ext_pre_choice.mpr
            (Or.inr ⟨a, t, Y, hEq, hft, ⟨X, hX, ha⟩⟩))
      · exact Or.inr hT
    · exact Or.inr ⟨hs, hW, Or.inr rfl⟩
  · rintro (⟨hne, hor⟩ | ⟨hs, hW, -⟩)
    · refine Or.inl ⟨hne, ?_⟩
      rcases hor with hB | hT
      · rw [in_failures_Ext_pre_choice] at hB
        rcases hB with ⟨Y, hEq, -⟩ | ⟨a, t, Y, hEq, hft, X, hX, ha⟩
        · exact absurd (Prod.mk.inj hEq).1 hne
        · exact Or.inl (in_failures_Rep_int_choice_set.mpr ⟨X, hX,
            in_failures_Ext_pre_choice.mpr (Or.inr ⟨a, t, Y, hEq, hft, ha⟩)⟩)
      · exact Or.inr hT
    · exact Or.inr ⟨hs, hW, Or.inr rfl⟩

theorem cspF_Rep_int_choice_input_Dist_DIV
    {Xs : Set (Set α)} {Pf : α → proc p α} {M : p → domFType α} :
    eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] proc.DIV) M M
      ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] proc.DIV) := by
  cspF_auto

theorem cspF_Rep_int_choice_input_Dist
    {Xs : Set (Set α)} {Pf : α → proc p α} {Q : proc p α} {M : p → domFType α} :
    Q = proc.SKIP ∨ Q = proc.DIV →
      eqF ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] Q) M M
        ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] Q) := by
  rintro (rfl | rfl)
  · exact cspF_Rep_int_choice_input_Dist_SKIP
  · exact cspF_Rep_int_choice_input_Dist_DIV

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

private theorem Tick_notin_Ev_image' {X : Set α} : (event.Tick : event α) ∉ event.Ev '' X := by
  rintro ⟨a, -, ha⟩
  cases ha

/-- In an interleaving the two refusals agree off `Tick`, so the hidden events are
    refused by both components. -/
private theorem EvX_subset_left {X : Set α} {A B W : Set (event α)}
    (hU : (event.Ev '' X) ∪ W = A ∪ B)
    (hAB : A \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) =
      B \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick})) :
    (event.Ev '' X : Set (event α)) ⊆ A := by
  intro e he
  have hmem : e ∈ A ∪ B := by
    rw [← hU]
    exact Or.inl he
  rcases hmem with hA | hB
  · exact hA
  · have hne : e ∉ ((event.Ev '' (∅ : Set α)) ∪ ({event.Tick} : Set (event α))) := by
      rintro (⟨a, ha, -⟩ | hT)
      · exact ha
      · rw [Set.mem_singleton_iff] at hT
        rw [hT] at he
        exact Tick_notin_Ev_image' he
    have hmem' : e ∈ B \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := ⟨hB, hne⟩
    rw [← hAB] at hmem'
    exact hmem'.1

private theorem ren_inv_union_Tick {r : Set (α × α)} {V : Set (event α)} :
    ren_inv r (V ∪ {event.Tick}) = ren_inv r V ∪ {event.Tick} := by
  rw [Set.union_singleton, ren_inv_insert_Tick, Set.union_singleton]

private theorem mem_par_empty_refusal {e : event α} :
    (e ∈ ((event.Ev '' (∅ : Set α)) ∪ ({event.Tick} : Set (event α)))) ↔ e = event.Tick := by
  constructor
  · rintro (⟨a, ha, -⟩ | hT)
    · exact ha.elim
    · exact Set.mem_singleton_iff.mp hT
  · intro h
    exact Or.inr (Set.mem_singleton_iff.mpr h)

private theorem ren_inv_union {r : Set (α × α)} {A B : Set (event α)} :
    ren_inv r (A ∪ B) = ren_inv r A ∪ ren_inv r B := by
  ext e
  constructor
  · rintro ⟨eb, (hb | hb), hc⟩
    · exact Or.inl ⟨eb, hb, hc⟩
    · exact Or.inr ⟨eb, hb, hc⟩
  · rintro (⟨eb, hb, hc⟩ | ⟨eb, hb, hc⟩)
    · exact ⟨eb, Or.inl hb, hc⟩
    · exact ⟨eb, Or.inr hb, hc⟩

theorem cspF_Seq_compo_hide_dist
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (P ;; Q) X) M M ((proc.Hiding P X) ;; proc.Hiding Q X) := by
  refine cspF_eqF_of_eqT cspT_Seq_compo_hide_dist ?_
  intro t W
  rw [in_failures_Hiding, in_failures_Seq_compo]
  constructor
  · rintro ⟨s, Y, hEq, hs⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Seq_compo] at hs
    rcases hs with ⟨t1, W1, hEq1, hP, hno⟩ | ⟨s1, t1, W1, hEq1, hT, hQ, hno⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq1
      refine Or.inl ⟨hide_tr s X, W, rfl, ?_, hide_tr_noTick.mpr hno⟩
      rw [in_failures_Hiding]
      exact ⟨s, W ∪ {event.Tick}, rfl, by rw [← Set.union_assoc]; exact hP⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq1
      refine Or.inr ⟨hide_tr s1 X, hide_tr t1 X, W, by rw [hide_tr_appt (Or.inl hno)], ?_, ?_,
        hide_tr_noTick.mpr hno⟩
      · rw [in_traces_Hiding]
        refine ⟨(s1 ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α), ?_, hT⟩
        rw [hide_tr_appt (Or.inl hno), hide_tr_Tick]
      · rw [in_failures_Hiding]
        exact ⟨t1, W, rfl, hQ⟩
  · rintro (⟨t1, W1, hEq, hP, hno⟩ | ⟨u, v, W1, hEq, hT, hQ, hno⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Hiding] at hP
      obtain ⟨s, Y, hEqs, hsP⟩ := hP
      obtain ⟨hts, rfl⟩ := Prod.mk.inj hEqs
      refine ⟨s, W, by rw [hts], ?_⟩
      rw [in_failures_Seq_compo]
      refine Or.inl ⟨s, (event.Ev '' X) ∪ W, rfl, by rw [Set.union_assoc]; exact hsP, ?_⟩
      rw [← hide_tr_noTick (X := X), ← hts]
      exact hno
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_traces_Hiding] at hT
      rw [in_failures_Hiding] at hQ
      obtain ⟨w, hwEq, hwP⟩ := hT
      obtain ⟨t', Y', hEqt, ht'Q⟩ := hQ
      obtain ⟨hvt, rfl⟩ := Prod.mk.inj hEqt
      rcases trace_last_noTick_or_Tick w with hwno | ⟨w', hw'no, rfl⟩
      · exfalso
        have hcontra : noTick (u ^^^ (Abs_trace [event.Tick] : traceType α)) := by
          rw [hwEq]
          exact hide_tr_noTick.mpr hwno
        exact not_noTick_Tick (decompo_appt_noTick_only_if (Or.inl hno) hcontra).2
      · rw [hide_tr_appt (Or.inl hw'no), hide_tr_Tick] at hwEq
        have hu : u = hide_tr w' X :=
          ((appt_same_last hno (hide_tr_noTick.mpr hw'no)).mp hwEq).1
        subst hu
        subst hvt
        refine ⟨(w' ^^^ t' : traceType α), W, (by rw [hide_tr_appt (Or.inl hw'no)]), ?_⟩
        rw [in_failures_Seq_compo]
        exact Or.inr ⟨w', t', (event.Ev '' X) ∪ W, rfl, hwP, ht'Q, hw'no⟩

theorem cspF_Interleave_hide_dist
    {P Q : proc p α} {X : Set α} {M : p → domFType α} :
    eqF (proc.Hiding (P |[(∅ : Set α)]| Q) X) M M
      ((proc.Hiding P X) |[(∅ : Set α)]| proc.Hiding Q X) := by
  refine cspF_eqF_of_eqT cspT_Interleave_hide_dist ?_
  intro t W
  rw [in_failures_Hiding, in_failures_Parallel]
  constructor
  · rintro ⟨u, Y, hEq, hu⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Parallel] at hu
    obtain ⟨u2, Y1, Z1, hEq1, hYZ, s, t1, hpar, hsP, ht1Q⟩ := hu
    obtain ⟨rfl, hU⟩ := Prod.mk.inj hEq1
    have hEvY : (event.Ev '' X : Set (event α)) ⊆ Y1 := EvX_subset_left hU hYZ
    have hEvZ : (event.Ev '' X : Set (event α)) ⊆ Z1 :=
      EvX_subset_left (by rw [hU, Set.union_comm]) hYZ.symm
    have hpt : ∀ a : event α,
        (a ∈ Y1 ∧ a ∉ ((event.Ev '' (∅ : Set α)) ∪ ({event.Tick} : Set (event α)))) ↔
          (a ∈ Z1 ∧ a ∉ ((event.Ev '' (∅ : Set α)) ∪ ({event.Tick} : Set (event α)))) := by
      intro a
      constructor
      · intro h
        have hm : a ∈ Z1 \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := by rw [← hYZ]; exact h
        exact hm
      · intro h
        have hm : a ∈ Y1 \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := by rw [hYZ]; exact h
        exact hm
    have hWeq : W = ((event.Ev '' X) ∪ Y1) ∩ W ∪ ((event.Ev '' X) ∪ Z1) ∩ W := by
      ext e
      constructor
      · intro he
        have hmem : e ∈ Y1 ∪ Z1 := by
          rw [← hU]
          exact Or.inr he
        rcases hmem with h | h
        · exact Or.inl ⟨Or.inr h, he⟩
        · exact Or.inr ⟨Or.inr h, he⟩
      · rintro (⟨-, he⟩ | ⟨-, he⟩) <;> exact he
    refine ⟨hide_tr u X, ((event.Ev '' X) ∪ Y1) ∩ W, ((event.Ev '' X) ∪ Z1) ∩ W, by rw [← hWeq], ?_,
      hide_tr s X, hide_tr t1 X, interleave_of_hide_tr hpar, ?_, ?_⟩
    · ext e
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_union]
      have h1 := hpt e
      simp only [Set.mem_union] at h1
      tauto
    · rw [in_failures_Hiding]
      refine ⟨s, ((event.Ev '' X) ∪ Y1) ∩ W, rfl, memF_F2 hsP ?_⟩
      rintro e (he | ⟨(he | he), -⟩)
      · exact hEvY he
      · exact hEvY he
      · exact he
    · rw [in_failures_Hiding]
      refine ⟨t1, ((event.Ev '' X) ∪ Z1) ∩ W, rfl, memF_F2 ht1Q ?_⟩
      rintro e (he | ⟨(he | he), -⟩)
      · exact hEvZ he
      · exact hEvZ he
      · exact he
  · rintro ⟨u2, Y', Z', hEq, hYZ, s', t', hpar, hsP, ht'Q⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Hiding] at hsP ht'Q
    obtain ⟨s, Y1, hEqs, hsP'⟩ := hsP
    obtain ⟨t1, Z1, hEqt, ht1Q'⟩ := ht'Q
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqt
    obtain ⟨v, rfl, hv⟩ := interleave_of_hide_tr_ex.mp hpar
    refine ⟨v, Y' ∪ Z', rfl, ?_⟩
    rw [in_failures_Parallel]
    refine ⟨v, (event.Ev '' X) ∪ Y', (event.Ev '' X) ∪ Z', ?_, ?_, s, t1, hv, hsP', ht1Q'⟩
    · have hsplit :
          (event.Ev '' X) ∪ (Y' ∪ Z') = ((event.Ev '' X) ∪ Y') ∪ ((event.Ev '' X) ∪ Z') := by
        ext e
        simp only [Set.mem_union]
        tauto
      rw [← hsplit]
    · have hpt : ∀ a : event α,
          (a ∈ Y' ∧ a ∉ ((event.Ev '' (∅ : Set α)) ∪ ({event.Tick} : Set (event α)))) ↔
            (a ∈ Z' ∧ a ∉ ((event.Ev '' (∅ : Set α)) ∪ ({event.Tick} : Set (event α)))) := by
        intro a
        constructor
        · intro h
          have hm : a ∈ Z' \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := by rw [← hYZ]; exact h
          exact hm
        · intro h
          have hm : a ∈ Y' \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := by rw [hYZ]; exact h
          exact hm
      ext e
      simp only [Set.mem_diff, Set.mem_union]
      have h1 := hpt e
      simp only [Set.mem_union] at h1
      tauto

theorem cspF_Seq_compo_renaming_dist
    {P Q : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF ((P ;; Q)[[r]]) M M ((P[[r]]) ;; (Q[[r]])) := by
  refine cspF_eqF_of_eqT cspT_Seq_compo_renaming_dist ?_
  intro t W
  rw [in_failures_Renaming, in_failures_Seq_compo]
  constructor
  · rintro ⟨s, t', W', hEq, hren, hs⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Seq_compo] at hs
    rcases hs with ⟨t1, W1, hEq1, hP, hno⟩ | ⟨s1, t1, W1, hEq1, hT, hQ, hno⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq1
      refine Or.inl ⟨t, W, rfl, ?_, ren_tr_noTick_left hren hno⟩
      rw [in_failures_Renaming]
      refine ⟨s, t, W ∪ {event.Tick}, rfl, hren, ?_⟩
      rw [ren_inv_union_Tick]
      exact hP
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq1
      obtain ⟨u, v, rfl, h1, h2, -⟩ := (ren_tr_appt_decompo_left (Or.inl hno)).mp hren
      refine Or.inr ⟨u, v, W, rfl, ?_, ?_, ren_tr_noTick_left h1 hno⟩
      · rw [in_traces_Renaming]
        exact ⟨(s1 ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α),
          ren_tr_appt h1 ren_tr_Tick (Or.inl hno), hT⟩
      · rw [in_failures_Renaming]
        exact ⟨t1, v, W, rfl, h2, hQ⟩
  · rintro (⟨t1, W1, hEq, hP, hno⟩ | ⟨u, v, W1, hEq, hT, hQ, hno⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_failures_Renaming] at hP
      obtain ⟨s, t'', W'', hEqs, hren, hsP⟩ := hP
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqs
      refine ⟨s, t, W, rfl, hren, ?_⟩
      rw [in_failures_Seq_compo]
      refine Or.inl ⟨s, ren_inv r W, rfl, ?_, ren_tr_noTick_right hren hno⟩
      rw [← ren_inv_union_Tick]
      exact hsP
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
      rw [in_traces_Renaming] at hT
      rw [in_failures_Renaming] at hQ
      obtain ⟨w, hwren, hwP⟩ := hT
      obtain ⟨t1, v', W', hEqv, hvren, ht1Q⟩ := hQ
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqv
      obtain ⟨w1, w2, rfl, h1, h2, -⟩ := (ren_tr_appt_decompo_right (Or.inl hno)).mp hwren
      have hw2 : w2 = (Abs_trace [event.Tick] : traceType α) := ren_tr_Tick2.mp h2
      subst hw2
      have hw1no : noTick w1 := ren_tr_noTick_right h1 hno
      refine ⟨(w1 ^^^ t1 : traceType α), (u ^^^ v : traceType α), W, rfl,
        ren_tr_appt h1 hvren (Or.inl hw1no), ?_⟩
      rw [in_failures_Seq_compo]
      exact Or.inr ⟨w1, t1, ren_inv r W, rfl, hwP, ht1Q, hw1no⟩

theorem cspF_Interleave_renaming_dist
    {P Q : proc p α} {r : Set (α × α)} {M : p → domFType α} :
    eqF (((P |[(∅ : Set α)]| Q))[[r]]) M M ((P[[r]]) |[(∅ : Set α)]| (Q[[r]])) := by
  refine cspF_eqF_of_eqT cspT_Interleave_renaming_dist ?_
  intro t W
  rw [in_failures_Renaming, in_failures_Parallel]
  constructor
  · rintro ⟨s, t', W', hEq, hren, hs⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Parallel] at hs
    obtain ⟨u, Y, Z, hEq1, hYZ, s1, t1, hpar, hsP, ht1Q⟩ := hs
    obtain ⟨rfl, hinvW⟩ := Prod.mk.inj hEq1
    obtain ⟨s', t'', hpar', hs'ren, ht'ren⟩ := interleave_of_ren_tr_only_if hpar hren
    have hYZ' : ∀ e : event α, (e ∈ Y ∧ e ≠ event.Tick) ↔ (e ∈ Z ∧ e ≠ event.Tick) := by
      intro e
      constructor
      · rintro ⟨hY, hne⟩
        have hm : e ∈ Z \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := by
          rw [← hYZ]
          exact ⟨hY, fun h => hne (mem_par_empty_refusal.mp h)⟩
        exact ⟨hm.1, hne⟩
      · rintro ⟨hZ, hne⟩
        have hm : e ∈ Y \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) := by
          rw [hYZ]
          exact ⟨hZ, fun h => hne (mem_par_empty_refusal.mp h)⟩
        exact ⟨hm.1, hne⟩
    by_cases hT : (event.Tick : event α) ∈ Y ∨ (event.Tick : event α) ∈ Z
    · have hTW : (event.Tick : event α) ∈ W := by
        have hTinv : (event.Tick : event α) ∈ ren_inv r W := by
          rw [hinvW]
          exact hT
        obtain ⟨eb, hb, hc⟩ := hTinv
        rcases hc with ⟨-, rfl⟩ | ⟨a, b, -, hc, -⟩
        · exact hb
        · exact absurd hc.symm (by simp)
      refine ⟨t, (W \ {event.Tick}) ∪ (Y ∩ {event.Tick}),
        (W \ {event.Tick}) ∪ (Z ∩ {event.Tick}), ?_, ?_, s', t'', hpar', ?_, ?_⟩
      · congr 1
        ext e
        constructor
        · intro he
          by_cases hTe : e = event.Tick
          · subst hTe
            rcases hT with h | h
            · exact Or.inl (Or.inr ⟨h, rfl⟩)
            · exact Or.inr (Or.inr ⟨h, rfl⟩)
          · exact Or.inl (Or.inl ⟨he, fun h => hTe (Set.mem_singleton_iff.mp h)⟩)
        · rintro ((⟨he, -⟩ | ⟨-, he⟩) | (⟨he, -⟩ | ⟨-, he⟩))
          · exact he
          · rw [Set.mem_singleton_iff] at he
            rw [he]
            exact hTW
          · exact he
          · rw [Set.mem_singleton_iff] at he
            rw [he]
            exact hTW
      · ext e
        simp only [Set.mem_diff, Set.mem_union, Set.mem_inter_iff, Set.mem_singleton_iff]
        tauto
      · rw [in_failures_Renaming]
        refine ⟨s1, s', (W \ {event.Tick}) ∪ (Y ∩ {event.Tick}), rfl, hs'ren, memF_F2 hsP ?_⟩
        rintro e ⟨eb, hebY, hcase⟩
        rcases hcase with ⟨rfl, rfl⟩ | ⟨a, b, hr, rfl, rfl⟩
        · rcases hebY with ⟨-, hne⟩ | ⟨hY, -⟩
          · exact absurd (Set.mem_singleton_iff.mpr rfl) hne
          · exact hY
        · rcases hebY with ⟨hW, -⟩ | ⟨-, hTk⟩
          · have hmem : (event.Ev a : event α) ∈ ren_inv r W :=
              ⟨event.Ev b, hW, Or.inr ⟨a, b, hr, rfl, rfl⟩⟩
            rw [hinvW] at hmem
            rcases hmem with h | h
            · exact h
            · exact ((hYZ' (event.Ev a)).mpr ⟨h, by simp⟩).1
          · exact absurd (Set.mem_singleton_iff.mp hTk) (by simp)
      · rw [in_failures_Renaming]
        refine ⟨t1, t'', (W \ {event.Tick}) ∪ (Z ∩ {event.Tick}), rfl, ht'ren, memF_F2 ht1Q ?_⟩
        rintro e ⟨eb, hebZ, hcase⟩
        rcases hcase with ⟨rfl, rfl⟩ | ⟨a, b, hr, rfl, rfl⟩
        · rcases hebZ with ⟨-, hne⟩ | ⟨hZ, -⟩
          · exact absurd (Set.mem_singleton_iff.mpr rfl) hne
          · exact hZ
        · rcases hebZ with ⟨hW, -⟩ | ⟨-, hTk⟩
          · have hmem : (event.Ev a : event α) ∈ ren_inv r W :=
              ⟨event.Ev b, hW, Or.inr ⟨a, b, hr, rfl, rfl⟩⟩
            rw [hinvW] at hmem
            rcases hmem with h | h
            · exact ((hYZ' (event.Ev a)).mp ⟨h, by simp⟩).1
            · exact h
          · exact absurd (Set.mem_singleton_iff.mp hTk) (by simp)
    · push_neg at hT
      obtain ⟨hTY, hTZ⟩ := hT
      have hYeqZ : Y = Z := by
        ext e
        by_cases hTe : e = event.Tick
        · subst hTe
          constructor
          · intro h; exact absurd h hTY
          · intro h; exact absurd h hTZ
        · constructor
          · intro h; exact ((hYZ' e).mp ⟨h, hTe⟩).1
          · intro h; exact ((hYZ' e).mpr ⟨h, hTe⟩).1
      have hinvY : ren_inv r W = Y := by
        rw [hinvW, ← hYeqZ, Set.union_self]
      refine ⟨t, W, W, by rw [Set.union_self], rfl, s', t'', hpar', ?_, ?_⟩
      · rw [in_failures_Renaming]
        exact ⟨s1, s', W, rfl, hs'ren, by rw [hinvY]; exact hsP⟩
      · rw [in_failures_Renaming]
        exact ⟨t1, t'', W, rfl, ht'ren, by rw [hinvY, hYeqZ]; exact ht1Q⟩
  · rintro ⟨u, Y', Z', hEq, hYZ, s', t', hpar, hsP, ht'Q⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
    rw [in_failures_Renaming] at hsP ht'Q
    obtain ⟨s1, s'', Y'', hEqs, hs1ren, hs1P⟩ := hsP
    obtain ⟨t1, t'', Z'', hEqt, ht1ren, ht1Q⟩ := ht'Q
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqs
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEqt
    obtain ⟨v, hv, hvren⟩ := interleave_of_ren_tr_if hpar hs1ren ht1ren
    refine ⟨v, t, Y' ∪ Z', rfl, hvren, ?_⟩
    rw [in_failures_Parallel]
    refine ⟨v, ren_inv r Y', ren_inv r Z', by rw [ren_inv_union], ?_, s1, t1, hv, hs1P, ht1Q⟩
    ext e
    constructor
    · rintro ⟨⟨eb, hebY, hcase⟩, hne⟩
      rcases hcase with ⟨rfl, rfl⟩ | ⟨a, b, hr, rfl, rfl⟩
      · exact absurd (mem_par_empty_refusal.mpr rfl) hne
      · refine ⟨⟨event.Ev b, ?_, Or.inr ⟨a, b, hr, rfl, rfl⟩⟩, hne⟩
        have hm : (event.Ev b : event α) ∈ Y' \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) :=
          ⟨hebY, fun h => by simpa using mem_par_empty_refusal.mp h⟩
        rw [hYZ] at hm
        exact hm.1
    · rintro ⟨⟨eb, hebZ, hcase⟩, hne⟩
      rcases hcase with ⟨rfl, rfl⟩ | ⟨a, b, hr, rfl, rfl⟩
      · exact absurd (mem_par_empty_refusal.mpr rfl) hne
      · refine ⟨⟨event.Ev b, ?_, Or.inr ⟨a, b, hr, rfl, rfl⟩⟩, hne⟩
        have hm : (event.Ev b : event α) ∈ Z' \ ((event.Ev '' (∅ : Set α)) ∪ {event.Tick}) :=
          ⟨hebZ, fun h => by simpa using mem_par_empty_refusal.mp h⟩
        rw [← hYZ] at hm
        exact hm.1

theorem cspF_Act_prefix_dist {a : α} {P Q : proc p α} {M : p → domFType α} :
    eqF (a ~> (P |~| Q)) M M ((a ~> P) |~| (a ~> Q)) := by
  cspF_auto

theorem cspF_Int_choice_Act_prefix_delay {a : α} {P Q : proc p α} {M : p → domFType α} :
    eqF ((a ~> P) |~| (a ~> Q)) M M (a ~> (P |~| Q)) := by
  cspF_auto

theorem cspF_Int_choice_Act_prefix_delay_eq
    {a b : α} {P Q : proc p α} {M : p → domFType α} :
    a = b → eqF ((a ~> P) |~| (b ~> Q)) M M (a ~> (P |~| Q)) := by
  cspF_auto

theorem cspF_Ext_pre_choice_dist
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) M M
      ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice X Qf)) := by
  cspF_auto

theorem cspF_Int_choice_Ext_pre_choice_delay
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice X Qf)) M M
      (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) := by
  cspF_auto

theorem cspF_Int_choice_Ext_pre_choice_delay_eq
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domFType α} :
    X = Y →
      eqF ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice Y Qf)) M M
        (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) := by
  cspF_auto

theorem cspF_Act_prefix_delay_sum
    {C : sets_nats α} {a : α} {Pf : aset_anat α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C fun c => a ~> Pf c) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α) (a ~> proc.Rep_int_choice C Pf)) := by
  cspF_auto

theorem cspF_Ext_pre_choice_delay_sum
    {C : sets_nats α} {X : Set α} {Pf : aset_anat α → α → proc p α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C fun c => proc.Ext_pre_choice X (Pf c)) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => proc.Rep_int_choice C fun c => Pf c x)) := by
  cspF_auto

theorem cspF_Act_prefix_delay_nat
    {N : Set Nat} {a : α} {Pf : Nat → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N fun n => a ~> Pf n) M M
      (procIte (N = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_nat N Pf)) := by
  cspF_auto

theorem cspF_Ext_pre_choice_delay_nat
    {N : Set Nat} {X : Set α} {Pf : Nat → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N fun n => proc.Ext_pre_choice X (Pf n)) M M
      (procIte (N = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_nat N fun n => Pf n x)) := by
  cspF_auto

theorem cspF_Act_prefix_delay_set
    {Xs : Set (Set α)} {a : α} {Pf : Set α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs fun X => a ~> Pf X) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_set Xs Pf)) := by
  cspF_auto

theorem cspF_Ext_pre_choice_delay_set
    {Xs : Set (Set α)} {X : Set α} {Pf : Set α → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs fun Y => proc.Ext_pre_choice X (Pf Y)) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_set Xs fun Y => Pf Y x)) := by
  cspF_auto

theorem cspF_Act_prefix_delay_com [Inhabited α]
    {X : Set α} {a : α} {Pf : α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com X fun x => a ~> Pf x) M M
      (procIte (X = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_com X Pf)) := by
  cspF_auto

theorem cspF_Ext_pre_choice_delay_com [Inhabited α]
    {X Y : Set α} {Pf : α → α → proc p α} {M : p → domFType α} :
    eqF (Rep_int_choice_com Y fun y => proc.Ext_pre_choice X (Pf y)) M M
      (procIte (Y = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_com Y fun y => Pf y x)) := by
  cspF_auto

theorem cspF_Act_prefix_delay_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {a : α} {Pf : β → proc p α}
    {M : p → domFType α} :
    eqF (Rep_int_choice_f f X fun x => a ~> Pf x) M M
      (procIte (X = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_f f X Pf)) := by
  cspF_auto

theorem cspF_Ext_pre_choice_delay_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set α} {Y : Set β} {Pf : β → α → proc p α}
    {M : p → domFType α} :
    eqF (Rep_int_choice_f f Y fun y => proc.Ext_pre_choice X (Pf y)) M M
      (procIte (Y = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_f f Y fun y => Pf y x)) := by
  cspF_auto

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

theorem cspF_Alpha_Parallel_dist_l
    {P1 P2 Q : proc p α} {X Y : Set α} {M : p → domFType α} :
    eqF ((P1 |~| P2) |[X,Y]| Q) M M (((P1 |[X,Y]| Q)) |~| ((P2 |[X,Y]| Q))) := by
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_Parallel_dist_l cspF_reflex_eq_P)
  exact cspF_Parallel_dist_l

theorem cspF_Alpha_Parallel_dist_r
    {P Q1 Q2 : proc p α} {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| (Q1 |~| Q2)) M M (((P |[X,Y]| Q1)) |~| ((P |[X,Y]| Q2))) := by
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_reflex_eq_P cspF_Parallel_dist_l)
  exact cspF_Parallel_dist_r

theorem cspF_Alpha_Parallel_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (proc.Rep_int_choice C Pf |[X,Y]| Q) M M
        (proc.Rep_int_choice C fun c => Pf c |[X,Y]| Q) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl (cspF_Parallel_Dist_sum_l_nonempty h) cspF_reflex_eq_P)
  exact cspF_Parallel_Dist_sum_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (proc.Rep_int_choice C Pf |[X,Y]| Q) M M
      (procIte (sumset C = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (proc.Rep_int_choice C fun c => Pf c |[X,Y]| Q)) := by
  by_cases h : sumset C = ∅
  · simp only [procIte, if_pos h]
    exact cspF_Alpha_parallel_cong rfl rfl (cspF_Rep_int_choice_sum_DIV h) cspF_reflex_eq_P
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_sum_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    sumset C ≠ ∅ →
      eqF (P |[X,Y]| proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P |[X,Y]| Qf c) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_Parallel_Dist_sum_l_nonempty h))
  exact cspF_Parallel_Dist_sum_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P |[X,Y]| Qf c)) := by
  by_cases h : sumset C = ∅
  · simp only [procIte, if_pos h]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_reflex_eq_P (cspF_Rep_int_choice_sum_DIV h)
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_sum_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (Rep_int_choice_nat N Pf |[X,Y]| Q) M M
        (Rep_int_choice_nat N fun n => Pf n |[X,Y]| Q) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl (cspF_Parallel_Dist_nat_l_nonempty h) cspF_reflex_eq_P)
  exact cspF_Parallel_Dist_nat_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_nat N Pf |[X,Y]| Q) M M
      (procIte (N = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_nat N fun n => Pf n |[X,Y]| Q)) := by
  by_cases h : N = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_Rep_int_choice_nat_DIV cspF_reflex_eq_P
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_nat_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    N ≠ ∅ →
      eqF (P |[X,Y]| Rep_int_choice_nat N Qf) M M
        (Rep_int_choice_nat N fun n => P |[X,Y]| Qf n) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_Parallel_Dist_nat_l_nonempty h))
  exact cspF_Parallel_Dist_nat_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P |[X,Y]| Qf n)) := by
  by_cases h : N = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_reflex_eq_P cspF_Rep_int_choice_nat_DIV
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_nat_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    Xs ≠ ∅ →
      eqF (Rep_int_choice_set Xs Pf |[Y,Z]| Q) M M
        (Rep_int_choice_set Xs fun X => Pf X |[Y,Z]| Q) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl (cspF_Parallel_Dist_set_l_nonempty h) cspF_reflex_eq_P)
  exact cspF_Parallel_Dist_set_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_set Xs Pf |[Y,Z]| Q) M M
      (procIte (Xs = ∅) (((proc.DIV : proc p α) |[Y,Z]| Q))
        (Rep_int_choice_set Xs fun X => Pf X |[Y,Z]| Q)) := by
  by_cases h : Xs = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_Rep_int_choice_set_DIV cspF_reflex_eq_P
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_set_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    Xs ≠ ∅ →
      eqF (P |[Y,Z]| Rep_int_choice_set Xs Qf) M M
        (Rep_int_choice_set Xs fun X => P |[Y,Z]| Qf X) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_Parallel_Dist_set_l_nonempty h))
  exact cspF_Parallel_Dist_set_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α}
    {Y Z : Set α} {M : p → domFType α} :
    eqF (P |[Y,Z]| Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P |[Y,Z]| (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P |[Y,Z]| Qf X)) := by
  by_cases h : Xs = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_reflex_eq_P cspF_Rep_int_choice_set_DIV
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_set_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_com_l_nonempty [Inhabited α]
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (Rep_int_choice_com A Pf |[X,Y]| Q) M M
        (Rep_int_choice_com A fun x => Pf x |[X,Y]| Q) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl (cspF_Parallel_Dist_com_l_nonempty h) cspF_reflex_eq_P)
  exact cspF_Parallel_Dist_com_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_com_l [Inhabited α]
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_com A Pf |[X,Y]| Q) M M
      (procIte (A = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_com A fun x => Pf x |[X,Y]| Q)) := by
  by_cases h : A = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_Rep_int_choice_com_DIV cspF_reflex_eq_P
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_com_l_nonempty h

theorem cspF_Alpha_Parallel_Dist_com_r_nonempty [Inhabited α]
    {A : Set α} {Qf : α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (P |[X,Y]| Rep_int_choice_com A Qf) M M
        (Rep_int_choice_com A fun x => P |[X,Y]| Qf x) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_Parallel_Dist_com_l_nonempty h))
  exact cspF_Parallel_Dist_com_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_com_r [Inhabited α]
    {A : Set α} {Qf : α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| Rep_int_choice_com A Qf) M M
      (procIte (A = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_com A fun x => P |[X,Y]| Qf x)) := by
  by_cases h : A = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_reflex_eq_P cspF_Rep_int_choice_com_DIV
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_com_r_nonempty h

theorem cspF_Alpha_Parallel_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (Rep_int_choice_f f A Pf |[X,Y]| Q) M M
        (Rep_int_choice_f f A fun x => Pf x |[X,Y]| Q) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl (cspF_Parallel_Dist_f_l_nonempty hf h) cspF_reflex_eq_P)
  exact cspF_Parallel_Dist_f_l_nonempty hf h

theorem cspF_Alpha_Parallel_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (Rep_int_choice_f f A Pf |[X,Y]| Q) M M
      (procIte (A = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_f f A fun x => Pf x |[X,Y]| Q)) := by
  by_cases h : A = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl (cspF_Rep_int_choice_f_DIV hf) cspF_reflex_eq_P
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_f_l_nonempty hf h

theorem cspF_Alpha_Parallel_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Qf : β → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    A ≠ ∅ →
      eqF (P |[X,Y]| Rep_int_choice_f f A Qf) M M
        (Rep_int_choice_f f A fun x => P |[X,Y]| Qf x) := by
  intro h
  simp only [Alpha_parallel_def]
  apply cspF_trans_left_eq
    (cspF_Parallel_cong rfl cspF_reflex_eq_P (cspF_Parallel_Dist_f_l_nonempty hf h))
  exact cspF_Parallel_Dist_f_r_nonempty hf h

theorem cspF_Alpha_Parallel_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Qf : β → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domFType α} :
    eqF (P |[X,Y]| Rep_int_choice_f f A Qf) M M
      (procIte (A = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_f f A fun x => P |[X,Y]| Qf x)) := by
  by_cases h : A = ∅
  · subst h
    simp only [procIte]
    exact cspF_Alpha_parallel_cong rfl rfl cspF_reflex_eq_P (cspF_Rep_int_choice_f_DIV hf)
  · simp only [procIte, if_neg h]
    exact cspF_Alpha_Parallel_Dist_f_r_nonempty hf h

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
