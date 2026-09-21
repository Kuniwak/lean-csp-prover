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

import LeanCspProver.CSP_T.CSP_T_law_basic
import LeanCspProver.CSP_T.CSP_T_law_alpha_par
import LeanCspProver.CSP_T.CSP_T_simp

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

theorem cspT_Ext_choice_dist_l {P1 P2 Q : proc p α} {M : p → domTType α} :
    eqT ((P1 |~| P2) [+] Q) M M ((P1 [+] Q) |~| (P2 [+] Q)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice, in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Ext_choice_dist_r {P Q1 Q2 : proc p α} {M : p → domTType α} :
    eqT (P [+] (Q1 |~| Q2)) M M ((P [+] Q1) |~| (P [+] Q2)) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm <;>
    · rw [subdomT_iff]; intro t ht
      simp only [in_traces_Ext_choice, in_traces_Int_choice] at ht ⊢; tauto

theorem cspT_Parallel_dist_l {P1 P2 Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT ((P1 |~| P2) |[X]| Q) M M ((P1 |[X]| Q) |~| (P2 |[X]| Q)) := by
  cspT_auto

theorem cspT_Parallel_dist_r {P Q1 Q2 : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| (Q1 |~| Q2)) M M ((P |[X]| Q1) |~| (P |[X]| Q2)) := by
  cspT_auto

theorem cspT_Hiding_dist {P1 P2 : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (P1 |~| P2) X) M M ((proc.Hiding P1 X) |~| (proc.Hiding P2 X)) := by
  cspT_auto

theorem cspT_Renaming_dist {P1 P2 : proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((P1 |~| P2)[[r]]) M M ((P1[[r]]) |~| (P2[[r]])) := by
  cspT_auto

theorem cspT_Seq_compo_dist {P1 P2 Q : proc p α} {M : p → domTType α} :
    eqT ((P1 |~| P2) ;; Q) M M ((P1 ;; Q) |~| (P2 ;; Q)) := by
  cspT_auto

theorem cspT_Depth_rest_dist {P1 P2 : proc p α} {n : Nat} {M : p → domTType α} :
    eqT ((P1 |~| P2) |. n) M M ((P1 |. n) |~| (P2 |. n)) := by
  cspT_auto

theorem cspT_Rep_int_choice_sum_dist
    {C : sets_nats α} {Pf Qf : aset_anat α → proc p α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice C (fun c => Pf c |~| Qf c)) M M
      ((proc.Rep_int_choice C Pf) |~| (proc.Rep_int_choice C Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_dist
    {N : Set Nat} {Pf Qf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N (fun n => Pf n |~| Qf n)) M M
      ((Rep_int_choice_nat N Pf) |~| (Rep_int_choice_nat N Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_dist
    {Xs : Set (Set α)} {Pf Qf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs (fun X => Pf X |~| Qf X)) M M
      ((Rep_int_choice_set Xs Pf) |~| (Rep_int_choice_set Xs Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_com_dist [Inhabited α]
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com X (fun a => Pf a |~| Qf a)) M M
      ((Rep_int_choice_com X Pf) |~| (Rep_int_choice_com X Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_f_dist [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf Qf : β → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f X (fun a => Pf a |~| Qf a)) M M
      ((Rep_int_choice_f f X Pf) |~| (Rep_int_choice_f f X Qf)) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Rep_int_choice_dist` is represented by
   `cspT_Rep_int_choice_sum_dist`, `cspT_Rep_int_choice_nat_dist`,
   `cspT_Rep_int_choice_set_dist`, `cspT_Rep_int_choice_com_dist`, and
   `cspT_Rep_int_choice_f_dist`. -/

/- The Isabelle theorem bundle `cspT_dist` is represented by
   `cspT_Ext_choice_dist_l`, `cspT_Ext_choice_dist_r`,
   `cspT_Parallel_dist_l`, `cspT_Parallel_dist_r`, `cspT_Hiding_dist`,
   `cspT_Renaming_dist`, `cspT_Seq_compo_dist`, `cspT_Depth_rest_dist`,
   and `cspT_Rep_int_choice_dist`. -/

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

theorem cspT_Ext_choice_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT ((proc.Rep_int_choice C Pf) [+] Q) M M
        (proc.Rep_int_choice C fun c => Pf c [+] Q) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((proc.Rep_int_choice C Pf) [+] Q) M M
      (procIte (sumset C = ∅) ((proc.DIV : proc p α) [+] Q)
        (proc.Rep_int_choice C fun c => Pf c [+] Q)) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (P [+] proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P [+] Qf c) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT (P [+] proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P [+] (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P [+] Qf c)) := by
  cspT_auto

theorem cspT_Parallel_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (proc.Rep_int_choice C Pf |[X]| Q) M M
        (proc.Rep_int_choice C fun c => Pf c |[X]| Q) := by
  cspT_auto

theorem cspT_Parallel_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice C Pf |[X]| Q) M M
      (procIte (sumset C = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (proc.Rep_int_choice C fun c => Pf c |[X]| Q)) := by
  cspT_auto

theorem cspT_Parallel_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X : Set α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (P |[X]| proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P |[X]| Qf c) := by
  cspT_auto

theorem cspT_Parallel_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P |[X]| (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P |[X]| Qf c)) := by
  cspT_auto

theorem cspT_Hiding_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {X : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (proc.Rep_int_choice C Pf) X) M M
      (proc.Rep_int_choice C fun c => proc.Hiding (Pf c) X) := by
  cspT_auto

theorem cspT_Renaming_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((proc.Rep_int_choice C Pf)[[r]]) M M
      (proc.Rep_int_choice C fun c => (Pf c)[[r]]) := by
  cspT_auto

theorem cspT_Seq_compo_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((proc.Rep_int_choice C Pf) ;; Q) M M
      (proc.Rep_int_choice C fun c => Pf c ;; Q) := by
  cspT_auto

theorem cspT_Depth_rest_Dist_sum
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {m : Nat} {M : p → domTType α} :
    eqT ((proc.Rep_int_choice C Pf) |. m) M M
      (proc.Rep_int_choice C fun c => Pf c |. m) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Dist_sum` is represented by
   `cspT_Ext_choice_Dist_sum_l`, `cspT_Ext_choice_Dist_sum_r`,
   `cspT_Parallel_Dist_sum_l`, `cspT_Parallel_Dist_sum_r`,
   `cspT_Hiding_Dist_sum`, `cspT_Renaming_Dist_sum`,
   `cspT_Seq_compo_Dist_sum`, and `cspT_Depth_rest_Dist_sum`. -/

/- The Isabelle theorem bundle `cspT_Dist_sum_nonempty` is represented by
   `cspT_Ext_choice_Dist_sum_l_nonempty`,
   `cspT_Ext_choice_Dist_sum_r_nonempty`,
   `cspT_Parallel_Dist_sum_l_nonempty`,
   `cspT_Parallel_Dist_sum_r_nonempty`, `cspT_Hiding_Dist_sum`,
   `cspT_Renaming_Dist_sum`, `cspT_Seq_compo_Dist_sum`, and
   `cspT_Depth_rest_Dist_sum`. -/

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

theorem cspT_Ext_choice_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domTType α} :
    N ≠ ∅ → eqT ((Rep_int_choice_nat N Pf) [+] Q) M M
      (Rep_int_choice_nat N fun n => Pf n [+] Q) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_nat N Pf) [+] Q) M M
      (procIte (N = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_nat N fun n => Pf n [+] Q)) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {M : p → domTType α} :
    N ≠ ∅ → eqT (P [+] Rep_int_choice_nat N Qf) M M
      (Rep_int_choice_nat N fun n => P [+] Qf n) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT (P [+] Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P [+] Qf n)) := by
  cspT_auto

theorem cspT_Parallel_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {X : Set α} {M : p → domTType α} :
    N ≠ ∅ → eqT (Rep_int_choice_nat N Pf |[X]| Q) M M
      (Rep_int_choice_nat N fun n => Pf n |[X]| Q) := by
  cspT_auto

theorem cspT_Parallel_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N Pf |[X]| Q) M M
      (procIte (N = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_nat N fun n => Pf n |[X]| Q)) := by
  cspT_auto

theorem cspT_Parallel_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    N ≠ ∅ → eqT (P |[X]| Rep_int_choice_nat N Qf) M M
      (Rep_int_choice_nat N fun n => P |[X]| Qf n) := by
  cspT_auto

theorem cspT_Parallel_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P |[X]| Qf n)) := by
  cspT_auto

theorem cspT_Hiding_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {X : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (Rep_int_choice_nat N Pf) X) M M
      (Rep_int_choice_nat N fun n => proc.Hiding (Pf n) X) := by
  cspT_auto

theorem cspT_Renaming_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((Rep_int_choice_nat N Pf)[[r]]) M M
      (Rep_int_choice_nat N fun n => (Pf n)[[r]]) := by
  cspT_auto

theorem cspT_Seq_compo_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_nat N Pf) ;; Q) M M
      (Rep_int_choice_nat N fun n => Pf n ;; Q) := by
  cspT_auto

theorem cspT_Depth_rest_Dist_nat
    {N : Set Nat} {Pf : Nat → proc p α} {m : Nat} {M : p → domTType α} :
    eqT ((Rep_int_choice_nat N Pf) |. m) M M
      (Rep_int_choice_nat N fun n => Pf n |. m) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Dist_nat` is represented by
   `cspT_Ext_choice_Dist_nat_l`, `cspT_Ext_choice_Dist_nat_r`,
   `cspT_Parallel_Dist_nat_l`, `cspT_Parallel_Dist_nat_r`,
   `cspT_Hiding_Dist_nat`, `cspT_Renaming_Dist_nat`,
   `cspT_Seq_compo_Dist_nat`, and `cspT_Depth_rest_Dist_nat`. -/

/- The Isabelle theorem bundle `cspT_Dist_nat_nonempty` is represented by
   `cspT_Ext_choice_Dist_nat_l_nonempty`,
   `cspT_Ext_choice_Dist_nat_r_nonempty`,
   `cspT_Parallel_Dist_nat_l_nonempty`,
   `cspT_Parallel_Dist_nat_r_nonempty`, `cspT_Hiding_Dist_nat`,
   `cspT_Renaming_Dist_nat`, `cspT_Seq_compo_Dist_nat`, and
   `cspT_Depth_rest_Dist_nat`. -/

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

theorem cspT_Ext_choice_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domTType α} :
    Xs ≠ ∅ → eqT ((Rep_int_choice_set Xs Pf) [+] Q) M M
      (Rep_int_choice_set Xs fun X => Pf X [+] Q) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_set Xs Pf) [+] Q) M M
      (procIte (Xs = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_set Xs fun X => Pf X [+] Q)) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {M : p → domTType α} :
    Xs ≠ ∅ → eqT (P [+] Rep_int_choice_set Xs Qf) M M
      (Rep_int_choice_set Xs fun X => P [+] Qf X) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT (P [+] Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P [+] Qf X)) := by
  cspT_auto

theorem cspT_Parallel_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {Y : Set α} {M : p → domTType α} :
    Xs ≠ ∅ → eqT (Rep_int_choice_set Xs Pf |[Y]| Q) M M
      (Rep_int_choice_set Xs fun X => Pf X |[Y]| Q) := by
  cspT_auto

theorem cspT_Parallel_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {Y : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs Pf |[Y]| Q) M M
      (procIte (Xs = ∅) (((proc.DIV : proc p α) |[Y]| Q))
        (Rep_int_choice_set Xs fun X => Pf X |[Y]| Q)) := by
  cspT_auto

theorem cspT_Parallel_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {Y : Set α} {M : p → domTType α} :
    Xs ≠ ∅ → eqT (P |[Y]| Rep_int_choice_set Xs Qf) M M
      (Rep_int_choice_set Xs fun X => P |[Y]| Qf X) := by
  cspT_auto

theorem cspT_Parallel_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α} {Y : Set α} {M : p → domTType α} :
    eqT (P |[Y]| Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P |[Y]| (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P |[Y]| Qf X)) := by
  cspT_auto

theorem cspT_Hiding_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Y : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (Rep_int_choice_set Xs Pf) Y) M M
      (Rep_int_choice_set Xs fun X => proc.Hiding (Pf X) Y) := by
  cspT_auto

theorem cspT_Renaming_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((Rep_int_choice_set Xs Pf)[[r]]) M M
      (Rep_int_choice_set Xs fun X => (Pf X)[[r]]) := by
  cspT_auto

theorem cspT_Seq_compo_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_set Xs Pf) ;; Q) M M
      (Rep_int_choice_set Xs fun X => Pf X ;; Q) := by
  cspT_auto

theorem cspT_Depth_rest_Dist_set
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {m : Nat} {M : p → domTType α} :
    eqT ((Rep_int_choice_set Xs Pf) |. m) M M
      (Rep_int_choice_set Xs fun X => Pf X |. m) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Dist_set` is represented by
   `cspT_Ext_choice_Dist_set_l`, `cspT_Ext_choice_Dist_set_r`,
   `cspT_Parallel_Dist_set_l`, `cspT_Parallel_Dist_set_r`,
   `cspT_Hiding_Dist_set`, `cspT_Renaming_Dist_set`,
   `cspT_Seq_compo_Dist_set`, and `cspT_Depth_rest_Dist_set`. -/

/- The Isabelle theorem bundle `cspT_Dist_set_nonempty` is represented by
   `cspT_Ext_choice_Dist_set_l_nonempty`,
   `cspT_Ext_choice_Dist_set_r_nonempty`,
   `cspT_Parallel_Dist_set_l_nonempty`,
   `cspT_Parallel_Dist_set_r_nonempty`, `cspT_Hiding_Dist_set`,
   `cspT_Renaming_Dist_set`, `cspT_Seq_compo_Dist_set`, and
   `cspT_Depth_rest_Dist_set`. -/

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

theorem cspT_Ext_choice_Dist_com_l_nonempty [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    X ≠ ∅ → eqT ((Rep_int_choice_com X Pf) [+] Q) M M
      (Rep_int_choice_com X fun x => Pf x [+] Q) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_com_r_nonempty [Inhabited α]
    {X : Set α} {Qf : α → proc p α} {P : proc p α} {M : p → domTType α} :
    X ≠ ∅ → eqT (P [+] Rep_int_choice_com X Qf) M M
      (Rep_int_choice_com X fun x => P [+] Qf x) := by
  cspT_auto

theorem cspT_Parallel_Dist_com_l_nonempty [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {Q : proc p α} {X : Set α} {M : p → domTType α} :
    Y ≠ ∅ → eqT (Rep_int_choice_com Y Pf |[X]| Q) M M
      (Rep_int_choice_com Y fun x => Pf x |[X]| Q) := by
  cspT_auto

theorem cspT_Parallel_Dist_com_r_nonempty [Inhabited α]
    {Y : Set α} {Qf : α → proc p α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    Y ≠ ∅ → eqT (P |[X]| Rep_int_choice_com Y Qf) M M
      (Rep_int_choice_com Y fun x => P |[X]| Qf x) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_com_l [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_com X Pf) [+] Q) M M
      (procIte (X = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_com X fun x => Pf x [+] Q)) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_com_r [Inhabited α]
    {X : Set α} {Qf : α → proc p α} {P : proc p α} {M : p → domTType α} :
    eqT (P [+] Rep_int_choice_com X Qf) M M
      (procIte (X = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_com X fun x => P [+] Qf x)) := by
  cspT_auto

theorem cspT_Parallel_Dist_com_l [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_com Y Pf |[X]| Q) M M
      (procIte (Y = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_com Y fun x => Pf x |[X]| Q)) := by
  cspT_auto

theorem cspT_Parallel_Dist_com_r [Inhabited α]
    {Y : Set α} {Qf : α → proc p α} {P : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| Rep_int_choice_com Y Qf) M M
      (procIte (Y = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_com Y fun x => P |[X]| Qf x)) := by
  cspT_auto

theorem cspT_Hiding_Dist_com [Inhabited α]
    {Y : Set α} {Pf : α → proc p α} {X : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (Rep_int_choice_com Y Pf) X) M M
      (Rep_int_choice_com Y fun x => proc.Hiding (Pf x) X) := by
  cspT_auto

theorem cspT_Renaming_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((Rep_int_choice_com X Pf)[[r]]) M M
      (Rep_int_choice_com X fun x => (Pf x)[[r]]) := by
  cspT_auto

theorem cspT_Seq_compo_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_com X Pf) ;; Q) M M
      (Rep_int_choice_com X fun x => Pf x ;; Q) := by
  cspT_auto

theorem cspT_Depth_rest_Dist_com [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {n : Nat} {M : p → domTType α} :
    eqT ((Rep_int_choice_com X Pf) |. n) M M
      (Rep_int_choice_com X fun x => Pf x |. n) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Dist_com` is represented by
   `cspT_Ext_choice_Dist_com_l`, `cspT_Ext_choice_Dist_com_r`,
   `cspT_Parallel_Dist_com_l`, `cspT_Parallel_Dist_com_r`,
   `cspT_Hiding_Dist_com`, `cspT_Renaming_Dist_com`,
   `cspT_Seq_compo_Dist_com`, and `cspT_Depth_rest_Dist_com`. -/

/- The Isabelle theorem bundle `cspT_Dist_com_nonempty` is represented by
   `cspT_Ext_choice_Dist_com_l_nonempty`,
   `cspT_Ext_choice_Dist_com_r_nonempty`,
   `cspT_Parallel_Dist_com_l_nonempty`,
   `cspT_Parallel_Dist_com_r_nonempty`, `cspT_Hiding_Dist_com`,
   `cspT_Renaming_Dist_com`, `cspT_Seq_compo_Dist_com`, and
   `cspT_Depth_rest_Dist_com`. -/

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

theorem cspT_Ext_choice_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domTType α} :
    X ≠ ∅ → eqT ((Rep_int_choice_f f X Pf) [+] Q) M M
      (Rep_int_choice_f f X fun x => Pf x [+] Q) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Qf : β → proc p α} {P : proc p α}
    {M : p → domTType α} :
    X ≠ ∅ → eqT (P [+] Rep_int_choice_f f X Qf) M M
      (Rep_int_choice_f f X fun x => P [+] Qf x) := by
  cspT_auto

theorem cspT_Parallel_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domTType α} :
    Y ≠ ∅ → eqT (Rep_int_choice_f f Y Pf |[X]| Q) M M
      (Rep_int_choice_f f Y fun x => Pf x |[X]| Q) := by
  cspT_auto

theorem cspT_Parallel_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Qf : β → proc p α} {P : proc p α}
    {X : Set α} {M : p → domTType α} :
    Y ≠ ∅ → eqT (P |[X]| Rep_int_choice_f f Y Qf) M M
      (Rep_int_choice_f f Y fun x => P |[X]| Qf x) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domTType α} :
    eqT ((Rep_int_choice_f f X Pf) [+] Q) M M
      (procIte (X = ∅) ((proc.DIV : proc p α) [+] Q)
        (Rep_int_choice_f f X fun x => Pf x [+] Q)) := by
  cspT_auto

theorem cspT_Ext_choice_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Qf : β → proc p α} {P : proc p α}
    {M : p → domTType α} :
    eqT (P [+] Rep_int_choice_f f X Qf) M M
      (procIte (X = ∅) (P [+] (proc.DIV : proc p α))
        (Rep_int_choice_f f X fun x => P [+] Qf x)) := by
  cspT_auto

theorem cspT_Parallel_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f Y Pf |[X]| Q) M M
      (procIte (Y = ∅) (((proc.DIV : proc p α) |[X]| Q))
        (Rep_int_choice_f f Y fun x => Pf x |[X]| Q)) := by
  cspT_auto

theorem cspT_Parallel_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Qf : β → proc p α} {P : proc p α}
    {X : Set α} {M : p → domTType α} :
    eqT (P |[X]| Rep_int_choice_f f Y Qf) M M
      (procIte (Y = ∅) (P |[X]| (proc.DIV : proc p α))
        (Rep_int_choice_f f Y fun x => P |[X]| Qf x)) := by
  cspT_auto

theorem cspT_Hiding_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {Y : Set β} {Pf : β → proc p α} {X : Set α}
    {M : p → domTType α} :
    eqT (proc.Hiding (Rep_int_choice_f f Y Pf) X) M M
      (Rep_int_choice_f f Y fun x => proc.Hiding (Pf x) X) := by
  cspT_auto

theorem cspT_Renaming_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {r : Set (α × α)}
    {M : p → domTType α} :
    eqT ((Rep_int_choice_f f X Pf)[[r]]) M M
      (Rep_int_choice_f f X fun x => (Pf x)[[r]]) := by
  cspT_auto

theorem cspT_Seq_compo_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {Q : proc p α}
    {M : p → domTType α} :
    eqT ((Rep_int_choice_f f X Pf) ;; Q) M M
      (Rep_int_choice_f f X fun x => Pf x ;; Q) := by
  cspT_auto

theorem cspT_Depth_rest_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf : β → proc p α} {n : Nat}
    {M : p → domTType α} :
    eqT ((Rep_int_choice_f f X Pf) |. n) M M
      (Rep_int_choice_f f X fun x => Pf x |. n) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Dist_f` is represented by
   `cspT_Ext_choice_Dist_f_l`, `cspT_Ext_choice_Dist_f_r`,
   `cspT_Parallel_Dist_f_l`, `cspT_Parallel_Dist_f_r`,
   `cspT_Hiding_Dist_f`, `cspT_Renaming_Dist_f`,
   `cspT_Seq_compo_Dist_f`, and `cspT_Depth_rest_Dist_f`. -/

/- The Isabelle theorem bundle `cspT_Dist_f_nonempty` is represented by
   `cspT_Ext_choice_Dist_f_l_nonempty`,
   `cspT_Ext_choice_Dist_f_r_nonempty`,
   `cspT_Parallel_Dist_f_l_nonempty`,
   `cspT_Parallel_Dist_f_r_nonempty`, `cspT_Hiding_Dist_f`,
   `cspT_Renaming_Dist_f`, `cspT_Seq_compo_Dist_f`, and
   `cspT_Depth_rest_Dist_f`. -/

/- The Isabelle theorem bundle `cspT_Dist` is represented by
   `cspT_Dist_sum`, `cspT_Dist_nat`, `cspT_Dist_set`, `cspT_Dist_com`,
   and `cspT_Dist_f`. -/

/- The Isabelle theorem bundle `cspT_Dist_nonempty` is represented by
   `cspT_Dist_sum_nonempty`, `cspT_Dist_nat_nonempty`,
   `cspT_Dist_set_nonempty`, `cspT_Dist_com_nonempty`, and
   `cspT_Dist_f_nonempty`. -/

/-
(*****************************************************************

      additional distribution over replicated internal choice

         1. (!! :X .. (a -> P))
         2. (!! :Y .. (? :X -> P))

 *****************************************************************)
-/

theorem cspT_Act_prefix_Dist_sum
    {C : sets_nats α} {a : α} {Pf : aset_anat α → proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (a ~> proc.Rep_int_choice C Pf) M M
        (proc.Rep_int_choice C fun c => a ~> Pf c) := by
  cspT_auto

theorem cspT_Ext_pre_choice_Dist_sum
    {C : sets_nats α} {X : Set α} {Pf : aset_anat α → α → proc p α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (proc.Ext_pre_choice X fun x => proc.Rep_int_choice C fun c => Pf c x) M M
        (proc.Rep_int_choice C fun c => proc.Ext_pre_choice X (Pf c)) := by
  cspT_auto

theorem cspT_Act_prefix_Dist_nat
    {N : Set Nat} {a : α} {Pf : Nat → proc p α} {M : p → domTType α} :
    N ≠ ∅ →
      eqT (a ~> Rep_int_choice_nat N Pf) M M
        (Rep_int_choice_nat N fun n => a ~> Pf n) := by
  cspT_auto

theorem cspT_Ext_pre_choice_Dist_nat
    {N : Set Nat} {X : Set α} {Pf : Nat → α → proc p α} {M : p → domTType α} :
    N ≠ ∅ →
      eqT (proc.Ext_pre_choice X fun x => Rep_int_choice_nat N fun n => Pf n x) M M
        (Rep_int_choice_nat N fun n => proc.Ext_pre_choice X (Pf n)) := by
  cspT_auto

theorem cspT_Act_prefix_Dist_set
    {Xs : Set (Set α)} {a : α} {Pf : Set α → proc p α} {M : p → domTType α} :
    Xs ≠ ∅ →
      eqT (a ~> Rep_int_choice_set Xs Pf) M M
        (Rep_int_choice_set Xs fun X => a ~> Pf X) := by
  cspT_auto

theorem cspT_Ext_pre_choice_Dist_set
    {X : Set α} {Ys : Set (Set α)} {Pf : Set α → α → proc p α} {M : p → domTType α} :
    Ys ≠ ∅ →
      eqT (proc.Ext_pre_choice X fun x => Rep_int_choice_set Ys fun Y => Pf Y x) M M
        (Rep_int_choice_set Ys fun Y => proc.Ext_pre_choice X (Pf Y)) := by
  cspT_auto

theorem cspT_Act_prefix_Dist_com [Inhabited α]
    {X : Set α} {a : α} {Pf : α → proc p α} {M : p → domTType α} :
    X ≠ ∅ →
      eqT (a ~> Rep_int_choice_com X Pf) M M
        (Rep_int_choice_com X fun x => a ~> Pf x) := by
  cspT_auto

theorem cspT_Ext_pre_choice_Dist_com [Inhabited α]
    {X Y : Set α} {Pf : α → α → proc p α} {M : p → domTType α} :
    Y ≠ ∅ →
      eqT (proc.Ext_pre_choice X fun x => Rep_int_choice_com Y fun y => Pf y x) M M
        (Rep_int_choice_com Y fun y => proc.Ext_pre_choice X (Pf y)) := by
  cspT_auto

theorem cspT_Act_prefix_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {a : α} {Pf : β → proc p α}
    {M : p → domTType α} :
    X ≠ ∅ →
      eqT (a ~> Rep_int_choice_f f X Pf) M M
        (Rep_int_choice_f f X fun x => a ~> Pf x) := by
  cspT_auto

theorem cspT_Ext_pre_choice_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set α} {Y : Set β} {Pf : β → α → proc p α}
    {M : p → domTType α} :
    Y ≠ ∅ →
      eqT (proc.Ext_pre_choice X fun x => Rep_int_choice_f f Y fun y => Pf y x) M M
        (Rep_int_choice_f f Y fun y => proc.Ext_pre_choice X (Pf y)) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Act_prefix_Dist` is represented by
   `cspT_Act_prefix_Dist_sum`, `cspT_Act_prefix_Dist_nat`,
   `cspT_Act_prefix_Dist_set`, `cspT_Act_prefix_Dist_com`, and
   `cspT_Act_prefix_Dist_f`. -/

/- The Isabelle theorem bundle `cspT_Ext_pre_choice_Dist` is represented by
   `cspT_Ext_pre_choice_Dist_sum`, `cspT_Ext_pre_choice_Dist_nat`,
   `cspT_Ext_pre_choice_Dist_set`, `cspT_Ext_pre_choice_Dist_com`, and
   `cspT_Ext_pre_choice_Dist_f`. -/

/-
(*****************************************************************
      distribution over external choice
         1. (P1 [+] P2) [[r]]
         2. (P1 [+] P2) |. n
 *****************************************************************)
-/

theorem cspT_Renaming_Ext_dist
    {P1 P2 : proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((P1 [+] P2)[[r]]) M M ((P1[[r]]) [+] (P2[[r]])) := by
  cspT_auto

theorem cspT_Depth_rest_Ext_dist
    {P1 P2 : proc p α} {n : Nat} {M : p → domTType α} :
    eqT ((P1 [+] P2) |. n) M M ((P1 |. n) [+] (P2 |. n)) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Ext_dist` is represented by
   `cspT_Renaming_Ext_dist` and `cspT_Depth_rest_Ext_dist`. -/

/-
(*---------------------------------------------------------*
 |                   complex distribution                  |
 *---------------------------------------------------------*)
-/

theorem cspT_Rep_int_choice_sum_input_set
    {C : sets_nats α} {Yf : aset_anat α → Set α} {Rff : aset_anat α → α → proc p α}
    {M : p → domTType α} :
    eqT (proc.Rep_int_choice C fun c => proc.Ext_pre_choice (Yf c) (Rff c)) M M
      (Rep_int_choice_set (Yf '' sumset C) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          proc.Rep_int_choice C fun c =>
            procIte (a ∈ Yf c) (Rff c a) (proc.DIV : proc p α)) := by
  cspT_auto

theorem cspT_Rep_int_choice_nat_input_set
    {N : Set Nat} {Yf : Nat → Set α} {Rff : Nat → α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N fun n => proc.Ext_pre_choice (Yf n) (Rff n)) M M
      (Rep_int_choice_set (Yf '' N) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ a ∈ Yf n} fun n => Rff n a) := by
  cspT_auto

theorem cspT_Rep_int_choice_set_input_set
    {Xs : Set (Set α)} {Yf : Set α → Set α} {Rff : Set α → α → proc p α}
    {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs fun X => proc.Ext_pre_choice (Yf X) (Rff X)) M M
      (Rep_int_choice_set (Yf '' Xs) fun Y =>
        proc.Ext_pre_choice Y fun a =>
          Rep_int_choice_set {X | X ∈ Xs ∧ a ∈ Yf X} fun X => Rff X a) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Rep_int_choice_input_set` is
   represented by `cspT_Rep_int_choice_sum_input_set`,
   `cspT_Rep_int_choice_nat_input_set`, and
   `cspT_Rep_int_choice_set_input_set`. -/

theorem cspT_Rep_int_choice_Ext_Dist_sum
    {C : sets_nats α} {Pf Qf : aset_anat α → proc p α} {M : p → domTType α} :
    (∀ c, c ∈ sumset C → Qf c = proc.SKIP ∨ Qf c = proc.DIV) →
      eqT (proc.Rep_int_choice C fun c => Pf c [+] Qf c) M M
        ((proc.Rep_int_choice C Pf) [+] (proc.Rep_int_choice C Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_Ext_Dist_nat
    {N : Set Nat} {Pf Qf : Nat → proc p α} {M : p → domTType α} :
    (∀ n, n ∈ N → Qf n = proc.SKIP ∨ Qf n = proc.DIV) →
      eqT (Rep_int_choice_nat N fun n => Pf n [+] Qf n) M M
        ((Rep_int_choice_nat N Pf) [+] (Rep_int_choice_nat N Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_Ext_Dist_set
    {Xs : Set (Set α)} {Pf Qf : Set α → proc p α} {M : p → domTType α} :
    (∀ X, X ∈ Xs → Qf X = proc.SKIP ∨ Qf X = proc.DIV) →
      eqT (Rep_int_choice_set Xs fun X => Pf X [+] Qf X) M M
        ((Rep_int_choice_set Xs Pf) [+] (Rep_int_choice_set Xs Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_Ext_Dist_com [Inhabited α]
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    (∀ a, a ∈ X → Qf a = proc.SKIP ∨ Qf a = proc.DIV) →
      eqT (Rep_int_choice_com X fun a => Pf a [+] Qf a) M M
        ((Rep_int_choice_com X Pf) [+] (Rep_int_choice_com X Qf)) := by
  cspT_auto

theorem cspT_Rep_int_choice_Ext_Dist_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {Pf Qf : β → proc p α} {M : p → domTType α} :
    (∀ a, a ∈ X → Qf a = proc.SKIP ∨ Qf a = proc.DIV) →
      eqT (Rep_int_choice_f f X fun a => Pf a [+] Qf a) M M
        ((Rep_int_choice_f f X Pf) [+] (Rep_int_choice_f f X Qf)) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_Rep_int_choice_Ext_Dist` is
   represented by `cspT_Rep_int_choice_Ext_Dist_sum`,
   `cspT_Rep_int_choice_Ext_Dist_nat`,
   `cspT_Rep_int_choice_Ext_Dist_set`,
   `cspT_Rep_int_choice_Ext_Dist_com`, and
   `cspT_Rep_int_choice_Ext_Dist_f`. -/

theorem cspT_Rep_int_choice_input
    {Xs : Set (Set α)} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) M M
      (proc.Ext_pre_choice (Set.sUnion Xs) Pf) := by
  cspT_auto

theorem cspT_Rep_int_choice_input_Dist
    {Xs : Set (Set α)} {Pf : α → proc p α} {Q : proc p α} {M : p → domTType α} :
    eqT ((Rep_int_choice_set Xs fun X => proc.Ext_pre_choice X Pf) [+] Q) M M
      ((proc.Ext_pre_choice (Set.sUnion Xs) Pf) [+] Q) := by
  cspT_auto

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 * =================================================== *)
-/

theorem cspT_Seq_compo_hide_dist
    {P Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (P ;; Q) X) M M ((proc.Hiding P X) ;; proc.Hiding Q X) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Hiding] at ht
    obtain ⟨s, rfl, hs⟩ := ht
    rw [in_traces_Seq_compo] at hs
    rw [in_traces_Seq_compo]
    rcases hs with ⟨s1, rfl, hs1⟩ | ⟨s1, t1, rfl, hs1, ht1, hno⟩
    · exact Or.inl ⟨hide_tr s1 X, rmTick_hide, in_traces_Hiding.mpr ⟨s1, rfl, hs1⟩⟩
    · refine Or.inr ⟨hide_tr s1 X, hide_tr t1 X, hide_tr_appt (Or.inl hno), ?_, ?_,
        hide_tr_noTick.mpr hno⟩
      · refine in_traces_Hiding.mpr
          ⟨(s1 ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α), ?_, hs1⟩
        rw [hide_tr_appt (Or.inl hno), hide_tr_Tick]
      · exact in_traces_Hiding.mpr ⟨t1, rfl, ht1⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Seq_compo] at ht
    rw [in_traces_Hiding]
    rcases ht with ⟨u, rfl, hu⟩ | ⟨u, v, rfl, hu, hv, hno⟩
    · rw [in_traces_Hiding] at hu
      obtain ⟨s, rfl, hs⟩ := hu
      rcases trace_last_noTick_or_Tick s with hsno | ⟨s', hs'no, rfl⟩
      · refine ⟨s, ?_, in_traces_Seq_compo.mpr (Or.inl ⟨s, (rmTick_nochange hsno).symm, hs⟩)⟩
        rw [rmTick_nochange (hide_tr_noTick.mpr hsno)]
      · refine ⟨s', ?_, in_traces_Seq_compo.mpr
          (Or.inl ⟨(s' ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α),
            (rmTick_last_Tick hs'no).symm, hs⟩)⟩
        rw [hide_tr_appt (Or.inl hs'no), hide_tr_Tick,
          rmTick_last_Tick (hide_tr_noTick.mpr hs'no)]
    · rw [in_traces_Hiding] at hu hv
      obtain ⟨s, hsEq, hs⟩ := hu
      obtain ⟨t', rfl, ht'⟩ := hv
      rcases trace_last_noTick_or_Tick s with hsno | ⟨s'', hs''no, rfl⟩
      · exfalso
        have hcontra : noTick (u ^^^ (Abs_trace [event.Tick] : traceType α)) := by
          rw [hsEq]
          exact hide_tr_noTick.mpr hsno
        exact not_noTick_Tick (decompo_appt_noTick_only_if (Or.inl hno) hcontra).2
      · rw [hide_tr_appt (Or.inl hs''no), hide_tr_Tick] at hsEq
        have hu' : u = hide_tr s'' X :=
          ((appt_same_last hno (hide_tr_noTick.mpr hs''no)).mp hsEq).1
        subst hu'
        refine ⟨(s'' ^^^ t' : traceType α), (hide_tr_appt (Or.inl hs''no)).symm, ?_⟩
        exact in_traces_Seq_compo.mpr (Or.inr ⟨s'', t', rfl, hs, ht', hs''no⟩)

theorem cspT_Interleave_hide_dist
    {P Q : proc p α} {X : Set α} {M : p → domTType α} :
    eqT (proc.Hiding (P |[(∅ : Set α)]| Q) X) M M
      ((proc.Hiding P X) |[(∅ : Set α)]| proc.Hiding Q X) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Hiding] at ht
    obtain ⟨w, rfl, hw⟩ := ht
    rw [in_traces_Parallel] at hw
    obtain ⟨s, t1, hpar, hs, ht1⟩ := hw
    rw [in_traces_Parallel]
    exact ⟨hide_tr s X, hide_tr t1 X, interleave_of_hide_tr hpar,
      in_traces_Hiding.mpr ⟨s, rfl, hs⟩, in_traces_Hiding.mpr ⟨t1, rfl, ht1⟩⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Parallel] at ht
    obtain ⟨s', t'', hpar, hs', ht''⟩ := ht
    rw [in_traces_Hiding] at hs' ht''
    obtain ⟨s, rfl, hs⟩ := hs'
    obtain ⟨t1, rfl, ht1⟩ := ht''
    obtain ⟨v, rfl, hv⟩ := interleave_of_hide_tr_ex.mp hpar
    rw [in_traces_Hiding]
    exact ⟨v, rfl, in_traces_Parallel.mpr ⟨s, t1, hv, hs, ht1⟩⟩

theorem cspT_Seq_compo_renaming_dist
    {P Q : proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT ((P ;; Q)[[r]]) M M ((P[[r]]) ;; (Q[[r]])) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Renaming] at ht
    obtain ⟨s, hren, hs⟩ := ht
    rw [in_traces_Seq_compo] at hs
    rw [in_traces_Seq_compo]
    rcases hs with ⟨s1, rfl, hs1⟩ | ⟨s1, t1, rfl, hs1, ht1, hno⟩
    · have hnoT : noTick t := ren_tr_noTick_left hren noTick_rmTick
      exact Or.inl ⟨t, (rmTick_nochange hnoT).symm,
        in_traces_Renaming.mpr ⟨rmTick s1, hren,
          memT_prefix_closed hs1 rmTick_prefix_rev_simp⟩⟩
    · obtain ⟨t1', t2', rfl, h1, h2, -⟩ := (ren_tr_appt_decompo_left (Or.inl hno)).mp hren
      refine Or.inr ⟨t1', t2', rfl, ?_, in_traces_Renaming.mpr ⟨t1, h2, ht1⟩,
        ren_tr_noTick_left h1 hno⟩
      exact in_traces_Renaming.mpr
        ⟨(s1 ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α),
          ren_tr_appt h1 ren_tr_Tick (Or.inl hno), hs1⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Seq_compo] at ht
    rw [in_traces_Renaming]
    rcases ht with ⟨u, rfl, hu⟩ | ⟨u, v, rfl, hu, hv, hno⟩
    · rw [in_traces_Renaming] at hu
      obtain ⟨s, hren, hs⟩ := hu
      rcases trace_last_noTick_or_Tick s with hsno | ⟨s', hs'no, rfl⟩
      · refine ⟨s, ?_, in_traces_Seq_compo.mpr (Or.inl ⟨s, (rmTick_nochange hsno).symm, hs⟩)⟩
        rw [rmTick_nochange (ren_tr_noTick_left hren hsno)]
        exact hren
      · obtain ⟨u1, u2, rfl, h1, h2, -⟩ := (ren_tr_appt_decompo_left (Or.inl hs'no)).mp hren
        have hu2 : u2 = (Abs_trace [event.Tick] : traceType α) := ren_tr_Tick1.mp h2
        subst hu2
        refine ⟨s', ?_, in_traces_Seq_compo.mpr
          (Or.inl ⟨(s' ^^^ (Abs_trace [event.Tick] : traceType α) : traceType α),
            (rmTick_last_Tick hs'no).symm, hs⟩)⟩
        rw [rmTick_last_Tick (ren_tr_noTick_left h1 hs'no)]
        exact h1
    · rw [in_traces_Renaming] at hu hv
      obtain ⟨s, hren, hs⟩ := hu
      obtain ⟨t1, htr, ht1⟩ := hv
      obtain ⟨s1, s2, rfl, h1, h2, -⟩ := (ren_tr_appt_decompo_right (Or.inl hno)).mp hren
      have hs2 : s2 = (Abs_trace [event.Tick] : traceType α) := ren_tr_Tick2.mp h2
      subst hs2
      have hs1no : noTick s1 := ren_tr_noTick_right h1 hno
      exact ⟨(s1 ^^^ t1 : traceType α), ren_tr_appt h1 htr (Or.inl hs1no),
        in_traces_Seq_compo.mpr (Or.inr ⟨s1, t1, rfl, hs, ht1, hs1no⟩)⟩

theorem cspT_Interleave_renaming_dist
    {P Q : proc p α} {r : Set (α × α)} {M : p → domTType α} :
    eqT (((P |[(∅ : Set α)]| Q))[[r]]) M M ((P[[r]]) |[(∅ : Set α)]| (Q[[r]])) := by
  rw [cspT_eqT_semantics]
  apply le_antisymm
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Renaming] at ht
    obtain ⟨w, hren, hw⟩ := ht
    rw [in_traces_Parallel] at hw
    obtain ⟨s, t1, hpar, hs, ht1⟩ := hw
    obtain ⟨s', t', hpar', hsr, htr⟩ := interleave_of_ren_tr_only_if hpar hren
    rw [in_traces_Parallel]
    exact ⟨s', t', hpar', in_traces_Renaming.mpr ⟨s, hsr, hs⟩,
      in_traces_Renaming.mpr ⟨t1, htr, ht1⟩⟩
  · rw [subdomT_iff]
    intro t ht
    rw [in_traces_Parallel] at ht
    obtain ⟨s', t', hpar, hs', ht'⟩ := ht
    rw [in_traces_Renaming] at hs' ht'
    obtain ⟨s, hsr, hs⟩ := hs'
    obtain ⟨t1, htr, ht1⟩ := ht'
    obtain ⟨u, hu, hur⟩ := interleave_of_ren_tr_if hpar hsr htr
    rw [in_traces_Renaming]
    exact ⟨u, hur, in_traces_Parallel.mpr ⟨s, t1, hu, hs, ht1⟩⟩

theorem cspT_Act_prefix_dist {a : α} {P Q : proc p α} {M : p → domTType α} :
    eqT (a ~> (P |~| Q)) M M ((a ~> P) |~| (a ~> Q)) := by
  rw [cspT_eqT_semantics]; apply le_antisymm
  · rw [subdomT_iff]; intro t ht
    simp only [in_traces_Act_prefix, in_traces_Int_choice] at ht ⊢
    rcases ht with rfl | ⟨s, hts, hs⟩
    · exact Or.inl (Or.inl rfl)
    · rcases hs with h | h
      · exact Or.inl (Or.inr ⟨s, hts, h⟩)
      · exact Or.inr (Or.inr ⟨s, hts, h⟩)
  · rw [subdomT_iff]; intro t ht
    simp only [in_traces_Act_prefix, in_traces_Int_choice] at ht ⊢
    rcases ht with (rfl | ⟨s, hts, h⟩) | (rfl | ⟨s, hts, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hts, Or.inl h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hts, Or.inr h⟩

theorem cspT_Int_choice_Act_prefix_delay {a : α} {P Q : proc p α} {M : p → domTType α} :
    eqT ((a ~> P) |~| (a ~> Q)) M M (a ~> (P |~| Q)) := by
  rw [cspT_eqT_semantics]; apply le_antisymm
  · rw [subdomT_iff]; intro t ht
    simp only [in_traces_Act_prefix, in_traces_Int_choice] at ht ⊢
    rcases ht with (rfl | ⟨s, hts, h⟩) | (rfl | ⟨s, hts, h⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hts, Or.inl h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨s, hts, Or.inr h⟩
  · rw [subdomT_iff]; intro t ht
    simp only [in_traces_Act_prefix, in_traces_Int_choice] at ht ⊢
    rcases ht with rfl | ⟨s, hts, hs⟩
    · exact Or.inl (Or.inl rfl)
    · rcases hs with h | h
      · exact Or.inl (Or.inr ⟨s, hts, h⟩)
      · exact Or.inr (Or.inr ⟨s, hts, h⟩)

theorem cspT_Int_choice_Act_prefix_delay_eq
    {a b : α} {P Q : proc p α} {M : p → domTType α} :
    a = b → eqT ((a ~> P) |~| (b ~> Q)) M M (a ~> (P |~| Q)) := by
  intro hab; subst hab; exact cspT_Int_choice_Act_prefix_delay

theorem cspT_Ext_pre_choice_dist
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) M M
      ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice X Qf)) := by
  cspT_auto

theorem cspT_Int_choice_Ext_pre_choice_delay
    {X : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    eqT ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice X Qf)) M M
      (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) := by
  cspT_auto

theorem cspT_Int_choice_Ext_pre_choice_delay_eq
    {X Y : Set α} {Pf Qf : α → proc p α} {M : p → domTType α} :
    X = Y →
      eqT ((proc.Ext_pre_choice X Pf) |~| (proc.Ext_pre_choice Y Qf)) M M
        (proc.Ext_pre_choice X fun x => Pf x |~| Qf x) := by
  cspT_auto

theorem cspT_Act_prefix_delay_sum
    {C : sets_nats α} {a : α} {Pf : aset_anat α → proc p α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice C fun c => a ~> Pf c) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α) (a ~> proc.Rep_int_choice C Pf)) := by
  cspT_auto

theorem cspT_Ext_pre_choice_delay_sum
    {C : sets_nats α} {X : Set α} {Pf : aset_anat α → α → proc p α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice C fun c => proc.Ext_pre_choice X (Pf c)) M M
      (procIte (sumset C = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => proc.Rep_int_choice C fun c => Pf c x)) := by
  cspT_auto

theorem cspT_Act_prefix_delay_nat
    {N : Set Nat} {a : α} {Pf : Nat → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N fun n => a ~> Pf n) M M
      (procIte (N = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_nat N Pf)) := by
  cspT_auto

theorem cspT_Ext_pre_choice_delay_nat
    {N : Set Nat} {X : Set α} {Pf : Nat → α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N fun n => proc.Ext_pre_choice X (Pf n)) M M
      (procIte (N = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_nat N fun n => Pf n x)) := by
  cspT_auto

theorem cspT_Act_prefix_delay_set
    {Xs : Set (Set α)} {a : α} {Pf : Set α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs fun X => a ~> Pf X) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_set Xs Pf)) := by
  cspT_auto

theorem cspT_Ext_pre_choice_delay_set
    {Xs : Set (Set α)} {X : Set α} {Pf : Set α → α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs fun Y => proc.Ext_pre_choice X (Pf Y)) M M
      (procIte (Xs = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_set Xs fun Y => Pf Y x)) := by
  cspT_auto

theorem cspT_Act_prefix_delay_com [Inhabited α]
    {X : Set α} {a : α} {Pf : α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com X fun x => a ~> Pf x) M M
      (procIte (X = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_com X Pf)) := by
  cspT_auto

theorem cspT_Ext_pre_choice_delay_com [Inhabited α]
    {X Y : Set α} {Pf : α → α → proc p α} {M : p → domTType α} :
    eqT (Rep_int_choice_com Y fun y => proc.Ext_pre_choice X (Pf y)) M M
      (procIte (Y = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_com Y fun y => Pf y x)) := by
  cspT_auto

theorem cspT_Act_prefix_delay_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set β} {a : α} {Pf : β → proc p α}
    {M : p → domTType α} :
    eqT (Rep_int_choice_f f X fun x => a ~> Pf x) M M
      (procIte (X = ∅) (proc.DIV : proc p α) (a ~> Rep_int_choice_f f X Pf)) := by
  cspT_auto

theorem cspT_Ext_pre_choice_delay_f [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {X : Set α} {Y : Set β} {Pf : β → α → proc p α}
    {M : p → domTType α} :
    eqT (Rep_int_choice_f f Y fun y => proc.Ext_pre_choice X (Pf y)) M M
      (procIte (Y = ∅) (proc.DIV : proc p α)
        (proc.Ext_pre_choice X fun x => Rep_int_choice_f f Y fun y => Pf y x)) := by
  cspT_auto

/- The Isabelle theorem bundle `cspT_choice_delay` is represented by
   `cspT_Int_choice_Act_prefix_delay`,
   `cspT_Int_choice_Ext_pre_choice_delay`, `cspT_Act_prefix_delay_sum`,
   `cspT_Ext_pre_choice_delay_sum`, `cspT_Act_prefix_delay_nat`,
   `cspT_Ext_pre_choice_delay_nat`, `cspT_Act_prefix_delay_set`,
   `cspT_Ext_pre_choice_delay_set`, `cspT_Act_prefix_delay_com`,
   `cspT_Ext_pre_choice_delay_com`, `cspT_Act_prefix_delay_f`, and
   `cspT_Ext_pre_choice_delay_f`. -/

/- The Isabelle theorem bundle `cspT_choice_delay_eq` is represented by
   `cspT_Int_choice_Act_prefix_delay_eq` and
   `cspT_Int_choice_Ext_pre_choice_delay_eq`. -/

/-
(*********************************************************
                       P |[X,Y]| Q
 *********************************************************)
-/

theorem cspT_Alpha_Parallel_dist_l
    {P1 P2 Q : proc p α} {X Y : Set α} {M : p → domTType α} :
    eqT ((P1 |~| P2) |[X,Y]| Q) M M (((P1 |[X,Y]| Q)) |~| ((P2 |[X,Y]| Q))) := by
  cspT_auto

theorem cspT_Alpha_Parallel_dist_r
    {P Q1 Q2 : proc p α} {X Y : Set α} {M : p → domTType α} :
    eqT (P |[X,Y]| (Q1 |~| Q2)) M M (((P |[X,Y]| Q1)) |~| ((P |[X,Y]| Q2))) := by
  cspT_auto

theorem cspT_Alpha_Parallel_Dist_sum_l_nonempty
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (proc.Rep_int_choice C Pf |[X,Y]| Q) M M
        (proc.Rep_int_choice C fun c => Pf c |[X,Y]| Q) := by
  cspT_auto

-- `by_cases` on the index set + the `Rep_int_choice_*_DIV` law; cheap, no big unfolding
theorem cspT_Alpha_Parallel_Dist_sum_l
    {C : sets_nats α} {Pf : aset_anat α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (proc.Rep_int_choice C Pf |[X,Y]| Q) M M
      (procIte (sumset C = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (proc.Rep_int_choice C fun c => Pf c |[X,Y]| Q)) := by
  by_cases h : sumset C = ∅
  · rw [procIte_pos h]
    exact cspT_Alpha_parallel_cong rfl rfl (cspT_Rep_int_choice_sum_DIV h) cspT_reflex_eq_P
  · rw [procIte_neg h]
    exact cspT_Alpha_Parallel_Dist_sum_l_nonempty h

theorem cspT_Alpha_Parallel_Dist_sum_r_nonempty
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    sumset C ≠ ∅ →
      eqT (P |[X,Y]| proc.Rep_int_choice C Qf) M M
        (proc.Rep_int_choice C fun c => P |[X,Y]| Qf c) := by
  cspT_auto

theorem cspT_Alpha_Parallel_Dist_sum_r
    {C : sets_nats α} {Qf : aset_anat α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (P |[X,Y]| proc.Rep_int_choice C Qf) M M
      (procIte (sumset C = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (proc.Rep_int_choice C fun c => P |[X,Y]| Qf c)) := by
  apply cspT_trans_left_eq (cspT_Alpha_parallel_commut)
  apply cspT_trans_left_eq (cspT_Alpha_Parallel_Dist_sum_l)
  by_cases h : sumset C = ∅
  · simp only [procIte, if_pos h]
    exact cspT_Alpha_parallel_commut
  · simp only [procIte, if_neg h]
    exact cspT_Rep_int_choice_cong_sum rfl (fun c _ => cspT_Alpha_parallel_commut)

theorem cspT_Alpha_Parallel_Dist_nat_l_nonempty
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    N ≠ ∅ →
      eqT (Rep_int_choice_nat N Pf |[X,Y]| Q) M M
        (Rep_int_choice_nat N fun n => Pf n |[X,Y]| Q) := by
  cspT_auto

-- `by_cases` on the index set + the `Rep_int_choice_*_DIV` law; cheap, no big unfolding
theorem cspT_Alpha_Parallel_Dist_nat_l
    {N : Set Nat} {Pf : Nat → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_nat N Pf |[X,Y]| Q) M M
      (procIte (N = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_nat N fun n => Pf n |[X,Y]| Q)) := by
  by_cases h : N = ∅
  · subst h
    rw [procIte_pos rfl]
    exact cspT_Alpha_parallel_cong rfl rfl cspT_Rep_int_choice_nat_DIV cspT_reflex_eq_P
  · rw [procIte_neg h]
    exact cspT_Alpha_Parallel_Dist_nat_l_nonempty h

theorem cspT_Alpha_Parallel_Dist_nat_r_nonempty
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    N ≠ ∅ →
      eqT (P |[X,Y]| Rep_int_choice_nat N Qf) M M
        (Rep_int_choice_nat N fun n => P |[X,Y]| Qf n) := by
  cspT_auto

theorem cspT_Alpha_Parallel_Dist_nat_r
    {N : Set Nat} {Qf : Nat → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (P |[X,Y]| Rep_int_choice_nat N Qf) M M
      (procIte (N = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_nat N fun n => P |[X,Y]| Qf n)) := by
  apply cspT_trans_left_eq (cspT_Alpha_parallel_commut)
  apply cspT_trans_left_eq (cspT_Alpha_Parallel_Dist_nat_l)
  by_cases h : N = ∅
  · simp only [procIte, if_pos h]
    exact cspT_Alpha_parallel_commut
  · simp only [procIte, if_neg h]
    exact cspT_Rep_int_choice_cong_nat rfl (fun n _ => cspT_Alpha_parallel_commut)

theorem cspT_Alpha_Parallel_Dist_set_l_nonempty
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α}
    {Y Z : Set α} {M : p → domTType α} :
    Xs ≠ ∅ →
      eqT (Rep_int_choice_set Xs Pf |[Y,Z]| Q) M M
        (Rep_int_choice_set Xs fun X => Pf X |[Y,Z]| Q) := by
  cspT_auto

-- `by_cases` on the index set + the `Rep_int_choice_*_DIV` law; cheap, no big unfolding
theorem cspT_Alpha_Parallel_Dist_set_l
    {Xs : Set (Set α)} {Pf : Set α → proc p α} {Q : proc p α}
    {Y Z : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_set Xs Pf |[Y,Z]| Q) M M
      (procIte (Xs = ∅) (((proc.DIV : proc p α) |[Y,Z]| Q))
        (Rep_int_choice_set Xs fun X => Pf X |[Y,Z]| Q)) := by
  by_cases h : Xs = ∅
  · subst h
    rw [procIte_pos rfl]
    exact cspT_Alpha_parallel_cong rfl rfl cspT_Rep_int_choice_set_DIV cspT_reflex_eq_P
  · rw [procIte_neg h]
    exact cspT_Alpha_Parallel_Dist_set_l_nonempty h

theorem cspT_Alpha_Parallel_Dist_set_r_nonempty
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α}
    {Y Z : Set α} {M : p → domTType α} :
    Xs ≠ ∅ →
      eqT (P |[Y,Z]| Rep_int_choice_set Xs Qf) M M
        (Rep_int_choice_set Xs fun X => P |[Y,Z]| Qf X) := by
  cspT_auto

theorem cspT_Alpha_Parallel_Dist_set_r
    {Xs : Set (Set α)} {Qf : Set α → proc p α} {P : proc p α}
    {Y Z : Set α} {M : p → domTType α} :
    eqT (P |[Y,Z]| Rep_int_choice_set Xs Qf) M M
      (procIte (Xs = ∅) (P |[Y,Z]| (proc.DIV : proc p α))
        (Rep_int_choice_set Xs fun X => P |[Y,Z]| Qf X)) := by
  apply cspT_trans_left_eq (cspT_Alpha_parallel_commut)
  apply cspT_trans_left_eq (cspT_Alpha_Parallel_Dist_set_l)
  by_cases h : Xs = ∅
  · simp only [procIte, if_pos h]
    exact cspT_Alpha_parallel_commut
  · simp only [procIte, if_neg h]
    exact cspT_Rep_int_choice_cong_set rfl (fun X _ => cspT_Alpha_parallel_commut)

theorem cspT_Alpha_Parallel_Dist_com_l_nonempty [Inhabited α]
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    A ≠ ∅ →
      eqT (Rep_int_choice_com A Pf |[X,Y]| Q) M M
        (Rep_int_choice_com A fun x => Pf x |[X,Y]| Q) := by
  cspT_auto

-- `by_cases` on the index set + the `Rep_int_choice_*_DIV` law; cheap, no big unfolding
theorem cspT_Alpha_Parallel_Dist_com_l [Inhabited α]
    {A : Set α} {Pf : α → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_com A Pf |[X,Y]| Q) M M
      (procIte (A = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_com A fun x => Pf x |[X,Y]| Q)) := by
  by_cases h : A = ∅
  · subst h
    rw [procIte_pos rfl]
    exact cspT_Alpha_parallel_cong rfl rfl cspT_Rep_int_choice_com_DIV cspT_reflex_eq_P
  · rw [procIte_neg h]
    exact cspT_Alpha_Parallel_Dist_com_l_nonempty h

theorem cspT_Alpha_Parallel_Dist_com_r_nonempty [Inhabited α]
    {A : Set α} {Qf : α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    A ≠ ∅ →
      eqT (P |[X,Y]| Rep_int_choice_com A Qf) M M
        (Rep_int_choice_com A fun x => P |[X,Y]| Qf x) := by
  cspT_auto

theorem cspT_Alpha_Parallel_Dist_com_r [Inhabited α]
    {A : Set α} {Qf : α → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (P |[X,Y]| Rep_int_choice_com A Qf) M M
      (procIte (A = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_com A fun x => P |[X,Y]| Qf x)) := by
  apply cspT_trans_left_eq (cspT_Alpha_parallel_commut)
  apply cspT_trans_left_eq (cspT_Alpha_Parallel_Dist_com_l)
  by_cases h : A = ∅
  · simp only [procIte, if_pos h]
    exact cspT_Alpha_parallel_commut
  · simp only [procIte, if_neg h]
    exact cspT_Rep_int_choice_cong_com rfl (fun x _ => cspT_Alpha_parallel_commut)

theorem cspT_Alpha_Parallel_Dist_f_l_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    A ≠ ∅ →
      eqT (Rep_int_choice_f f A Pf |[X,Y]| Q) M M
        (Rep_int_choice_f f A fun x => Pf x |[X,Y]| Q) := by
  cspT_auto

-- `by_cases` on the index set + the `Rep_int_choice_*_DIV` law; cheap, no big unfolding
theorem cspT_Alpha_Parallel_Dist_f_l [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Pf : β → proc p α} {Q : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (Rep_int_choice_f f A Pf |[X,Y]| Q) M M
      (procIte (A = ∅) (((proc.DIV : proc p α) |[X,Y]| Q))
        (Rep_int_choice_f f A fun x => Pf x |[X,Y]| Q)) := by
  by_cases h : A = ∅
  · subst h
    rw [procIte_pos rfl]
    exact cspT_Alpha_parallel_cong rfl rfl (cspT_Rep_int_choice_f_DIV hf) cspT_reflex_eq_P
  · rw [procIte_neg h]
    exact cspT_Alpha_Parallel_Dist_f_l_nonempty hf h

theorem cspT_Alpha_Parallel_Dist_f_r_nonempty [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Qf : β → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    A ≠ ∅ →
      eqT (P |[X,Y]| Rep_int_choice_f f A Qf) M M
        (Rep_int_choice_f f A fun x => P |[X,Y]| Qf x) := by
  cspT_auto

theorem cspT_Alpha_Parallel_Dist_f_r [Inhabited α] [Inhabited β]
    {f : β → α} (hf : Injective f) {A : Set β} {Qf : β → proc p α} {P : proc p α}
    {X Y : Set α} {M : p → domTType α} :
    eqT (P |[X,Y]| Rep_int_choice_f f A Qf) M M
      (procIte (A = ∅) (P |[X,Y]| (proc.DIV : proc p α))
        (Rep_int_choice_f f A fun x => P |[X,Y]| Qf x)) := by
  apply cspT_trans_left_eq (cspT_Alpha_parallel_commut)
  apply cspT_trans_left_eq (cspT_Alpha_Parallel_Dist_f_l hf)
  by_cases h : A = ∅
  · simp only [procIte, if_pos h]
    exact cspT_Alpha_parallel_commut
  · simp only [procIte, if_neg h]
    exact cspT_Rep_int_choice_cong_f hf rfl (fun x _ => cspT_Alpha_parallel_commut)

/- The Isabelle theorem bundle `cspT_dist_Alpha_Parallel` is represented by
   `cspT_Alpha_Parallel_dist_l` and `cspT_Alpha_Parallel_dist_r`. -/

/- The Isabelle theorem bundle `cspT_Dist_Alpha_Parallel` is represented by
   `cspT_Alpha_Parallel_Dist_sum_l`, `cspT_Alpha_Parallel_Dist_sum_r`,
   `cspT_Alpha_Parallel_Dist_nat_l`, `cspT_Alpha_Parallel_Dist_nat_r`,
   `cspT_Alpha_Parallel_Dist_set_l`, `cspT_Alpha_Parallel_Dist_set_r`,
   `cspT_Alpha_Parallel_Dist_com_l`, `cspT_Alpha_Parallel_Dist_com_r`,
   `cspT_Alpha_Parallel_Dist_f_l`, and `cspT_Alpha_Parallel_Dist_f_r`. -/

/- The Isabelle theorem bundle `cspT_Dist_Alpha_Parallel_nonempty` is
   represented by `cspT_Alpha_Parallel_Dist_sum_l_nonempty`,
   `cspT_Alpha_Parallel_Dist_sum_r_nonempty`,
   `cspT_Alpha_Parallel_Dist_nat_l_nonempty`,
   `cspT_Alpha_Parallel_Dist_nat_r_nonempty`,
   `cspT_Alpha_Parallel_Dist_set_l_nonempty`,
   `cspT_Alpha_Parallel_Dist_set_r_nonempty`,
   `cspT_Alpha_Parallel_Dist_com_l_nonempty`,
   `cspT_Alpha_Parallel_Dist_com_r_nonempty`,
   `cspT_Alpha_Parallel_Dist_f_l_nonempty`, and
   `cspT_Alpha_Parallel_Dist_f_r_nonempty`. -/

end
