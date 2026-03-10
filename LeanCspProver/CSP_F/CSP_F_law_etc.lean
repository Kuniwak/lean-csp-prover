           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2004         |
            |                  April 2006               |
            |                  March 2007  (modified)   |
            |                                           |
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                October 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP_F.CSP_F_law_aux
import LeanCspProver.CSP_T.CSP_T_law_etc

open Function
open SumType

noncomputable section

/-
(*------------------------*
         |~| --> !!
 *------------------------*)
-/

axiom cspF_Int_choice_to_Rep
    {P Q : proc p α} {M : p → domFType α} :
    eqF (P |~| Q) M M
      (Rep_int_choice_nat ({0, 1} : Set Nat) fun n => IF n = 0 THEN P ELSE Q)

/- (*** cspF_Rep_int_choice_set_input ***) -/

axiom cspF_Rep_int_choice_sum_set_input
    {C : sets_nats α} {Xsf : aset_anat α → Set (Set α)} {Pff : aset_anat α → α → proc p α}
    {M : p → domFType α} :
    eqF
      (proc.Rep_int_choice C fun c =>
        Rep_int_choice_set (Xsf c) fun X => proc.Ext_pre_choice X (Pff c))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ c, c ∈ sumset C ∧ Xs = Xsf c}) fun X =>
        proc.Ext_pre_choice X fun a =>
          proc.Rep_int_choice (sub_sumset C fun c => ∃ X, X ∈ Xsf c ∧ a ∈ X) fun c =>
            Pff c a)

/- (*** cspF_Rep_int_choice_set_input ***) -/

axiom cspF_Rep_int_choice_set_input
    {N : Set Nat} {Xsf : Nat → Set (Set α)} {Pff : Nat → α → proc p α}
    {M : p → domFType α} :
    eqF
      (Rep_int_choice_nat N fun n =>
        Rep_int_choice_set (Xsf n) fun X => proc.Ext_pre_choice X (Pff n))
      M M
      (Rep_int_choice_set (Set.sUnion {Xs | ∃ n, n ∈ N ∧ Xs = Xsf n}) fun X =>
        proc.Ext_pre_choice X fun a =>
          Rep_int_choice_nat {n | n ∈ N ∧ ∃ X, X ∈ Xsf n ∧ a ∈ X} fun n =>
            Pff n a)

/- (*** cspF_Rep_int_choice_set_set_DIV ***) -/

axiom cspF_Rep_int_choice_set_set_DIV
    {Xs Ys : Set (Set α)} {M : p → domFType α} :
    Xs ≠ ∅ →
      Ys ≠ ∅ →
      eqF
        (Rep_int_choice_set Xs fun X =>
          Rep_int_choice_set Ys fun Y =>
            proc.Ext_pre_choice (X ∪ Y) fun _ => (proc.DIV : proc p α))
        M M
        (Rep_int_choice_set {Z | ∃ X, X ∈ Xs ∧ ∃ Y, Y ∈ Ys ∧ Z = X ∪ Y} fun Z =>
          proc.Ext_pre_choice Z fun _ => (proc.DIV : proc p α))

/-
(*********************************************************
               (P [+] SKIP) |~| (Q [+] SKIP)
 *********************************************************)

(* p.289 *)
-/

axiom cspF_Int_choice_Ext_choice_SKIP
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.SKIP) |~| (Q [+] proc.SKIP)) M M (P [+] Q [+] proc.SKIP)

/-
(*********************************************************
               (P [+] DIV) |~| (Q [+] DIV)
 *********************************************************)
-/

axiom cspF_Int_choice_Ext_choice_DIV
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.DIV) |~| (Q [+] proc.DIV)) M M (P [+] Q [+] proc.DIV)

/-
(*********************************************************
             (P [+] SKIP) |~| (Q [+] DIV)
 *********************************************************)
-/

axiom cspF_Int_choice_Ext_choice_SKIP_DIV
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.SKIP) |~| (Q [+] proc.DIV)) M M (P [+] Q [+] proc.SKIP)

/-
(*********************************************************
             (P [+] DIV) |~| (Q [+] SKIP)
 *********************************************************)
-/

axiom cspF_Int_choice_Ext_choice_DIV_SKIP
    {P Q : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.DIV) |~| (Q [+] proc.SKIP)) M M (P [+] Q [+] proc.SKIP)

/-
(*********************************************************
         (P [+] SKIP or DIV) |~| (Q [+] DIV or SKIP)
 *********************************************************)
-/

axiom cspF_Int_choice_Ext_choice_SKIP_or_DIV
    {P1 P2 Q1 Q2 : proc p α} {M : p → domFType α} :
    (P2 = proc.SKIP ∨ P2 = proc.DIV) →
      (Q2 = proc.SKIP ∨ Q2 = proc.DIV) →
      eqF ((P1 [+] P2) |~| (Q1 [+] Q2)) M M (P1 [+] Q1 [+] (P2 |~| Q2))

/-
(*********************************************************
                    (P [+] DIV) |~| P
 *********************************************************)
-/

axiom cspF_Ext_choice_DIV_Int_choice_Id
    {P : proc p α} {M : p → domFType α} :
    eqF ((P [+] proc.DIV) |~| P) M M P

/-
(* =================================================== *
 |             addition for CSP-Prover 5               |
 |                    (renaming)                       |
 * =================================================== *)
-/

axiom cspF_Ext_pre_choice_Renaming_fun_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {f : α → α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[fun_to_rel f]]) M M
      (proc.Ext_pre_choice (f '' X) fun y =>
        Rep_int_choice_com {x | x ∈ X ∧ y = f x} fun x =>
          (Pf x)[[fun_to_rel f]])

axiom cspF_Act_prefix_Renaming_fun_step
    {a : α} {P : proc p α} {f : α → α} {M : p → domFType α} :
    eqF (((a ~> P)[[fun_to_rel f]]) ) M M (f a ~> P[[fun_to_rel f]])

/- The Isabelle theorem bundle `cspF_Renaming_fun_step` is represented by
   `cspF_Ext_pre_choice_Renaming_fun_step` and
   `cspF_Act_prefix_Renaming_fun_step`. -/

axiom cspF_Act_prefix_Renaming1_event1_step_in
    {a b : α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[a <--> b]]) ) M M (b ~> P[[a <--> b]])

axiom cspF_Act_prefix_Renaming1_event2_step_in
    {a b : α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[b <--> a]]) ) M M (b ~> P[[b <--> a]])

axiom cspF_Act_prefix_Renaming1_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domFType α} :
    a ≠ c →
      b ≠ c →
      eqF (((c ~> P)[[a <--> b]]) ) M M (c ~> P[[a <--> b]])

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming1_event_step` is
   represented by `cspF_Act_prefix_Renaming1_event1_step_in`,
   `cspF_Act_prefix_Renaming1_event2_step_in`, and
   `cspF_Act_prefix_Renaming1_event_step_notin`. -/

axiom cspF_Act_prefix_Renaming2_set_event_step_in
    {a b : α} {A : Set α} {P : proc p α} {M : p → domFType α} :
    a ∈ A →
      eqF (((a ~> P)[[A <<- b]]) ) M M (b ~> P[[A <<- b]])

axiom cspF_Act_prefix_Renaming2_set_event_step_notin
    {b c : α} {A : Set α} {P : proc p α} {M : p → domFType α} :
    c ∉ A →
      eqF (((c ~> P)[[A <<- b]]) ) M M (c ~> P[[A <<- b]])

axiom cspF_Act_prefix_Renaming2_set_event_step
    {a b : α} {A : Set α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[A <<- b]]) ) M M
      (procIte (a ∈ A) (b ~> P[[A <<- b]]) (a ~> P[[A <<- b]]))

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming2_set_event_steps` is
   represented by `cspF_Act_prefix_Renaming2_set_event_step_in` and
   `cspF_Act_prefix_Renaming2_set_event_step_notin`. -/

axiom cspF_Act_prefix_Renaming2_event_step_in
    {a b : α} {P : proc p α} {M : p → domFType α} :
    eqF (((a ~> P)[[a <-- b]]) ) M M (b ~> P[[a <-- b]])

axiom cspF_Act_prefix_Renaming2_event_step_notin
    {a b c : α} {P : proc p α} {M : p → domFType α} :
    c ≠ a →
      eqF (((c ~> P)[[a <-- b]]) ) M M (c ~> P[[a <-- b]])

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming2_event_step` is
   represented by `cspF_Act_prefix_Renaming2_event_step_in` and
   `cspF_Act_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming_event_step` is
   represented by `cspF_Act_prefix_Renaming1_event_step` and
   `cspF_Act_prefix_Renaming2_event_step`. -/

axiom cspF_Act_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((((f v) ~> P)[[f <==> g]]) ) M M (g v ~> P[[f <==> g]])

axiom cspF_Act_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((((f v) ~> P)[[g <==> f]]) ) M M (g v ~> P[[g <==> f]])

axiom cspF_Act_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α} {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqF ((((h v) ~> P)[[f <==> g]]) ) M M ((h v) ~> P[[f <==> g]])

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming1_channel_step` is
   represented by `cspF_Act_prefix_Renaming1_channel1_step_in`,
   `cspF_Act_prefix_Renaming1_channel2_step_in`, and
   `cspF_Act_prefix_Renaming1_channel_step_notin`. -/

axiom cspF_Act_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((((f v) ~> P)[[f <== g]]) ) M M (g v ~> P[[f <== g]])

axiom cspF_Act_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f : x → α} {g : x → α} {h : y → α} {v : y}
    {P : proc p α} {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqF ((((h v) ~> P)[[f <== g]]) ) M M ((h v) ~> P[[f <== g]])

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming2_channel_step` is
   represented by `cspF_Act_prefix_Renaming2_channel_step_in` and
   `cspF_Act_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming_channel_step` is
   represented by `cspF_Act_prefix_Renaming1_channel_step` and
   `cspF_Act_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Act_prefix_Renaming_step` is represented
   by `cspF_Act_prefix_Renaming_fun_step`,
   `cspF_Act_prefix_Renaming_event_step`, and
   `cspF_Act_prefix_Renaming_channel_step`. -/

axiom cspF_Ext_pre_choice_Renaming1_event1_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]]))

axiom cspF_Ext_pre_choice_Renaming1_event2_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    a = b →
      eqF ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
        ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
          (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
          (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]]))

axiom cspF_Ext_pre_choice_Renaming1_event_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[a <--> b]]) M M
      ((procIte (a ∈ X) (b ~> (Pf a)[[a <--> b]]) proc.STOP) [+]
        (procIte (b ∈ X) (a ~> (Pf b)[[a <--> b]]) proc.STOP) [+]
        (proc.Ext_pre_choice (X \ ({a, b} : Set α)) fun x => (Pf x)[[a <--> b]]))

axiom cspF_Ext_pre_choice_Renaming2_set_event_step_in [Inhabited α]
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domFType α} :
    X ∩ A ≠ ∅ →
      eqF ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]])

axiom cspF_Ext_pre_choice_Renaming2_set_event_step_notin
    {X A : Set α} {Pf : α → proc p α} {b : α} {M : p → domFType α} :
    X ∩ A = ∅ →
      eqF ((proc.Ext_pre_choice X Pf)[[A <<- b]]) M M
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- b]])

axiom cspF_Ext_pre_choice_Renaming2_set_event_step [Inhabited α]
    {X A : Set α} {Pf : α → proc p α} {a : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[A <<- a]]) M M
      (procIte (X ∩ A ≠ ∅)
        ((a ~> Rep_int_choice_com (X ∩ A) fun x => (Pf x)[[A <<- a]]) [+]
          proc.Ext_pre_choice (X \ A) fun x => (Pf x)[[A <<- a]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[A <<- a]]))

axiom cspF_Ext_pre_choice_Renaming2_event_step [Inhabited α]
    {X : Set α} {Pf : α → proc p α} {a b : α} {M : p → domFType α} :
    eqF ((proc.Ext_pre_choice X Pf)[[a <-- b]]) M M
      (procIte (a ∈ X)
        ((b ~> (Pf a)[[a <-- b]]) [+]
          proc.Ext_pre_choice (X \ ({a} : Set α)) fun x => (Pf x)[[a <-- b]])
        (proc.Ext_pre_choice X fun x => (Pf x)[[a <-- b]]))

/- The Isabelle theorem bundle `cspF_Ext_pre_choice_Renaming_event_step` is
   represented by `cspF_Ext_pre_choice_Renaming1_event_step`,
   `cspF_Ext_pre_choice_Renaming2_set_event_step`, and
   `cspF_Ext_pre_choice_Renaming2_event_step`. -/

axiom cspF_Send_prefix_Renaming1_event1_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Send_prefix f v P)[[a <--> f v]]) M M (a ~> P[[a <--> f v]])

axiom cspF_Send_prefix_Renaming1_event2_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Send_prefix f v P)[[f v <--> a]]) M M (a ~> P[[f v <--> a]])

axiom cspF_Send_prefix_Renaming1_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domFType α} :
    a ≠ f v →
      b ≠ f v →
      eqF ((Send_prefix f v P)[[a <--> b]]) M M
        (Send_prefix f v (P[[a <--> b]]))

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming1_event_step` is
   represented by `cspF_Send_prefix_Renaming1_event1_step_in`,
   `cspF_Send_prefix_Renaming1_event2_step_in`, and
   `cspF_Send_prefix_Renaming1_event_step_notin`. -/

axiom cspF_Send_prefix_Renaming2_set_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domFType α} :
    f v ∈ A →
      eqF ((Send_prefix f v P)[[A <<- a]]) M M (a ~> P[[A <<- a]])

axiom cspF_Send_prefix_Renaming2_set_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {b : α}
    {M : p → domFType α} :
    f v ∉ A →
      eqF ((Send_prefix f v P)[[A <<- b]]) M M
        (Send_prefix f v (P[[A <<- b]]))

axiom cspF_Send_prefix_Renaming2_set_event_step
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {A : Set α} {a : α}
    {M : p → domFType α} :
    eqF ((Send_prefix f v P)[[A <<- a]]) M M
      (procIte (f v ∈ A) (a ~> P[[A <<- a]]) (Send_prefix f v (P[[A <<- a]])))

axiom cspF_Send_prefix_Renaming2_event_step_in
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a : α} {M : p → domFType α} :
    eqF ((Send_prefix f v P)[[f v <-- a]]) M M (a ~> P[[f v <-- a]])

axiom cspF_Send_prefix_Renaming2_event_step_notin
    {x : Type _} {f : x → α} {v : x} {P : proc p α} {a b : α} {M : p → domFType α} :
    a ≠ f v →
      eqF ((Send_prefix f v P)[[a <-- b]]) M M
        (Send_prefix f v (P[[a <-- b]]))

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming2_event_step` is
   represented by `cspF_Send_prefix_Renaming2_event_step_in` and
   `cspF_Send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming_event_step` is
   represented by `cspF_Send_prefix_Renaming1_event_step` and
   `cspF_Send_prefix_Renaming2_event_step`. -/

axiom cspF_Send_prefix_Renaming1_channel1_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((Send_prefix f v P)[[f <==> g]]) M M (Send_prefix g v (P[[f <==> g]]))

axiom cspF_Send_prefix_Renaming1_channel2_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((Send_prefix f v P)[[g <==> f]]) M M (Send_prefix g v (P[[g <==> f]]))

axiom cspF_Send_prefix_Renaming1_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      ((∀ x, h v ≠ g x) ∨ h v ∉ Set.range g) →
      eqF ((Send_prefix h v P)[[f <==> g]]) M M
        (Send_prefix h v (P[[f <==> g]]))

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming1_channel_step` is
   represented by `cspF_Send_prefix_Renaming1_channel1_step_in`,
   `cspF_Send_prefix_Renaming1_channel2_step_in`, and
   `cspF_Send_prefix_Renaming1_channel_step_notin`. -/

axiom cspF_Send_prefix_Renaming2_channel_step_in
    {x : Type _} {f g : x → α} {v : x} {P : proc p α} {M : p → domFType α} :
    Injective f →
      (∀ x y, f x ≠ g y) →
      eqF ((Send_prefix f v P)[[f <== g]]) M M (Send_prefix g v (P[[f <== g]]))

axiom cspF_Send_prefix_Renaming2_channel_step_notin
    {x y : Type _} {f g : x → α} {h : y → α} {v : y} {P : proc p α}
    {M : p → domFType α} :
    ((∀ x, h v ≠ f x) ∨ h v ∉ Set.range f) →
      eqF ((Send_prefix h v P)[[f <== g]]) M M
        (Send_prefix h v (P[[f <== g]]))

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming2_channel_step` is
   represented by `cspF_Send_prefix_Renaming2_channel_step_in` and
   `cspF_Send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming_channel_step` is
   represented by `cspF_Send_prefix_Renaming1_channel_step` and
   `cspF_Send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Send_prefix_Renaming_step` is
   represented by `cspF_Send_prefix_Renaming_event_step` and
   `cspF_Send_prefix_Renaming_channel_step`. -/

axiom cspF_Rec_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqF ((Rec_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]])

axiom cspF_Rec_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, x ∈ X → a ≠ f x) →
      eqF ((Rec_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]])

axiom cspF_Rec_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      ((∀ x, x ∈ X → b ≠ f x) ∨ b ∉ f '' X) →
      eqF ((Rec_prefix f X Pf)[[a <--> b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <--> b]])

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming1_event_step` is
   represented by `cspF_Rec_prefix_Renaming1_event1_step_in`,
   `cspF_Rec_prefix_Renaming1_event2_step_in`, and
   `cspF_Rec_prefix_Renaming1_event_step_notin`. -/

axiom cspF_Rec_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqF ((Rec_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
          Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])

axiom cspF_Rec_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {A : Set α} {b : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqF ((Rec_prefix f X Pf)[[A <<- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[A <<- b]])

axiom cspF_Rec_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Rec_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) [+]
            Rec_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Rec_prefix f X fun x => (Pf x)[[A <<- a]]))

axiom cspF_Rec_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      eqF ((Rec_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) [+]
          Rec_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]])

axiom cspF_Rec_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited x] {f : x → α} {X : Set x} {Pf : x → proc p α}
    {a b : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → a ≠ f x) ∨ a ∉ f '' X) →
      eqF ((Rec_prefix f X Pf)[[a <-- b]]) M M
        (Rec_prefix f X fun x => (Pf x)[[a <-- b]])

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming2_event_step` is
   represented by `cspF_Rec_prefix_Renaming2_event_step_in` and
   `cspF_Rec_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming_event_step` is
   represented by `cspF_Rec_prefix_Renaming1_event_step` and
   `cspF_Rec_prefix_Renaming2_event_step`. -/

axiom cspF_Rec_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix f X Pf)[[f <==> g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <==> g]])

axiom cspF_Rec_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix f X Pf)[[g <==> f]]) M M
        (Rec_prefix g X fun x => (Pf x)[[g <==> f]])

/- The Isabelle lemmas `Renaming_channel_fun_h` and
   `Renaming_channel_fun_map_h` are already represented in
   `LeanCspProver.CSP.Infra_ren`. -/

axiom cspF_Rec_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domFType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix h X Pf)[[f <==> g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <==> g]])

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming1_channel_step` is
   represented by `cspF_Rec_prefix_Renaming1_channel1_step_in`,
   `cspF_Rec_prefix_Renaming1_channel2_step_in`, and
   `cspF_Rec_prefix_Renaming1_channel_step_notin`. -/

axiom cspF_Rec_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited x] {f g : x → α} {X : Set x} {Pf : x → proc p α}
    {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix f X Pf)[[f <== g]]) M M
        (Rec_prefix g X fun x => (Pf x)[[f <== g]])

axiom cspF_Rec_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited y] {f g : x → α} {h : y → α} {X : Set y}
    {Pf : y → proc p α} {M : p → domFType α} :
    Injective h →
      ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      (∀ x y, f x ≠ g y) →
      eqF ((Rec_prefix h X Pf)[[f <== g]]) M M
        (Rec_prefix h X fun x => (Pf x)[[f <== g]])

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming2_channel_step` is
   represented by `cspF_Rec_prefix_Renaming2_channel_step_in` and
   `cspF_Rec_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming_channel_step` is
   represented by `cspF_Rec_prefix_Renaming1_channel_step` and
   `cspF_Rec_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Rec_prefix_Renaming_step` is represented
   by `cspF_Rec_prefix_Renaming_event_step` and
   `cspF_Rec_prefix_Renaming_channel_step`. -/

axiom cspF_Nondet_send_prefix_Renaming1_event1_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqF ((Nondet_send_prefix f X Pf)[[a <--> f v]]) M M
        ((a ~> (Pf v)[[a <--> f v]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[a <--> f v]])

axiom cspF_Nondet_send_prefix_Renaming1_event2_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqF ((Nondet_send_prefix f X Pf)[[f v <--> a]]) M M
        ((a ~> (Pf v)[[f v <--> a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <--> a]])

axiom cspF_Nondet_send_prefix_Renaming1_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domFType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      ((∀ x, b ≠ f x) ∨ b ∉ Set.range f) →
      eqF ((Nondet_send_prefix f X Pf)[[a <--> b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <--> b]])

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming1_event_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_event1_step_in`,
   `cspF_Nondet_send_prefix_Renaming1_event2_step_in`, and
   `cspF_Nondet_send_prefix_Renaming1_event_step_notin`. -/

axiom cspF_Nondet_send_prefix_Renaming2_set_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      (∃ x, x ∈ X ∧ f x ∈ A) →
      eqF ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
          Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])

axiom cspF_Nondet_send_prefix_Renaming2_set_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    ((∀ x, x ∈ X → f x ∉ A) ∨ A ∩ (f '' X) = ∅) →
      eqF ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]])

axiom cspF_Nondet_send_prefix_Renaming2_set_event_step
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {A : Set α} {a : α} {M : p → domFType α} :
    Injective f →
      eqF ((Nondet_send_prefix f X Pf)[[A <<- a]]) M M
        (procIte (∃ x, x ∈ X ∧ f x ∈ A)
          ((a ~> Rep_int_choice_f f {x | x ∈ X ∧ f x ∈ A} fun x => (Pf x)[[A <<- a]]) |~|
            Nondet_send_prefix f (X \ {x | x ∈ X ∧ f x ∈ A}) fun x => (Pf x)[[A <<- a]])
          (Nondet_send_prefix f X fun x => (Pf x)[[A <<- a]]))

axiom cspF_Nondet_send_prefix_Renaming2_event_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {v : x} {a : α} {M : p → domFType α} :
    Injective f →
      v ∈ X →
      (∀ x, a ≠ f x) →
      eqF ((Nondet_send_prefix f X Pf)[[f v <-- a]]) M M
        ((a ~> (Pf v)[[f v <-- a]]) |~|
          Nondet_send_prefix f (X \ ({v} : Set x)) fun x => (Pf x)[[f v <-- a]])

axiom cspF_Nondet_send_prefix_Renaming2_event_step_notin
    {x : Type _} [Inhabited α] [Inhabited x] {f : x → α} {X : Set x}
    {Pf : x → proc p α} {a b : α} {M : p → domFType α} :
    ((∀ x, a ≠ f x) ∨ a ∉ Set.range f) →
      eqF ((Nondet_send_prefix f X Pf)[[a <-- b]]) M M
        (Nondet_send_prefix f X fun x => (Pf x)[[a <-- b]])

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming2_event_step`
   is represented by `cspF_Nondet_send_prefix_Renaming2_event_step_in` and
   `cspF_Nondet_send_prefix_Renaming2_event_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming_event_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_event_step` and
   `cspF_Nondet_send_prefix_Renaming2_event_step`. -/

axiom cspF_Nondet_send_prefix_Renaming1_channel1_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Nondet_send_prefix f X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <==> g]])

axiom cspF_Nondet_send_prefix_Renaming1_channel2_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Nondet_send_prefix f X Pf)[[g <==> f]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[g <==> f]])

axiom cspF_Nondet_send_prefix_Renaming1_channel_step_notin
    {x y : Type _} [Inhabited α] [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domFType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      ((∀ x y, g x ≠ h y) ∨ Set.range g ∩ Set.range h = ∅) →
      eqF ((Nondet_send_prefix h X Pf)[[f <==> g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <==> g]])

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming1_channel_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_channel1_step_in`,
   `cspF_Nondet_send_prefix_Renaming1_channel2_step_in`, and
   `cspF_Nondet_send_prefix_Renaming1_channel_step_notin`. -/

axiom cspF_Nondet_send_prefix_Renaming2_channel_step_in
    {x : Type _} [Inhabited α] [Inhabited x] {f g : x → α} {X : Set x}
    {Pf : x → proc p α} {M : p → domFType α} :
    Injective f →
      Injective g →
      (∀ x y, f x ≠ g y) →
      eqF ((Nondet_send_prefix f X Pf)[[f <== g]]) M M
        (Nondet_send_prefix g X fun x => (Pf x)[[f <== g]])

axiom cspF_Nondet_send_prefix_Renaming2_channel_step_notin
    {x y : Type _} [Inhabited α] [Inhabited y] {f g : x → α} {h : y → α}
    {X : Set y} {Pf : y → proc p α} {M : p → domFType α} :
    ((∀ x y, f x ≠ h y) ∨ Set.range f ∩ Set.range h = ∅) →
      eqF ((Nondet_send_prefix h X Pf)[[f <== g]]) M M
        (Nondet_send_prefix h X fun x => (Pf x)[[f <== g]])

/- The Isabelle theorem bundle
   `cspF_Nondet_send_prefix_Renaming2_channel_step` is represented by
   `cspF_Nondet_send_prefix_Renaming2_channel_step_in` and
   `cspF_Nondet_send_prefix_Renaming2_channel_step_notin`. -/

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming_channel_step`
   is represented by `cspF_Nondet_send_prefix_Renaming1_channel_step` and
   `cspF_Nondet_send_prefix_Renaming2_channel_step`. -/

/- The Isabelle theorem bundle `cspF_Nondet_send_prefix_Renaming_step` is
   represented by `cspF_Nondet_send_prefix_Renaming_event_step` and
   `cspF_Nondet_send_prefix_Renaming_channel_step`. -/

/- The Isabelle theorem bundle `cspF_prefix_Renaming_in_step` is represented
   by the `..._step_in` theorems in this file. -/

/- The Isabelle theorem bundle `cspF_prefix_Renaming_notin_step` is
   represented by the `..._step_notin` theorems together with
   `cspF_Act_prefix_Renaming2_set_event_step`,
   `cspF_Send_prefix_Renaming2_set_event_step`,
   `cspF_Rec_prefix_Renaming2_set_event_step`,
   `cspF_Nondet_send_prefix_Renaming2_set_event_step`, and
   `cspF_Ext_pre_choice_Renaming_event_step`. -/

end
