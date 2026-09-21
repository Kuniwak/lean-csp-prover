           /- -------------------------------------------*
            |        CSP-Prover on Isabelle2009         |
            |                   June 2009  (modified)   |
            |                                           |
            |        Yoshinao Isobe (AIST JAPAN)        |
            *------------------------------------------- -/

import LeanCspProver.CSP.Trace_hide
import LeanCspProver.CSP.Trace_par
import LeanCspProver.CSP.Trace_ren
import LeanCspProver.CSP.Trace_seq

open Function
open event

/- *****************************************************************

         1.

 ***************************************************************** -/

/- -------------- *
     hide & seq
 * -------------- -/

theorem rmTick_hide {s : traceType α} {X : Set α} :
    hide_tr (rmTick s) X = rmTick (hide_tr s X) := by
  rcases trace_last_noTick_or_Tick s with hs | ⟨s', hs', hsEq⟩
  · have hsX : noTick (hide_tr s X) := (hide_tr_noTick (s := s) (X := X)).2 hs
    rw [rmTick_nochange hs, rmTick_nochange hsX]
  · have hsX : noTick (hide_tr s' X) := (hide_tr_noTick (s := s') (X := X)).2 hs'
    rw [hsEq]
    calc
      hide_tr (rmTick (s' ^^^ (Abs_trace [Tick] : traceType α))) X
          = hide_tr s' X := by rw [rmTick_last_Tick hs']
      _ = rmTick (hide_tr s' X ^^^ (Abs_trace [Tick] : traceType α)) := by
            symm
            exact rmTick_last_Tick hsX
      _ = rmTick (hide_tr (s' ^^^ (Abs_trace [Tick] : traceType α)) X) := by
            rw [hide_tr_appt (X := X) (s := s') (t := Abs_trace [Tick]) (Or.inl hs'), hide_tr_Tick]

/- -------------- *
     hide & par
 * -------------- -/

theorem interleave_of_hide_tr_lm {u s t : traceType α} {X : Set α} :
  u ∈ par_tr s (∅ : Set α) t →
    hide_tr u X ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) := by
  intro h
  induction h with
  | parx_nil_nil =>
      rw [hide_tr_nil]
      exact par_tr_nil_nil
  | parx_Tick_Tick =>
      rw [hide_tr_Tick]
      exact par_tr_Tick_Tick
  | parx_Ev_nil hpar ha ih =>
      rename_i u1 s1 a
      rw [hide_tr_nil] at ih ⊢
      by_cases hX : a ∈ X
      · rw [hide_tr_in hX, hide_tr_in hX]
        exact ih
      · rw [hide_tr_notin_appt hX, hide_tr_notin_appt hX]
        exact par_tr_Ev_nil ih ha
  | parx_nil_Ev hpar ha ih =>
      rename_i u1 t1 a
      rw [hide_tr_nil] at ih ⊢
      by_cases hX : a ∈ X
      · rw [hide_tr_in hX, hide_tr_in hX]
        exact ih
      · rw [hide_tr_notin_appt hX, hide_tr_notin_appt hX]
        exact par_tr_nil_Ev ih ha
  | parx_Ev_sync hpar ha ih =>
      exact ha.elim
  | parx_Ev_left hpar ha ih =>
      rename_i u1 s1 t1 a
      by_cases hX : a ∈ X
      · rw [hide_tr_in hX, hide_tr_in hX]
        exact ih
      · rw [hide_tr_notin_appt hX, hide_tr_notin_appt hX]
        exact par_tr_Ev_left ih ha
  | parx_Ev_right hpar ha ih =>
      rename_i u1 s1 t1 a
      by_cases hX : a ∈ X
      · rw [hide_tr_in hX, hide_tr_in hX]
        exact ih
      · rw [hide_tr_notin_appt hX, hide_tr_notin_appt hX]
        exact par_tr_Ev_right ih ha

/- interleave_of_hide_tr -/

theorem interleave_of_hide_tr {u s t : traceType α} {X : Set α} :
    u ∈ par_tr s (∅ : Set α) t →
      hide_tr u X ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) := by
  exact interleave_of_hide_tr_lm

/- -------------------------------------------------------------- -/

/- (*** Lean port helpers ***) -/

theorem interleave_hide_nil_left {α : Type _} {X : Set α} {t u : traceType α} :
    u ∈ par_tr (hide_tr (<> : traceType α) X) (∅ : Set α) (hide_tr t X) →
      ∃ v, u = hide_tr v X ∧ v ∈ par_tr (<> : traceType α) (∅ : Set α) t := by
  intro hu
  rw [hide_tr_nil] at hu
  obtain ⟨heq, hT, -⟩ := par_tr_nil_left_only_if hu
  refine ⟨t, heq, par_tr_nil_left_if ?_ (by simp)⟩
  intro hTick
  refine hT ?_
  rw [heq]
  refine hide_tr_in_event.mpr ⟨?_, hTick⟩
  rintro ⟨x, -, hx⟩
  cases hx

theorem interleave_hide_nil_right {α : Type _} {X : Set α} {s u : traceType α} :
    u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr (<> : traceType α) X) →
      ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) (<> : traceType α) := by
  intro hu
  obtain ⟨v, hveq, hv⟩ := interleave_hide_nil_left (par_tr_sym_only_if hu)
  exact ⟨v, hveq, par_tr_sym_only_if hv⟩

theorem interleave_of_hide_tr_ex_ind {α : Type _} {X : Set α} :
    ∀ (n : Nat) (s t u : traceType α), lengtht s + lengtht t <= n →
      u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) →
        ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t := by
  intro n
  induction n with
  | zero =>
      intro s t u hlen hu
      have hs : s = <> := lengtht_zero.mp (by omega)
      subst hs
      exact interleave_hide_nil_left hu
  | succ n ih =>
      intro s t u hlen hu
      rcases trace_nil_or_Tick_or_Ev s with rfl | rfl | ⟨a, s', rfl⟩
      · exact interleave_hide_nil_left hu
      · rcases trace_nil_or_Tick_or_Ev t with rfl | rfl | ⟨b, t', rfl⟩
        · exact interleave_hide_nil_right hu
        · rw [hide_tr_Tick] at hu
          exact ⟨Abs_trace [Tick], by rw [par_tr_Tick2.mp hu, hide_tr_Tick], par_tr_Tick_Tick⟩
        · have hlb : lengtht (Abs_trace [Ev b] ^^^ t') = Nat.succ (lengtht t') :=
            lengtht_app_event_Suc_head
          have hlT : lengtht (Abs_trace [Tick] : traceType α) = 1 := lengtht_one_event
          by_cases hb : b ∈ X
          · rw [hide_tr_in hb] at hu
            obtain ⟨v, hveq, hv⟩ := ih (Abs_trace [Tick]) t' u (by omega) hu
            exact ⟨Abs_trace [Ev b] ^^^ v, by rw [hveq, hide_tr_in hb],
              par_tr_Ev_right hv (by simp)⟩
          · rw [hide_tr_notin_appt hb, hide_tr_Tick] at hu
            obtain ⟨-, w, rfl, hw⟩ := par_tr_Tick_Ev_rev hu
            obtain ⟨v, hveq, hv⟩ := ih (Abs_trace [Tick]) t' w (by omega)
              (by rw [hide_tr_Tick]; exact hw)
            exact ⟨Abs_trace [Ev b] ^^^ v, by rw [hveq, hide_tr_notin_appt hb],
              par_tr_Ev_right hv (by simp)⟩
      · have hla : lengtht (Abs_trace [Ev a] ^^^ s') = Nat.succ (lengtht s') :=
          lengtht_app_event_Suc_head
        by_cases ha : a ∈ X
        · rw [hide_tr_in ha] at hu
          obtain ⟨v, hveq, hv⟩ := ih s' t u (by omega) hu
          exact ⟨Abs_trace [Ev a] ^^^ v, by rw [hveq, hide_tr_in ha],
            par_tr_Ev_left hv (by simp)⟩
        · rcases trace_nil_or_Tick_or_Ev t with rfl | rfl | ⟨b, t', rfl⟩
          · exact interleave_hide_nil_right hu
          · have hlT : lengtht (Abs_trace [Tick] : traceType α) = 1 := lengtht_one_event
            rw [hide_tr_notin_appt ha, hide_tr_Tick] at hu
            obtain ⟨-, w, rfl, hw⟩ := par_tr_Tick_Ev_rev (par_tr_sym_only_if hu)
            obtain ⟨v, hveq, hv⟩ := ih s' (Abs_trace [Tick]) w (by omega)
              (by rw [hide_tr_Tick]; exact par_tr_sym_only_if hw)
            exact ⟨Abs_trace [Ev a] ^^^ v, by rw [hveq, hide_tr_notin_appt ha],
              par_tr_Ev_left hv (by simp)⟩
          · have hlb : lengtht (Abs_trace [Ev b] ^^^ t') = Nat.succ (lengtht t') :=
              lengtht_app_event_Suc_head
            by_cases hb : b ∈ X
            · rw [hide_tr_in hb] at hu
              obtain ⟨v, hveq, hv⟩ := ih (Abs_trace [Ev a] ^^^ s') t' u (by omega) hu
              exact ⟨Abs_trace [Ev b] ^^^ v, by rw [hveq, hide_tr_in hb],
                par_tr_Ev_right hv (by simp)⟩
            · rw [hide_tr_notin_appt ha, hide_tr_notin_appt hb] at hu
              obtain ⟨c, w, rfl, hcase⟩ := par_tr_head_Ev_Ev.mp hu
              rcases hcase with ⟨hc, -, -, -⟩ | ⟨-, hw, hac⟩ | ⟨-, hw, hbc⟩
              · exact hc.elim
              · subst hac
                obtain ⟨v, hveq, hv⟩ := ih s' (Abs_trace [Ev b] ^^^ t') w (by omega)
                  (by rw [hide_tr_notin_appt hb]; exact hw)
                exact ⟨Abs_trace [Ev a] ^^^ v, by rw [hveq, hide_tr_notin_appt ha],
                  par_tr_Ev_left hv (by simp)⟩
              · subst hbc
                obtain ⟨v, hveq, hv⟩ := ih (Abs_trace [Ev a] ^^^ s') t' w (by omega)
                  (by rw [hide_tr_notin_appt ha]; exact hw)
                exact ⟨Abs_trace [Ev b] ^^^ v, by rw [hveq, hide_tr_notin_appt hb],
                  par_tr_Ev_right hv (by simp)⟩

theorem interleave_of_hide_tr_ex_only_if_lm {u s t : traceType α} {X : Set α} :
  u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) →
    ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t := by
  intro hu
  exact interleave_of_hide_tr_ex_ind (lengtht s + lengtht t) s t u le_rfl hu

theorem interleave_of_hide_tr_ex_only_if {u s t : traceType α} {X : Set α} :
    u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X) →
      ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t := by
  exact interleave_of_hide_tr_ex_only_if_lm

/- interleave_of_hide_tr_ex -/

theorem interleave_of_hide_tr_ex {u s t : traceType α} {X : Set α} :
    (u ∈ par_tr (hide_tr s X) (∅ : Set α) (hide_tr t X)) ↔
      ∃ v, u = hide_tr v X ∧ v ∈ par_tr s (∅ : Set α) t := by
  constructor
  · exact interleave_of_hide_tr_ex_only_if
  · rintro ⟨v, rfl, hv⟩
    exact interleave_of_hide_tr hv

/- --------------------------------------------------- *
        distribution renaming over Interleaving
 * --------------------------------------------------- -/

theorem interleave_of_ren_tr_only_if_all {u s t : traceType α} {r : Set (α × β)} {v : traceType β} :
   u ∈ par_tr s (∅ : Set α) t → u [[r]]* v →
     ∃ s' t', v ∈ par_tr s' (∅ : Set β) t' ∧ s [[r]]* s' ∧ t [[r]]* t' := by
  intro h
  induction h generalizing v with
  | parx_nil_nil =>
      intro hv
      rw [ren_tr_nil1.mp hv]
      exact ⟨<>, <>, par_tr_nil_nil, ren_tr_nil, ren_tr_nil⟩
  | parx_Tick_Tick =>
      intro hv
      rw [ren_tr_Tick1.mp hv]
      exact ⟨Abs_trace [Tick], Abs_trace [Tick], par_tr_Tick_Tick, ren_tr_Tick, ren_tr_Tick⟩
  | parx_Ev_nil hpar ha ih =>
      intro hv
      obtain ⟨b, v1, rfl, hab, hv1⟩ := ren_tr_decompo_left_only_if hv
      obtain ⟨s1', t1', hpar', hs', ht'⟩ := ih hv1
      have ht1 : t1' = <> := ren_tr_nil1.mp ht'
      subst ht1
      exact ⟨Abs_trace [Ev b] ^^^ s1', <>, par_tr_Ev_nil hpar' (by simp),
        ren_tr_Ev hs' hab, ren_tr_nil⟩
  | parx_nil_Ev hpar ha ih =>
      intro hv
      obtain ⟨b, v1, rfl, hab, hv1⟩ := ren_tr_decompo_left_only_if hv
      obtain ⟨s1', t1', hpar', hs', ht'⟩ := ih hv1
      have hs1 : s1' = <> := ren_tr_nil1.mp hs'
      subst hs1
      exact ⟨<>, Abs_trace [Ev b] ^^^ t1', par_tr_nil_Ev hpar' (by simp),
        ren_tr_nil, ren_tr_Ev ht' hab⟩
  | parx_Ev_sync hpar ha ih =>
      exact ha.elim
  | parx_Ev_left hpar ha ih =>
      intro hv
      obtain ⟨b, v1, rfl, hab, hv1⟩ := ren_tr_decompo_left_only_if hv
      obtain ⟨s1', t1', hpar', hs', ht'⟩ := ih hv1
      exact ⟨Abs_trace [Ev b] ^^^ s1', t1', par_tr_Ev_left hpar' (by simp),
        ren_tr_Ev hs' hab, ht'⟩
  | parx_Ev_right hpar ha ih =>
      intro hv
      obtain ⟨b, v1, rfl, hab, hv1⟩ := ren_tr_decompo_left_only_if hv
      obtain ⟨s1', t1', hpar', hs', ht'⟩ := ih hv1
      exact ⟨s1', Abs_trace [Ev b] ^^^ t1', par_tr_Ev_right hpar' (by simp),
        hs', ren_tr_Ev ht' hab⟩

theorem interleave_of_ren_tr_only_if
    {u s t : traceType α} {r : Set (α × β)} {v : traceType β} :
    u ∈ par_tr s (∅ : Set α) t → u [[r]]* v →
      ∃ s' t', v ∈ par_tr s' (∅ : Set β) t' ∧ s [[r]]* s' ∧ t [[r]]* t' := by
  intro hu hv
  exact interleave_of_ren_tr_only_if_all hu hv

theorem interleave_of_ren_tr_if_all {v : traceType β} {r : Set (α × β)}
    {s t : traceType α} {s' t' : traceType β} :
   v ∈ par_tr s' (∅ : Set β) t' → s [[r]]* s' → t [[r]]* t' →
     ∃ u, u ∈ par_tr s (∅ : Set α) t ∧ u [[r]]* v := by
  intro h
  induction h generalizing s t with
  | parx_nil_nil =>
      intro hs ht
      rw [ren_tr_nil2.mp hs, ren_tr_nil2.mp ht]
      exact ⟨<>, par_tr_nil_nil, ren_tr_nil⟩
  | parx_Tick_Tick =>
      intro hs ht
      rw [ren_tr_Tick2.mp hs, ren_tr_Tick2.mp ht]
      exact ⟨Abs_trace [Tick], par_tr_Tick_Tick, ren_tr_Tick⟩
  | parx_Ev_nil hpar ha ih =>
      intro hs ht
      obtain ⟨c, s1, rfl, hca, hs1⟩ := ren_tr_decompo_right_only_if hs
      have ht0 : t = <> := ren_tr_nil2.mp ht
      subst ht0
      obtain ⟨u1, hu1, hren⟩ := ih hs1 ren_tr_nil
      exact ⟨Abs_trace [Ev c] ^^^ u1, par_tr_Ev_nil hu1 (by simp), ren_tr_Ev hren hca⟩
  | parx_nil_Ev hpar ha ih =>
      intro hs ht
      obtain ⟨c, t1, rfl, hca, ht1⟩ := ren_tr_decompo_right_only_if ht
      have hs0 : s = <> := ren_tr_nil2.mp hs
      subst hs0
      obtain ⟨u1, hu1, hren⟩ := ih ren_tr_nil ht1
      exact ⟨Abs_trace [Ev c] ^^^ u1, par_tr_nil_Ev hu1 (by simp), ren_tr_Ev hren hca⟩
  | parx_Ev_sync hpar ha ih =>
      exact ha.elim
  | parx_Ev_left hpar ha ih =>
      intro hs ht
      obtain ⟨c, s1, rfl, hca, hs1⟩ := ren_tr_decompo_right_only_if hs
      obtain ⟨u1, hu1, hren⟩ := ih hs1 ht
      exact ⟨Abs_trace [Ev c] ^^^ u1, par_tr_Ev_left hu1 (by simp), ren_tr_Ev hren hca⟩
  | parx_Ev_right hpar ha ih =>
      intro hs ht
      obtain ⟨c, t1, rfl, hca, ht1⟩ := ren_tr_decompo_right_only_if ht
      obtain ⟨u1, hu1, hren⟩ := ih hs ht1
      exact ⟨Abs_trace [Ev c] ^^^ u1, par_tr_Ev_right hu1 (by simp), ren_tr_Ev hren hca⟩

theorem interleave_of_ren_tr_if
    {v : traceType β} {s' t' : traceType β} {r : Set (α × β)}
    {s t : traceType α} :
    v ∈ par_tr s' (∅ : Set β) t' → s [[r]]* s' → t [[r]]* t' →
      ∃ u, u ∈ par_tr s (∅ : Set α) t ∧ u [[r]]* v := by
  intro hv hs ht
  exact interleave_of_ren_tr_if_all hv hs ht

/- (*** Lean port helpers for the Renaming channel section ***) -/

theorem ren_tr_rest_tr {α : Type _} {r : Set (α × α)} {s t : traceType α} {Y Z : Set α} :
    (∀ a b, (a, b) ∈ r → (a ∈ Y ↔ b ∈ Z)) → s [[r]]* t →
      (s rest-tr Y) [[r]]* (t rest-tr Z) := by
  intro hcond h
  induction h with
  | renx_nil =>
      rw [rest_tr_nil, rest_tr_nil]
      exact ren_tr_nil
  | renx_Tick =>
      rw [rest_tr_Tick, rest_tr_Tick]
      exact ren_tr_Tick
  | renx_Ev hst hab ih =>
      rename_i s1 t1 a b
      by_cases hY : a ∈ Y
      · rw [rest_tr_in_appt hY, rest_tr_in_appt ((hcond a b hab).mp hY)]
        exact ren_tr_Ev ih hab
      · rw [rest_tr_notin hY, rest_tr_notin (fun hc => hY ((hcond a b hab).mpr hc))]
        exact ih

theorem Renaming_channel_range_iff {x α : Type _} {f g : x → α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      ∀ a b, (a, b) ∈ (f <==> g) → (a ∈ Set.range f ↔ b ∈ Set.range g) := by
  intro hf hg hfg a b hab
  have hb : b = Renaming1_channel_fun f g a := by simpa using hab
  constructor
  · rintro ⟨k, rfl⟩
    rw [Renaming1_channel_fun_f hf hfg] at hb
    exact ⟨k, hb.symm⟩
  · rintro ⟨k, hk⟩
    have ha : a = Renaming1_channel_fun f g b := by
      rw [hb, ren_R1cf_involutive hf hg]
    rw [← hk, Renaming_channel_fun_g hg hfg] at ha
    exact ⟨k, ha.symm⟩

theorem Renaming_channel_notin_ranges {x α : Type _} {f g : x → α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      ∀ a b, (a, b) ∈ (f <==> g) → a ∉ Set.range f → a ∉ Set.range g → b = a := by
  intro hf hg hfg a b hab haf hag
  have hb : b = Renaming1_channel_fun f g a := by simpa using hab
  rw [ren_R1cf_fix (fun y hy => haf ⟨y, hy⟩) (fun y hy => hag ⟨y, hy⟩)] at hb
  exact hb

theorem Renaming_channel_mem_iff {x α : Type _} {f g : x → α} {Y : Set α} :
    Injective f → Injective g → (∀ x y, f x ≠ g y) →
      Set.range f ∩ Y = ∅ → Set.range g ∩ Y = ∅ →
        ∀ a b, (a, b) ∈ (f <==> g) → (a ∈ Y ↔ b ∈ Y) := by
  intro hf hg hfg hYf hYg a b hab
  rw [Set.eq_empty_iff_forall_notMem] at hYf hYg
  by_cases haf : a ∈ Set.range f
  · have hbg : b ∈ Set.range g := (Renaming_channel_range_iff hf hg hfg a b hab).mp haf
    exact ⟨fun hY => absurd ⟨haf, hY⟩ (hYf a), fun hY => absurd ⟨hbg, hY⟩ (hYg b)⟩
  · by_cases hag : a ∈ Set.range g
    · have hbf : b ∈ Set.range f := by
        obtain ⟨k, hk⟩ := hag
        have hb : b = Renaming1_channel_fun f g a := by simpa using hab
        rw [← hk, Renaming_channel_fun_g hg hfg] at hb
        exact ⟨k, hb.symm⟩
      exact ⟨fun hY => absurd ⟨hag, hY⟩ (hYg a), fun hY => absurd ⟨hbf, hY⟩ (hYf b)⟩
    · rw [Renaming_channel_notin_ranges hf hg hfg a b hab haf hag]

theorem Renaming_channel_mid_compose_ind {x α : Type _} {left mid right : x → α} :
    Injective left → Injective mid → Injective right →
      (∀ x y, right x ≠ mid y) → (∀ x y, left x ≠ mid y) → (∀ x y, right x ≠ left y) →
        ∀ M P : traceType α, M [[(right <==> mid)]]* P →
          sett M ⊆ Set.insert (Tick : event α) (Ev '' Set.range mid) →
            ∀ Q, M [[(left <==> mid)]]* Q → P [[(right <==> left)]]* Q := by
  intro hleft hmid hright hrm hlm hrl M P h
  induction h with
  | renx_nil =>
      intro _ Q hQ
      rw [ren_tr_nil1.mp hQ]
      exact ren_tr_nil
  | renx_Tick =>
      intro _ Q hQ
      rw [ren_tr_Tick1.mp hQ]
      exact ren_tr_Tick
  | renx_Ev hMP hab ih =>
      rename_i M1 P1 a b
      intro hsett Q hQ
      obtain ⟨c, Q1, rfl, hac, hQ1⟩ := ren_tr_decompo_left_only_if hQ
      have hamid : a ∈ Set.range mid := by
        rcases hsett (ren_sett_Ev_appt.mpr (Or.inl rfl)) with h0 | h0
        · cases h0
        · obtain ⟨k, hk, hke⟩ := h0
          have hka : k = a := inj_Ev hke
          subst hka
          exact hk
      obtain ⟨k, rfl⟩ := hamid
      have hb : b = right k := by
        have h1 : b = Renaming1_channel_fun right mid (mid k) := by simpa using hab
        rw [Renaming_channel_fun_g hmid hrm] at h1
        exact h1
      have hc : c = left k := by
        have h1 : c = Renaming1_channel_fun left mid (mid k) := by simpa using hac
        rw [Renaming_channel_fun_g hmid hlm] at h1
        exact h1
      refine ren_tr_Ev (ih ?_ Q1 hQ1) ?_
      · intro e he
        exact hsett (ren_sett_Ev_appt.mpr (Or.inr he))
      · rw [hb, hc]
        simpa using (Renaming1_channel_fun_f hright hrl (x := k)).symm

/- ------------------------------- *
         Renaming channel
 * ------------------------------- -/

/- Renaming_channel & rest-tr -/

theorem ren_tr_rest_Renaming_channel {x α : Type _} {left mid right : x → α}
    {s s1 s2 : traceType α} :
  Injective right → Injective mid → Injective left →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    s1 [[(right <==> mid)]]* (s rest-tr (Set.range left ∪ Set.range mid)) →
    s2 [[(left <==> mid)]]* (s rest-tr (Set.range mid ∪ Set.range right)) →
    (s1 rest-tr Set.range right) [[(right <==> left)]]* (s2 rest-tr Set.range left) := by
  intro hright hmid hleft hrm hlm hrl hs1 hs2
  have c1 := ren_tr_rest_tr (Renaming_channel_range_iff hright hmid hrm) hs1
  have c2 := ren_tr_rest_tr (Renaming_channel_range_iff hleft hmid hlm) hs2
  rw [rest_tr_of_rest_tr_subset2 Set.subset_union_right] at c1
  rw [rest_tr_of_rest_tr_subset2 Set.subset_union_left] at c2
  exact Renaming_channel_mid_compose_ind hleft hmid hright hrm hlm hrl _ _
    (ren_tr_Renaming_channel_sym_rule hright hmid c1) rest_tr_subset_event _
    (ren_tr_Renaming_channel_sym_rule hleft hmid c2)

/- no renaming events -/

theorem Renaming_channel_tr_rest_eq {x α : Type _} {f g : x → α}
    {Y : Set α} {s t : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    Set.range f ∩ Y = ∅ →
    Set.range g ∩ Y = ∅ →
    s [[(f <==> g)]]* t →
    s rest-tr Y = t rest-tr Y := by
  intro hf hg hfg hYf hYg h
  induction h with
  | renx_nil =>
      rw [rest_tr_nil]
  | renx_Tick =>
      rw [rest_tr_Tick]
  | renx_Ev hst hab ih =>
      rename_i s1 t1 a b
      have hiff := Renaming_channel_mem_iff hf hg hfg hYf hYg a b hab
      by_cases hY : a ∈ Y
      · rw [rest_tr_in_appt hY, rest_tr_in_appt (hiff.mp hY), ih]
        have hba : b = a := by
          by_cases haf : a ∈ Set.range f
          · rw [Set.eq_empty_iff_forall_notMem] at hYf
            exact absurd ⟨haf, hY⟩ (hYf a)
          · by_cases hag : a ∈ Set.range g
            · rw [Set.eq_empty_iff_forall_notMem] at hYg
              exact absurd ⟨hag, hY⟩ (hYg a)
            · exact Renaming_channel_notin_ranges hf hg hfg a b hab haf hag
        rw [hba]
      · rw [rest_tr_notin hY, rest_tr_notin (fun hc => hY (hiff.mpr hc))]
        exact ih

theorem Renaming_channel_tr_rest_eq_range {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* t →
    s rest-tr Set.range h = t rest-tr Set.range h := by
  intro hf hg hfg hfh hgh h
  refine Renaming_channel_tr_rest_eq hf hg hfg ?_ ?_ h
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨⟨x0, rfl⟩, ⟨y0, hy⟩⟩
    exact hfh x0 y0 hy.symm
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro e ⟨⟨x0, rfl⟩, ⟨y0, hy⟩⟩
    exact hgh x0 y0 hy.symm

/- --- Renaming channel & sett 2 (no used) --- -/

theorem Renaming_channel_range_sett_lm {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* (t rest-tr (Set.range f ∪ Set.range h)) →
    sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  intro hf hh hg hfg hfh hgh h
  exact Renaming1_channel_sett1 hf hh hg hfg hfh hgh rest_tr_subset_event h

theorem Renaming_channel_range_sett1 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* (t rest-tr (Set.range f ∪ Set.range h)) →
    sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  intro hf hh hg hfg hfh hgh h
  exact Renaming1_channel_sett1 hf hh hg hfg hfh hgh rest_tr_subset_event h

theorem Renaming_channel_range_sett2 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(f <==> g)]]* (t rest-tr (Set.range h ∪ Set.range f)) →
    sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g)) := by
  intro hf hh hg hfg hfh hgh h
  exact Renaming1_channel_sett2 hf hh hg hfg hfh hgh rest_tr_subset_event h

theorem Renaming_channel_range_sett3 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(g <==> f)]]* (t rest-tr (Set.range f ∪ Set.range h)) →
    sett s ⊆ insert Tick (Ev '' (Set.range g ∪ Set.range h)) := by
  intro hf hh hg hfg hfh hgh h
  exact Renaming1_channel_sett3 hf hh hg hfg hfh hgh rest_tr_subset_event h

theorem Renaming_channel_range_sett4 {x y α : Type _} {f g : x → α} {h : y → α}
    {s t : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    s [[(g <==> f)]]* (t rest-tr (Set.range h ∪ Set.range f)) →
    sett s ⊆ insert Tick (Ev '' (Set.range h ∪ Set.range g)) := by
  intro hf hh hg hfg hfh hgh h
  exact Renaming1_channel_sett4 hf hh hg hfg hfh hgh rest_tr_subset_event h

/- Isabelle: lemmas Renaming_channel_range_sett =
       Renaming_channel_range_sett1
       Renaming_channel_range_sett2
       Renaming_channel_range_sett3
       Renaming_channel_range_sett4 -/

theorem ren_tr_unique_on {α : Type _} {r1 r2 : Set (α × α)} {s t1 : traceType α} :
    s [[r1]]* t1 → (∀ a, Ev a ∈ sett s → ∀ b c, (a, b) ∈ r1 → (a, c) ∈ r2 → b = c) →
      ∀ t2, s [[r2]]* t2 → t1 = t2 := by
  intro h
  induction h with
  | renx_nil =>
      intro _ t2 h2
      exact (ren_tr_nil1.mp h2).symm
  | renx_Tick =>
      intro _ t2 h2
      exact (ren_tr_Tick1.mp h2).symm
  | renx_Ev hst hab ih =>
      rename_i s1 t1' a b
      intro hcond t2 h2
      obtain ⟨c, t2', rfl, hac, h2'⟩ := ren_tr_decompo_left_only_if h2
      have hbc : b = c := hcond a (ren_sett_Ev_appt.mpr (Or.inl rfl)) b c hab hac
      rw [hbc, ih (fun a' ha' => hcond a' (ren_sett_Ev_appt.mpr (Or.inr ha'))) t2' h2']

theorem par_tr_exists_of_rest_eq {α : Type _} {X : Set α} :
    ∀ (n : Nat) (s t : traceType α), lengtht s + lengtht t <= n →
      s rest-tr X = t rest-tr X → ∃ v, v ∈ s |[X]|tr t := by
  intro n
  induction n with
  | zero =>
      intro s t hlen heq
      have hs : s = <> := lengtht_zero.mp (by omega)
      have ht : t = <> := lengtht_zero.mp (by omega)
      subst hs
      subst ht
      exact ⟨<>, par_tr_nil_nil⟩
  | succ n ih =>
      intro s t hlen heq
      rcases trace_nil_or_Tick_or_Ev s with rfl | rfl | ⟨a, s', rfl⟩
      · rw [rest_tr_nil] at heq
        have hE : sett t ∩ Set.insert (Tick : event α) (Ev '' X) = ∅ :=
          rest_tr_nilt_sett.mp heq.symm
        rw [Set.eq_empty_iff_forall_notMem] at hE
        refine ⟨t, par_tr_nil_left_if (fun hTick => hE Tick ⟨hTick, Set.mem_insert _ _⟩) ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro e ⟨he1, he2⟩
        exact hE e ⟨he1, Set.mem_insert_of_mem _ he2⟩
      · rw [rest_tr_Tick] at heq
        obtain ⟨t', rfl, hEt, hnt⟩ := rest_tr_Tick_sett.mp heq.symm
        rw [Set.eq_empty_iff_forall_notMem] at hEt
        have hsett : sett (t' ^^^ (Abs_trace [Tick] : traceType α)) =
            sett t' ∪ {(Tick : event α)} := by
          rw [sett_appt1 (Or.inl hnt), sett_one]
        refine ⟨t' ^^^ Abs_trace [Tick], par_tr_Tick_left_if ?_ ?_⟩
        · rw [hsett]
          exact Or.inr rfl
        · rw [Set.eq_empty_iff_forall_notMem]
          rintro e ⟨he1, he2⟩
          rw [hsett] at he1
          rcases he1 with he1 | he1
          · exact hEt e ⟨he1, he2⟩
          · rw [Set.mem_singleton_iff] at he1
            subst he1
            obtain ⟨y, -, hy⟩ := he2
            cases hy
      · have hla : lengtht (Abs_trace [Ev a] ^^^ s') = Nat.succ (lengtht s') :=
          lengtht_app_event_Suc_head
        by_cases ha : a ∈ X
        · rw [rest_tr_in_appt ha] at heq
          rcases trace_nil_or_Tick_or_Ev t with rfl | rfl | ⟨b, t', rfl⟩
          · rw [rest_tr_nil] at heq
            simp at heq
          · rw [rest_tr_Tick] at heq
            rcases (appt_decompo_one (Or.inl (noTick_Ev a))).mp heq with ⟨h1, -⟩ | ⟨h1, -⟩ <;>
              simp at h1
          · have hlb : lengtht (Abs_trace [Ev b] ^^^ t') = Nat.succ (lengtht t') :=
              lengtht_app_event_Suc_head
            by_cases hb : b ∈ X
            · rw [rest_tr_in_appt hb] at heq
              obtain ⟨hab, hst⟩ := appt_same_head_only_if heq
              subst hab
              obtain ⟨v, hv⟩ := ih s' t' (by omega) hst
              exact ⟨Abs_trace [Ev a] ^^^ v, par_tr_Ev_sync hv ha⟩
            · rw [rest_tr_notin hb] at heq
              obtain ⟨v, hv⟩ := ih (Abs_trace [Ev a] ^^^ s') t' (by omega)
                (by rw [rest_tr_in_appt ha]; exact heq)
              exact ⟨Abs_trace [Ev b] ^^^ v, par_tr_Ev_right hv hb⟩
        · rw [rest_tr_notin ha] at heq
          obtain ⟨v, hv⟩ := ih s' t (by omega) heq
          exact ⟨Abs_trace [Ev a] ^^^ v, par_tr_Ev_left hv ha⟩

/- --- compose restricted traces --- -/

theorem Renaming_channel_tr_par_comp {x α : Type _} {f g h : x → α}
    {n : Nat} {s t u : traceType α} :
  Injective f → Injective h → Injective g →
    (∀ x y, f x ≠ g y) →
    (∀ x y, f x ≠ h y) →
    (∀ x y, g x ≠ h y) →
    lengtht s + lengtht t ≤ n →
    sett s ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range g)) →
    sett t ⊆ insert Tick (Ev '' (Set.range f ∪ Set.range g)) →
    (s rest-tr Set.range f) [[(f <==> g)]]* (t rest-tr Set.range g) →
    ((noTick s ∧ noTick t ∧ noTick u) ∨ (¬ noTick s ∧ ¬ noTick t ∧ ¬ noTick u)) →
    ∃ sh th, (∃ v, v ∈ (sh |[Set.range h]|tr th)) ∧ s [[(f <==> h)]]* sh ∧ t [[(g <==> h)]]* th
      := by
  intro hf hh hg hfg hfh hgh hlen hss htt hrest hTick
  obtain ⟨sh, hsh⟩ := ren_tr_exists_of_fun (F := Renaming1_channel_fun f h) (s := s)
  obtain ⟨th, hth⟩ := ren_tr_exists_of_fun (F := Renaming1_channel_fun g h) (s := t)
  have hshT : s [[(f <==> h)]]* sh := hsh
  have hthT : t [[(g <==> h)]]* th := hth
  refine ⟨sh, th, ?_, hshT, hthT⟩
  have c1 := ren_tr_rest_tr (Renaming_channel_range_iff hf hh hfh) hshT
  have c2 := ren_tr_rest_tr (Renaming_channel_range_iff hg hh hgh) hthT
  have c3 := ren_tr_fun_comp hrest _ c2
  have heq : sh rest-tr Set.range h = th rest-tr Set.range h := by
    refine ren_tr_unique_on c1 ?_ _ c3
    intro a ha b c hb hc
    have haf : a ∈ Set.range f := by
      rcases rest_tr_subset_event ha with h0 | h0
      · cases h0
      · obtain ⟨k, hk, hke⟩ := h0
        have hka : k = a := inj_Ev hke
        subst hka
        exact hk
    obtain ⟨k, rfl⟩ := haf
    have hb1 : b = Renaming1_channel_fun f h (f k) := hb
    rw [Renaming1_channel_fun_f hf hfh] at hb1
    have hc1 : c = Renaming1_channel_fun g h (Renaming1_channel_fun f g (f k)) := hc
    rw [Renaming1_channel_fun_f hf hfg, Renaming1_channel_fun_f hg hgh] at hc1
    rw [hb1, hc1]
  exact par_tr_exists_of_rest_eq (lengtht sh + lengtht th) sh th le_rfl heq

/- -------------- distribution Renaming over restriction -------------- -/

theorem Renaming_channel_rest_tr_dist_only_if {x α : Type _}
    {left right mid : x → α}
    {n : Nat} {s t smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    lengtht s + lengtht t ≤ n →
    (s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left) →
    s [[(right <==> mid)]]* smid →
    t [[(left <==> mid)]]* tmid →
    smid rest-tr Set.range mid = tmid rest-tr Set.range mid := by
  intro hleft hmid hright hrm hlm hrl hlen hrest hs ht
  have c1 := ren_tr_rest_tr (Renaming_channel_range_iff hright hmid hrm) hs
  have c2 := ren_tr_rest_tr (Renaming_channel_range_iff hleft hmid hlm) ht
  have c3 := ren_tr_fun_comp hrest _ c2
  refine ren_tr_unique_on c1 ?_ _ c3
  intro a ha b c hb hc
  have har : a ∈ Set.range right := by
    rcases rest_tr_subset_event ha with h0 | h0
    · cases h0
    · obtain ⟨k, hk, hke⟩ := h0
      have hka : k = a := inj_Ev hke
      subst hka
      exact hk
  obtain ⟨k, rfl⟩ := har
  have hb1 : b = Renaming1_channel_fun right mid (right k) := hb
  rw [Renaming1_channel_fun_f hright hrm] at hb1
  have hc1 : c =
      Renaming1_channel_fun left mid (Renaming1_channel_fun right left (right k)) := hc
  rw [Renaming1_channel_fun_f hright hrl, Renaming1_channel_fun_f hleft hlm] at hc1
  rw [hb1, hc1]

theorem Renaming_channel_rest_tr_dist_if {x α : Type _}
    {left right mid : x → α}
    {n : Nat} {s t smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    lengtht s + lengtht t ≤ n →
    sett s ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    sett t ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    smid rest-tr Set.range mid = tmid rest-tr Set.range mid →
    s [[(right <==> mid)]]* smid →
    t [[(left <==> mid)]]* tmid →
    (s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left) := by
  intro hleft hmid hright hrm hlm hrl hlen hss htt heq hs ht
  have c1 := ren_tr_rest_tr (Renaming_channel_range_iff hright hmid hrm) hs
  have c2 := ren_tr_rest_tr (Renaming_channel_range_iff hleft hmid hlm) ht
  rw [← heq] at c2
  exact Renaming_channel_mid_compose_ind hleft hmid hright hrm hlm hrl _ _
    (ren_tr_Renaming_channel_sym_rule hright hmid c1) rest_tr_subset_event _
    (ren_tr_Renaming_channel_sym_rule hleft hmid c2)

theorem Renaming_channel_rest_tr_dist {x α : Type _}
    {left right mid : x → α}
    {s t smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    sett s ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    sett t ⊆ insert Tick (Ev '' (Set.range left ∪ Set.range right)) →
    s [[(right <==> mid)]]* smid →
    t [[(left <==> mid)]]* tmid →
    (((s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left)) ↔
      smid rest-tr Set.range mid = tmid rest-tr Set.range mid) := by
  intro hleft hmid hright hrm hlm hrl hs ht hsren htren
  constructor
  · intro hrest
    exact Renaming_channel_rest_tr_dist_only_if
      (left := left) (mid := mid) (right := right)
      (n := lengtht s + lengtht t)
      hleft hmid hright hrm hlm hrl (le_rfl) hrest hsren htren
  · intro hmidEq
    exact Renaming_channel_rest_tr_dist_if
      (left := left) (mid := mid) (right := right)
      (n := lengtht s + lengtht t)
      hleft hmid hright hrm hlm hrl (le_rfl) hs ht hmidEq hsren htren

/- ----------------- Renaming, rest-tr, dist ------------------- -/

theorem Renaming_channel_rest_tr_dist_only_if_EX {x α : Type _}
    {left right mid : x → α} {smid tmid : traceType α} :
  Injective left → Injective mid → Injective right →
    (∀ x y, right x ≠ mid y) →
    (∀ x y, left x ≠ mid y) →
    (∀ x y, right x ≠ left y) →
    (∃ s t,
      (s rest-tr Set.range right) [[(right <==> left)]]* (t rest-tr Set.range left) ∧
      s [[(right <==> mid)]]* smid ∧
      t [[(left <==> mid)]]* tmid) →
    smid rest-tr Set.range mid = tmid rest-tr Set.range mid := by
  intro hleft hmid hright hrm hlm hrl h
  rcases h with ⟨s, t, hrest, hsren, htren⟩
  exact Renaming_channel_rest_tr_dist_only_if
    (left := left) (mid := mid) (right := right)
    (n := lengtht s + lengtht t)
    hleft hmid hright hrm hlm hrl (le_rfl) hrest hsren htren

/- ----------------- TRenaming and rest-tr ------------------- -/

theorem Renaming_channel_rest_tr_eq_n {x α : Type _} {f g : x → α}
    {n : Nat} {s t s' t' : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    lengtht s + lengtht t ≤ n →
    s rest-tr Set.range f = t rest-tr Set.range f →
    s [[(f <==> g)]]* s' →
    t [[(f <==> g)]]* t' →
    s' rest-tr Set.range g = t' rest-tr Set.range g := by
  intro hf hg hfg hlen heq hs ht
  have c1 := ren_tr_rest_tr (Renaming_channel_range_iff hf hg hfg) hs
  have c2 := ren_tr_rest_tr (Renaming_channel_range_iff hf hg hfg) ht
  rw [heq] at c1
  exact ren_tr_fun_unique c1 _ c2

theorem Renaming_channel_rest_tr_eq_EX {x α : Type _} {f g : x → α}
    {s' t' : traceType α} :
  Injective f → Injective g → (∀ x y, f x ≠ g y) →
    (∃ s t,
      s rest-tr Set.range f = t rest-tr Set.range f ∧
      s [[(f <==> g)]]* s' ∧
      t [[(f <==> g)]]* t') →
    s' rest-tr Set.range g = t' rest-tr Set.range g := by
  intro hf hg hfg h
  rcases h with ⟨s, t, hrest, hsren, htren⟩
  exact Renaming_channel_rest_tr_eq_n
    (f := f) (g := g)
    (n := lengtht s + lengtht t)
    hf hg hfg (le_rfl) hrest hsren htren
