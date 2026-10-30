module

public import Freezing1.ForwardComponentContinuation
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The actual survival law of an existing forward vertex

A choice at step i is made from the active population at time i-1. The
survival product below is derived from the true continuation kernels with
this denominator. A persistent vertex identifier at most the starting time
cannot be introduced again by a later attachment. No infinite trajectory
or conditional independence assertion is assumed here.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def vertexSurvivalFactor (x : SignSequence) (i : ℕ) : ℝ :=
  if x i then 1 else 1 - 1 / (activeCount x (i - 1) : ℝ)

theorem vertexSurvivalFactor_nonneg {x : SignSequence} {i : ℕ}
    (hi : ((i - 1 : ℕ) : ℕ∞) < extinctionTime x) :
    0 ≤ vertexSurvivalFactor x i := by
  have hp := ((lt_extinctionTime_iff x (i - 1)).mp hi) (i - 1) le_rfl
  have hR : (1 : ℝ) ≤ activeCount x (i - 1) := by exact_mod_cast hp
  unfold vertexSurvivalFactor
  split_ifs
  · norm_num
  · have hh : 1 / (activeCount x (i - 1) : ℝ) ≤ 1 :=
      (div_le_one (by linarith)).mpr hR
    linarith

theorem step_active_old {a : ℕ} {s : State} {r v : ℕ}
    (hr : r ≤ a) (hv : v ∈ s.active) (sign : Bool) :
    r ∈ (step s (a + 1) sign v).active ↔
      r ∈ s.active ∧ (sign = true ∨ r ≠ v) := by
  have hnew : r ≠ a + 1 := by omega
  rw [step, ite_eq_left hv]
  cases sign <;> simp [attach, freeze, hnew, and_comm]

theorem transitionLaw_old_active_probability {a : ℕ} {s : State}
    (hne : s.active.Nonempty) {r : ℕ} (hr : r ≤ a) (sign : Bool) :
    (transitionLaw s (a + 1) sign).real {q | r ∈ q.active} =
      (if r ∈ s.active then (1 : ℝ) else 0) *
        (if sign then 1 else 1 - 1 / (s.active.card : ℝ)) := by
  classical
  have hf : s.active.filter (fun v => step s (a + 1) sign v ∈ {q | r ∈ q.active}) =
      if r ∈ s.active then (if sign then s.active else s.active.erase r) else ∅ := by
    ext v
    by_cases hv : v ∈ s.active
    · rw [Finset.mem_filter]
      simp only [hv, true_and, Set.mem_ofPred_eq, step_active_old hr hv]
      cases sign <;> by_cases hmem : r ∈ s.active <;> simp [hmem, hv, eq_comm]
    · simp only [Finset.mem_filter, hv, false_and]
      cases sign <;> by_cases hmem : r ∈ s.active <;> simp [hmem, hv]
  change ((transitionLaw s (a + 1) sign) {q | r ∈ q.active}).toReal = _
  rw [transitionLaw_apply _ _ _ hne]
  simp only [Set.mem_ofPred_eq] at hf ⊢
  erw [hf]
  have hcard : 0 < s.active.card := hne.card_pos
  have hR : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hcard.ne'
  cases sign <;> by_cases hmem : r ∈ s.active
  · simp only [hmem, Bool.false_eq_true, ↓reduceIte, Finset.card_erase_of_mem hmem,
      ENNReal.toReal_div, ENNReal.toReal_natCast, one_mul]
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    field_simp
  · simp [hmem]
  · simp [hmem, ENNReal.toReal_div, hR]
  · simp [hmem]

theorem transitionLaw_vertex_survival {x : SignSequence} {a : ℕ} {s : State}
    (hs : PhaseData x a s) (hne : s.active.Nonempty) {r : ℕ} (hr : r ≤ a) :
    (transitionLaw s (a + 1) (x (a + 1))).real {q | r ∈ q.active} =
      (if r ∈ s.active then (1 : ℝ) else 0) * vertexSurvivalFactor x (a + 1) := by
  rw [transitionLaw_old_active_probability hne hr]
  have hc : (s.active.card : ℝ) = (activeCount x a : ℝ) := by exact_mod_cast hs.count
  simp only [vertexSurvivalFactor, Nat.add_sub_cancel, hc]

/-- Exact finite survival probability from a genuine phase state, before or
at the extinction endpoint. This is a product of the actual kernels. -/
theorem continuationLaw_vertex_survival_measure {x : SignSequence} {a k : ℕ} {s : State}
    (hs : PhaseData x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    {r : ℕ} (hr : r ≤ a) :
    (continuationLaw x a k s) {q | r ∈ q.active} =
      if r ∈ s.active then
        ∏ i ∈ Finset.Ioc a (a + k), ENNReal.ofReal (vertexSurvivalFactor x i) else 0 := by
  induction k generalizing a s with
  | zero =>
    by_cases hmem : r ∈ s.active <;> simp [continuationLaw, hmem]
  | succ k ih =>
    have haτ : (a : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show a < a + (k + 1) by omega)) hτ
    have hpos := ((lt_extinctionTime_iff x a).mp haτ) a le_rfl
    have hne : s.active.Nonempty := by
      apply Finset.card_pos.mp
      have hc := hs.count
      omega
    have hend : (((a + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hτ
    have hnext := transitionLaw_phaseData hs hne
    have hfirst : (transitionLaw s (a + 1) (x (a + 1))) {q | r ∈ q.active} =
        if r ∈ s.active then ENNReal.ofReal (vertexSurvivalFactor x (a + 1)) else 0 := by
      rw [← ofReal_measureReal, transitionLaw_vertex_survival hs hne hr]
      split_ifs <;> simp
    have he : a + (k + 1) = (a + 1) + k := by omega
    rw [continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ q, {q' : State | r ∈ q'.active}.indicator
          (fun _ => ∏ i ∈ Finset.Ioc (a + 1) (a + 1 + k),
            ENNReal.ofReal (vertexSurvivalFactor x i)) q
          ∂transitionLaw s (a + 1) (x (a + 1)) := by
        apply lintegral_congr_ae
        filter_upwards [hnext] with q hq
        rw [ih hq hend (hr.trans (Nat.le_succ a))]
        by_cases hmem : r ∈ q.active <;> simp [hmem]
      _ = (∏ i ∈ Finset.Ioc (a + 1) (a + 1 + k),
          ENNReal.ofReal (vertexSurvivalFactor x i)) *
          (transitionLaw s (a + 1) (x (a + 1))) {q | r ∈ q.active} :=
        lintegral_indicator_const (by trivial) _
      _ = _ := by
        rw [hfirst, he]
        have hp := Finset.prod_Ioc_consecutive
          (fun i => ENNReal.ofReal (vertexSurvivalFactor x i))
          (Nat.le_succ a) (show a + 1 ≤ a + 1 + k by omega)
        simp only [Nat.Ioc_succ_singleton, Finset.prod_singleton] at hp
        by_cases hmem : r ∈ s.active
        · simp only [hmem, ↓reduceIte]
          rw [mul_comm]
          exact hp
        · simp [hmem]

theorem continuationLaw_vertex_survival {x : SignSequence} {a k : ℕ} {s : State}
    (hs : PhaseData x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    {r : ℕ} (hr : r ≤ a) :
    (continuationLaw x a k s).real {q | r ∈ q.active} =
      (if r ∈ s.active then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.Ioc a (a + k), vertexSurvivalFactor x i := by
  change ((continuationLaw x a k s) {q | r ∈ q.active}).toReal = _
  rw [continuationLaw_vertex_survival_measure hs hτ hr]
  by_cases hmem : r ∈ s.active
  · simp only [hmem, ↓reduceIte, one_mul, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    apply ENNReal.toReal_ofReal
    apply vertexSurvivalFactor_nonneg
    have ht : i - 1 < a + k := by have := Finset.mem_Ioc.mp hi; omega
    exact lt_of_lt_of_le (by exact_mod_cast ht) hτ
  · simp [hmem]

end Freezing1.Forward
