module

public import Freezing1.IidScheduleDrift
public import Freezing1.SIRBiasedWalkCritical
public import Freezing1.ForwardAbsorption
public import Freezing1.ForwardPlaneLaw

/-!
# Extinction of the actual infinite iid sign schedule

Every finite source-walk extinction event is identified with the genuine
absorbed plane process, by the original finite iid mixture and its exact
chronological count projection. Continuity from below then transfers the
proved walk extinction probability to the actual infinite sign product.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

theorem measurable_activeCount (n : ℕ) : Measurable (fun x : SignSequence => activeCount x n) := by
  unfold activeCount
  apply Measurable.add measurable_const
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable (fun b : Bool => if b then (1 : ℤ) else -1)).comp
      (measurable_pi_apply (i + 1))

theorem activeCount_eq_of_schedule_prefix {x y : SignSequence} {n : ℕ}
    (h : SchedulesAgreeThrough x y n) : activeCount x n = activeCount y n := by
  unfold activeCount
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [h (i + 1) (by omega) (by have := Finset.mem_range.mp hi; omega)]

namespace Forward

theorem treeLaw_absorbed_probability (x : SignSequence) (n : ℕ) :
    treeLaw x n {s | s.active = ∅} = if extinctionTime x ≤ n then 1 else 0 := by
  by_cases hτ : extinctionTime x ≤ n
  · rw [ite_eq_left hτ]
    have hfinite : extinctionTime x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hτ
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfinite
    have han : a ≤ n := by
      have hh : (a : ℕ∞) ≤ n := by rw [ha]; exact hτ
      exact_mod_cast hh
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le han
    rw [hk, treeLaw_constant_after_extinction ha.symm k]
    exact (mem_ae_iff_prob_eq_one (by trivial)).mp (treeLaw_active_empty_at_extinction ha.symm)
  · rw [ite_eq_right hτ]
    have hne := treeLaw_active_nonempty x n (lt_of_not_ge hτ)
    simpa only [not_imp, not_false_eq_true, and_true] using ae_iff.mp (hne.mono fun s hs he => hs.ne_empty he)

end Forward

namespace ForwardAnnealed

/-- A finite-horizon source extinction event. -/
def extinctBy (n : ℕ) : Set SignSequence := {x | ∃ k ≤ n, activeCount x k = 0}

def everExtinct : Set SignSequence := {x | ∃ k, activeCount x k = 0}

theorem measurableSet_extinctBy (n : ℕ) : MeasurableSet (extinctBy n) := by
  apply measurableSet_setOfPred.mpr
  exact Measurable.exists fun k => measurable_const.and ((measurable_activeCount k).eq measurable_const)

theorem measurableSet_everExtinct : MeasurableSet everExtinct := by
  apply measurableSet_setOfPred.mpr
  exact Measurable.exists fun k => (measurable_activeCount k).eq measurable_const

theorem extinctBy_mono : Monotone extinctBy := by
  intro n m hnm x hx
  obtain ⟨k, hkn, hk⟩ := hx
  exact ⟨k, hkn.trans hnm, hk⟩

theorem iUnion_extinctBy : (⋃ n, extinctBy n) = everExtinct := by
  ext x
  simp only [Set.mem_iUnion, extinctBy, everExtinct, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, k, _, hk⟩; exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩; exact ⟨k, k, le_rfl, hk⟩

theorem iid_extinctBy_probability (p : unitInterval) (n : ℕ) :
    iidSignLaw p (extinctBy n) =
      finiteSignLaw p n {w | extinctionTime (wordSchedule w) ≤ n} := by
  rw [← iidSignLaw_prefix p n,
    Measure.map_apply (Measurable.of_eval fun i => measurable_pi_apply (i.val + 1))
      (Set.to_countable _).measurableSet]
  congr 1
  ext x
  rw [Set.mem_preimage, Set.mem_ofPred_eq, extinctionTime_le_iff]
  constructor
  · rintro ⟨k, hkn, hk⟩
    exact ⟨k, hkn, (activeCount_eq_of_schedule_prefix
      ((prefix_wordSchedule_agrees x n).mono hkn)).trans hk⟩
  · rintro ⟨k, hkn, hk⟩
    exact ⟨k, hkn, (activeCount_eq_of_schedule_prefix
      ((prefix_wordSchedule_agrees x n).mono hkn)).symm.trans hk⟩

theorem treeLaw_absorbed_probability_eq_iid (p : unitInterval) (n : ℕ) :
    treeLaw p n {s | s.active = ∅} = iidSignLaw p (extinctBy n) := by
  rw [iid_extinctBy_probability, treeLaw_eq_iid_sign_mixture,
    Measure.bind_apply (by trivial) (measurable_of_countable _).aemeasurable]
  simp_rw [Forward.treeLaw_absorbed_probability]
  let A : Set (Fin n → Bool) := {w | extinctionTime (wordSchedule w) ≤ n}
  calc
    _ = ∫⁻ w, A.indicator 1 w ∂finiteSignLaw p n := by
      apply lintegral_congr
      intro w
      simp only [A, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    _ = _ := lintegral_indicator_one (Set.to_countable A).measurableSet

theorem plane_zero_probability_eq_iid (p : unitInterval) (n : ℕ) :
    PlaneForward.fullLaw p PlaneForward.initial {H | (H n).active.card = 0} =
      iidSignLaw p (extinctBy n) := by
  have hm : MeasurableSet {s : PlaneForward.State | s.active.card = 0} := by trivial
  calc
    _ = ((treeLaw p n).map Forward.State.toPlaneState) {s | s.active.card = 0} := by
      rw [map_treeLaw_toPlaneState, Measure.map_apply (measurable_pi_apply n) hm]
      rfl
    _ = treeLaw p n {s | s.active.card = 0} := by
      rw [Measure.map_apply Forward.measurable_toPlaneState hm]
      apply measure_congr
      filter_upwards [treeLaw_valid p n] with s hs
      exact propext (by
        change s.toPlaneState.active.card = 0 ↔ s.active.card = 0
        rw [Forward.toPlaneState_active_card hs])
    _ = treeLaw p n {s | s.active = ∅} := by simp only [Finset.card_eq_zero]
    _ = _ := treeLaw_absorbed_probability_eq_iid p n

/-- Actual iid source-schedule extinction has exactly the same probability
as extinction of the actual absorbed plane process. -/
theorem iid_everExtinct_probability_eq_plane (p : unitInterval) :
    iidSignLaw p everExtinct =
      PlaneForward.fullLaw p PlaneForward.initial {H | ∃ k, (H k).active.card = 0} := by
  have hraw : Tendsto (fun n => iidSignLaw p (extinctBy n)) atTop
      (𝓝 (iidSignLaw p everExtinct)) := by
    simpa only [iUnion_extinctBy, Function.comp_def] using
      (tendsto_measure_iUnion_atTop (μ := iidSignLaw p) extinctBy_mono)
  have hm : ∀ k, MeasurableSet {H : ℕ → PlaneForward.State | (H k).active.card = 0} := by
    intro k
    exact (measurable_of_countable (fun s : PlaneForward.State => s.active.card = 0)).setOf.preimage
      (measurable_pi_apply k)
  have hplane := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := PlaneForward.fullLaw p PlaneForward.initial)
    (A := {H | ∃ k, (H k).active.card = 0})
    PlaneForward.measurableSet_ever_absorbed hm (by
      filter_upwards [PlaneForward.fullLaw_held_after_empty p] with H hheld
      by_cases hever : ∃ a, (H a).active.card = 0
      · obtain ⟨a, ha⟩ := hever
        filter_upwards [eventually_ge_atTop a] with k hk
        have hz : (H k).active.card = 0 := by
          rw [PlaneForward.held_after_empty_persists hheld (Finset.card_eq_zero.mp ha) k hk]
          exact ha
        simp only [hz, true_iff]
        exact ⟨a, ha⟩
      · exact Filter.Eventually.of_forall fun k => by
          have hz : (H k).active.card ≠ 0 := fun hk => hever ⟨k, hk⟩
          simp only [hever, hz, iff_self])
  simp only [plane_zero_probability_eq_iid] at hplane
  exact tendsto_nhds_unique hraw hplane

/-- A28, including its critical endpoint, for the actual infinite iid signs. -/
theorem iid_extinction_of_le_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    ∀ᵐ x ∂iidSignLaw p, ∃ k, activeCount x k = 0 := by
  apply (mem_ae_iff_prob_eq_one measurableSet_everExtinct).mpr
  rw [iid_everExtinct_probability_eq_plane]
  exact (mem_ae_iff_prob_eq_one PlaneForward.measurableSet_ever_absorbed).mp
    (PlaneForward.fullLaw_ever_absorbed_ae_of_le_half p hp)

/-- The source raw iid walk's supercritical extinction odds, derived
through actual finite-prefix laws rather than postulated as a model law. -/
theorem iid_everExtinct_probability_supercritical (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    iidSignLaw p everExtinct = ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  rw [iid_everExtinct_probability_eq_plane]
  exact PlaneForward.fullLaw_ever_absorbed_probability p hp

/-- The event used for source conditioning is the actual nonextinction
complement, with its exact probability in the supercritical regime. -/
theorem iid_nonextinction_probability_supercritical (p : unitInterval)
    (hp : (1 : ℝ) / 2 < p) :
    iidSignLaw p {x | extinctionTime x = ⊤} =
      1 - ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  have he : {x : SignSequence | extinctionTime x = ⊤} = everExtinctᶜ := by
    ext x
    unfold extinctionTime everExtinct
    by_cases hx : ∃ k, activeCount x k = 0
    · simp [hx]
    · simp [hx]
      exact fun k hk => hx ⟨k, hk⟩
  rw [he, measure_compl measurableSet_everExtinct (measure_ne_top _ _), measure_univ,
    iid_everExtinct_probability_supercritical p hp]

end ForwardAnnealed

end Freezing1
