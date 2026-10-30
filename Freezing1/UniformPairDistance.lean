module

public import Freezing1.CanonicalPairSampling
public import Freezing1.ReverseHistoryDistance
public import Freezing1.UniformCoalescence

/-!
# A common law for two heights, their distance, and their coalescence time

The two labels are sampled independently conditional on one actual history.
All four coordinates retain their dependence; diagonal pairs are included.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- An almost-everywhere kernel property passes to its actual mixture. -/
theorem ae_bind_of_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {κ : α → Measure β} (hκ : AEMeasurable κ μ)
    {P : β → Prop} (hP : MeasurableSet {b | P b})
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, P b) : ∀ᵐ b ∂μ.bind κ, P b := by
  rw [ae_iff]
  change (μ.bind κ) {b | P b}ᶜ = 0
  rw [Measure.bind_apply hP.compl hκ]
  apply lintegral_eq_zero_of_ae_eq_zero
  exact h.mono fun a ha => (ae_iff.mp ha)

namespace CanonicalTree

abbrev PairCoalescenceData := ℕ × ℕ × ℕ × ℕ

noncomputable def pairCoalescenceLaw (x : SignSequence) (n : ℕ) :
    Measure PairCoalescenceData :=
  (ReverseHistory.fullLaw x n).bind fun H =>
    (uniformVertex x n).bind fun u => (uniformVertex x n).map fun v =>
      (H.current.depth u, H.current.depth v, H.current.graph.dist u v,
        ReverseHistory.coalescenceTime n H u v)

theorem pairCoalescenceLaw_probability (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : IsProbabilityMeasure (pairCoalescenceLaw x n) := by
  let := uniformVertex_isProbabilityMeasure (activeCount_nonneg_of_le_extinctionTime hn)
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  apply Filter.Eventually.of_forall
  intro H
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  apply Filter.Eventually.of_forall
  intro u
  exact Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance

theorem pairCoalescenceLaw_map_triple (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (pairCoalescenceLaw x n).map (fun z => (z.1, z.2.1, z.2.2.1)) =
      forwardPairDataLaw x n := by
  rw [forwardPairDataLaw_eq_history x n hn]
  unfold pairCoalescenceLaw historyPairDataLaw
  rw [Measure.map_bind measurable_from_top.aemeasurable (by fun_prop)]
  congr 1
  funext H
  rw [Measure.map_bind (measurable_of_countable _).aemeasurable (by fun_prop)]
  congr 1
  funext u
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem pairCoalescenceLaw_map_coalescence (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (pairCoalescenceLaw x n).map (fun z => z.2.2.2) =
      ReverseHistory.uniformCoalescenceLaw x n := by
  rw [ReverseHistory.uniformCoalescenceLaw_eq_conditional x n hn]
  unfold pairCoalescenceLaw
  rw [Measure.map_bind measurable_from_top.aemeasurable (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHistory.lawAfter_current_valid x n n hn le_rfl] with H hH
  have hv : H.current.vertices = vertexLabels x n := by
    simpa only [Nat.sub_self, Reverse.phaseLabels_zero] using hH.vertices_eq
  rw [hv, ← uniformVertex, Measure.map_bind (measurable_of_countable _).aemeasurable (by fun_prop)]
  congr 1
  funext u
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem history_uniform_height (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (ReverseHistory.fullLaw x n).bind (fun H => (uniformVertex x n).map H.current.depth) =
      Forward.uniformHeightLaw x n := by
  have hm : (ReverseHistory.fullLaw x n).map ReverseHistory.History.current =
      Reverse.treeLaw x n := ReverseHistory.map_lawAfter_current x n n
  rw [forward_uniformHeightLaw_eq_reverse x n hn, ← hm,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHistory.lawAfter_current_valid x n n hn le_rfl] with H hH
  have hv : H.current.vertices = vertexLabels x n := by
    simpa only [Nat.sub_self, Reverse.phaseLabels_zero] using hH.vertices_eq
  simp only [hv, uniformVertex]

theorem pairCoalescenceLaw_map_first (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (pairCoalescenceLaw x n).map Prod.fst = Forward.uniformHeightLaw x n := by
  let := uniformVertex_isProbabilityMeasure (activeCount_nonneg_of_le_extinctionTime hn)
  rw [← history_uniform_height x n hn]
  unfold pairCoalescenceLaw
  rw [Measure.map_bind measurable_from_top.aemeasurable (by fun_prop)]
  congr 1
  funext H
  rw [Measure.map_bind (measurable_of_countable _).aemeasurable (by fun_prop)]
  calc
    _ = (uniformVertex x n).bind (fun u => Measure.dirac (H.current.depth u)) := by
      congr 1
      funext u
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [Function.comp_def, Measure.map_const, measure_univ, one_smul]
    _ = _ := Measure.bind_dirac_eq_map _ (by fun_prop)

theorem pairCoalescenceLaw_map_second (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (pairCoalescenceLaw x n).map (fun z => z.2.1) = Forward.uniformHeightLaw x n := by
  let := uniformVertex_isProbabilityMeasure (activeCount_nonneg_of_le_extinctionTime hn)
  rw [← history_uniform_height x n hn]
  unfold pairCoalescenceLaw
  rw [Measure.map_bind measurable_from_top.aemeasurable (by fun_prop)]
  congr 1
  funext H
  rw [Measure.map_bind (measurable_of_countable _).aemeasurable (by fun_prop)]
  calc
    _ = (uniformVertex x n).bind (fun _ => (uniformVertex x n).map H.current.depth) := by
      congr 1
      funext u
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by simp only [Measure.bind_const, measure_univ, one_smul]

theorem pairCoalescenceLaw_geometry (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ z ∂pairCoalescenceLaw x n,
      0 ≤ (z.1 : ℝ) + z.2.1 - z.2.2.1 ∧
      (z.1 : ℝ) + z.2.1 - z.2.2.1 ≤ 2 * (z.2.2.2 : ℝ) := by
  have hmem : ∀ᵐ u ∂uniformVertex x n, u ∈ vertexLabels x n := by
    rw [ae_iff]
    simp [uniformVertex, Measure.uniformOfFinset_apply]
  have hall : ∀ᵐ H ∂ReverseHistory.fullLaw x n, ∀ u v,
      u ∈ vertexLabels x n → v ∈ vertexLabels x n →
      0 ≤ (H.current.depth u : ℝ) + H.current.depth v - H.current.graph.dist u v ∧
      (H.current.depth u : ℝ) + H.current.depth v - H.current.graph.dist u v ≤
        2 * (ReverseHistory.coalescenceTime n H u v : ℝ) := by
    apply ae_all_iff.mpr
    intro u
    apply ae_all_iff.mpr
    intro v
    by_cases hu : u ∈ vertexLabels x n
    · by_cases hv : v ∈ vertexLabels x n
      · simpa only [ReverseHistory.stage_zero, hu, hv, true_implies] using
          ReverseHistory.fullLaw_distance_defect_bounds x n hn hu hv
      · exact Filter.Eventually.of_forall fun _ _ hv' => (hv hv').elim
    · exact Filter.Eventually.of_forall fun _ hu' _ => (hu hu').elim
  apply ae_bind_of_ae measurable_from_top.aemeasurable (by measurability)
  filter_upwards [hall] with H hH
  apply ae_bind_of_ae (measurable_of_countable _).aemeasurable (by measurability)
  filter_upwards [hmem] with u hu
  apply (ae_map_iff (by fun_prop) (by measurability)).mpr
  filter_upwards [hmem] with v hv using hH u v hu hv

end CanonicalTree
end Freezing1
