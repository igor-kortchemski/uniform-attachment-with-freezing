module

public import Freezing1.PlaneGraphGeometry
public import Freezing1.MainSIRUniformHeightStrong

/-!
# Heights and distances of genuine conditional plane-tree samples
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

theorem vertexHeightKernel_le_maximum (s : State) :
    ∀ᵐ h ∂vertexHeightKernel s, h ≤ s.vertices.sup List.length := by
  change ∀ᵐ h ∂(if s.vertices.Nonempty then _ else _), _
  split_ifs with hs
  · apply (ae_map_iff (measurable_of_countable _).aemeasurable (by measurability)).mpr
    have hu : ∀ᵐ u ∂Measure.uniformOfFinset s.vertices, u ∈ s.vertices := by
      rw [ae_iff]
      simp [Measure.uniformOfFinset_apply]
    filter_upwards [hu] with u hu
    exact Finset.le_sup hu
  · simp

theorem Valid.pairDataKernel_metric_bounds {s : State} (hs : Valid s) :
    ∀ᵐ z ∂pairDataKernel s,
      z.1 ≤ s.vertices.sup List.length ∧ z.2.1 ≤ s.vertices.sup List.length ∧
        z.2.2 ≤ z.1 + z.2.1 := by
  have hne : s.vertices.Nonempty := ⟨[], hs.root_mem⟩
  have : IsProbabilityMeasure (Measure.uniformOfFinset s.vertices) :=
    FiniteUniform.uniformOfFinset_probability hne
  have hu : ∀ᵐ u ∂Measure.uniformOfFinset s.vertices, u ∈ s.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  change ((if s.vertices.Nonempty then _ else _) : Measure (ℕ × ℕ × ℕ)) _ = 1
  rw [ite_eq_left hne, Measure.bind_apply (by measurability)
    (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ _u, (1 : ℝ≥0∞) ∂Measure.uniformOfFinset s.vertices := by
      apply lintegral_congr_ae
      filter_upwards [hu] with u hu'
      apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
      apply (ae_map_iff (measurable_of_countable _).aemeasurable (by measurability)).mpr
      filter_upwards [hu] with v hv
      exact ⟨Finset.le_sup hu', Finset.le_sup hv, hs.parentGraph_dist_le_lengths hu' hv⟩
    _ = 1 := by simp

theorem vertexHeightKernel_upper_tail_eq_zero (s : State) {ell eps : ℝ}
    (hell : 0 < ell) (hsmall : ((s.vertices.sup List.length : ℕ) : ℝ) / ell < eps) :
    vertexHeightKernel s {h | eps ≤ (h : ℝ) / ell} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [vertexHeightKernel_le_maximum s] with h hh hbad
  have hhR : (h : ℝ) ≤ ((s.vertices.sup List.length : ℕ) : ℝ) := by exact_mod_cast hh
  exact (not_lt_of_ge (hbad.trans (div_le_div_of_nonneg_right hhR hell.le))) hsmall

theorem Valid.pairDataKernel_distance_upper_tail_eq_zero {s : State} (hs : Valid s)
    {ell eps : ℝ} (hell : 0 < ell)
    (hsmall : 2 * ((s.vertices.sup List.length : ℕ) : ℝ) / ell < eps) :
    pairDataKernel s {z | eps ≤ (z.2.2 : ℝ) / ell} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hs.pairDataKernel_metric_bounds] with z hz hbad
  have hh : z.2.2 ≤ 2 * s.vertices.sup List.length := by omega
  have hhR : (z.2.2 : ℝ) ≤ 2 * ((s.vertices.sup List.length : ℕ) : ℝ) := by exact_mod_cast hh
  exact (not_lt_of_ge (hbad.trans (div_le_div_of_nonneg_right hhR hell.le))) hsmall

end Freezing1.PlaneForward
