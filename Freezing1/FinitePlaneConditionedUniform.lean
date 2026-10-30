module

public import Freezing1.FinitePlaneUniformLaw
public import Freezing1.FinitePlaneExtinctionTime

/-!
# The iid-sign tree conditioned on its extinction time (source Examples, second bullet)

For the actual chronological plane tree built from iid signs, conditioning on
the first active-zero time $\tau=2m-1$ gives the uniform law on all finite
plane trees with $m$ vertices. The conditioning event is a genuine event of
the actual history, equal almost surely to the event that the limiting tree
is finite with $m$ vertices; its probability is explicit and positive.
Even times have probability zero.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open MeasureTheory ProbabilityTheory PlaneTree PlaneForward
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem measure_extinctionTimeIs_eq_class (p : unitInterval) (hp : (p : ℝ) < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs (2 * m - 1) H} =
      (planeLimitLaw p : Measure Tree) (finitePlaneSet m) := by
  rw [← map_fullLaw_chainLimit p hp,
    Measure.map_apply_of_aemeasurable (aemeasurable_chainLimit p hp)
      (measurableSet_finitePlaneSet m)]
  apply measure_congr
  filter_upwards [ae_extinctionTimeIs_iff_finiteVertexCount p hp m hm] with H hH
  exact propext hH

/-- The exact probability that the first extinction time is `2m-1`. -/
theorem measure_extinctionTimeIs (p : unitInterval) (hp : (p : ℝ) < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs (2 * m - 1) H} =
      (Fintype.card (FinitePlaneClass m) : ℝ≥0∞) *
        ENNReal.ofReal ((1 - (p : ℝ)) ^ m * (p : ℝ) ^ (m - 1)) := by
  rw [measure_extinctionTimeIs_eq_class p hp m hm]
  have := measure_finitePlaneSet_inter (m := m) (planeLimitLaw p : Measure Tree)
    (c := ENNReal.ofReal ((1 - (p : ℝ)) ^ m * (p : ℝ) ^ (m - 1)))
    (fun T => planeLimitLaw_atom p hp m T.val T.property.1 T.property.2) Set.univ
  simpa only [Set.inter_univ, Finset.mem_univ, Set.mem_univ, Finset.filter_true,
    Finset.card_univ] using this

theorem measure_extinctionTimeIs_pos (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs (2 * m - 1) H} := by
  rw [measure_extinctionTimeIs p hp m hm]
  have : Nonempty (FinitePlaneClass m) := finitePlaneClass_nonempty hm
  apply ENNReal.mul_pos
  · exact_mod_cast Fintype.card_ne_zero
  · exact (ENNReal.ofReal_pos.mpr (mul_pos (pow_pos (sub_pos.mpr hp) _) (pow_pos hp0 _))).ne'

/-- Source Examples, second bullet. For the actual iid-sign chronological plane tree with
success probability `p ∈ (0,1)` (the symmetric source case is `p = 1/2`), conditionally on
the first active-zero time being `2m-1`, the terminal plane tree is uniform on all finite
plane trees with `m` vertices. The conditioning event has positive probability. -/
theorem iid_signs_conditioned_extinction_uniform_plane (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs (2 * m - 1) H} ∧
      ((PlaneForward.fullLaw p PlaneForward.initial)[|{H | ExtinctionTimeIs (2 * m - 1) H}]).map chainLimit =
        finitePlaneUniform m := by
  refine ⟨measure_extinctionTimeIs_pos p hp0 hp1 m hm, ?_⟩
  set μ := PlaneForward.fullLaw p PlaneForward.initial with hμ
  set E : Set (ℕ → State) := {H | ExtinctionTimeIs (2 * m - 1) H} with hE
  have hEm : MeasurableSet E := measurableSet_extinctionTimeIs _
  have hae : E =ᵐ[μ] chainLimit ⁻¹' finitePlaneSet m := by
    filter_upwards [ae_extinctionTimeIs_iff_finiteVertexCount p hp1 m hm] with H hH
    exact propext hH
  have hν : (planeLimitLaw p : Measure Tree)[|finitePlaneSet m] = finitePlaneUniform m := by
    apply cond_finitePlaneSet_eq_uniform hm _ (c :=
      ENNReal.ofReal ((1 - (p : ℝ)) ^ m * (p : ℝ) ^ (m - 1)))
    · exact (ENNReal.ofReal_pos.mpr
        (mul_pos (pow_pos (sub_pos.mpr hp1) _) (pow_pos hp0 _))).ne'
    · exact ENNReal.ofReal_ne_top
    · exact fun T => planeLimitLaw_atom p hp1 m T.val T.property.1 T.property.2
  rw [← hν]
  ext S hS
  have hmeas : AEMeasurable chainLimit (μ[|E]) :=
    (aemeasurable_chainLimit p hp1).mono_ac cond_absolutelyContinuous
  have h1 : μ E = (planeLimitLaw p : Measure Tree) (finitePlaneSet m) :=
    measure_extinctionTimeIs_eq_class p hp1 m hm
  have h2 : μ (E ∩ chainLimit ⁻¹' S) =
      (planeLimitLaw p : Measure Tree) (finitePlaneSet m ∩ S) := by
    rw [← map_fullLaw_chainLimit p hp1,
      Measure.map_apply_of_aemeasurable (aemeasurable_chainLimit p hp1)
        ((measurableSet_finitePlaneSet m).inter hS), Set.preimage_inter]
    exact measure_congr (hae.inter (Filter.EventuallyEq.refl _ _))
  rw [Measure.map_apply_of_aemeasurable hmeas hS, cond_apply hEm, h1, h2,
    cond_apply (measurableSet_finitePlaneSet m)]

/-- The same conclusion for the actual stopped tree `T_n`, read at the extinction time
`n = 2m-1` itself rather than through the limit. -/
theorem iid_signs_conditioned_extinction_uniform_plane_at_time (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    ((PlaneForward.fullLaw p PlaneForward.initial)[|{H | ExtinctionTimeIs (2 * m - 1) H}]).map
        (fun H => shape (H (2 * m - 1))) = finitePlaneUniform m := by
  rw [← (iid_signs_conditioned_extinction_uniform_plane p hp0 hp1 m hm).2]
  have hEm := measurableSet_extinctionTimeIs (2 * m - 1)
  have hall : ∀ᵐ H ∂PlaneForward.fullLaw p PlaneForward.initial,
      ExtinctionTimeIs (2 * m - 1) H → chainLimit H = shape (H (2 * m - 1)) := by
    filter_upwards [fullLaw_tendsto_chainLimit p hp1, fullLaw_held_after_empty p] with H hlim hheld h
    exact chainLimit_eq_shape_of_absorbed hheld hlim h.1
  apply Measure.map_congr
  filter_upwards [ae_cond_mem hEm, cond_absolutelyContinuous.ae_le hall] with H hH hH'
  exact (hH' hH).symm

/-- Impossible even extinction times have probability zero. -/
theorem measure_extinctionTimeIs_even (p : unitInterval) {n : ℕ} (hn : n % 2 = 0) :
    PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs n H} = 0 := by
  have h := ae_not_extinctionTimeIs_of_even p hn
  rw [ae_iff] at h
  simpa using h

end Freezing1.ForwardAnnealed
