module

public import Freezing1.MaximumTailMoments

/-!
# Bounded maximum-height moments over all rows

The source tail argument supplies a common eventual bound. The finitely
many earlier genuine moments are absorbed explicitly, yielding literal
whole-sequence boundedness. This corollary has separate authorship from
the independent review of the root-authored tail route.
-/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

theorem maximum_error_moments_bounded_all_rows (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) ≤ C := by
  let f : ℕ → ℝ := fun n => ∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
    ∂Forward.treeLaw (rows n) n
  let K : ℝ := (7 : ℝ) ^ p + p * ∫ u in Ioi (7 : ℝ), bennettMomentDensity p (1 / 2) u
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_maximum_error_moment_le_source_integral rows hτ hlog hp)
  have hN' : ∀ n ≥ N, f n ≤ K := hN
  refine ⟨|K| + ∑ i ∈ Finset.range N, |f i|,
    add_nonneg (abs_nonneg K) (Finset.sum_nonneg fun i _ => abs_nonneg (f i)), fun n => ?_⟩
  change f n ≤ _
  by_cases hn : n < N
  · exact (le_abs_self (f n)).trans
      ((Finset.single_le_sum (fun i _ => abs_nonneg (f i)) (Finset.mem_range.mpr hn)).trans
        (le_add_of_nonneg_left (abs_nonneg K)))
  · exact (hN' n (Nat.le_of_not_gt hn)).trans
      ((le_abs_self K).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg (f i)))))

theorem maximum_error_eLpNorm_bounded_all_rows (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n) atTop (𝓝 0))
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n : ℕ,
      eLpNorm (fun s => (Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1)
        (ENNReal.ofReal p) (Forward.treeLaw (rows n) n) ≤ C := by
  have hp0 : 0 < p := by linarith
  obtain ⟨K, _, hK⟩ := maximum_error_moments_bounded_all_rows rows hτ hlog hp
  have h1p : 0 ≤ 1 / p := by positivity
  refine ⟨ENNReal.ofReal K ^ (1 / p), by finiteness, fun n => ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
    ENNReal.ofReal_ne_top measurable_from_top.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp0.le]
  apply ENNReal.rpow_le_rpow ?_ h1p
  calc
    _ = ENNReal.ofReal (∫ s, |(Forward.treeHeight s : ℝ) / heightScale (rows n) n - 1| ^ p
        ∂Forward.treeLaw (rows n) n) := by
      simp_rw [Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      exact (ofReal_integral_eq_lintegral_ofReal
        (Forward.integrable_maximum_error_rpow (rows n) n hp0.le)
        (Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hK n)

end Freezing1
