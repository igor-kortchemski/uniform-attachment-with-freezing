module

public import Freezing1.UniformBirthRandomMean
public import Freezing1.BernoulliLowerMeanMoments

/-!
# The literal conditional Bennett and layer-cake statements

At each fixed birth time the law is the actual independent unmasked array,
with the attachment mask applied inside the sum. The moment identity is
extended-valued, so zero mean is not hidden by totalized Bochner integrals.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem maskedRealCoordinate_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    HasLaw (fun Y => (maskedCoordinate x i Y : ℝ))
      (bernoulliMeasure (1 : ℝ) 0 (Reverse.attachmentParameter x n (horizon_le_extinction h) i))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  have hcast : HasLaw (fun k : ℕ => (k : ℝ))
      (bernoulliMeasure (1 : ℝ) 0 (Reverse.attachmentParameter x n (horizon_le_extinction h) i))
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.attachmentParameter x n (horizon_le_extinction h) i)) := by
    refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
    rw [map_bernoulliMeasure]
    simp only [Nat.cast_one, Nat.cast_zero]
  exact hcast.fun_comp (maskedCoordinate_hasLaw x n h i)

theorem maskedRealCoordinates_independent (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    iIndepFun (fun i : Fin n => fun Y => (maskedCoordinate x i Y : ℝ))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  have hh := (bernoulliProductLaw_independent (reciprocalParameter x n h)).comp
    (fun i (v : ℕ) => ((if x (i.val + 1) then v else 0 : ℕ) : ℝ))
    (fun _ => measurable_of_countable _)
  simpa only [Function.comp_def, maskedCoordinate] using hh

noncomputable def fixedRelativeError (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (b : ℕ) (Y : Fin n → ℕ) : ℝ := (truncatedSum x b Y : ℝ) / truncatedMean x n h b - 1

theorem fixedRelativeError_exp_integrable (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (b : ℕ) (theta : ℝ) :
    Integrable (fun Y => Real.exp (theta * fixedRelativeError x n h b Y))
      (bernoulliProductLaw (reciprocalParameter x n h)) := by
  have hh := bernoulli_centered_exp_integrable
    (fun i : Fin n => measurable_of_countable (fun Y => (maskedCoordinate x i Y : ℝ)))
    (maskedRealCoordinates_independent x n h) (maskedRealCoordinate_hasLaw x n h)
    (Finset.univ.filter fun i : Fin n => i.val < b) theta
  simpa only [fixedRelativeError, truncatedSum, Nat.cast_sum, truncatedMean] using hh

theorem fixedRelativeError_rpow_integrable (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (b : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun Y => |fixedRelativeError x n h b Y| ^ q)
      (bernoulliProductLaw (reciprocalParameter x n h)) :=
  integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero
    (fixedRelativeError_exp_integrable x n h b 1) (fixedRelativeError_exp_integrable x n h b (-1)) hq

/-- Source 1436, with the exact rate at the closed threshold. -/
theorem fixedRelativeError_closed_tail (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (b : ℕ) (hm : 0 < truncatedMean x n h b) {u : ℝ} (hu : 0 < u) :
    (bernoulliProductLaw (reciprocalParameter x n h)).real
      {Y | u ≤ |fixedRelativeError x n h b Y|} ≤
      2 * Real.exp (-truncatedMean x n h b * bennettRate u) := by
  have hh := bernoulli_normalized_closed_deviation_le
    (fun i : Fin n => measurable_of_countable (fun Y => (maskedCoordinate x i Y : ℝ)))
    (maskedRealCoordinates_independent x n h) (maskedRealCoordinate_hasLaw x n h)
    (Finset.univ.filter fun i : Fin n => i.val < b) hm hu
  simpa only [fixedRelativeError, truncatedSum, Nat.cast_sum, truncatedMean] using hh

/-- Source 1432 as a nonnegative moment identity, including zero mean. -/
theorem fixedRelativeError_layercake (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (b : ℕ) {q : ℝ} (hq : 0 < q) :
    (∫⁻ Y, ENNReal.ofReal (|fixedRelativeError x n h b Y| ^ q)
      ∂bernoulliProductLaw (reciprocalParameter x n h)) =
      ENNReal.ofReal q * ∫⁻ u in Ioi (0 : ℝ),
        bernoulliProductLaw (reciprocalParameter x n h)
          {Y | u ≤ |fixedRelativeError x n h b Y|} * ENNReal.ofReal (u ^ (q - 1)) :=
  lintegral_rpow_eq_lintegral_meas_le_mul _ (Eventually.of_forall (fun _ => abs_nonneg _))
    (measurable_of_countable _).aemeasurable hq

/-- The literal integrated Bennett upper bound; the factor two remains
inside the integral to retain its extended-valued meaning at zero mean. -/
theorem fixedRelativeError_bennett_moment_bound (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) (b : ℕ) (hm : 0 < truncatedMean x n h b)
    {q : ℝ} (hq : 0 < q) :
    (∫⁻ Y, ENNReal.ofReal (|fixedRelativeError x n h b Y| ^ q)
      ∂bernoulliProductLaw (reciprocalParameter x n h)) ≤
      ENNReal.ofReal q * ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (2 * Real.exp (-truncatedMean x n h b * bennettRate u)) *
          ENNReal.ofReal (u ^ (q - 1)) := by
  rw [fixedRelativeError_layercake x n h b hq]
  refine mul_le_mul' (le_refl _) ?_
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  refine mul_le_mul' ?_ (le_refl _)
  have hh := fixedRelativeError_closed_tail x n h b hm hu
  rw [Measure.real] at hh
  calc
    _ = ENNReal.ofReal ((bernoulliProductLaw (reciprocalParameter x n h))
        {Y | u ≤ |fixedRelativeError x n h b Y|}).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hh

noncomputable def relativeMomentBound (q : ℝ) : ℝ :=
  2 * (q / (1 / 2)) ^ q * Real.exp ((1 / 2) * Real.exp 1)

theorem fixedRelativeError_moment_le (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {b : ℕ} (hb : 1 ≤ b) {q : ℝ} (hq : 0 ≤ q) :
    (∫ Y, |fixedRelativeError x n h b Y| ^ q ∂bernoulliProductLaw (reciprocalParameter x n h)) ≤
      relativeMomentBound q := by
  have hm := truncatedMean_ge_half x n h hn hb
  have hh := bernoulli_centered_lower_mean_moment_le
    (fun i : Fin n => measurable_of_countable (fun Y => (maskedCoordinate x i Y : ℝ)))
    (maskedRealCoordinates_independent x n h) (maskedRealCoordinate_hasLaw x n h)
    (Finset.univ.filter fun i : Fin n => i.val < b) (by norm_num : (0 : ℝ) < 1 / 2) hm hq
  simpa only [fixedRelativeError, truncatedSum, Nat.cast_sum, truncatedMean, relativeMomentBound] using hh

end Freezing1.UniformBirth
