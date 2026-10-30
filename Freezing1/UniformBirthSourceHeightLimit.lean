module

public import Freezing1.UniformBirthMomentConclusions
public import Freezing1.MainLinearHeightScale
public import Freezing1.CanonicalUniformSampling
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Source A43, using the proved reverse random-birth mean and moments. -/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem randomSum_log_tendsto_Lp_of_scale (rows : ℕ → SignSequence)
    (hrows : ∀ n, PositiveThrough (rows n) n) (hbulk : BulkLowerBound rows)
    {K : ℝ} (hscale : Tendsto (fun n => heightScale (rows n) n / Real.log (n : ℝ)) atTop (nhds K))
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm
      (fun z => randomSum (rows n) z / Real.log (n : ℝ) - K)
      (ENNReal.ofReal p) (auxiliaryLaw (rows n) n (hrows n))) atTop (nhds 0) := by
  have hp0 : 0 < p := by linarith
  let s : ℕ → ℝ := fun n => heightScale (rows n) n / Real.log (n : ℝ)
  have hs : Tendsto s atTop (nhds K) := hscale
  have hsnorm : Tendsto (fun n => ENNReal.ofReal |s n|) atTop (nhds (ENNReal.ofReal |K|)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs.abs
  have hprod := ENNReal.Tendsto.mul hsnorm (Or.inr (by simp))
    (randomSum_normalized_tendsto_Lp rows hrows hbulk hp) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hprod
  have hdiff : Tendsto (fun n => ENNReal.ofReal |s n - K|) atTop (nhds 0) := by
    have hh := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hs.sub_const K).abs
    simpa only [sub_self, abs_zero, ENNReal.ofReal_zero, Function.comp_def] using hh
  have htotal := hprod.add hdiff
  rw [add_zero] at htotal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htotal
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hscale0 := (heightScale_pos hn (hrows n)).ne'
  have he : (fun z => randomSum (rows n) z / Real.log (n : ℝ) - K) =
      (s n) • sumNormalizationError (rows n) n (hrows n) + (fun _ => s n - K) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sumNormalizationError, s]
    field_simp [hscale0]; ring
  rw [he]
  calc
    _ ≤ eLpNorm ((s n) • sumNormalizationError (rows n) n (hrows n)) (ENNReal.ofReal p)
          (auxiliaryLaw (rows n) n (hrows n)) +
        eLpNorm (fun _ : ℕ × (Fin n → ℕ) => s n - K) (ENNReal.ofReal p)
          (auxiliaryLaw (rows n) n (hrows n)) :=
      eLpNorm_add_le (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    _ = _ := by
      rw [eLpNorm_const_smul, eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top]
      simp only [measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs]

theorem auxiliary_uniformHeight_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    HasLaw (fun z : ℕ × (Fin n → ℕ) => truncatedSum x z.1 z.2)
      (Forward.uniformHeightLaw x n) (auxiliaryLaw x n h) := by
  refine ⟨(measurable_of_countable _).aemeasurable, ?_⟩
  have hm := congrArg (fun μ : Measure (ℕ × ℕ) => μ.map Prod.snd)
    (actualBirthHeightLaw_eq_auxiliary x n h)
  rw [actualBirthHeightLaw, Measure.map_bind (measurable_from_top).aemeasurable
    (measurable_of_countable _).aemeasurable, auxiliaryBirthHeightLaw,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)] at hm
  rw [CanonicalTree.forward_uniformHeightLaw_eq_reverse x n (horizon_le_extinction h)]
  symm
  calc
    _ = (Reverse.treeLaw x n).bind (fun F =>
      ((Measure.uniformOfFinset F.vertices).map (fun v => (birthTime n v, F.depth v))).map Prod.snd) := by
      apply Measure.bind_congr_right
      exact Eventually.of_forall (fun F => by
        dsimp only
        rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
        rfl)
    _ = _ := hm

/-- The Introduction's uniform-height limit, now also obtained by the
paper's actual reverse random-mean proof. All vertices are sampled uniformly. -/
theorem linear_uniform_height_via_random_mean
    (rows : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n => A n / Real.log (n : ℝ)) atTop (nhds 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hnear : NearOriginLimsup rows A c) (hbulk : BulkLiminf rows)
    {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun k : ℕ => (k : ℝ) / Real.log (n : ℝ) - (c + 1) / (2 * c))
      (ENNReal.ofReal p) (Forward.uniformHeightLaw (rows n) n)) atTop (nhds 0) := by
  let hs : ∀ n, PositiveThrough (rows n) n := fun n => (lt_extinctionTime_iff (rows n) n).mp (hτ n)
  have hb := (bulkLiminf_iff rows hs).mp hbulk
  have hh := randomSum_log_tendsto_Lp_of_scale rows hs hb
    (linear_heightScale_tendsto rows A hc hc1 hA hAinf hsmall hτ hnear hbulk) hp
  convert hh using 1
  funext n
  exact (eLpNorm_comp_measurePreserving (measurable_of_countable _).aestronglyMeasurable
    ((auxiliary_uniformHeight_hasLaw (rows n) n (hs n)).measurePreserving (measurable_of_countable _))).symm

end Freezing1.UniformBirth
