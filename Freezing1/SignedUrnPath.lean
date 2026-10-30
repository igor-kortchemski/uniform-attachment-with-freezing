module

public import Freezing1.SignedUrnContinuation
public import Freezing1.ReversePairHeightTails

/-!
# Actual finite trajectories of the signed urn

A trajectory records its initial occupancy and every subsequent occupancy.
The recursive law samples precisely the signed urn transitions. Crossing
probabilities below include the initial time and preserve the entire path.
-/

@[expose] public section

namespace Freezing1.SignedUrn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

structure Trajectory where
  values : List ℤ

instance : MeasurableSpace Trajectory := ⊤
instance : DiscreteMeasurableSpace Trajectory := ⟨fun _ => trivial⟩

def prepend (u : ℤ) (H : Trajectory) : Trajectory := ⟨u :: H.values⟩

noncomputable def pathLaw (Z : ℕ → ℤ) : ℕ → ℕ → ℤ → Measure Trajectory
  | _, 0, u => Measure.dirac ⟨[u]⟩
  | a, k + 1, u => (transitionLaw (Z a) (Z (a + 1) - Z a) u).bind
      (fun w => (pathLaw Z (a + 1) k w).map (prepend u))

instance pathLaw_probability (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) :
    IsProbabilityMeasure (pathLaw Z a k u) := by
  induction k generalizing a u with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    change IsProbabilityMeasure ((transitionLaw _ _ _).bind _)
    apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    apply Filter.Eventually.of_forall
    intro w
    let := ih (a + 1) w
    exact Measure.isProbabilityMeasure_map_iff measurable_from_top.aemeasurable |>.mpr inferInstance

/-- The event that the normalized occupancy crosses an exponential barrier
at one of the recorded times, with either sign of θ. -/
def crosses (Z : ℕ → ℤ) (θ r : ℝ) : ℕ → List ℤ → Prop
  | _, [] => False
  | a, u :: us => r ≤ θ * ((u : ℝ) / Z a) ∨ crosses Z θ r (a + 1) us

noncomputable def crossingProbability (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) (θ r : ℝ) : ℝ :=
  (pathLaw Z a k u).real {H | crosses Z θ r a H.values}

theorem crossingProbability_integral (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) (θ r : ℝ) :
    crossingProbability Z a k u θ r =
      ∫ H, (if crosses Z θ r a H.values then (1 : ℝ) else 0) ∂pathLaw Z a k u := by
  exact (integral_ite_indicator _ _ (by trivial)).symm

theorem crossingProbability_zero (Z : ℕ → ℤ) (a : ℕ) (u : ℤ) (θ r : ℝ) :
    crossingProbability Z a 0 u θ r = if r ≤ θ * ((u : ℝ) / Z a) then 1 else 0 := by
  rw [crossingProbability_integral]
  simp [pathLaw, crosses]

theorem crossingProbability_succ (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) (θ r : ℝ) :
    crossingProbability Z a (k + 1) u θ r =
      if r ≤ θ * ((u : ℝ) / Z a) then 1 else
        ∫ w, crossingProbability Z (a + 1) k w θ r
          ∂transitionLaw (Z a) (Z (a + 1) - Z a) u := by
  rw [crossingProbability_integral, pathLaw]
  have hi : Integrable (fun H : Trajectory =>
      if crosses Z θ r a H.values then (1 : ℝ) else 0)
      ((transitionLaw (Z a) (Z (a + 1) - Z a) u).bind
        (fun w => (pathLaw Z (a + 1) k w).map (prepend u))) := by
    change Integrable _ (pathLaw Z a (k + 1) u)
    apply integrable_unitInterval_function _ measurable_from_top
    intro H
    split_ifs <;> norm_num
  rw [integral_bind_of_integrable _ _ (measurable_of_countable _) hi]
  have hmap : ∀ w, (∫ H, (if crosses Z θ r a H.values then (1 : ℝ) else 0)
      ∂(pathLaw Z (a + 1) k w).map (prepend u)) =
      ∫ H, (if r ≤ θ * ((u : ℝ) / Z a) ∨ crosses Z θ r (a + 1) H.values
        then (1 : ℝ) else 0) ∂pathLaw Z (a + 1) k w := by
    intro w
    rw [integral_map measurable_from_top.aemeasurable measurable_from_top.aestronglyMeasurable]
    simp only [prepend, crosses]
  simp_rw [hmap]
  by_cases hc : r ≤ θ * ((u : ℝ) / Z a)
  · simp [hc]
  · simp only [hc, false_or, ↓reduceIte]
    congr 1
    funext w
    exact (crossingProbability_integral Z (a + 1) k w θ r).symm

/-- A finite maximal bound from backward exponential comparison, including
the initial time. This keeps the true path dependence and both signs of θ. -/
theorem crossingProbability_le (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) {θ : ℝ}
    (hbudget : |θ| * squareBudget Z a k ≤ 1 / 4)
    (hinc : ∀ i ∈ Finset.Ioc a (a + k), |θ / (Z i : ℝ)| ≤ 1 / 4) (r : ℝ) :
    crossingProbability Z a k u θ r ≤
      Real.exp ((θ * (1 + θ * squareBudget Z a k)) * ((u : ℝ) / Z a) - r) := by
  induction k generalizing a u with
  | zero =>
    rw [crossingProbability_zero]
    simp only [squareBudget, Finset.Ioc_self, Finset.sum_empty,
      mul_zero, add_zero, mul_one]
    split_ifs with hc
    · exact Real.one_le_exp (sub_nonneg.mpr hc)
    · exact (Real.exp_pos _).le
  | succ k ih =>
    have hZa := hZ a (by simp)
    have hx : 0 ≤ (u : ℝ) / Z a :=
      div_nonneg (by exact_mod_cast hu) (by exact_mod_cast hZa.le)
    have hnext : 0 < Z a + (Z (a + 1) - Z a) := by
      simpa using hZ (a + 1) (by simp)
    have hstep := hz a (by simp)
    have hB : |θ| * squareBudget Z (a + 1) k ≤ 1 / 4 := by
      rw [squareBudget_succ] at hbudget
      have hn := mul_nonneg (abs_nonneg θ) (sq_nonneg ((Z (a + 1) : ℝ)⁻¹))
      nlinarith
    have ht : (Z a : ℝ) + ((Z (a + 1) - Z a : ℤ) : ℝ) = Z (a + 1) := by
      push_cast; ring
    have hsmall : |θ * (((Z (a + 1) - Z a : ℤ) : ℝ) /
        ((Z a : ℝ) + ((Z (a + 1) - Z a : ℤ) : ℝ)))| ≤ 1 / 4 := by
      have hi := hinc (a + 1) (by simp)
      rw [ht]
      rcases hstep with hp | hm
      · rw [hp]; simpa only [Int.cast_one, mul_one_div] using hi
      · rw [hm]; simpa only [Int.cast_neg, Int.cast_one, div_neg, neg_div,
          mul_neg, mul_one_div, abs_neg] using hi
    rw [crossingProbability_succ]
    split_ifs with hc
    · apply Real.one_le_exp
      have hn := mul_nonneg (mul_nonneg (sq_nonneg θ) (squareBudget_nonneg Z a (k + 1))) hx
      nlinarith
    · calc
        _ ≤ ∫ w, Real.exp ((θ * (1 + θ * squareBudget Z (a + 1) k)) *
            ((w : ℝ) / Z (a + 1)) - r) ∂transitionLaw (Z a) (Z (a + 1) - Z a) u := by
          apply integral_mono_ae (integrable_bernoulliMeasure _ _ _ _)
            (integrable_bernoulliMeasure _ _ _ _)
          filter_upwards [transitionLaw_valid hZa hnext hstep hu huZ] with w hw
          exact ih
            (fun i hi => hZ i (by simp only [Finset.mem_Icc] at hi ⊢; omega))
            (fun i hi => hz i (by simp only [Finset.mem_Ico] at hi ⊢; omega))
            hw.1 (by simpa using hw.2) hB
            (fun i hi => hinc i (by simp only [Finset.mem_Ioc] at hi ⊢; omega))
        _ = Real.exp (-r) * (∫ w, Real.exp ((θ * (1 + θ * squareBudget Z (a + 1) k)) *
            ((w : ℝ) / Z (a + 1))) ∂transitionLaw (Z a) (Z (a + 1) - Z a) u) := by
          simp_rw [Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
          rw [integral_mul_const]
          ring
        _ ≤ _ := by
          have hs := backward_exponential_step hZa hnext hu huZ
            (squareBudget_nonneg Z (a + 1) k) hB hsmall
          rw [ht] at hs
          have hsq : (((Z (a + 1) - Z a : ℤ) : ℝ) / Z (a + 1)) ^ 2 =
              ((Z (a + 1) : ℝ)⁻¹) ^ 2 := by
            rcases hstep with hp | hm
            · rw [hp]; simp
            · rw [hm]; simp [div_pow]
          rw [hsq] at hs
          have hh := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-r)).le
          rw [← Real.exp_add] at hh
          convert hh using 1
          congr 1
          rw [squareBudget_succ]
          ring

end Freezing1.SignedUrn
