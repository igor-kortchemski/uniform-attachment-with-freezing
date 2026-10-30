module

public import Freezing1.SignedUrn
public import Freezing1.ReversePairHeightBlocks

/-!
# Finite continuation of the signed urn

The law is the iterated actual two-point kernel, with a prescribed integer
population schedule. No moment estimate is part of its definition.
-/

@[expose] public section

namespace Freezing1.SignedUrn

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Start at time a and perform k transitions of the prescribed schedule. -/
noncomputable def continuationLaw (Z : ℕ → ℤ) : ℕ → ℕ → ℤ → Measure ℤ
  | _, 0, u => Measure.dirac u
  | a, k + 1, u => (transitionLaw (Z a) (Z (a + 1) - Z a) u).bind
      (continuationLaw Z (a + 1) k)

instance continuationLaw_probability (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) :
    IsProbabilityMeasure (continuationLaw Z a k u) := by
  induction k generalizing a u with
  | zero => change IsProbabilityMeasure (Measure.dirac u); infer_instance
  | succ k ih =>
    change IsProbabilityMeasure ((transitionLaw _ _ _).bind _)
    exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall (fun v => ih (a + 1) v))

/-- Any real test function is integrable for this finite-branching law. -/
theorem continuationLaw_integrable (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) (f : ℤ → ℝ) :
    Integrable f (continuationLaw Z a k u) := by
  induction k generalizing a u with
  | zero => exact integrable_dirac (by simp)
  | succ k ih =>
    let κ : Kernel ℤ ℤ := ⟨continuationLaw Z (a + 1) k, measurable_of_countable _⟩
    have hκ : IsMarkovKernel κ := ⟨fun v => continuationLaw_probability Z (a + 1) k v⟩
    let μ := transitionLaw (Z a) (Z (a + 1) - Z a) u
    have hi : Integrable f ((κ ∘ₖ Kernel.const Unit μ) ()) := by
      apply (ProbabilityTheory.integrable_comp_iff
        (measurable_of_countable f).aestronglyMeasurable).mpr
      constructor
      · exact Filter.Eventually.of_forall (fun v => ih (a + 1) v)
      · exact integrable_bernoulliMeasure _ _ _ _
    simpa only [κ, μ, continuationLaw, Kernel.coe_mk, Kernel.comp_apply,
      Kernel.const_apply] using hi

/-- Recursion of expectations through the actual transition, not a separately
postulated scalar process. -/
theorem integral_continuationLaw_succ (Z : ℕ → ℤ) (a k : ℕ) (u : ℤ) (f : ℤ → ℝ) :
    (∫ v, f v ∂continuationLaw Z a (k + 1) u) =
      ∫ w, (∫ v, f v ∂continuationLaw Z (a + 1) k w)
        ∂transitionLaw (Z a) (Z (a + 1) - Z a) u := by
  exact integral_bind_of_integrable _ _ (measurable_of_countable _)
    (continuationLaw_integrable Z a (k + 1) u f)

theorem continuationLaw_valid (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) :
    ∀ᵐ v ∂continuationLaw Z a k u, 0 ≤ v ∧ v ≤ Z (a + k) := by
  induction k generalizing a u with
  | zero => simpa [continuationLaw] using (show 0 ≤ u ∧ u ≤ Z a from ⟨hu, huZ⟩)
  | succ k ih =>
    have hZa := hZ a (by simp)
    have hnext : 0 < Z a + (Z (a + 1) - Z a) := by
      simpa using hZ (a + 1) (by simp)
    have hv := transitionLaw_valid hZa hnext (hz a (by simp)) hu huZ
    apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
    rw [continuationLaw, Measure.bind_apply (Set.to_countable _).measurableSet
      (measurable_of_countable _).aemeasurable]
    calc
      _ = ∫⁻ _w, (1 : ℝ≥0∞) ∂transitionLaw (Z a) (Z (a + 1) - Z a) u := by
        apply lintegral_congr_ae
        filter_upwards [hv] with w hw
        have hi := ih (a := a + 1) (u := w)
          (fun i hi => hZ i (by simp only [Finset.mem_Icc] at hi ⊢; omega))
          (fun i hi => hz i (by simp only [Finset.mem_Ico] at hi ⊢; omega))
          hw.1 (by simpa using hw.2)
        have he : a + 1 + k = a + (k + 1) := by omega
        rw [he] at hi
        exact (ae_iff_prob_eq_one (measurable_of_countable _)).mp hi
      _ = 1 := by simp

/-- Quadratic budget over the next k transitions. -/
noncomputable def squareBudget (Z : ℕ → ℤ) (a k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc a (a + k), ((Z i : ℝ)⁻¹) ^ 2

theorem squareBudget_nonneg (Z : ℕ → ℤ) (a k : ℕ) : 0 ≤ squareBudget Z a k :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem squareBudget_succ (Z : ℕ → ℤ) (a k : ℕ) :
    squareBudget Z a (k + 1) = ((Z (a + 1) : ℝ)⁻¹) ^ 2 + squareBudget Z (a + 1) k := by
  unfold squareBudget
  rw [show a + (k + 1) = (a + 1) + k by omega]
  symm
  simpa only [Nat.Ioc_succ_singleton, Finset.sum_singleton] using
    Finset.sum_Ioc_consecutive (fun i => ((Z i : ℝ)⁻¹) ^ 2)
      (Nat.le_succ a) (show a + 1 ≤ a + 1 + k by omega)

/-- The finite endpoint MGF, proved by backward iteration of the actual urn.
The two smallness hypotheses are exactly the quadratic and largest-step budgets. -/
theorem continuationLaw_exponential_le (Z : ℕ → ℤ) {a k : ℕ} {u : ℤ}
    (hZ : ∀ i ∈ Finset.Icc a (a + k), 0 < Z i)
    (hz : ∀ i ∈ Finset.Ico a (a + k), Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z a) {θ : ℝ}
    (hbudget : |θ| * squareBudget Z a k ≤ 1 / 4)
    (hinc : ∀ i ∈ Finset.Ioc a (a + k), |θ / (Z i : ℝ)| ≤ 1 / 4) :
    (∫ v, Real.exp (θ * ((v : ℝ) / Z (a + k))) ∂continuationLaw Z a k u) ≤
      Real.exp ((θ * (1 + θ * squareBudget Z a k)) * ((u : ℝ) / Z a)) := by
  induction k generalizing a u with
  | zero => simp [continuationLaw, squareBudget]
  | succ k ih =>
    have hend : a + 1 + k = a + (k + 1) := by omega
    have hZa := hZ a (by simp)
    have hnext : 0 < Z a + (Z (a + 1) - Z a) := by
      simpa using hZ (a + 1) (by simp)
    have hstep := hz a (by simp)
    have hB : |θ| * squareBudget Z (a + 1) k ≤ 1 / 4 := by
      rw [squareBudget_succ] at hbudget
      have hn := mul_nonneg (abs_nonneg θ) (sq_nonneg ((Z (a + 1) : ℝ)⁻¹))
      nlinarith
    have hsmall : |θ * (((Z (a + 1) - Z a : ℤ) : ℝ) /
        ((Z a : ℝ) + ((Z (a + 1) - Z a : ℤ) : ℝ)))| ≤ 1 / 4 := by
      have hi := hinc (a + 1) (by simp)
      have ht : (Z a : ℝ) + ((Z (a + 1) - Z a : ℤ) : ℝ) = Z (a + 1) := by push_cast; ring
      rw [ht]
      rcases hstep with hp | hm
      · rw [hp]; simpa only [Int.cast_one, mul_one_div] using hi
      · rw [hm]; simpa only [Int.cast_neg, Int.cast_one, div_neg, neg_div,
          mul_neg, mul_one_div, abs_neg] using hi
    rw [integral_continuationLaw_succ]
    calc
      _ ≤ ∫ w, Real.exp ((θ * (1 + θ * squareBudget Z (a + 1) k)) *
          ((w : ℝ) / Z (a + 1))) ∂transitionLaw (Z a) (Z (a + 1) - Z a) u := by
        apply integral_mono_ae (integrable_bernoulliMeasure _ _ _ _)
          (integrable_bernoulliMeasure _ _ _ _)
        filter_upwards [transitionLaw_valid hZa hnext hstep hu huZ] with w hw
        have hh := ih (a := a + 1) (u := w)
          (fun i hi => hZ i (by simp only [Finset.mem_Icc] at hi ⊢; omega))
          (fun i hi => hz i (by simp only [Finset.mem_Ico] at hi ⊢; omega))
          hw.1 (by simpa using hw.2) hB
          (fun i hi => hinc i (by simp only [Finset.mem_Ioc] at hi ⊢; omega))
        simpa only [hend] using hh
      _ ≤ _ := by
        have hs := backward_exponential_step hZa hnext hu huZ
          (squareBudget_nonneg Z (a + 1) k) hB hsmall
        have ht : (Z a : ℝ) + ((Z (a + 1) - Z a : ℤ) : ℝ) = Z (a + 1) := by push_cast; ring
        rw [ht] at hs
        have hsq : (((Z (a + 1) - Z a : ℤ) : ℝ) / Z (a + 1)) ^ 2 =
            ((Z (a + 1) : ℝ)⁻¹) ^ 2 := by
          rcases hstep with hp | hm
          · rw [hp]; simp
          · rw [hm]; simp [div_pow]
        rw [hsq] at hs
        simpa only [squareBudget_succ, add_comm (squareBudget Z (a + 1) k)] using hs

end Freezing1.SignedUrn
