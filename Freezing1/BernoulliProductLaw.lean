module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Explicit independent Bernoulli products and their partial sums

The probability space is an actual finite product of two-point measures.
Adding a previously unused coordinate has exactly the same shifted-Bernoulli
kernel as the height recursion in the reverse forest construction.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def bernoulliProductLaw (p : ι → unitInterval) : Measure (ι → ℕ) :=
  Measure.pi fun i => bernoulliMeasure (1 : ℕ) 0 (p i)

instance bernoulliProductLaw_probability (p : ι → unitInterval) :
    IsProbabilityMeasure (bernoulliProductLaw p) := by
  unfold bernoulliProductLaw
  infer_instance

theorem bernoulliProductLaw_coordinate (p : ι → unitInterval) (i : ι) :
    HasLaw (fun ω : ι → ℕ => ω i) (bernoulliMeasure (1 : ℕ) 0 (p i))
      (bernoulliProductLaw p) :=
  (measurePreserving_eval (fun j => bernoulliMeasure (1 : ℕ) 0 (p j)) i).hasLaw

theorem bernoulliProductLaw_independent (p : ι → unitInterval) :
    iIndepFun (fun i (ω : ι → ℕ) => ω i) (bernoulliProductLaw p) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

noncomputable def bernoulliPartialSumLaw (p : ι → unitInterval) (s : Finset ι) : Measure ℕ :=
  (bernoulliProductLaw p).map (fun ω => ∑ i ∈ s, ω i)

instance bernoulliPartialSumLaw_probability (p : ι → unitInterval) (s : Finset ι) :
    IsProbabilityMeasure (bernoulliPartialSumLaw p s) := by
  unfold bernoulliPartialSumLaw
  exact Measure.isProbabilityMeasure_map_iff (by fun_prop) |>.mpr inferInstance

theorem bernoulliPartialSumLaw_hasLaw (p : ι → unitInterval) (s : Finset ι) :
    HasLaw (fun ω : ι → ℕ => ∑ i ∈ s, ω i) (bernoulliPartialSumLaw p s)
      (bernoulliProductLaw p) := hasLaw_map (by fun_prop)

@[simp] theorem bernoulliPartialSumLaw_empty (p : ι → unitInterval) :
    bernoulliPartialSumLaw p ∅ = Measure.dirac 0 := by
  simp [bernoulliPartialSumLaw]

/-- Binding by a Bernoulli unit increment is additive convolution. -/
theorem bind_shifted_bernoulli_eq_conv (μ : Measure ℕ) (p : unitInterval) :
    μ.bind (fun d => bernoulliMeasure (d + 1) d p) =
      μ ∗ bernoulliMeasure (1 : ℕ) 0 p := by
  rw [Measure.conv, Measure.prod_eq_of_sfinite,
    Measure.map_bind (measurable_of_countable _).aemeasurable (by fun_prop)]
  congr 1
  funext d
  rw [Measure.map_map (by fun_prop) (by fun_prop), map_bernoulliMeasure]
  simp only [Function.comp_def, add_zero]

/-- The exact partial-sum recursion, derived from the product-space independence. -/
theorem bernoulliPartialSumLaw_insert [DecidableEq ι] (p : ι → unitInterval) (s : Finset ι)
    {i : ι} (hi : i ∉ s) :
    bernoulliPartialSumLaw p (insert i s) =
      (bernoulliPartialSumLaw p s).bind
        (fun d => bernoulliMeasure (d + 1) d (p i)) := by
  have h_ind : IndepFun (fun ω : ι → ℕ => ∑ j ∈ s, ω j) (fun ω => ω i)
      (bernoulliProductLaw p) := by
    simpa only [Finset.sum_fn] using
      (bernoulliProductLaw_independent p).indepFun_finsetSum_of_notMem
        (fun _ => measurable_pi_apply _) hi
  have h_sum := IndepFun.hasLaw_fun_add (bernoulliPartialSumLaw_hasLaw p s)
    (bernoulliProductLaw_coordinate p i) h_ind
  calc
    bernoulliPartialSumLaw p (insert i s) =
        (bernoulliProductLaw p).map (fun ω => (∑ j ∈ s, ω j) + ω i) := by
      unfold bernoulliPartialSumLaw
      congr 1
      funext ω
      simp [Finset.sum_insert hi, add_comm]
    _ = bernoulliPartialSumLaw p s ∗ bernoulliMeasure (1 : ℕ) 0 (p i) := h_sum.map_eq
    _ = _ := (bind_shifted_bernoulli_eq_conv _ _).symm

end Freezing1
