module

import Freezing1.UniformActiveMoments

/-!
Independent expanded statement and axiom probe for root-authored A33 modules
and the A34 uniform-moment clause. The source's split at seven and displayed
tail-integral asymptotic are deliberately outside this certificate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical
open Freezing1

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    Forward.uniformActiveHeightLaw x n =
      (Measure.pi fun i : Fin n => bernoulliMeasure (1 : ℕ) 0
        (UniformBirth.reciprocalParameter x n h i)).map
        (fun Y => ∑ i : Fin n, if x (i.val + 1) then Y i else 0) := by
  rw [uniformActiveHeightLaw_eq_bernoulli_array x n h]
  change (bernoulliProductLaw _).map _ = (bernoulliProductLaw _).map _
  congr 1
  funext Y
  have hf : (Finset.univ.filter fun i : Fin n => i.val < n) = Finset.univ :=
    Finset.filter_eq_self.mpr fun i _ => i.is_lt
  simp only [UniformBirth.truncatedSum, hf, UniformBirth.maskedCoordinate]

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    (UniformBirth.reciprocalParameter x n h i : ℝ) =
      1 / (activeCount x (i.val + 1) : ℝ) := rfl

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    HasLaw (fun Y : Fin n → ℕ => Y i)
      (bernoulliMeasure (1 : ℕ) 0 (UniformBirth.reciprocalParameter x n h i))
      (Measure.pi fun j : Fin n => bernoulliMeasure (1 : ℕ) 0
        (UniformBirth.reciprocalParameter x n h j)) :=
  bernoulliProductLaw_coordinate _ i

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    iIndepFun (fun i : Fin n => fun Y : Fin n → ℕ => Y i)
      (Measure.pi fun i : Fin n => bernoulliMeasure (1 : ℕ) 0
        (UniformBirth.reciprocalParameter x n h i)) :=
  bernoulliProductLaw_independent _

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n)
    (u : ℝ) (hu : 0 < u) :
    (Forward.uniformActiveHeightLaw x n).real
      {k | u ≤ |(k : ℝ) / heightScale x n - 1|} ≤
      2 * Real.exp (-heightScale x n * ((1 + u) * Real.log (1 + u) - u)) :=
  uniformActiveHeight_closed_deviation_le x n h hn hu

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n)
    (u : ℝ) (hu : 0 < u) :
    (Forward.uniformActiveHeightLaw x n).real
      {k | u < |(k : ℝ) / heightScale x n - 1|} ≤
      2 * Real.exp (-heightScale x n * ((1 + u) * Real.log (1 + u) - u)) :=
  uniformActiveHeight_strict_deviation_le x n h hn hu

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n => (Forward.uniformActiveHeightLaw (rows n) n).real
      {k | u ≤ |(k : ℝ) / heightScale (rows n) n - 1|}) atTop (𝓝 0) :=
  uniformActiveHeight_closed_deviation_tendsto rows hrows hu

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫ k, |(k : ℝ) / heightScale x n - 1| ^ q ∂Forward.uniformActiveHeightLaw x n) ≤
      2 * (q / (1 / 2)) ^ q * Real.exp ((1 / 2) * Real.exp 1) :=
  activeHeightError_moment_le x n h hn hq

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (p : ℝ) (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (fun k : ℕ => (k : ℝ) / heightScale (rows n) n - 1)
      (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw (rows n) n)) atTop (𝓝 0) :=
  uniformActiveHeight_tendsto_Lp_via_bernoulli rows hrows hp

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n) :
    (1 : ℝ) / 2 ≤ heightScale x n := by
  have hh := UniformBirth.truncatedMean_ge_half x n h hn hn
  simpa only [UniformBirth.truncatedMean_eq_heightScale x n h (b := n) le_rfl] using hh

#print axioms CanonicalTree.forward_uniformActiveHeightLaw_eq_reverse
#print axioms uniformActiveHeightLaw_eq_bernoulli_array
#print axioms bernoulliProductLaw_independent
#print axioms UniformBirth.truncatedMean_eq_heightScale
#print axioms uniformActiveHeight_closed_deviation_le
#print axioms uniformActiveHeight_strict_deviation_le
#print axioms uniformActiveHeight_closed_deviation_tendsto
#print axioms activeHeightError_moment_le
#print axioms activeHeightError_eLpNorm_le
#print axioms uniformActiveHeight_tendsto_Lp_via_bernoulli
