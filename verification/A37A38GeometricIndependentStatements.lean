module

import Freezing1.GeometricHeightUniform
import Freezing1.GeometricHeightSourceChecks
import Freezing1.IntervalFreezingCounts

/-! Source-reconstructed checks by a reviewer who did not implement the
geometric-block proof. -/

open Filter
open scoped Topology BigOperators Classical
open Freezing1 Freezing1.GeometricHeight

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b) :
    (intervalPlusCount x a b : ℤ) - intervalMinusCount x a b =
      activeCount x b - activeCount x a :=
  intervalPlusCount_sub_intervalMinusCount x hab

example (x : SignSequence) (a b : ℕ) (β C : ℝ)
    (hβ : 1 < β) (hβC : β < C) (ha : 1 ≤ a) (hratio : (a : ℝ) * C < b) :
    heightInterval x a b =
      heightInterval x a (Nat.floor (β ^ Nat.ceil (Real.log a / Real.log β))) +
      (∑ k ∈ Finset.Ico (Nat.ceil (Real.log a / Real.log β))
        (Nat.floor (Real.log b / Real.log β)),
          heightInterval x (Nat.floor (β ^ k)) (Nat.floor (β ^ (k + 1)))) +
      heightInterval x (Nat.floor (β ^ Nat.floor (Real.log b / Real.log β))) b := by
  simpa only [firstIndex, lastIndex, cut, ← heightInterval_eq_intervalSum] using
    intervalSum_partition (fun i => if x i then 1 / (activeCount x i : ℝ) else 0)
      hβ hβC ha hratio

example (x : SignSequence) (a b : ℕ) (β C A c η : ℝ)
    (hβ : 1 < β) (hβC : β < C) (hA : 1 ≤ A) (ha : A ≤ a)
    (hratio : (a : ℝ) * C < b) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c)
    (hsign : 0 ≤ (((c + 1) / 2) * (1 - 1 / β - 2 / (β * A)) - η) / (c + η))
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    ((((c + 1) / 2) * (1 - 1 / β - 2 / (β * A)) - η) / (c + η)) / Real.log β -
      2 * ((((c + 1) / 2) * (1 - 1 / β - 2 / (β * A)) - η) / (c + η)) / Real.log C ≤
      heightInterval x a b / Real.log ((b : ℝ) / a) ∧
    heightInterval x a b / Real.log ((b : ℝ) / a) ≤
      ((((c + 1) / 2) * (β - 1 + 1 / A) + β * η) / (c - η)) / Real.log β +
        (2 * (β - 1) + 1 / A) / (c - η) / Real.log C :=
  heightInterval_geometric_bounds hβ hβC hA ha hratio hc hη hηc hsign herr

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c C : ℝ)
    (hnear : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ i : ℕ, A n ≤ i → (i : ℝ) ≤ ε * n → |(activeCount (x n) i : ℝ) / i - c| ≤ δ)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hC : 1 < C) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      ∀ a b : ℕ, A n ≤ a → a < b → (b : ℝ) ≤ ε * n → (a : ℝ) * C < b →
        |heightInterval (x n) a b / Real.log ((b : ℝ) / a) - (c + 1) / (2 * c)| ≤ δ :=
  uniformLogIntervals_of_nearOriginLinear_geometric hnear hA hc hC

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c C : ℝ)
    (hnear : NearOriginLimsup x A c) (hApos : ∀ n, 0 < A n)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 < C)
    (hsurv : ∀ n, PositiveThrough (x n) n) :
    Tendsto (fun ε : ℝ => limsup (fun n => logIntervalMaximum x A c C ε n) atTop)
      (𝓝[>] 0) (𝓝 0) :=
  logIntervalLimsup_of_nearOriginLimsup_geometric hnear hApos hA hc hc1 hC hsurv

#print axioms intervalPlusCount_and_intervalMinusCount_identities
#print axioms intervalSum_partition
#print axioms complete_block_bounds
#print axioms heightInterval_geometric_bounds
#print axioms eventually_source_lowerBlock_positive
#print axioms uniformLogIntervals_of_nearOriginLinear_geometric
#print axioms logIntervalLimsup_of_nearOriginLimsup_geometric
#print axioms printed_partition_height_counterexample
#print axioms printed_last_count_counterexample
#print axioms printed_last_denominator_counterexample
