module

import Freezing1.GeometricHeightUniform
import Freezing1.GeometricHeightSourceChecks
import Freezing1.IntervalFreezingCounts

/-! Author-created expanded geometric-route/source-correction probe. -/

open Filter
open scoped Topology BigOperators Classical NNReal
open Freezing1 Freezing1.GeometricHeight

set_option backward.isDefEq.respectTransparency false

example (x : SignSequence) (a b : ℕ) (hab : a ≤ b) :
    (intervalPlusCount x a b : ℝ) - intervalMinusCount x a b =
        (activeCount x b : ℝ) - activeCount x a ∧
    (intervalPlusCount x a b : ℝ) + intervalMinusCount x a b = (b : ℝ) - a :=
  intervalPlusCount_and_intervalMinusCount_identities x hab

example (x : SignSequence) (β C : ℝ) (a b : ℕ) (hβ : 1 < β) (hβC : β < C)
    (ha : 1 ≤ a) (hab : (a : ℝ) * C < b) :
    heightInterval x a b = heightInterval x a (Nat.floor (β ^ firstIndex β a)) +
      (∑ k ∈ Finset.Ico (firstIndex β a) (lastIndex β b),
        heightInterval x (Nat.floor (β ^ k)) (Nat.floor (β ^ (k + 1)))) +
      heightInterval x (Nat.floor (β ^ lastIndex β b)) b := by
  simpa only [← heightInterval_eq_intervalSum, cut] using intervalSum_partition
    (fun i => if x i then 1 / (activeCount x i : ℝ) else 0) hβ hβC ha hab

example (x : SignSequence) (β t A c η : ℝ) (hβ : 1 < β) (hA : 1 ≤ A)
    (hAt : A ≤ t) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc (Nat.floor t) (Nat.floor (β * t)),
      |(activeCount x i : ℝ) / i - c| ≤ η) :
    (((c + 1) / 2) * (1 - 1 / β - 2 / (β * A)) - η) / (c + η) ≤
        heightInterval x (Nat.floor t) (Nat.floor (β * t)) ∧
    heightInterval x (Nat.floor t) (Nat.floor (β * t)) ≤
      (((c + 1) / 2) * (β - 1 + 1 / A) + β * η) / (c - η) :=
  complete_block_bounds hβ hA hAt hc hη hηc herr

example (x : SignSequence) (b : ℕ) (β t A c η : ℝ) (hA : 1 ≤ A)
    (hAt : A ≤ t) (htb : t ≤ (b : ℝ)) (hb : (b : ℝ) ≤ β * t)
    (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc (Nat.floor t) b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    heightInterval x (Nat.floor t) b ≤ (β - 1 + 1 / A) / (c - η) :=
  final_partial_bound hA hAt htb hb hη hηc herr

example (x : SignSequence) (a b : ℕ) (β C A c η : ℝ) (hβ : 1 < β)
    (hβC : β < C) (hA : 1 ≤ A) (hAa : A ≤ a) (haC : (a : ℝ) * C < b)
    (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c) (hL : 0 ≤ lowerBlock c β η A)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    lowerBlock c β η A / Real.log β - 2 * lowerBlock c β η A / Real.log C ≤
        heightInterval x a b / Real.log ((b : ℝ) / a) ∧
    heightInterval x a b / Real.log ((b : ℝ) / a) ≤
      upperBlock c β η A / Real.log β +
        (2 * (β - 1) + 1 / A) / (c - η) / Real.log C :=
  heightInterval_geometric_bounds hβ hβC hA hAa haC hc hη hηc hL herr

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c β : ℝ)
    (hn : NearOriginLinear x A c) (hA : Tendsto A atTop atTop) (hc : 0 < c) (hβ : 1 < β) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
      0 ≤ nearOriginMaximum x A c ε n ∧ nearOriginMaximum x A c ε n < c ∧
      0 < lowerBlock c β (nearOriginMaximum x A c ε n) (A n) :=
  eventually_source_lowerBlock_positive hn hA hc hβ

example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c C : ℝ)
    (hnear : NearOriginLimsup x A c) (hApos : ∀ n, 0 < A n)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 < C)
    (hsurv : ∀ n, PositiveThrough (x n) n) :
    Tendsto (fun ε : ℝ => limsup (fun n : ℕ =>
      ((((((Finset.range (n + 1)).product (Finset.range (n + 1))).filter fun p =>
        A n ≤ (p.1 : ℝ) ∧ p.1 < p.2 ∧ (p.2 : ℝ) ≤ ε * n ∧ (p.1 : ℝ) * C < p.2).sup
          (fun p => (⟨|heightInterval (x n) p.1 p.2 / Real.log ((p.2 : ℝ) / p.1) -
            (c + 1) / (2 * c)|, abs_nonneg _⟩ : ℝ≥0))) : ℝ≥0) : ℝ)) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  have hh := logIntervalLimsup_of_nearOriginLimsup_geometric hnear hApos hA hc hc1 hC hsurv
  change Tendsto (fun ε : ℝ => limsup (fun n : ℕ => logIntervalMaximum x A c C ε n) atTop)
    (𝓝[>] 0) (𝓝 0) at hh
  simpa only [logIntervalMaximum, logIntervalPairs] using hh

example : firstIndex 4 2 = 1 ∧ lastIndex 4 3 = 0 ∧
    cut 4 (firstIndex 4 2) > 3 ∧ cut 4 (lastIndex 4 3) < 2 :=
  printed_partition_indices_counterexample

example : let β : ℝ := 4 / 3
    firstIndex β 2 = 3 ∧ lastIndex β 3 = 3 ∧
    1 < β ∧ β < (7 / 5 : ℝ) ∧ (2 : ℝ) * (7 / 5) < 3 ∧
    β ^ 3 ≤ (3 : ℝ) ∧ (3 : ℝ) < β ^ 4 ∧
    (β ^ 4 - β ^ 3) < (intervalPlusCount (fun _ => true) (Nat.floor (β ^ 3)) 3 : ℝ) :=
  printed_last_count_counterexample

#print axioms intervalSum_partition
#print axioms index_count_bounds
#print axioms complete_block_bounds
#print axioms initial_partial_bound
#print axioms final_partial_bound
#print axioms heightInterval_geometric_unnormalized
#print axioms heightInterval_geometric_bounds
#print axioms lowerBlock_source_endpoint
#print axioms exists_beta_zero_envelopes
#print axioms exists_diagonal_tolerance
#print axioms eventually_source_lowerBlock_positive
#print axioms uniformLogIntervals_of_nearOriginLinear_geometric
#print axioms logIntervalLimsup_of_nearOriginLimsup_geometric
#print axioms printed_partition_height_counterexample
#print axioms printed_last_count_counterexample
#print axioms printed_last_denominator_counterexample
#print axioms intervalPlusCount_sub_intervalMinusCount
#print axioms intervalPlusCount_and_intervalMinusCount_identities
