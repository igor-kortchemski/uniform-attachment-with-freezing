module

import Freezing1.ForwardActiveHeightMgf
import Freezing1.ForwardIntrinsicSupport

open MeasureTheory
open Freezing1 Freezing1.Forward
open scoped Classical ENNReal

/-! Authored exact-type reconstruction: (A87) exact exponential-moment domination of the height
of a vertex born after time n by H+1 plus independent Bernoulli(1/S_i) increments, for the fixed
schedule and conditionally on the forward state at time n; (A14) schedule-free increasing labelled
trees are exactly the union over schedules of the forward supports. -/

example {x : SignSequence} {n : ℕ} {s : State} (hs : ValidAt n s)
    (hc : (s.active.card : ℤ) = activeCount x n) (K : ℕ) (hpos : PositiveThrough x (n + K))
    {c : ℝ≥0∞} (hc1 : 1 ≤ c) {k : ℕ} (hk : k + 1 ≤ K) (hx : x (n + k + 1) = true)
    {H : ℕ} (hH : ∀ a ∈ s.active, s.height a ≤ H) :
    ∫⁻ r, c ^ r.height (n + k + 1) ∂treeLawFrom x n s (k + 1) ≤
      c * (∏ i ∈ Finset.range k, (1 + (if x (n + i + 1) = true then
        (((activeCount x (n + i)).toNat : ℝ≥0∞) + 1)⁻¹ else 0) * (c - 1))) * c ^ H :=
  newVertex_height_pow_le hs hc K hpos hc1 hk hx hH

-- exact identity for the uniform active vertex
example {x : SignSequence} {n : ℕ} {s : State} (hs : ValidAt n s)
    (hc : (s.active.card : ℤ) = activeCount x n) (K : ℕ) (hpos : PositiveThrough x (n + K))
    (c : ℝ≥0∞) (k : ℕ) (hk : k ≤ K) :
    ∫⁻ r, activeHMean r (fun h => c ^ h) ∂treeLawFrom x n s k =
      (∏ i ∈ Finset.range k, attachFactor x c (n + i)) * activeHMean s (fun h => c ^ h) :=
  lintegral_activeHMean_pow_treeLawFrom hs hc K hpos c k hk

example {N : ℕ} {s : State} :
    IncreasingLabelled N s ↔
      ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧ (treeLaw x N) {s} ≠ 0 :=
  increasingLabelled_iff_exists_support

example {N : ℕ} {s : State} (h : IncreasingLabelled N s) :
    ∃ x : SignSequence, (N : ℕ∞) ≤ extinctionTime x ∧
      (treeLaw x N).real {s} = forwardHistoryWeight x N :=
  h.exists_mass

#print axioms Freezing1.Forward.newVertex_height_pow_le
#print axioms Freezing1.Forward.lintegral_activeHMean_pow_treeLawFrom
#print axioms Freezing1.Forward.increasingLabelled_iff_exists_support
#print axioms Freezing1.Forward.IncreasingLabelled.exists_mass
