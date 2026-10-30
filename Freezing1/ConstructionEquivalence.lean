module

public import Freezing1.AtomicMeasureComparison
public import Freezing1.CanonicalReversePointMass
public import Freezing1.CanonicalForwardShape

/-!
# Equality in law of the two constructions

The canonical reverse state has an actual forward history. Its point mass
equals the forward product because its reachable fiber has exactly `S_n!`
elements, each with the proved reverse mass. Atomic probability comparison
then identifies the full state laws and their common source observable.

The observable retains the rooted graph, every frozen label, and every edge
timestamp (recovered as the maximum endpoint birth ID). Only the arbitrary
names of active reverse vertices are forgotten. The proof uses the corrected
reachable support, not the paper's insufficient shape-only support assertion.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory
open scoped ENNReal

theorem reverseStateLaw_hasForwardHistory (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ s ∂reverseStateLaw x n, Forward.HasHistory x n s := by
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [treeLaw_reverseState_historyShape x n hn] with F hF
  exact hF.hasHistory

/-- Equality of complete canonical functional states, including the endpoint
where all vertices have frozen. -/
theorem reverseStateLaw_eq_forward_treeLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    reverseStateLaw x n = Forward.treeLaw x n := by
  apply probability_eq_of_ae_singleton_eq
  · filter_upwards [reverseStateLaw_real_singleton_ae x n hn] with s hs
    intro hzero
    rw [Measure.real, hzero, ENNReal.toReal_zero] at hs
    exact (ne_of_gt (forwardHistoryWeight_pos x n hn)) hs.symm
  · filter_upwards [reverseStateLaw_real_singleton_ae x n hn,
      reverseStateLaw_hasForwardHistory x n hn] with s hs hhist
    have hforward := Forward.treeLaw_real_singleton_of_hasHistory x n hn hhist
    calc
      (reverseStateLaw x n) {s} = ENNReal.ofReal ((reverseStateLaw x n).real {s}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = ENNReal.ofReal ((Forward.treeLaw x n).real {s}) := by rw [hs, hforward]
      _ = (Forward.treeLaw x n) {s} := ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- The two source algorithms have the same rooted, edge-timestamped,
frozen-label-preserving tree law after erasing active-label distinctions. -/
theorem construction_laws_eq (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) : forwardLaw x n = reverseLaw x n := by
  unfold forwardLaw
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn]
  exact map_reverseStateLaw x n hn

end Freezing1.CanonicalTree
