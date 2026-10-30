module

public import Freezing1.ForwardCutTruncation
public import Freezing1.ForwardTruncationLaw

/-!
# The terminal block count has its genuine prefix marginal

The block statistic read from the final tree agrees with the same statistic
at its right endpoint, both deterministically and in law. The endpoint
identification with the tagged continuation is proved in ForwardTaggedCounts.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical

theorem treeLaw_blockTallCount_prefix (x : SignSequence) {n b : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hb : b ≤ n) (a : ℕ) (t : ℝ) :
    (treeLaw x n).map (fun s => blockTallCount s a b t) =
      (treeLaw x b).map (fun s => blockTallCount s a b t) := by
  rw [← treeLaw_map_truncate x hn hb,
    Measure.map_map measurable_from_top measurable_from_top]
  apply Measure.map_congr
  filter_upwards [treeLaw_valid x n] with s hs
  exact (blockTallCount_truncateAt hs a b t).symm

end Freezing1.Forward
