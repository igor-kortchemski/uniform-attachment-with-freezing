module

import Freezing1.MainHeight

open MeasureTheory Filter
open scoped Topology ENNReal

example (schedule : ℕ → Freezing1.SignSequence)
    (survives : ∀ n : ℕ, (n : ℕ∞) < Freezing1.extinctionTime (schedule n))
    (exponent : ℝ) (hexponent : 1 ≤ exponent) :
    Tendsto
      (fun n : ℕ => eLpNorm
        (fun h : ℕ => (h : ℝ) / Freezing1.heightScale (schedule n) n - 1)
        (ENNReal.ofReal exponent)
        (Freezing1.Forward.uniformActiveHeightLaw (schedule n) n))
      atTop (𝓝 0) :=
  Freezing1.uniform_active_height_tendsto_Lp schedule survives hexponent

#print axioms Freezing1.uniform_active_height_tendsto_Lp
#print axioms Freezing1.Forward.ValidAt.exists_tree_walk_length_height
#print axioms Freezing1.Forward.ValidAt.height_eq_tree_dist
