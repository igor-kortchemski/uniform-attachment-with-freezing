module

import Freezing1.MainMaximum

open MeasureTheory Filter
open scoped Topology ENNReal

example (schedule : ℕ → Freezing1.SignSequence)
    (survives : ∀ n : ℕ, (n : ℕ∞) < Freezing1.extinctionTime (schedule n))
    (epsilon : ℝ) (hpos : 0 < epsilon) (hlt : epsilon < 1) :
    Tendsto
      (fun n : ℕ => (Freezing1.Forward.treeLaw (schedule n) n).real
        {s | 1 - epsilon ≤ (Freezing1.Forward.treeHeight s : ℝ) /
            Freezing1.heightScale (schedule n) n ∧
          (Freezing1.Forward.treeHeight s : ℝ) / Freezing1.heightScale (schedule n) n ≤
            Real.exp 1 + epsilon})
      atTop (𝓝 1) :=
  Freezing1.maximum_height_window_tendsto_one schedule survives hpos hlt

example (schedule : ℕ → Freezing1.SignSequence)
    (survives : ∀ n : ℕ, (n : ℕ∞) < Freezing1.extinctionTime (schedule n))
    (negligible : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / Freezing1.heightScale (schedule n) n)
      atTop (𝓝 0))
    (exponent : ℝ) (hexponent : 1 ≤ exponent) :
    Tendsto
      (fun n : ℕ => eLpNorm
        (fun s => (Freezing1.Forward.treeHeight s : ℝ) /
          Freezing1.heightScale (schedule n) n - 1)
        (ENNReal.ofReal exponent) (Freezing1.Forward.treeLaw (schedule n) n))
      atTop (𝓝 0) :=
  Freezing1.maximum_height_tendsto_Lp schedule survives negligible hexponent

#print axioms Freezing1.maximum_height_window_tendsto_one
#print axioms Freezing1.maximum_height_tendsto_Lp
