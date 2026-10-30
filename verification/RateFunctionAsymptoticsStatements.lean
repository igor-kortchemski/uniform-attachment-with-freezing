module

import Freezing1.BennettSmallMean

open Filter Asymptotics
open scoped Topology

example : Tendsto (fun u : ℝ =>
    ((1 + u) * Real.log (1 + u) - u) / (u * Real.log u)) atTop (𝓝 1) :=
  Freezing1.bennettRate_div_mul_log_tendsto_one

example : (fun u : ℝ => (1 + u) * Real.log (1 + u) - u) ~[atTop]
    (fun u => u * Real.log u) := Freezing1.bennettRate_isEquivalent_mul_log

example (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun r : ℝ => r * ((1 + ε / r) * Real.log (1 + ε / r) - ε / r))
      (𝓝[>] 0) atTop := Freezing1.smallMean_bennettExponent_tendsto_atTop hε

example (mean : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hpos : ∀ᶠ n in atTop, 0 < mean n)
    (hsmall : Tendsto (fun n : ℕ => mean n / Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-mean n *
      ((1 + ε * Real.log n / mean n) * Real.log (1 + ε * Real.log n / mean n) -
        ε * Real.log n / mean n))) atTop (𝓝 0) :=
  Freezing1.bennett_unionBound_tendsto_zero mean hε hpos hsmall

#print axioms Freezing1.bennettRate_div_mul_log_tendsto_one
#print axioms Freezing1.bennettRate_isEquivalent_mul_log
#print axioms Freezing1.bennettRate_div_self_tendsto_atTop
#print axioms Freezing1.smallMean_bennettExponent_tendsto_atTop
#print axioms Freezing1.bennett_unionBound_tendsto_zero
