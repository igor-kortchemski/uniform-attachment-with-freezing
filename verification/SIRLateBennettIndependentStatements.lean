module

import Freezing1.SIRLateBennett

open Filter Asymptotics MeasureTheory
open Freezing1 Freezing1.SIR
open scoped Classical Topology

-- Independently reconstructed exact source rate asymptotic.
example : Tendsto (fun u : ℝ => ((1 + u) * Real.log (1 + u) - u) /
    (u * Real.log u)) atTop (𝓝 1) :=
  bennettRate_div_mul_log_tendsto_one

example : (fun u : ℝ => (1 + u) * Real.log (1 + u) - u) ~[atTop]
    (fun u : ℝ => u * Real.log u) :=
  bennettRate_isEquivalent_mul_log

-- Positivity is explicit; the zero-mean stochastic branch is a separate theorem below.
example (eps : ℝ) (heps : 0 < eps) :
    Tendsto (fun r : ℝ => r * (((1 + eps / r) * Real.log (1 + eps / r)) - eps / r))
      (𝓝[>] 0) atTop :=
  smallMean_bennettExponent_tendsto_atTop heps

example (m : ℕ → ℝ) (eps : ℝ) (heps : 0 < eps)
    (hmpos : ∀ᶠ n in atTop, 0 < m n)
    (hm : Tendsto (fun n : ℕ => m n / Real.log n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp
      (-m n * bennettRate (eps * Real.log n / m n))) atTop (𝓝 0) :=
  bennett_unionBound_tendsto_zero m heps hmpos hm

-- Actual conditional fixed-word bound: explicit extra edge and complete horizon factor.
example (n : ℕ) (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w)
    (D a : ℝ) (hD : 0 < D) (ha : 0 < a) (hcharge : wordLateBirthCharge n w ≤ D) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
      {s | 1 + D + a ≤ (Forward.cutMaximum s n : ℝ)} ≤
        (2 * n + 2 : ℝ) * Real.exp
          (-D * (((1 + a / D) * Real.log (1 + a / D)) - a / D)) :=
  terminal_word_cutMaximum_bennett n w hw hD ha hcharge

example (n : ℕ) (w : Fin (2 * n + 1) → Bool) (hw : SignWordFeasible n w)
    (hcharge : wordLateBirthCharge n w ≤ 0) (L : ℝ) (hL : 1 < L) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
      {s | L ≤ (Forward.cutMaximum s n : ℝ)} = 0 :=
  terminal_word_cutMaximum_zero_charge n w hw hcharge hL

#print axioms bennettRate_div_mul_log_tendsto_one
#print axioms bennettRate_isEquivalent_mul_log
#print axioms bennettRate_div_self_tendsto_atTop
#print axioms smallMean_bennettExponent_tendsto_atTop
#print axioms bennett_unionBound_tendsto_zero
#print axioms terminal_word_cutMaximum_tail
#print axioms terminal_word_cutMaximum_bennett
#print axioms terminal_word_cutMaximum_zero_charge
