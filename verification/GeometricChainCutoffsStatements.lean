module

import Freezing1.GeometricChainCutoffs

open Freezing1 Filter
open scoped Topology

example (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (hA : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((Nat.floor (Real.log (ε * n / C) / Real.log (C : ℝ)) -
        Nat.ceil (Real.log (A n) / Real.log (C : ℝ)) : ℕ) : ℝ) *
      Real.log (C : ℝ) / Real.log (n : ℝ)) atTop (𝓝 1) :=
  chain_log_span_tendsto_one C hC hA hsmall hε

example (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) :
    Tendsto (fun n => Nat.ceil (Real.log (A n) / Real.log (C : ℝ))) atTop atTop :=
  chainLowerIndex_tendsto_atTop C hC hA

#print axioms Freezing1.chainLowerIndex
#print axioms Freezing1.chainUpperIndex
#print axioms Freezing1.chainLowerIndex_tendsto_atTop
#print axioms Freezing1.chainLowerIndex_pow_lower
#print axioms Freezing1.chainUpperIndex_pow_upper
#print axioms Freezing1.tendsto_log_realCutoff_div_log_zero
#print axioms Freezing1.chainLowerIndex_div_log_tendsto_zero
#print axioms Freezing1.chainUpperArgument_tendsto_atTop
#print axioms Freezing1.chainUpperArgument_div_log_tendsto
#print axioms Freezing1.chainUpperIndex_div_log_tendsto
#print axioms Freezing1.eventually_chain_indices_lt
#print axioms Freezing1.eventually_chain_cutoff_bounds
#print axioms Freezing1.chain_log_span_tendsto_one
