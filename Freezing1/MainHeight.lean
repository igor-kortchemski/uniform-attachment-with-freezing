module

public import Freezing1.ForwardHeight
public import Freezing1.MGFLimits

/-!
# Main height results for uniform attachment with freezing

The laws in these statements are constructed from Algorithm 1: first sample
the random tree, then choose uniformly among its active vertices. The stored
vertex height has been proved equal to graph distance from the root.

The proof of part I uses a direct forward-process recurrence for the active
height law, its MGF bound, and uniform higher moments. It does not assert the
paper's reverse-process Bernoulli representation or the equivalence of the two
constructions; these remain separate formalization obligations.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory Filter
open scoped Topology ENNReal

/-- Theorem `thm:height` (I): for every admissible triangular array of schedules,
the height of a conditionally uniform active vertex, normalized by `h_n⁺`,
converges to one in every real `Lᵖ`, `p ≥ 1`.

The probability measures may depend on `n`; convergence to the constant one
is expressed by convergence of the actual error norms under those laws. -/
theorem uniform_active_height_tendsto_Lp (x : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) {p : ℝ} (hp : 1 ≤ p) :
    Tendsto (fun n => eLpNorm (fun k : ℕ => (k : ℝ) / heightScale (x n) n - 1)
      (ENNReal.ofReal p) (Forward.uniformActiveHeightLaw (x n) n)) atTop (𝓝 0) := by
  apply normalized_tendsto_Lp_of_mgf_bound
    (Z := fun _ k : ℕ => (k : ℝ)) (a := fun n => heightScale (x n) n)
  · intro n
    exact measurable_of_countable _
  · intro n θ
    exact Forward.uniformActiveHeightLaw_integrable_exp (x n) n θ
  · intro n θ
    exact Forward.uniformActiveHeightLaw_mgf_le (x n) n (hτ n) θ
  · exact tendsto_heightScale_atTop x (fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n))
  · exact hp

end Freezing1
