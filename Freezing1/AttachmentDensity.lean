module

public import Freezing1.AttachmentReciprocalSeries

/-! The literal density and post-step reciprocal assertions in source A21. -/

@[expose] public section

namespace Freezing1.Forward

open Filter
open scoped Topology

theorem attachment_density_ge_half (x : SignSequence) (hτ : extinctionTime x = ⊤)
    (n : ℕ) (hn : 1 ≤ n) : (1 : ℝ) / 2 ≤ (plusCount x n : ℝ) / n := by
  have hp : PositiveThrough x n := fun i _ => (extinctionTime_eq_top_iff x).mp hτ i
  have hh : (n : ℝ) ≤ 2 * (plusCount x n : ℝ) := by exact_mod_cast le_two_mul_plusCount hp
  apply (le_div_iff₀ (by exact_mod_cast (show 0 < n by omega) : (0 : ℝ) < n)).mpr
  linarith

theorem printed_attachment_reciprocal_sum_tendsto (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
      if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) atTop atTop :=
  tendsto_heightScale_atTop (fun _ => x)
    (fun _ i _ => (extinctionTime_eq_top_iff x).mp hτ i)

end Freezing1.Forward
