module

public import Freezing1.InterleavedSourceFirstSelection

/-! Exact first-selection probabilities, including the probability of
never selecting an absorbing coordinate. Fairness is used only to turn
the selection probability into one at a nonabsorbing starting state. -/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain Filter Set
open scoped ENNReal Topology Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

theorem firstSelectionValue_probability (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (x y z : E) (i side : Bool) :
    (InterleavedChain.fullLaw α κ (x, y, i)) (firstSelectionValue side z) =
      (InterleavedChain.fullLaw α κ (x, y, i)) (everSelected side) *
        α (coordinate (x, y, i) side) {z} := by
  let μ := InterleavedChain.fullLaw α κ (x, y, i)
  let a := coordinate (x, y, i) side
  let q := α a {z}
  let F : ℕ → (ℕ → State E) → ℝ≥0∞ :=
    fun N H => completion α a (observedCoordinate H side N) [z]
  let G : (ℕ → State E) → ℝ≥0∞ := fun H =>
    if H ∈ everSelected side then (if extracted H side 1 = z then 1 else 0) else q
  have hm (N : ℕ) : Measurable (F N) :=
    (measurable_of_countable (fun o : List E × List E =>
      completion α a (if side then o.1 else o.2) [z])).comp (measurable_observations N)
  have hlim : ∀ᵐ H ∂μ, Tendsto (fun N => F N H) atTop (𝓝 (G H)) := by
    apply Eventually.of_forall
    intro H
    have he : (fun N => F N H) =ᶠ[atTop] (fun _ => G H) :=
      completion_observed_singleton_eventually α H side a z
    exact tendsto_const_nhds.congr' he.symm
  have hint := tendsto_lintegral_of_dominated_convergence (μ := μ) (fun _ => 1)
    hm (fun N => Eventually.of_forall fun H => completion_le_one α a _ [z]) (by simp) hlim
  have hconst : (fun N => ∫⁻ H, F N H ∂μ) = fun _ : ℕ => q := by
    funext N
    exact lintegral_completion_observed_singleton α κ x y z i side N
  change Tendsto (fun N => ∫⁻ H, F N H ∂μ) atTop (𝓝 (∫⁻ H, G H ∂μ)) at hint
  rw [hconst] at hint
  have hval : ∫⁻ H, G H ∂μ = q := tendsto_nhds_unique hint tendsto_const_nhds
  have hG : G = (firstSelectionValue side z).indicator 1 +
      (everSelected side)ᶜ.indicator (fun _ => q) := by
    funext H
    by_cases hs : H ∈ everSelected side <;> by_cases hz : extracted H side 1 = z <;>
      simp [G, firstSelectionValue, hs, hz]
  rw [hG] at hval
  simp only [Pi.add_apply] at hval
  have hadd := lintegral_add_left (μ := μ)
    (f := (firstSelectionValue side z).indicator (1 : (ℕ → State E) → ℝ≥0∞))
    (measurable_const.indicator (measurableSet_firstSelectionValue side z))
    ((everSelected side)ᶜ.indicator (fun _ => q))
  rw [hadd,
    lintegral_indicator_one (measurableSet_firstSelectionValue side z),
    lintegral_indicator_const (measurableSet_everSelected side).compl] at hval
  rw [mul_comm q] at hval
  have hfinite : μ (everSelected side)ᶜ * q ≠ ⊤ := by
    exact ((mul_le_mul' (prob_le_one : μ (everSelected side)ᶜ ≤ 1)
      (prob_le_one : q ≤ 1)).trans_lt (by simp)).ne
  apply (ENNReal.add_left_inj hfinite).mp
  change μ (firstSelectionValue side z) + μ (everSelected side)ᶜ * q =
    μ (everSelected side) * q + μ (everSelected side)ᶜ * q
  calc
    _ = q := hval
    _ = _ := by rw [← add_mul, measure_add_measure_compl (measurableSet_everSelected side),
      measure_univ, one_mul]

theorem everSelected_probability_eq_one (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y : E) (i side : Bool)
    (ha : ¬Absorbing α (coordinate (x, y, i) side)) :
    (InterleavedChain.fullLaw α κ (x, y, i)) (everSelected side) = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_everSelected side)).mp
  cases side with
  | false => exact hf.2 x y i ha
  | true => exact hf.1 x y i ha

theorem firstSelectionValue_probability_of_nonabsorbing (α : Kernel E E) [IsMarkovKernel α]
    (κ : E × E → unitInterval) (hf : Fair α κ) (x y z : E) (i side : Bool)
    (ha : ¬Absorbing α (coordinate (x, y, i) side)) :
    (InterleavedChain.fullLaw α κ (x, y, i)) (firstSelectionValue side z) =
      α (coordinate (x, y, i) side) {z} := by
  rw [firstSelectionValue_probability,
    everSelected_probability_eq_one α κ hf x y i side ha, one_mul]

end Freezing1.InterleavedChain
