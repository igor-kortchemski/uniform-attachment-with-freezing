module

public import Freezing1.ForwardPlaneKernel
public import Freezing1.CountableMarkovAvoidance
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Non-starvation for the actual finite plane interleaving

Only the globally valid active-population growth bound is used. In particular
no validity assumption on either raw finite plane state is needed.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

private theorem ratio_mono {m M n : ℕ} (hm : 0 < m) (hmM : m ≤ M) :
    (m : ℝ) / (m + n : ℝ) ≤ (M : ℝ) / (M + n : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hM : 0 < (M : ℝ) := lt_of_lt_of_le hmR (by exact_mod_cast hmM)
  apply (div_le_div_iff₀ (by positivity : 0 < (m : ℝ) + n)
    (by positivity : 0 < (M : ℝ) + n)).mpr
  have hh : (m : ℝ) ≤ M := by exact_mod_cast hmM
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

private theorem selected_weight_left (x y : State)
    (h : x.active.card + y.active.card ≠ 0) :
    (unitInterval.toNNReal (selectionParameter (x, y)) : ℝ≥0∞) =
      ENNReal.ofReal ((x.active.card : ℝ) / (x.active.card + y.active.card : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal, selectionParameter_eq x y h]

private theorem selected_weight_right (x y : State)
    (h : x.active.card + y.active.card ≠ 0) :
    (unitInterval.toNNReal (unitInterval.symm (selectionParameter (x, y))) : ℝ≥0∞) =
      ENNReal.ofReal ((y.active.card : ℝ) / (x.active.card + y.active.card : ℝ)) := by
  rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal]
  change ENNReal.ofReal (1 - (selectionParameter (x, y) : ℝ)) = _
  rw [selectionParameter_eq x y h]
  congr 1
  have hh : (x.active.card : ℝ) + y.active.card ≠ 0 := by exact_mod_cast h
  field_simp
  ring

private theorem avoid_weight_bound {a b : ℕ} (ha : 0 < a) :
    (b : ℝ) / (a + b : ℝ) ≤ (a + b : ℝ) / (a + b + 1 : ℝ) := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  apply (div_le_div_iff₀ (by positivity : 0 < (a : ℝ) + b)
    (by positivity : 0 < (a : ℝ) + b + 1)).mpr
  nlinarith

private theorem avoidance_left_succ (p : unitInterval) (x y : State) (i : Bool) (n : ℕ) :
    CountableMarkovChain.avoidanceProbability
      (InterleavedChain.transition (transition p) selectionParameter)
      (fun s => s.2.2 = false) (x, y, i) (n + 1) =
    (unitInterval.toNNReal (unitInterval.symm (selectionParameter (x, y))) : ℝ≥0∞) *
      ∫⁻ z, CountableMarkovChain.avoidanceProbability
        (InterleavedChain.transition (transition p) selectionParameter)
        (fun s => s.2.2 = false) (x, z, false) n ∂transition p y := by
  rw [CountableMarkovChain.avoidanceProbability_succ]
  simp only [InterleavedChain.transition, Kernel.coe_mk, lintegral_add_measure,
    lintegral_smul_measure]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp
  rfl

private theorem avoidance_right_succ (p : unitInterval) (x y : State) (i : Bool) (n : ℕ) :
    CountableMarkovChain.avoidanceProbability
      (InterleavedChain.transition (transition p) selectionParameter)
      (fun s => s.2.2 = true) (x, y, i) (n + 1) =
    (unitInterval.toNNReal (selectionParameter (x, y)) : ℝ≥0∞) *
      ∫⁻ z, CountableMarkovChain.avoidanceProbability
        (InterleavedChain.transition (transition p) selectionParameter)
        (fun s => s.2.2 = true) (z, y, true) n ∂transition p x := by
  rw [CountableMarkovChain.avoidanceProbability_succ]
  simp only [InterleavedChain.transition, Kernel.coe_mk, lintegral_add_measure,
    lintegral_smul_measure]
  rw [lintegral_map (measurable_of_countable _) (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
  simp
  rfl

private theorem bound_succ (N n : ℕ) :
    ENNReal.ofReal ((N : ℝ) / (N + 1 : ℝ)) *
      ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) =
        ENNReal.ofReal ((N : ℝ) / (N + (n + 1) : ℝ)) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have h1 : (N : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (N : ℝ) + 1 + n ≠ 0 := by positivity
  have h3 : (N : ℝ) + (n + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem avoidance_left_bound (p : unitInterval) (n : ℕ) (x y : State) (i : Bool)
    (ha : 0 < x.active.card) :
    CountableMarkovChain.avoidanceProbability
      (InterleavedChain.transition (transition p) selectionParameter)
      (fun s => s.2.2 = false) (x, y, i) n ≤
        ENNReal.ofReal ((x.active.card + y.active.card : ℝ) /
          (x.active.card + y.active.card + n : ℝ)) := by
  induction n generalizing x y i with
  | zero =>
    rw [CountableMarkovChain.avoidanceProbability_zero]
    have hN : (x.active.card : ℝ) + y.active.card ≠ 0 := by positivity
    simp [hN]
  | succ n ih =>
    rw [avoidance_left_succ]
    let N := x.active.card + y.active.card
    have hN : N ≠ 0 := by dsimp [N]; omega
    have hw : (unitInterval.toNNReal
        (unitInterval.symm (selectionParameter (x, y))) : ℝ≥0∞) ≤
        ENNReal.ofReal ((N : ℝ) / (N + 1 : ℝ)) := by
      rw [selected_weight_right x y hN]
      exact ENNReal.ofReal_le_ofReal (by simpa [N, Nat.cast_add] using avoid_weight_bound (b := y.active.card) ha)
    have hi : (∫⁻ z, CountableMarkovChain.avoidanceProbability
        (InterleavedChain.transition (transition p) selectionParameter)
        (fun s => s.2.2 = false) (x, z, false) n ∂transition p y) ≤
        ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) := by
      calc
        _ ≤ ∫⁻ _z, ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) ∂transition p y := by
          apply lintegral_mono_ae
          filter_upwards [transition_active_card_le p y] with z hz
          have hpos : 0 < x.active.card + z.active.card := by omega
          have hle : x.active.card + z.active.card ≤ N + 1 := by dsimp [N]; omega
          exact (ih x z false ha).trans (ENNReal.ofReal_le_ofReal (by
            simpa [Nat.cast_add] using ratio_mono (n := n) hpos hle))
        _ = _ := by rw [lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ ENNReal.ofReal ((N : ℝ) / (N + 1 : ℝ)) *
          ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) := mul_le_mul' hw hi
      _ = _ := by
        rw [bound_succ]
        simp only [N, Nat.cast_add, Nat.cast_one]

theorem avoidance_right_bound (p : unitInterval) (n : ℕ) (x y : State) (i : Bool)
    (ha : 0 < y.active.card) :
    CountableMarkovChain.avoidanceProbability
      (InterleavedChain.transition (transition p) selectionParameter)
      (fun s => s.2.2 = true) (x, y, i) n ≤
        ENNReal.ofReal ((x.active.card + y.active.card : ℝ) /
          (x.active.card + y.active.card + n : ℝ)) := by
  induction n generalizing x y i with
  | zero =>
    rw [CountableMarkovChain.avoidanceProbability_zero]
    have hN : (x.active.card : ℝ) + y.active.card ≠ 0 := by positivity
    simp [hN]
  | succ n ih =>
    rw [avoidance_right_succ]
    let N := x.active.card + y.active.card
    have hN : N ≠ 0 := by dsimp [N]; omega
    have hw : (unitInterval.toNNReal (selectionParameter (x, y)) : ℝ≥0∞) ≤
        ENNReal.ofReal ((N : ℝ) / (N + 1 : ℝ)) := by
      rw [selected_weight_left x y hN]
      exact ENNReal.ofReal_le_ofReal (by
        simpa [N, Nat.cast_add, add_comm] using avoid_weight_bound (b := x.active.card) ha)
    have hi : (∫⁻ z, CountableMarkovChain.avoidanceProbability
        (InterleavedChain.transition (transition p) selectionParameter)
        (fun s => s.2.2 = true) (z, y, true) n ∂transition p x) ≤
        ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) := by
      calc
        _ ≤ ∫⁻ _z, ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) ∂transition p x := by
          apply lintegral_mono_ae
          filter_upwards [transition_active_card_le p x] with z hz
          have hpos : 0 < z.active.card + y.active.card := by omega
          have hle : z.active.card + y.active.card ≤ N + 1 := by dsimp [N]; omega
          exact (ih z y true ha).trans (ENNReal.ofReal_le_ofReal (by
            simpa [Nat.cast_add] using ratio_mono (n := n) hpos hle))
        _ = _ := by rw [lintegral_const, measure_univ, mul_one]
    calc
      _ ≤ ENNReal.ofReal ((N : ℝ) / (N + 1 : ℝ)) *
          ENNReal.ofReal ((N + 1 : ℝ) / (N + 1 + n : ℝ)) := mul_le_mul' hw hi
      _ = _ := by
        rw [bound_succ]
        simp only [N, Nat.cast_add, Nat.cast_one]

private theorem bound_tendsto_zero (N : ℕ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((N : ℝ) / (N + n : ℝ))) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => (N : ℝ) + n) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hR : Tendsto (fun n : ℕ => (N : ℝ) / (N + n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp hR

theorem fullLaw_eventually_select_left (p : unitInterval) (x y : State) (i : Bool)
    (ha : 0 < x.active.card) :
    ∀ᵐ H ∂InterleavedChain.fullLaw (transition p) selectionParameter (x, y, i),
      ∃ n : ℕ, 0 < n ∧ (H n).2.2 = true := by
  let E : Set (ℕ → InterleavedChain.State State) :=
    {H | ¬∃ n : ℕ, 0 < n ∧ (H n).2.2 = true}
  have hsub : ∀ n, E ⊆ {H | CountableMarkovChain.avoids (fun s => s.2.2 = false) n H} := by
    intro n H hH k hk _
    cases hm : (H k).2.2 with
    | false => rfl
    | true => exact (hH ⟨k, by omega, hm⟩).elim
  have hbound : ∀ n : ℕ, (InterleavedChain.fullLaw (transition p) selectionParameter (x, y, i)) E ≤
      ENNReal.ofReal ((x.active.card + y.active.card : ℝ) /
        (x.active.card + y.active.card + n : ℝ)) := by
    intro n
    exact (measure_mono (hsub n)).trans (avoidance_left_bound p n x y i ha)
  have hlim := bound_tendsto_zero (x.active.card + y.active.card)
  simp only [Nat.cast_add] at hlim
  have hz : (InterleavedChain.fullLaw (transition p) selectionParameter (x, y, i)) E = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) bot_le
  exact ae_iff.mpr hz

theorem fullLaw_eventually_select_right (p : unitInterval) (x y : State) (i : Bool)
    (ha : 0 < y.active.card) :
    ∀ᵐ H ∂InterleavedChain.fullLaw (transition p) selectionParameter (x, y, i),
      ∃ n : ℕ, 0 < n ∧ (H n).2.2 = false := by
  let E : Set (ℕ → InterleavedChain.State State) :=
    {H | ¬∃ n : ℕ, 0 < n ∧ (H n).2.2 = false}
  have hsub : ∀ n, E ⊆ {H | CountableMarkovChain.avoids (fun s => s.2.2 = true) n H} := by
    intro n H hH k hk _
    cases hm : (H k).2.2 with
    | false => exact (hH ⟨k, by omega, hm⟩).elim
    | true => rfl
  have hbound : ∀ n : ℕ, (InterleavedChain.fullLaw (transition p) selectionParameter (x, y, i)) E ≤
      ENNReal.ofReal ((x.active.card + y.active.card : ℝ) /
        (x.active.card + y.active.card + n : ℝ)) := by
    intro n
    exact (measure_mono (hsub n)).trans (avoidance_right_bound p n x y i ha)
  have hlim := bound_tendsto_zero (x.active.card + y.active.card)
  simp only [Nat.cast_add] at hlim
  have hz : (InterleavedChain.fullLaw (transition p) selectionParameter (x, y, i)) E = 0 :=
    le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) bot_le
  exact ae_iff.mpr hz

/-- The exact source non-starvation hypotheses hold for the actual kernel,
on its whole raw countable state space. -/
theorem interleaving_fair (p : unitInterval) (hp : (p : ℝ) < 1) :
    InterleavedChain.Fair (transition p) selectionParameter := by
  constructor
  · intro x y i hn
    apply fullLaw_eventually_select_left p x y i
    apply Finset.card_pos.mpr
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun he => hn ((absorbing_iff_active_empty p hp x).mpr he)
  · intro x y i hn
    apply fullLaw_eventually_select_right p x y i
    apply Finset.card_pos.mpr
    apply Finset.nonempty_iff_ne_empty.mpr
    exact fun he => hn ((absorbing_iff_active_empty p hp y).mpr he)

end Freezing1.PlaneForward
