module

public import Freezing1.SIRLateMaximum
public import Freezing1.BennettSmallMean

/-! A corrected conditional Bennett bound on the genuine fixed-word tree laws.
The extra edge, complete event horizon and zero-charge case are explicit. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory
open scoped Topology

theorem terminal_word_cutMaximum_bennett (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) {D a : ℝ} (hD : 0 < D) (ha : 0 < a)
    (hcharge : wordLateBirthCharge n w ≤ D) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
      {s | 1 + D + a ≤ (Forward.cutMaximum s n : ℝ)} ≤
        (2 * n + 2 : ℝ) * Real.exp (-D * bennettRate (a / D)) := by
  have hu : 0 < a / D := div_pos ha hD
  have hp : 0 < 1 + a / D := by linarith only [hu]
  have ht : 0 ≤ Real.log (1 + a / D) := Real.log_nonneg (by linarith only [hu])
  have hh := terminal_word_cutMaximum_tail n w hw ht
    (by linarith only [hD, ha] : 0 < 1 + D + a) hcharge
  have hid : Real.log (1 + a / D) +
      (D * (Real.exp (Real.log (1 + a / D)) - 1) -
        Real.log (1 + a / D) * (1 + D + a)) =
        -D * bennettRate (a / D) := by
    rw [Real.exp_log hp]
    unfold bennettRate
    field_simp
    ring
  rw [mul_assoc, ← Real.exp_add, hid] at hh
  exact hh

/-- Zero late charge gives zero probability of more than one extra cut edge.
This supplies the zero-mean asymptotic branch without evaluating a quotient at zero. -/
theorem terminal_word_cutMaximum_zero_charge (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) (hcharge : wordLateBirthCharge n w ≤ 0)
    {L : ℝ} (hL : 1 < L) :
    (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
      {s | L ≤ (Forward.cutMaximum s n : ℝ)} = 0 := by
  have hexp : Tendsto (fun j : ℕ => Real.exp (-((L - 1) * j))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.const_mul_atTop (sub_pos.mpr hL)))
  have hlim := hexp.const_mul (2 * n + 2 : ℝ)
  simp only [mul_zero] at hlim
  have hb : ∀ j : ℕ,
      (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).real
        {s | L ≤ (Forward.cutMaximum s n : ℝ)} ≤
          (2 * n + 2 : ℝ) * Real.exp (-((L - 1) * j)) := by
    intro j
    have hh := terminal_word_cutMaximum_tail n w hw (Nat.cast_nonneg j)
      (lt_trans zero_lt_one hL) hcharge
    simp only [zero_mul, zero_sub] at hh
    rw [mul_assoc, ← Real.exp_add] at hh
    have hid : (j : ℝ) + -((j : ℝ) * L) = -((L - 1) * j) := by ring
    rwa [hid] at hh
  exact le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hb)) measureReal_nonneg

end Freezing1.SIR
