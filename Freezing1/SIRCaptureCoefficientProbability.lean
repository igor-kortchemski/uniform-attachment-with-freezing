module

public import Freezing1.SIRCaptureCoefficientCounts
public import Freezing1.SIRCaptureCoefficientAnalytic

/-! The exact source epsilon coefficient, averaged over both epidemic branches. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal Topology

set_option backward.isDefEq.respectTransparency false

theorem reverseMissingFraction_le_of_card {n k j : ℕ} {H : ℕ → Counts} {a b : ℝ}
    (h0 : H 0 = initialCounts n) (hl : ∀ l, (H l).LegalNext (H (l + 1)))
    (hn : 0 < n) (hkj : k ≤ j) (hj : j ≤ 2 * n + 1)
    (hz : (H j).infectious = 0) (hb : 0 < b) (ha : 0 ≤ a)
    (hnum : ((j - k : ℕ) : ℝ) ≤ a * n)
    (hcard : b * n ≤ (captureVertexCount n (H (2 * n + 1)) : ℝ)) :
    reverseMissingFraction n k H ≤ a / b := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < b * n := mul_pos hb hnR
  calc
    _ ≤ ((j - k : ℕ) : ℝ) / (captureVertexCount n (H (2 * n + 1)) : ℝ) :=
      reverseMissingFraction_le_late_steps h0 hl hkj hj hz
    _ ≤ (a * n) / (captureVertexCount n (H (2 * n + 1)) : ℝ) :=
      div_le_div_of_nonneg_right hnum (Nat.cast_nonneg _)
    _ ≤ (a * n) / (b * n) := div_le_div_of_nonneg_left
      (mul_nonneg ha hnR.le) hden hcard
    _ = _ := by field_simp

theorem countsFullLaw_reverseMissing_integral_bound (rate : ℕ → ℝ≥0)
    {t d a b : ℝ} (ht : 0 ≤ t) (htd : t ≤ d) (hd : d ≤ 2)
    (hb : 0 < b) (ha : d - t < a) :
    ∀ᶠ n : ℕ in atTop,
      (∫ H, reverseMissingFraction n ⌊(n : ℝ) * t⌋₊ H ∂countsFullLaw (rate n) n) ≤
        (a / b) * (countsFullLaw (rate n) n).real
          {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious} +
        (countsFullLaw (rate n) n).real {H | 0 < (H ⌊(n : ℝ) * d⌋₊).infectious} +
        (countsFullLaw (rate n) n).real
          {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious ∧
            (captureVertexCount n (H (2 * n + 1)) : ℝ) < b * n} := by
  have ha0 : 0 < a := lt_of_le_of_lt (sub_nonneg.mpr htd) ha
  have hr : 0 ≤ a / b := (div_pos ha0 hb).le
  have hscale : Tendsto (fun n : ℕ => (a - (d - t)) * n) atTop atTop :=
    Tendsto.const_mul_atTop (sub_pos.mpr ha) tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop (0 : ℕ), hscale.eventually_gt_atTop 1] with n hn hlarge
  let k : ℕ := ⌊(n : ℝ) * t⌋₊
  let j : ℕ := ⌊(n : ℝ) * d⌋₊
  let G : Set (ℕ → Counts) := {H | 0 < (H k).infectious}
  let D : Set (ℕ → Counts) := {H | 0 < (H j).infectious}
  let B : Set (ℕ → Counts) := {H | 0 < (H k).infectious ∧
    (captureVertexCount n (H (2 * n + 1)) : ℝ) < b * n}
  have hG : MeasurableSet G := by dsimp only [G]; measurability
  have hD : MeasurableSet D := by dsimp only [D]; measurability
  have hB : MeasurableSet B := by
    dsimp only [B, captureVertexCount]
    measurability
  have hkj : k ≤ j := Nat.floor_mono (mul_le_mul_of_nonneg_left htd (Nat.cast_nonneg n))
  have hj : j ≤ 2 * n + 1 := by
    have h := StoppedCoupling.floor_time_index_le (n := n) (m := 2) hd
    dsimp only [j]
    omega
  have hk : k ≤ 2 * n + 1 := hkj.trans hj
  have hnum : ((j - k : ℕ) : ℝ) ≤ a * n := by
    rw [Nat.cast_sub hkj]
    have hjle : (j : ℝ) ≤ n * d := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (ht.trans htd))
    have hklt : (n : ℝ) * t < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    nlinarith only [hjle, hklt, hlarge]
  have hiG : Integrable (G.indicator (fun _ => a / b)) (countsFullLaw (rate n) n) :=
    (integrable_const _).indicator hG
  have hiD : Integrable (D.indicator (fun _ => (1 : ℝ))) (countsFullLaw (rate n) n) :=
    (integrable_const _).indicator hD
  have hiB : Integrable (B.indicator (fun _ => (1 : ℝ))) (countsFullLaw (rate n) n) :=
    (integrable_const _).indicator hB
  have hle : ∀ᵐ H ∂countsFullLaw (rate n) n,
      reverseMissingFraction n k H ≤
        G.indicator (fun _ => a / b) H + D.indicator (fun _ => (1 : ℝ)) H +
          B.indicator (fun _ => (1 : ℝ)) H := by
    filter_upwards [countsFullLaw_initial (rate n) n, countsFullLaw_legal (rate n) n] with H h0 hl
    by_cases hg : H ∈ G
    · by_cases hd' : H ∈ D
      · have hunit := (reverseMissingFraction_bounds n k H).2
        by_cases hb' : H ∈ B <;>
          simp [hg, hd', hb'] <;> linarith only [hunit, hr]
      · by_cases hb' : H ∈ B
        · have hunit := (reverseMissingFraction_bounds n k H).2
          simp only [Set.indicator_of_mem hg, Set.indicator_of_notMem hd', Set.indicator_of_mem hb']
          linarith only [hunit, hr]
        · have hz : (H j).infectious = 0 := by change ¬ 0 < (H j).infectious at hd'; omega
          have hc : b * n ≤ (captureVertexCount n (H (2 * n + 1)) : ℝ) :=
            le_of_not_gt (fun he => hb' ⟨hg, he⟩)
          have hbound := reverseMissingFraction_le_of_card h0 hl hn hkj hj hz hb ha0.le hnum hc
          simpa only [Set.indicator_of_mem hg, Set.indicator_of_notMem hd',
            Set.indicator_of_notMem hb', add_zero] using hbound
    · have hz : (H k).infectious = 0 := by change ¬ 0 < (H k).infectious at hg; omega
      rw [reverseMissingFraction_zero_of_absorbed hl hk hz]
      have hb' : H ∉ B := fun h => hg h.1
      simp only [Set.indicator_of_notMem hg, Set.indicator_of_notMem hb', zero_add, add_zero]
      by_cases hd' : H ∈ D <;> simp [hd']
  have hInt := integral_mono_ae (reverseMissingFraction_integrable (rate n) n k)
    ((hiG.add hiD).add hiB) hle
  simp only [Pi.add_apply] at hInt
  have hiGD : Integrable (fun H => G.indicator (fun _ => a / b) H +
      D.indicator (fun _ => (1 : ℝ)) H) (countsFullLaw (rate n) n) := hiG.add hiD
  rw [integral_add hiGD hiB, integral_add hiG hiD,
    integral_indicator_const _ hG, integral_indicator_const _ hD, integral_indicator_const _ hB] at hInt
  simp only [smul_eq_mul, mul_one] at hInt
  change _ ≤ (a / b) * (countsFullLaw (rate n) n).real G +
    (countsFullLaw (rate n) n).real D + (countsFullLaw (rate n) n).real B
  nlinarith only [hInt]

/-- The exact coefficient in the source, averaged over extinction and major
outbreak: every `0<eps<t0` has eventual missing probability strictly below eps. -/
theorem countsFullLaw_reverseMissing_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      (∫ H, reverseMissingFraction n ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊ H
        ∂countsFullLaw (rate n) n) < eps := by
  obtain ⟨d, b, a, ht, hdT, hd2, hb, hbT, ha, ha0, hslack⟩ :=
    exists_same_epsilon_capture_parameters hlam heps hepsT
  let t := fluidExtinctionTime (lam : ℝ) - eps
  have htT : t < fluidExtinctionTime lam := by dsimp only [t]; linarith only [heps]
  have hgate := countsFullLaw_preFluid_survival_tendsto rate lam hlam hscaled ht htT
  have hdead := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (countsFullLaw_alive_after_fluid_zero_tendsto rate hlam hscaled hdT hd2.le)
  have hsmall := countsFullLaw_alive_small_terminal_tendsto rate lam hlam hscaled ht htT hbT
  have hsum := ((hgate.const_mul (a / b)).add hdead).add hsmall
  simp only [ENNReal.toReal_zero, add_zero] at hsum
  have he : (a / b) * (1 - 1 / (lam : ℝ)) < eps := by nlinarith only [hslack]
  filter_upwards [countsFullLaw_reverseMissing_integral_bound rate ht.le
    (htT.trans hdT).le hd2.le hb ha, hsum.eventually (eventually_lt_nhds he)] with n hn hlimit
  exact hn.trans_lt hlimit

end Freezing1.SIR
