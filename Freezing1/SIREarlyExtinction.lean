module

public import Freezing1.SIRStrongCounts
public import Freezing1.SIRBiasedWalkExtinction
public import Freezing1.SIRIidCountProjection

/-!
# Exact early extinction probability for the actual stopped SIR chain

The lower bound uses fixed-prefix convergence to the actual absorbed iid
walk and its proved ruin probability. The upper bound uses the true adaptive
kernel and retains the general per-pair rate. No survival probability is
assumed as a premise.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

/-- Extinction events increase in time under the actual stopped law. -/
theorem countsFullLaw_extinction_probability_mono (rate : ℝ≥0) (n : ℕ)
    {k m : ℕ} (hkm : k ≤ m) :
    (countsFullLaw rate n).real {H | (H k).infectious = 0} ≤
      (countsFullLaw rate n).real {H | (H m).infectious = 0} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [countsFullLaw_legal rate n] with H hl hk
  rw [legalHistory_absorbed_persists hl hk m hkm]
  exact hk

/-- Any constant strictly above the limiting ruin probability bounds early
extinction, once the early observation fraction is sufficiently small. -/
theorem countsFullLaw_early_extinction_upper (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (hrlam : 1 < r * (lam : ℝ)) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioo (0 : ℝ) delta0,
      ∀ᶠ n : ℕ in atTop,
        (countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} ≤ r := by
  let delta0 : ℝ := (r * (lam : ℝ) - 1) / (2 * r * lam)
  have hx : 0 < r * (lam : ℝ) := by linarith
  obtain ⟨hr0, hl0⟩ := (mul_pos_iff.mp hx).resolve_right (by
    rintro ⟨hn, _⟩
    linarith)
  have hd0 : 0 < delta0 := by
    dsimp [delta0]
    exact div_pos (sub_pos.mpr hrlam) (by nlinarith)
  have hd1 : delta0 < 1 := by
    dsimp [delta0]
    apply (div_lt_one (by nlinarith : 0 < 2 * r * (lam : ℝ))).mpr
    nlinarith
  have hmargin : 1 < r * (lam : ℝ) * (1 - delta0) := by
    have he : r * (lam : ℝ) * (1 - delta0) = (r * (lam : ℝ) + 1) / 2 := by
      dsimp [delta0]
      field_simp [hr0.ne', hl0.ne']
      ring
    rw [he]
    linarith
  refine ⟨delta0, hd0, ?_⟩
  intro delta hdelta
  have hdlt : delta < 1 := hdelta.2.trans hd1
  have hlimit : 1 < r * (lam : ℝ) * (1 - delta) := by
    nlinarith [hdelta.2]
  have hh := (hscaled.const_mul r).mul_const (1 - delta)
  filter_upwards [hh.eventually (Ioi_mem_nhds hlimit)] with n hn
  have hm : ⌊delta * (n : ℝ)⌋₊ ≤ n := Nat.floor_le_of_le (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith)
  have hfloor := Nat.floor_le (mul_nonneg hdelta.1.le (Nat.cast_nonneg n))
  have hgap : (1 - delta) * (n : ℝ) ≤ ((n - ⌊delta * n⌋₊ : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm]
    nlinarith
  have hpressure : 1 ≤ r * (rate n : ℝ) * (n - ⌊delta * n⌋₊ : ℕ) := by
    have hh' := mul_le_mul_of_nonneg_left hgap (mul_nonneg hr (rate n).coe_nonneg)
    nlinarith
  have hbound := countsFullLaw_early_absorption_le (rate n) n ⌊delta * n⌋₊ hr hr1 hpressure
  have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [Measure.real, ENNReal.toReal_ofReal hr] using hh'

/-- The iid absorbed-walk extinction probabilities tend to `1 / lam`, with
the source infection probability substituted explicitly. -/
theorem biasedWalk_sir_extinction_tendsto (lam : ℝ≥0) (hlam : (1 : ℝ) < lam) :
    Tendsto (fun k : ℕ => (BiasedWalk.fullLaw (infectionProbability lam 1)).real
      {H | H k = 0}) atTop (𝓝 (1 / (lam : ℝ))) := by
  have hl0 : 0 < (lam : ℝ) := by linarith
  have hp : (1 : ℝ) / 2 < (infectionProbability lam 1 : ℝ) := by
    rw [infectionProbability_coe]
    simp only [Nat.cast_one, mul_one]
    apply (lt_div_iff₀ (by positivity : 0 < 1 + (lam : ℝ))).mpr
    linarith
  have hodds : (1 - (infectionProbability lam 1 : ℝ)) / (infectionProbability lam 1 : ℝ) =
      1 / (lam : ℝ) := by
    rw [infectionProbability_complement, infectionProbability_coe]
    simp only [Nat.cast_one, mul_one]
    field_simp
  have hh := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp
    (BiasedWalk.zero_probability_tendsto (infectionProbability lam 1) hp)
  rw [hodds, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (lam : ℝ))] at hh
  exact hh

/-- The actual fixed-prefix lower bound controls every positive linear early
horizon; there is no assumed limiting survival or coupling probability. -/
theorem countsFullLaw_early_extinction_lower (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      1 / (lam : ℝ) - eps <
        (countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} := by
  have hwalk := biasedWalk_sir_extinction_tendsto lam hlam
  obtain ⟨k, hk⟩ := (hwalk.eventually
    (Ioi_mem_nhds (by linarith : 1 / (lam : ℝ) - eps / 2 < 1 / (lam : ℝ)))).exists
  have hfixed := countsFullLaw_fixed_extinction_tendsto rate lam hscaled k
  have hscale : Tendsto (fun n : ℕ => delta * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hdelta tendsto_natCast_atTop_atTop
  filter_upwards [hfixed.eventually (Ioi_mem_nhds
    (by linarith : (BiasedWalk.fullLaw (infectionProbability lam 1)).real {H | H k = 0} - eps / 2 <
      (BiasedWalk.fullLaw (infectionProbability lam 1)).real {H | H k = 0})),
    hscale.eventually_ge_atTop (k : ℝ)] with n hn hnlarge
  have hkm : k ≤ ⌊delta * (n : ℝ)⌋₊ := Nat.le_floor hnlarge
  have hmono := countsFullLaw_extinction_probability_mono (rate n) n hkm
  linarith

/-- Exact early extinction probability with the order of limits required
for the shared-gate stopped fluid approximation. -/
theorem countsFullLaw_early_extinction_two_stage (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioo (0 : ℝ) delta0,
      ∀ᶠ n : ℕ in atTop,
        |(countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} -
          1 / (lam : ℝ)| < eps := by
  have hl0 : 0 < (lam : ℝ) := by linarith
  have hR0 : 0 < 1 / (lam : ℝ) := by positivity
  have hR1 : 1 / (lam : ℝ) < 1 := (div_lt_one hl0).mpr (by simpa using hlam)
  let r : ℝ := min ((1 + 1 / (lam : ℝ)) / 2) (1 / (lam : ℝ) + eps / 2)
  have hrR : 1 / (lam : ℝ) < r := by
    apply lt_min
    · linarith
    · linarith
  have hr : 0 ≤ r := hR0.le.trans hrR.le
  have hr1 : r ≤ 1 := by
    have hh := min_le_left ((1 + 1 / (lam : ℝ)) / 2) (1 / (lam : ℝ) + eps / 2)
    dsimp only [r]
    linarith
  have hrlam : 1 < r * (lam : ℝ) := by
    have hh := mul_lt_mul_of_pos_right hrR hl0
    simpa only [one_div_mul_cancel hl0.ne'] using hh
  have hreps : r < 1 / (lam : ℝ) + eps := by
    have hh := min_le_right ((1 + 1 / (lam : ℝ)) / 2) (1 / (lam : ℝ) + eps / 2)
    dsimp only [r]
    linarith
  obtain ⟨delta0, hd0, hupper⟩ := countsFullLaw_early_extinction_upper rate lam hscaled hr hr1 hrlam
  refine ⟨delta0, hd0, ?_⟩
  intro delta hdelta
  filter_upwards [hupper delta hdelta,
    countsFullLaw_early_extinction_lower rate lam hlam hscaled heps hdelta.1] with n hu hl
  rw [abs_lt]
  constructor <;> linarith

/-- The positive-infectious event is the complement of extinction for the
same actual stopped path law. -/
theorem countsFullLaw_survival_probability_eq_one_sub (rate : ℝ≥0) (n k : ℕ) :
    (countsFullLaw rate n).real {H | 0 < (H k).infectious} =
      1 - (countsFullLaw rate n).real {H | (H k).infectious = 0} := by
  have he : {H : ℕ → Counts | 0 < (H k).infectious} =
      {H | (H k).infectious = 0}ᶜ := by
    ext H
    simp only [mem_ofPred_eq, mem_compl_iff, Nat.pos_iff_ne_zero]
  rw [he, measureReal_compl (by measurability)]
  simp

theorem countsFullLaw_early_extinction_eventually (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      |(countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} -
        1 / (lam : ℝ)| < eps := by
  obtain ⟨delta0, hd0, hh⟩ := countsFullLaw_early_extinction_two_stage rate lam hlam hscaled heps
  have hp : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), 0 < delta := self_mem_nhdsWithin
  have hs : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < delta0 :=
    nhdsWithin_le_nhds (Iio_mem_nhds hd0)
  filter_upwards [hp, hs] with delta hdelta hsmall
  exact hh delta ⟨hdelta, hsmall⟩

/-- The gate used by the stopped fluid transfer has survival probability
`1 - 1 / lam`, with the same two-stage order and no survival premise. -/
theorem countsFullLaw_early_survival_eventually (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      |(countsFullLaw (rate n) n).real {H | 0 < (H ⌊delta * n⌋₊).infectious} -
        (1 - 1 / (lam : ℝ))| < eps := by
  filter_upwards [countsFullLaw_early_extinction_eventually rate lam hlam hscaled heps]
    with delta hdelta
  filter_upwards [hdelta] with n hn
  rw [countsFullLaw_survival_probability_eq_one_sub]
  have he : 1 - (countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} -
      (1 - 1 / (lam : ℝ)) =
      -((countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} - 1 / (lam : ℝ)) := by ring
  simpa only [he, abs_neg] using hn

end Freezing1.SIR
