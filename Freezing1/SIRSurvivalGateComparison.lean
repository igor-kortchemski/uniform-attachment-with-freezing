module

public import Freezing1.SIRSublinearExtinction
public import Freezing1.SIRFiniteRateCapture

/-!
# Comparing early survival gates in the actual stopped epidemic
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem countsFullLaw_extinction_between_eq_sub (rate : ℝ≥0) (n a b : ℕ) (hab : a ≤ b) :
    (countsFullLaw rate n).real {H | 0 < (H a).infectious ∧ (H b).infectious = 0} =
      (countsFullLaw rate n).real {H | (H b).infectious = 0} -
        (countsFullLaw rate n).real {H | (H a).infectious = 0} := by
  let E : Set (ℕ → Counts) := {H | (H a).infectious = 0}
  let F : Set (ℕ → Counts) := {H | (H b).infectious = 0}
  have hE : MeasurableSet E := by measurability
  have hi : (countsFullLaw rate n).real (F ∩ E) = (countsFullLaw rate n).real E := by
    unfold Measure.real
    congr 1
    apply measure_congr
    filter_upwards [countsFullLaw_legal rate n] with H hl
    apply propext
    constructor
    · exact fun h => h.2
    · intro he
      exact ⟨by
        change (H b).infectious = 0
        rw [legalHistory_absorbed_persists hl he b hab]
        exact he, he⟩
  have hh := measureReal_inter_add_sdiff (μ := countsFullLaw rate n) (s := F) hE
  rw [hi] at hh
  have he : {H : ℕ → Counts | 0 < (H a).infectious ∧ (H b).infectious = 0} = F \ E := by
    ext H
    simp only [E, F, Set.mem_sdiff, mem_ofPred_eq, Nat.pos_iff_ne_zero, and_comm]
  rw [he]
  change (countsFullLaw rate n).real (F \ E) = _
  linarith

theorem sublinear_cutoff_eventually_le_fraction (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0))
    {delta : ℝ} (hd : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, cutoff n ≤ ⌊delta * n⌋₊ := by
  filter_upwards [hsmall.eventually (eventually_lt_nhds hd), eventually_ge_atTop 1]
    with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  exact Nat.le_floor ((div_lt_iff₀ hn0).mp hn).le

/-- An epidemic alive at a diverging sublinear cutoff but extinct by a
small linear time has arbitrarily small probability, in that order. -/
theorem countsFullLaw_sublinear_fraction_gate_mismatch (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0))
    {eps : ℝ} (heps : 0 < eps) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ ∀ delta ∈ Ioo (0 : ℝ) delta0,
      ∀ᶠ n : ℕ in atTop, (countsFullLaw (rate n) n).real
        {H | 0 < (H (cutoff n)).infectious ∧ (H ⌊delta * n⌋₊).infectious = 0} < eps := by
  obtain ⟨delta0, hd0, hdelta⟩ :=
    countsFullLaw_early_extinction_two_stage rate lam hlam hscaled (by positivity : 0 < eps / 4)
  have hsub := countsFullLaw_sublinear_extinction_tendsto rate lam hlam hscaled cutoff hcutoff hsmall
  refine ⟨delta0, hd0, ?_⟩
  intro delta hd
  filter_upwards [hdelta delta hd,
    hsub.eventually (Ioi_mem_nhds (by linarith : 1 / (lam : ℝ) - eps / 4 < 1 / (lam : ℝ))),
    sublinear_cutoff_eventually_le_fraction cutoff hsmall hd.1] with n hn hsn horder
  rw [countsFullLaw_extinction_between_eq_sub _ _ _ _ horder]
  have hu := (abs_lt.mp hn).2
  linarith

/-- At every fixed positive time strictly before the positive fluid zero,
extinction has exactly the branching-process limiting probability. -/
theorem countsFullLaw_preFluid_extinction_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | (H ⌊(n : ℝ) * t⌋₊).infectious = 0}) atTop (𝓝 (1 / (lam : ℝ))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have heps : 0 < 1 / (lam : ℝ) - a := by linarith
    simpa only [sub_sub_cancel, mul_comm] using
      countsFullLaw_early_extinction_lower rate lam hlam hscaled heps ht
  · intro a ha
    let e : ℝ := a - 1 / (lam : ℝ)
    have he : 0 < e := by dsimp [e]; linarith
    obtain ⟨delta0, hd0, hdelta⟩ := countsFullLaw_early_extinction_two_stage
      rate lam hlam hscaled (by positivity : 0 < e / 4)
    have hprof : 0 < infectiousProfile (lam : ℝ) t := infectiousProfile_pos_before hlam ht htt
    let delta : ℝ := min (delta0 / 2) (infectiousProfile (lam : ℝ) t / 16)
    have hd : 0 < delta := lt_min (by positivity) (by positivity)
    have hdsmall : delta < delta0 := (min_le_left _ _).trans_lt (by linarith)
    have hdp : delta < infectiousProfile (lam : ℝ) t / 8 :=
      (min_le_right _ _).trans_lt (by linarith)
    have hbad : Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
        {H | 0 < (H ⌊delta * n⌋₊).infectious ∧
          (H ⌊(n : ℝ) * t⌋₊).infectious = 0}) atTop (𝓝 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mpr
        (countsFullLaw_gated_prefix_extinct_tendsto rate hlam hscaled ht htt hd hdp)
    filter_upwards [hdelta delta ⟨hd, hdsmall⟩,
      hbad.eventually (Iio_mem_nhds (by positivity : 0 < e / 4))] with n hn hbn
    have hbound : (countsFullLaw (rate n) n).real
        {H | (H ⌊(n : ℝ) * t⌋₊).infectious = 0} ≤
      (countsFullLaw (rate n) n).real {H | (H ⌊delta * n⌋₊).infectious = 0} +
      (countsFullLaw (rate n) n).real {H | 0 < (H ⌊delta * n⌋₊).infectious ∧
        (H ⌊(n : ℝ) * t⌋₊).infectious = 0} := by
      apply (measureReal_mono ?_ (measure_ne_top _ _)).trans (measureReal_union_le _ _)
      intro H hH
      by_cases hz : (H ⌊delta * n⌋₊).infectious = 0
      · exact Or.inl hz
      · exact Or.inr ⟨Nat.pos_of_ne_zero hz, hH⟩
    have hu := (abs_lt.mp hn).2
    dsimp only [e] at hu hbn
    linarith

theorem countsFullLaw_preFluid_survival_tendsto (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | 0 < (H ⌊(n : ℝ) * t⌋₊).infectious}) atTop (𝓝 (1 - 1 / (lam : ℝ))) := by
  simpa only [countsFullLaw_survival_probability_eq_one_sub] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      (countsFullLaw_preFluid_extinction_tendsto rate lam hlam hscaled ht htt)

theorem countsFullLaw_sublinear_preFluid_gate_mismatch (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (𝓝 0))
    {t : ℝ} (ht : 0 < t) (htt : t < fluidExtinctionTime lam) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real
      {H | 0 < (H (cutoff n)).infectious ∧ (H ⌊(n : ℝ) * t⌋₊).infectious = 0})
      atTop (𝓝 0) := by
  have hh := (countsFullLaw_preFluid_extinction_tendsto rate lam hlam hscaled ht htt).sub
    (countsFullLaw_sublinear_extinction_tendsto rate lam hlam hscaled cutoff hcutoff hsmall)
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [sublinear_cutoff_eventually_le_fraction cutoff hsmall ht] with n hn
  simpa only [mul_comm] using
    (countsFullLaw_extinction_between_eq_sub (rate n) n (cutoff n) ⌊(n : ℝ) * t⌋₊
      (by simpa only [mul_comm] using hn)).symm

end Freezing1.SIR
