module

public import Freezing1.SIRFiniteRateCapture
public import Freezing1.SIRStartup
public import Freezing1.LinearRegimeCutoffs

/-!
# Genuine finite-rate SIR near-origin and bulk profile estimates

The near-origin windows come from the proved relative startup estimate.
The bulk lower bounds come from the positive concave fluid curve, on the
same early survival gate. No deterministic profile is assumed of the word.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

theorem infectiousProfile_chord_lower {lam t s : ℝ} (hlam : 0 < lam)
    (ht : 0 < t) (hs : 0 ≤ s) (hst : s ≤ t) :
    s / t * infectiousProfile lam t ≤ infectiousProfile lam s := by
  have hc : ConcaveOn ℝ univ (infectiousProfile lam) :=
    (infectiousProfile_strictConcave hlam).concaveOn
  have hh := hc.2 (mem_univ (0 : ℝ)) (mem_univ t)
    (show 0 ≤ 1 - s / t from sub_nonneg.mpr ((div_le_one ht).mpr hst))
    (show 0 ≤ s / t from div_nonneg hs ht.le) (by ring : 1 - s / t + s / t = 1)
  simpa only [smul_eq_mul, infectiousProfile_zero hlam, mul_zero, zero_add,
    div_mul_cancel₀ s ht.ne'] using hh

noncomputable def finiteRateBulkFloor (lam t : ℝ) (j : ℕ) : ℝ :=
  min ((lam - 1) / (lam + 1)) (infectiousProfile lam t / (4 * t)) / ((j : ℝ) + 2)

theorem finiteRateBulkFloor_pos {lam t : ℝ} (hlam : 1 < lam)
    (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (j : ℕ) :
    0 < finiteRateBulkFloor lam t j := by
  have hp := infectiousProfile_pos_before hlam ht htt
  unfold finiteRateBulkFloor
  exact div_pos (lt_min (div_pos (by linarith) (by linarith)) (by positivity)) (by positivity)

theorem finiteRateBulkFloor_le_slope (lam t : ℝ) (j : ℕ) :
    finiteRateBulkFloor lam t j ≤ ((lam - 1) / (lam + 1)) / ((j : ℝ) + 2) :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)

theorem finiteRateBulkFloor_le_profile (lam t : ℝ) (j : ℕ) :
    finiteRateBulkFloor lam t j ≤ (infectiousProfile lam t / (4 * t)) / ((j : ℝ) + 2) :=
  div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)

theorem finiteRate_horizon_tendsto {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => ⌊t * (n : ℝ)⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop ht)

/-- Each fixed accuracy has a positive near-origin window, at any fixed
positive observation proportion and any diverging lower cutoff. -/
theorem exists_finiteRate_near_windows (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds (lam : ℝ)))
    (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) {t : ℝ} (ht : 0 < t) :
    ∃ window : ℕ → ℝ, (∀ j, 0 < window j ∧ window j < 1) ∧ ∀ j,
      Tendsto (fun n => countsFullLaw (rate n) n
        {C | ∃ i ≥ cutoff ⌊t * (n : ℝ)⌋₊, (i : ℝ) ≤ window j * ⌊t * (n : ℝ)⌋₊ ∧
          0 < (C i).infectious ∧ 1 / ((j : ℝ) + 1) ≤
            |((C i).infectious : ℝ) / i - ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|})
        atTop (nhds 0) := by
  have hcut := hcutoff.comp (finiteRate_horizon_tendsto ht)
  have hex : ∀ j : ℕ, ∃ d : ℝ, 0 < d ∧ ∀ e ∈ Ioc (0 : ℝ) d,
      Tendsto (fun n => countsFullLaw (rate n) n
        {C | ∃ i ≥ cutoff ⌊t * (n : ℝ)⌋₊, (i : ℝ) ≤ e * n ∧ 0 < (C i).infectious ∧
          1 / ((j : ℝ) + 1) ≤ |((C i).infectious : ℝ) / i -
            ((lam : ℝ) - 1) / ((lam : ℝ) + 1)|}) atTop (nhds 0) :=
    fun j => countsFullLaw_alive_relative_startup_tendsto rate lam hrate
      (fun n => cutoff ⌊t * (n : ℝ)⌋₊) hcut (by positivity)
  choose d hd hprob using hex
  let window : ℕ → ℝ := fun j => min (1 / 2) (d j / (t + 1))
  have hwpos (j : ℕ) : 0 < window j := lt_min (by norm_num) (div_pos (hd j) (by linarith))
  refine ⟨window, (fun j => ⟨hwpos j, (min_le_left _ _).trans_lt (by norm_num)⟩), ?_⟩
  intro j
  have he : window j * t ∈ Ioc (0 : ℝ) (d j) := by
    constructor
    · exact mul_pos (hwpos j) ht
    · have hh := (le_div_iff₀ (show 0 < t + 1 by linarith)).mp (min_le_right (1 / 2) (d j / (t + 1)))
      change window j * (t + 1) ≤ d j at hh
      nlinarith [hwpos j]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hprob j _ he) (fun _ => bot_le)
  intro n
  apply measure_mono
  rintro C ⟨i, hi, htime, halive, hbad⟩
  refine ⟨i, hi, ?_, halive, hbad⟩
  have hf := Nat.floor_le (mul_nonneg ht.le (Nat.cast_nonneg (α := ℝ) n))
  have hh := mul_le_mul_of_nonneg_left hf (hwpos j).le
  exact htime.trans (by nlinarith)

theorem finiteRate_bulk_bad_implies_fluid_error {lam t : ℝ} (hlam : 1 < lam)
    (ht : 0 < t) (htt : t < fluidExtinctionTime lam) {n m i j : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmlo : t * n / 2 ≤ m) (hmhi : (m : ℝ) ≤ t * n)
    (hi : (m : ℝ) / ((j : ℝ) + 2) ≤ i) (him : i ≤ m) (C : ℕ → Counts)
    (hbad : ((C i).infectious : ℝ) / m < finiteRateBulkFloor lam t j) :
    infectiousProfile lam t / (4 * ((j : ℝ) + 2)) ≤
      |((C i).infectious : ℝ) / n - infectiousProfile lam ((i : ℝ) / n)| := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hj : 0 < (j : ℝ) + 2 := by positivity
  have hp := infectiousProfile_pos_before hlam ht htt
  have hfloor := finiteRateBulkFloor_pos hlam ht htt j
  have hiR : (i : ℝ) ≤ m := by exact_mod_cast him
  have hslo : t / (2 * ((j : ℝ) + 2)) ≤ (i : ℝ) / n := by
    apply (le_div_iff₀ hnR).mpr
    have hh := (div_le_iff₀ hj).mp hi
    have hh' : t * (n : ℝ) / (2 * ((j : ℝ) + 2)) ≤ i :=
      (div_le_iff₀ (by positivity : 0 < 2 * ((j : ℝ) + 2))).mpr (by nlinarith)
    convert hh' using 1; ring
  have hshi : (i : ℝ) / n ≤ t := (div_le_iff₀ hnR).mpr (hiR.trans hmhi)
  have hchord := infectiousProfile_chord_lower (by linarith : 0 < lam) ht
    (div_nonneg (Nat.cast_nonneg i) hnR.le) hshi
  have hproflo : infectiousProfile lam t / (2 * ((j : ℝ) + 2)) ≤
      infectiousProfile lam ((i : ℝ) / n) := by
    have hh := mul_le_mul_of_nonneg_right hslo (div_nonneg hp.le ht.le)
    have he : t / (2 * ((j : ℝ) + 2)) * (infectiousProfile lam t / t) =
        infectiousProfile lam t / (2 * ((j : ℝ) + 2)) := by field_simp
    rw [he] at hh
    exact hh.trans (by convert hchord using 1; ring)
  have hI : ((C i).infectious : ℝ) / n < infectiousProfile lam t / (4 * ((j : ℝ) + 2)) := by
    have hb := (div_lt_iff₀ hmR).mp hbad
    have hmul := mul_le_mul_of_nonneg_left hmhi hfloor.le
    have hf := finiteRateBulkFloor_le_profile lam t j
    have hf' : finiteRateBulkFloor lam t j * t ≤
        infectiousProfile lam t / (4 * ((j : ℝ) + 2)) := by
      have hh := mul_le_mul_of_nonneg_right hf ht.le
      convert hh using 1; field_simp
    have hf'' := mul_le_mul_of_nonneg_right hf' hnR.le
    apply (div_lt_iff₀ hnR).mpr
    nlinarith
  have h2 : infectiousProfile lam t / (2 * ((j : ℝ) + 2)) =
      2 * (infectiousProfile lam t / (4 * ((j : ℝ) + 2))) := by field_simp; ring
  rw [h2] at hproflo
  have hneg := neg_le_abs (((C i).infectious : ℝ) / n - infectiousProfile lam ((i : ℝ) / n))
  linarith

theorem countsFullLaw_finiteRate_bulk_failure_tendsto (rate : ℕ → ℝ≥0)
    {lam t delta : ℝ} (hlam : 1 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (nhds lam))
    (ht : 0 < t) (htt : t < fluidExtinctionTime lam) (j : ℕ)
    (hd : 0 < delta) (hdsmall : delta < infectiousProfile lam t / (8 * ((j : ℝ) + 2))) :
    Tendsto (fun n => countsFullLaw (rate n) n
      {C | 0 < (C ⌊delta * (n : ℝ)⌋₊).infectious ∧ ∃ i : ℕ,
        (⌊t * (n : ℝ)⌋₊ : ℝ) / ((j : ℝ) + 2) ≤ i ∧ i ≤ ⌊t * (n : ℝ)⌋₊ ∧
        ((C i).infectious : ℝ) / ⌊t * (n : ℝ)⌋₊ < finiteRateBulkFloor lam t j})
      atTop (nhds 0) := by
  have hp := infectiousProfile_pos_before hlam ht htt
  let e : ℝ := infectiousProfile lam t / (4 * ((j : ℝ) + 2))
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : delta < e / 2 := by
    dsimp [e]
    convert hdsmall using 1; field_simp; norm_num
  have hlim := StoppedCoupling.gated_stopped_fluid_tendsto rate (by linarith : 0 < lam)
    hrate 2 he hd hsmall
  have hbound : ∀ᶠ n in atTop,
      countsFullLaw (rate n) n
        {C | 0 < (C ⌊delta * (n : ℝ)⌋₊).infectious ∧ ∃ i : ℕ,
          (⌊t * (n : ℝ)⌋₊ : ℝ) / ((j : ℝ) + 2) ≤ i ∧ i ≤ ⌊t * (n : ℝ)⌋₊ ∧
          ((C i).infectious : ℝ) / ⌊t * (n : ℝ)⌋₊ < finiteRateBulkFloor lam t j} ≤
      StoppedCoupling.fullLaw (rate n) n {H | ∃ i ≤ n * 2,
        e ≤ |((H i).1.infectious : ℝ) / n - StoppedCoupling.gatedProfile lam n ⌊delta * n⌋₊ H i|} := by
    have hratio := tendsto_floor_mul_div_nat ht.le
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      (finiteRate_horizon_tendsto ht).eventually (eventually_gt_atTop (0 : ℕ)),
      hratio.eventually (eventually_gt_nhds (half_lt_self ht))] with n hn hm hratio
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmlo : t * n / 2 ≤ (⌊t * (n : ℝ)⌋₊ : ℝ) := by
      have hh := (lt_div_iff₀ hnR).mp hratio
      nlinarith
    have hmhi := Nat.floor_le (mul_nonneg ht.le hnR.le)
    have hm2 : ⌊t * (n : ℝ)⌋₊ ≤ n * 2 := by
      apply Nat.floor_le_of_le
      have ht2 : t ≤ 2 := (htt.trans (fluidExtinctionTime_spec hlam).2.1).le
      push_cast
      nlinarith
    have hmap : Measurable (fun H : ℕ → StoppedCoupling.State => fun k => (H k).1) :=
      measurable_pi_iff.mpr fun k => measurable_fst.comp (measurable_pi_apply k)
    have hmeas : MeasurableSet {C : ℕ → Counts |
        0 < (C ⌊delta * (n : ℝ)⌋₊).infectious ∧ ∃ i : ℕ,
          (⌊t * (n : ℝ)⌋₊ : ℝ) / ((j : ℝ) + 2) ≤ i ∧ i ≤ ⌊t * (n : ℝ)⌋₊ ∧
          ((C i).infectious : ℝ) / ⌊t * (n : ℝ)⌋₊ < finiteRateBulkFloor lam t j} := by
      measurability
    rw [← StoppedCoupling.map_fullLaw_counts (rate n) n, Measure.map_apply hmap hmeas]
    apply measure_mono
    rintro H ⟨hgate, i, hi, him, hbad⟩
    have hpos := infectiousProfile_chord_lower (by linarith : 0 < lam) ht
      (div_nonneg (Nat.cast_nonneg i) hnR.le)
      ((div_le_iff₀ hnR).mpr ((by exact_mod_cast him : (i : ℝ) ≤ ⌊t * (n : ℝ)⌋₊).trans hmhi))
    have hnon : 0 ≤ infectiousProfile lam ((i : ℝ) / n) :=
      (mul_nonneg (div_nonneg (div_nonneg (Nat.cast_nonneg i) hnR.le) ht.le) hp.le).trans hpos
    refine ⟨i, him.trans hm2, ?_⟩
    rw [StoppedCoupling.gatedProfile, ite_eq_left hgate, max_eq_left hnon]
    exact finiteRate_bulk_bad_implies_fluid_error hlam ht htt hn hm hmlo hmhi hi him
      (fun k => (H k).1) hbad
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

end Freezing1.SIR
