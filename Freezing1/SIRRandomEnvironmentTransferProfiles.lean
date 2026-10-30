module

public import Freezing1.SIRRandomEnvironmentTransferUniform
public import Freezing1.MainLinearMaximumLower

/-!
# Uniform finite-environment versions of the deterministic linear theorem

One relative active-count profile on the whole interval after a cutoff
implies both near-origin and bulk hypotheses. Deterministic T04 can thus be
uniformized before averaging over a genuinely random environment.
-/

@[expose] public section

namespace Freezing1.SIR.RandomEnvironment

open Filter MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def ProfileGood (cutoff : ℕ → ℕ) (c : ℝ) (n : ℕ) (x : SignSequence) (e : ℝ) : Prop :=
  ∀ i : ℕ, cutoff n ≤ i → i ≤ n → |(activeCount x i : ℝ) / i - c| ≤ e

noncomputable def cutoffScale (cutoff : ℕ → ℕ) (n : ℕ) : ℝ := (cutoff n : ℝ) + 1

theorem cutoffScale_pos (cutoff : ℕ → ℕ) (n : ℕ) : 0 < cutoffScale cutoff n := by
  dsimp [cutoffScale]
  positivity

theorem cutoffScale_tendsto (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop) :
    Tendsto (cutoffScale cutoff) atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hcutoff)

theorem cutoffScale_sublog (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ => cutoffScale cutoff n / Real.log (n : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hh := hsmall.add ((tendsto_const_nhds (x := (1 : ℝ))).div_atTop hlog)
  simpa only [cutoffScale, add_div, add_zero] using hh

theorem ProfileGood.mono {cutoff : ℕ → ℕ} {c e d : ℝ} {n : ℕ} {x : SignSequence}
    (h : ProfileGood cutoff c n x e) (hed : e ≤ d) : ProfileGood cutoff c n x d :=
  fun i hi hin => (h i hi hin).trans hed

theorem balanced_profileGood (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n in atTop, ProfileGood cutoff c n (balancedSchedule c) e := by
  have hcut : Tendsto (fun n => (cutoff n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hcutoff
  filter_upwards [hcut.eventually (eventually_gt_atTop (3 / e))] with n hn
  intro i hi _
  have hiR : (cutoff n : ℝ) ≤ i := by exact_mod_cast hi
  have hip : (0 : ℝ) < i := (div_pos (by norm_num) he).trans (hn.trans_le hiR)
  apply (balancedSchedule_relative_error hc hc1 (by exact_mod_cast hip)).trans
  apply (div_le_iff₀ hip).mpr
  have hh := (div_lt_iff₀ he).mp (hn.trans_le hiR)
  nlinarith

theorem nearOrigin_of_profile (cutoff : ℕ → ℕ) (rows : ℕ → SignSequence) (c : ℝ)
    (hprofile : ∀ e > 0, ∀ᶠ n in atTop, ProfileGood cutoff c n (rows n) e) :
    NearOriginLinear rows (cutoffScale cutoff) c := by
  intro e he
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hprofile e he] with n hn
  intro i hi htime
  have hcutR : (cutoff n : ℝ) ≤ i := by
    change (cutoff n : ℝ) + 1 ≤ i at hi
    linarith
  have hinR : (i : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hn i (by exact_mod_cast hcutR) (by exact_mod_cast hinR)

theorem bulk_of_profile (cutoff : ℕ → ℕ) (rows : ℕ → SignSequence) {c : ℝ} (hc : 0 < c)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0))
    (hprofile : ∀ e > 0, ∀ᶠ n in atTop, ProfileGood cutoff c n (rows n) e) :
    BulkLowerBound rows := by
  intro e he _
  refine ⟨c * e / 2, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    hsmall.eventually (eventually_lt_nhds he), hprofile (c / 2) (by positivity)]
      with n hn hcut hgood
  intro i hi hin
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcutR : (cutoff n : ℝ) < e * n := (div_lt_iff₀ hnR).mp hcut
  have hci : cutoff n ≤ i := by exact_mod_cast (hcutR.trans_le hi).le
  have hiR : (0 : ℝ) < i := (mul_pos he hnR).trans_le hi
  have hh := (abs_le.mp (hgood i hci hin)).1
  have hlow : c / 2 ≤ (activeCount (rows n) i : ℝ) / i := by linarith
  have hlow' := (le_div_iff₀ hiR).mp hlow
  have hm := mul_le_mul_of_nonneg_left hi hc.le
  apply (le_div_iff₀ hnR).mpr
  nlinarith

theorem linear_inputs_of_profile (cutoff : ℕ → ℕ) (rows : ℕ → SignSequence)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0))
    (hpositive : ∀ n, PositiveThrough (rows n) n)
    (hprofile : ∀ e > 0, ∀ᶠ n in atTop, ProfileGood cutoff c n (rows n) e) :
    NearOriginLimsup rows (cutoffScale cutoff) c ∧ BulkLiminf rows := by
  refine ⟨(nearOriginLimsup_iff rows (cutoffScale cutoff) (cutoffScale_pos cutoff)
      hc.le hc1 hpositive).mpr (nearOrigin_of_profile cutoff rows c hprofile), ?_⟩
  apply (bulkLiminf_iff rows hpositive).mpr
  exact bulk_of_profile cutoff rows hc (tendsto_natCutoff_div_nat_zero_of_sublog hsmall) hprofile

theorem uniform_profile_bound (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (score : ℕ → SignSequence → ℝ)
    (hlimit : ∀ rows : ℕ → SignSequence, (∀ n, PositiveThrough (rows n) n) →
      (∀ e > 0, ∀ᶠ n in atTop, ProfileGood cutoff c n (rows n) e) →
      Tendsto (fun n => score n (rows n)) atTop (nhds 0))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ e > 0, ∃ N, ∀ n ≥ N, ∀ x, PositiveThrough x n → ProfileGood cutoff c n x e →
      score n x < eta := by
  apply uniform_bound_of_sequential (fun n x => PositiveThrough x n)
    (ProfileGood cutoff c) score (fun _ => balancedSchedule c) ?_ ?_ ?_ hlimit heta
  · intro n
    exact (lt_extinctionTime_iff _ _).mp (by rw [balancedSchedule_survives hc hc1]; simp)
  · exact fun e he => balanced_profileGood cutoff hcutoff hc hc1 he
  · exact fun _ _ _ _ hed hh => hh.mono hed

theorem uniform_profile_height_bound (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0))
    {c eps eta : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ e > 0, ∃ N, ∀ n ≥ N, ∀ x, PositiveThrough x n → ProfileGood cutoff c n x e →
      (Forward.uniformHeightLaw x n).real
        {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (c + 1) / (2 * c)|} < eta := by
  apply uniform_profile_bound cutoff hcutoff hc hc1 _ ?_ heta
  intro rows hpositive hprofile
  have hin := linear_inputs_of_profile cutoff rows hc hc1 hsmall hpositive hprofile
  have hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n) :=
    fun n => (lt_extinctionTime_iff _ _).mpr (hpositive n)
  have hscale := linear_heightScale_tendsto rows (cutoffScale cutoff) hc hc1
    (cutoffScale_pos cutoff) (cutoffScale_tendsto cutoff hcutoff) (cutoffScale_sublog cutoff hsmall)
    hτ hin.1 hin.2
  have hbulk := bulk_of_profile cutoff rows hc
    (tendsto_natCutoff_div_nat_zero_of_sublog hsmall) hprofile
  have hh := linear_uniform_height_deviation_tendsto_zero (by positivity : 0 < (c + 1) / (2 * c))
    hτ hscale hbulk heps
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hh
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using hr

theorem uniform_profile_distance_bound (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0))
    {c eps eta : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (heps : 0 < eps) (heta : 0 < eta) :
    ∃ e > 0, ∃ N, ∀ n ≥ N, ∀ x, PositiveThrough x n → ProfileGood cutoff c n x e →
      (CanonicalTree.forwardPairDataLaw x n).real
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c|} < eta := by
  apply uniform_profile_bound cutoff hcutoff hc hc1 _ ?_ heta
  intro rows hpositive hprofile
  have hin := linear_inputs_of_profile cutoff rows hc hc1 hsmall hpositive hprofile
  have hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n) :=
    fun n => (lt_extinctionTime_iff _ _).mpr (hpositive n)
  have hh := linear_uniform_distance_deviation_tendsto_zero rows (cutoffScale cutoff) hc hc1
    (cutoffScale_pos cutoff) (cutoffScale_tendsto cutoff hcutoff) (cutoffScale_sublog cutoff hsmall)
    hτ hin.1 hin.2 heps
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hh
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using hr

theorem uniform_profile_maximum_bound (cutoff : ℕ → ℕ) (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0))
    (c : LinearRegimeParameter) {eps eta : ℝ} (heps : 0 < eps) (heta : 0 < eta) :
    ∃ e > 0, ∃ N, ∀ n ≥ N, ∀ x, PositiveThrough x n → ProfileGood cutoff c n x e →
      (Forward.treeLaw x n).real {s | eps ≤ |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) -
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c|} < eta := by
  apply uniform_profile_bound cutoff hcutoff c.property.1 c.property.2 _ ?_ heta
  intro rows hpositive hprofile
  have hin := linear_inputs_of_profile cutoff rows c.property.1 c.property.2 hsmall hpositive hprofile
  have hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n) :=
    fun n => (lt_extinctionTime_iff _ _).mpr (hpositive n)
  have hh := linear_maximum_deviation_tendsto_zero c rows (cutoffScale cutoff)
    (cutoffScale_pos cutoff) (cutoffScale_tendsto cutoff hcutoff) (cutoffScale_sublog cutoff hsmall)
    hτ hin.1 hin.2 heps
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hh
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using hr

end Freezing1.SIR.RandomEnvironment
