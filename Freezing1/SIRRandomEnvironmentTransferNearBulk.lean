module

public import Freezing1.SIRRandomEnvironmentUniformNat
public import Freezing1.SIRRandomEnvironmentTransferProfiles

/-!
# Finite near-origin and bulk constraints for random environments

The finite-rate SIR fluid curve is nonlinear away from zero. These finite
families retain the distinct near-origin linear and positive-bulk inputs of
the deterministic theorem, instead of requiring one global linear profile.
-/

@[expose] public section

namespace Freezing1.SIR.RandomEnvironment

open Filter MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def NearBulkGood (cutoff : ℕ → ℕ) (c : ℝ) (window floor : ℕ → ℝ)
    (n : ℕ) (x : SignSequence) (J : ℕ) : Prop :=
  (∀ j ≤ J, ∀ i : ℕ, cutoff n ≤ i → (i : ℝ) ≤ window j * n →
    |(activeCount x i : ℝ) / i - c| ≤ 1 / ((j : ℝ) + 1)) ∧
  (∀ j ≤ J, ∀ i : ℕ, (n : ℝ) / ((j : ℝ) + 2) ≤ i → i ≤ n →
    floor j ≤ (activeCount x i : ℝ) / n)

theorem NearBulkGood.mono {cutoff : ℕ → ℕ} {c : ℝ} {window floor : ℕ → ℝ}
    {n I J : ℕ} {x : SignSequence} (h : NearBulkGood cutoff c window floor n x J)
    (hIJ : I ≤ J) : NearBulkGood cutoff c window floor n x I :=
  ⟨fun j hj => h.1 j (hj.trans hIJ), fun j hj => h.2 j (hj.trans hIJ)⟩

theorem balanced_nearBulkGood (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (window floor : ℕ → ℝ) (hwindow : ∀ j, window j < 1)
    (hfloor : ∀ j, floor j ≤ c / ((j : ℝ) + 2)) (J : ℕ) :
    ∀ᶠ n in atTop, NearBulkGood cutoff c window floor n (balancedSchedule c) J := by
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    balanced_profileGood cutoff hcutoff hc hc1 (by positivity : 0 < 1 / ((J : ℝ) + 1))]
      with n hn hgood
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro j hj i hcut hi
    have hin : i ≤ n := by
      have hh := mul_le_mul_of_nonneg_right (hwindow j).le (Nat.cast_nonneg (α := ℝ) n)
      have hh' : (i : ℝ) ≤ n := hi.trans (by simpa only [one_mul] using hh)
      exact_mod_cast hh'
    exact (hgood i hcut hin).trans (one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hj 1))
  · intro j _ i hi _
    have hd : 0 < (j : ℝ) + 2 := by positivity
    have hlow := (balancedSchedule_active_bounds hc hc1 i).1
    have hi' := (div_le_iff₀ hd).mp hi
    apply (hfloor j).trans
    apply (div_le_div_iff₀ hd hnR).mpr
    nlinarith

theorem nearOrigin_of_nearBulk (cutoff : ℕ → ℕ) (rows : ℕ → SignSequence) (c : ℝ)
    (window floor : ℕ → ℝ) (hwindow : ∀ j, 0 < window j ∧ window j < 1)
    (hgood : ∀ J, ∀ᶠ n in atTop, NearBulkGood cutoff c window floor n (rows n) J) :
    NearOriginLinear rows (cutoffScale cutoff) c := by
  intro eps heps
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / eps)
  have hJe : 1 / ((J : ℝ) + 1) ≤ eps := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hh := (div_lt_iff₀ heps).mp hJ
    nlinarith
  refine ⟨window J, (hwindow J).1, (hwindow J).2, ?_⟩
  filter_upwards [hgood J] with n hn
  intro i hi hin
  have hcut : cutoff n ≤ i := by
    change (cutoff n : ℝ) + 1 ≤ i at hi
    exact_mod_cast (show (cutoff n : ℝ) ≤ i by linarith)
  exact (hn.1 J le_rfl i hcut hin).trans hJe

theorem bulk_of_nearBulk (cutoff : ℕ → ℕ) (rows : ℕ → SignSequence) (c : ℝ)
    (window floor : ℕ → ℝ) (hfloor : ∀ j, 0 < floor j)
    (hgood : ∀ J, ∀ᶠ n in atTop, NearBulkGood cutoff c window floor n (rows n) J) :
    BulkLowerBound rows := by
  intro eps heps _
  obtain ⟨J, hJ⟩ := exists_nat_gt (1 / eps)
  refine ⟨floor J, hfloor J, ?_⟩
  filter_upwards [hgood J] with n hn
  intro i hi hin
  apply hn.2 J le_rfl i ?_ hin
  apply (div_le_iff₀ (by positivity : 0 < (J : ℝ) + 2)).mpr
  have hh := (div_lt_iff₀ heps).mp hJ
  have he : 1 ≤ eps * ((J : ℝ) + 2) := by nlinarith
  have hm := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) n)
  have hi' := mul_le_mul_of_nonneg_right hi (show 0 ≤ (J : ℝ) + 2 by positivity)
  nlinarith

theorem linear_inputs_of_nearBulk (cutoff : ℕ → ℕ) (rows : ℕ → SignSequence)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (window floor : ℕ → ℝ)
    (hwindow : ∀ j, 0 < window j ∧ window j < 1) (hfloor : ∀ j, 0 < floor j)
    (hpositive : ∀ n, PositiveThrough (rows n) n)
    (hgood : ∀ J, ∀ᶠ n in atTop, NearBulkGood cutoff c window floor n (rows n) J) :
    NearOriginLimsup rows (cutoffScale cutoff) c ∧ BulkLiminf rows := by
  exact ⟨(nearOriginLimsup_iff rows (cutoffScale cutoff) (cutoffScale_pos cutoff)
    hc.le hc1 hpositive).mpr (nearOrigin_of_nearBulk cutoff rows c window floor hwindow hgood),
    (bulkLiminf_iff rows hpositive).mpr (bulk_of_nearBulk cutoff rows c window floor hfloor hgood)⟩

theorem uniform_nearBulk_bound (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (window floor : ℕ → ℝ) (hwindow : ∀ j, window j < 1)
    (hfloor : ∀ j, floor j ≤ c / ((j : ℝ) + 2))
    (score : ℕ → SignSequence → ℝ)
    (hlimit : ∀ rows : ℕ → SignSequence, (∀ n, PositiveThrough (rows n) n) →
      (∀ J, ∀ᶠ n in atTop, NearBulkGood cutoff c window floor n (rows n) J) →
      Tendsto (fun n => score n (rows n)) atTop (nhds 0))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ J N : ℕ, ∀ n ≥ N, ∀ x, PositiveThrough x n → NearBulkGood cutoff c window floor n x J →
      score n x < eta := by
  apply uniform_bound_of_sequential_nat (fun n x => PositiveThrough x n)
    (NearBulkGood cutoff c window floor) score (fun _ => balancedSchedule c) ?_ ?_ ?_ hlimit heta
  · intro n
    exact (lt_extinctionTime_iff _ _).mp (by rw [balancedSchedule_survives hc hc1]; simp)
  · exact balanced_nearBulkGood cutoff hcutoff hc hc1 window floor hwindow hfloor
  · exact fun _ _ _ _ hIJ hh => hh.mono hIJ

theorem uniform_nearBulk_height_bound (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0))
    {c eps eta : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (heps : 0 < eps) (heta : 0 < eta)
    (window floor : ℕ → ℝ) (hwindow : ∀ j, 0 < window j ∧ window j < 1)
    (hfloor : ∀ j, 0 < floor j ∧ floor j ≤ c / ((j : ℝ) + 2)) :
    ∃ J N : ℕ, ∀ n ≥ N, ∀ x, PositiveThrough x n → NearBulkGood cutoff c window floor n x J →
      (Forward.uniformHeightLaw x n).real
        {h | eps ≤ |(h : ℝ) / Real.log (n : ℝ) - (c + 1) / (2 * c)|} < eta := by
  apply uniform_nearBulk_bound cutoff hcutoff hc hc1 window floor
    (fun j => (hwindow j).2) (fun j => (hfloor j).2) _ ?_ heta
  intro rows hpositive hgood
  have hin := linear_inputs_of_nearBulk cutoff rows hc hc1 window floor hwindow
    (fun j => (hfloor j).1) hpositive hgood
  have hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n) :=
    fun n => (lt_extinctionTime_iff _ _).mpr (hpositive n)
  have hscale := linear_heightScale_tendsto rows (cutoffScale cutoff) hc hc1
    (cutoffScale_pos cutoff) (cutoffScale_tendsto cutoff hcutoff) (cutoffScale_sublog cutoff hsmall)
    hτ hin.1 hin.2
  have hh := linear_uniform_height_deviation_tendsto_zero (by positivity : 0 < (c + 1) / (2 * c))
    hτ hscale (bulk_of_nearBulk cutoff rows c window floor (fun j => (hfloor j).1) hgood) heps
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hh
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using hr

theorem uniform_nearBulk_distance_bound (cutoff : ℕ → ℕ)
    (hcutoff : Tendsto cutoff atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / Real.log (n : ℝ)) atTop (nhds 0))
    {c eps eta : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (heps : 0 < eps) (heta : 0 < eta)
    (window floor : ℕ → ℝ) (hwindow : ∀ j, 0 < window j ∧ window j < 1)
    (hfloor : ∀ j, 0 < floor j ∧ floor j ≤ c / ((j : ℝ) + 2)) :
    ∃ J N : ℕ, ∀ n ≥ N, ∀ x, PositiveThrough x n → NearBulkGood cutoff c window floor n x J →
      (CanonicalTree.forwardPairDataLaw x n).real
        {z | eps ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c|} < eta := by
  apply uniform_nearBulk_bound cutoff hcutoff hc hc1 window floor
    (fun j => (hwindow j).2) (fun j => (hfloor j).2) _ ?_ heta
  intro rows hpositive hgood
  have hin := linear_inputs_of_nearBulk cutoff rows hc hc1 window floor hwindow
    (fun j => (hfloor j).1) hpositive hgood
  have hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n) :=
    fun n => (lt_extinctionTime_iff _ _).mpr (hpositive n)
  have hh := linear_uniform_distance_deviation_tendsto_zero rows (cutoffScale cutoff) hc hc1
    (cutoffScale_pos cutoff) (cutoffScale_tendsto cutoff hcutoff) (cutoffScale_sublog cutoff hsmall)
    hτ hin.1 hin.2 heps
  have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp hh
  simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using hr

end Freezing1.SIR.RandomEnvironment
