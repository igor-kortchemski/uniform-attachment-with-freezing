module

public import Freezing1.LinearRegimeUniform
public import Freezing1.LinearRegimeCutoffs

/-!
# Height-scale asymptotics in the linear regime

Theorem `thm:lineaire` (I), with the paper's literal nested-limit assumptions.
The middle interval is estimated by Abel summation. The early and late pieces
are treated as in the manuscript, with explicit integer cutoffs and endpoints.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology

/-- The bulk lower bound makes the contribution strictly after `floor (ε*n)`
negligible on the logarithmic scale. The lower bound may depend on `ε`. -/
theorem tendsto_bulkLate_heightScale_div_log_zero {x : ℕ → SignSequence}
    (hbulk : BulkLowerBound x) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    Tendsto (fun n : ℕ =>
      heightScaleOn (x n) (Finset.Ioc (Nat.floor (ε * n)) n) /
        Real.log (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hbound⟩ := hbulk ε hε hε1
  apply tendsto_late_heightScale_div_log_zero x
    (fun n => Finset.Ioc (Nat.floor (ε * n)) n) hδ
  · exact Eventually.of_forall fun n i hi =>
      Finset.mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hi).1,
        (Finset.mem_Ioc.mp hi).2⟩
  · filter_upwards [hbound, eventually_ge_atTop 1] with n hn hn1
    intro i hi _
    obtain ⟨hbi, hin⟩ := Finset.mem_Ioc.mp hi
    have hiε : ε * n ≤ (i : ℝ) := (Nat.lt_of_floor_lt hbi).le
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    exact (le_div_iff₀ hn0).mp (hn i hiε hin)

/-- Uniform logarithmic block estimates, together with the two negligible
pieces, determine the full height-scale limit. -/
theorem tendsto_heightScale_div_log_of_uniformIntervals
    {x : ℕ → SignSequence} {A : ℕ → ℝ} {c : ℝ}
    (hA : ∀ n, 0 < A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hs : ∀ n, PositiveThrough (x n) n)
    (hbulk : BulkLowerBound x) (hblocks : UniformLogIntervals x A c 2) :
    Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ))
      atTop (𝓝 ((c + 1) / (2 * c))) := by
  let K : ℝ := (c + 1) / (2 * c)
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨ε, hε, hε1, hblock⟩ := hblocks (η / 8) (by positivity)
  let a : ℕ → ℕ := fun n => Nat.ceil (A n)
  let b : ℕ → ℕ := fun n => Nat.floor (ε * n)
  let R : ℕ → ℝ := fun n => Real.log ((b n : ℝ) / a n) / Real.log (n : ℝ)
  let early : ℕ → ℝ := fun n => heightScale (x n) (a n) / Real.log (n : ℝ)
  let late : ℕ → ℝ := fun n =>
    heightScaleOn (x n) (Finset.Ioc (b n) n) / Real.log (n : ℝ)
  let baseline : ℕ → ℝ := fun n => early n + K * R n + late n
  have hearly : Tendsto early atTop (𝓝 0) :=
    tendsto_early_ceil_heightScale_div_log_zero x hs
      (Eventually.of_forall fun n => (hA n).le) hsmall
  have hlate : Tendsto late atTop (𝓝 0) :=
    tendsto_bulkLate_heightScale_div_log_zero hbulk hε hε1
  have hR : Tendsto R atTop (𝓝 1) :=
    tendsto_log_floor_div_ceil_div_log hA hsmall hε
  have hRabs : Tendsto (fun n => |R n|) atTop (𝓝 1) := by
    simpa only [abs_one] using hR.abs
  have hbase : Tendsto baseline atTop (𝓝 K) := by
    simpa only [zero_add, mul_one, add_zero] using (hearly.add (hR.const_mul K)).add hlate
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hblock, eventually_ceil_floor_cutoff_bounds hA hsmall hε hε1,
    hlog.eventually_gt_atTop 0,
    hRabs.eventually (gt_mem_nhds (by norm_num : (1 : ℝ) < 2)),
    (Metric.tendsto_nhds.mp hbase) (η / 2) (by positivity)]
    with n hblockn hcuts hln hRn hbasen
  have ha : 1 ≤ a n := hcuts.1
  have hab : a n ≤ b n := hcuts.2.1
  have hab' : a n < b n := hcuts.2.2.1
  have htwice : 2 * a n < b n := hcuts.2.2.2.1
  have hbn : b n ≤ n := hcuts.2.2.2.2
  have ha0 : (0 : ℝ) < a n := by exact_mod_cast (show 0 < a n by omega)
  have habR : (a n : ℝ) < b n := by exact_mod_cast hab'
  have hratio : 0 < Real.log ((b n : ℝ) / a n) :=
    Real.log_pos ((lt_div_iff₀ ha0).mpr (by simpa using habR))
  have hmid : |heightInterval (x n) (a n) (b n) /
      Real.log ((b n : ℝ) / a n) - K| ≤ η / 8 := by
    apply hblockn (a n) (b n) (Nat.le_ceil _) hab'
    · exact Nat.floor_le (by positivity)
    · have hh : (2 : ℝ) * a n < b n := by exact_mod_cast htwice
      linarith
  have hsplit : heightScale (x n) n =
      heightScale (x n) (a n) + heightInterval (x n) (a n) (b n) +
        heightScaleOn (x n) (Finset.Ioc (b n) n) := by
    rw [heightScale_add_heightInterval (x n) hab,
      heightScale_add_heightScaleOn_Ioc hbn]
  have hdiff : heightScale (x n) n / Real.log (n : ℝ) - baseline n =
      (heightInterval (x n) (a n) (b n) / Real.log ((b n : ℝ) / a n) - K) * R n := by
    dsimp only [baseline, early, late, R]
    rw [hsplit]
    field_simp
    ring
  rw [Real.dist_eq] at hbasen ⊢
  have hbound : |heightScale (x n) n / Real.log (n : ℝ) - baseline n| ≤ η / 4 := by
    rw [hdiff, abs_mul]
    calc
      _ ≤ (η / 8) * |R n| := mul_le_mul_of_nonneg_right hmid (abs_nonneg _)
      _ ≤ (η / 8) * 2 := mul_le_mul_of_nonneg_left hRn.le (by positivity)
      _ = η / 4 := by ring
  have htri := abs_add_le
    (heightScale (x n) n / Real.log (n : ℝ) - baseline n) (baseline n - K)
  have hid : heightScale (x n) n / Real.log (n : ℝ) - K =
      (heightScale (x n) n / Real.log (n : ℝ) - baseline n) + (baseline n - K) := by ring
  change |heightScale (x n) n / Real.log (n : ℝ) - K| < η
  rw [hid]
  linarith

/-- The first part of the Introduction's linear-regime theorem, with the
literal finite-max/limsup and finite-min/liminf hypotheses. -/
theorem linear_heightScale_tendsto
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) :
    Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ))
      atTop (𝓝 ((c + 1) / (2 * c))) := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hn := (nearOriginLimsup_iff x A hA hc.le hc1 hs).mp hnear
  have hb := (bulkLiminf_iff x hs).mp hbulk
  exact tendsto_heightScale_div_log_of_uniformIntervals hA hsmall hs hb
    (uniformLogIntervals_of_nearOriginLinear hn hAinf hc (by norm_num))

end Freezing1
