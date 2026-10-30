module

public import Freezing1.ForwardMaximum
public import Freezing1.HeightAsymptotics
public import Freezing1.ExponentialMomentTail

/-! The source's eventual maximum-height upper bound, uniform for all
real thresholds C ≥ 2. The finite bound retains the true extra-edge and
vertex-count factors before absorbing them uniformly. -/

@[expose] public section

namespace Freezing1

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology Classical

noncomputable def maximumRateSlack : ℝ := 1 + 7 / bennettRate 1

theorem maximumRateSlack_ge_one : 1 ≤ maximumRateSlack := by
  unfold maximumRateSlack
  have hg := bennettRate_pos (by norm_num : (0 : ℝ) < 1)
  have : 0 ≤ 7 / bennettRate 1 := by positivity
  linarith

theorem log_le_maximumRateSlack_mul_rate {C : ℝ} (hC : 2 ≤ C) :
    Real.log C ≤ maximumRateSlack * bennettRate (C - 1) := by
  have hg := bennettRate_pos (by norm_num : (0 : ℝ) < 1)
  have hmono : bennettRate 1 ≤ bennettRate (C - 1) :=
    strictMonoOn_bennettRate.monotoneOn (by norm_num) (by simp; linarith) (by linarith)
  have hgC : 0 ≤ bennettRate (C - 1) := hg.le.trans hmono
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < C)
  by_cases hsmall : C ≤ 8
  · have hseven : 7 ≤ maximumRateSlack * bennettRate (C - 1) := by
      calc
        (7 : ℝ) = (7 / bennettRate 1) * bennettRate 1 := by field_simp
        _ ≤ (7 / bennettRate 1) * bennettRate (C - 1) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by unfold maximumRateSlack; linarith) hgC
    linarith
  · have hself := self_le_bennettRate_of_seven (u := C - 1) (by linarith)
    exact hlog.trans (hself.trans
      (le_mul_of_one_le_left hgC maximumRateSlack_ge_one))

namespace Forward

/-- An unshifted finite bound with the child's factor `C` kept explicitly
as `log C`, rather than suppressing it in the manuscript's finite tail. -/
theorem treeHeight_unshifted_bennett_upper (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {C : ℝ} (hC : 1 ≤ C) :
    (treeLaw x n).real {s | C ≤ (treeHeight s : ℝ) / heightScale x n} ≤
      Real.exp (Real.log ((n : ℝ) + 1) + Real.log C -
        heightScale x n * bennettRate (C - 1)) := by
  let m := heightScale x n
  have hm : 0 < m := heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  have hC0 : 0 < C := by linarith
  have hθ : 0 ≤ Real.log C := Real.log_nonneg hC
  calc
    _ ≤ (treeLaw x n).real {s | C * m ≤ (treeHeight s : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro s hs
      exact (le_div_iff₀ hm).mp hs
    _ ≤ Real.exp (-Real.log C * (C * m)) *
        mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) (Real.log C) :=
      measure_ge_le_exp_mul_mgf _ hθ (treeLaw_integrable_exp_treeHeight x n _)
    _ ≤ Real.exp (-Real.log C * (C * m)) *
        (((n : ℝ) + 1) * Real.exp (Real.log C) * Real.exp (m * (Real.exp (Real.log C) - 1))) :=
      mul_le_mul_of_nonneg_left (treeHeight_mgf_upper x n hτ hθ) (Real.exp_pos _).le
    _ = ((n : ℝ) + 1) * Real.exp
        (-Real.log C * (C * m) + Real.log C + m * (Real.exp (Real.log C) - 1)) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = Real.exp (Real.log ((n : ℝ) + 1) +
        (-Real.log C * (C * m) + Real.log C + m * (Real.exp (Real.log C) - 1))) := by
      conv_rhs => rw [Real.exp_add, Real.exp_log (by positivity)]
    _ = _ := by
      congr 1
      rw [Real.exp_log hC0]
      dsimp only [m]
      unfold bennettRate
      rw [show 1 + (C - 1) = C by ring]
      ring

theorem treeHeight_uniform_bennett_upper_of_slack (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x)
    (hN : Real.log ((n : ℝ) + 1) ≤ bennettRate 1 / 4 * heightScale x n)
    (hm : 4 * maximumRateSlack ≤ heightScale x n) :
    ∀ C : ℝ, 2 ≤ C →
      (treeLaw x n).real {s | C ≤ (treeHeight s : ℝ) / heightScale x n} ≤
        Real.exp (-heightScale x n * bennettRate (C - 1) / 2) := by
  intro C hC
  have hgC : 0 ≤ bennettRate (C - 1) := bennettRate_nonneg (by linarith)
  have hm0 : 0 ≤ heightScale x n :=
    (heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)).le
  have hmono : bennettRate 1 ≤ bennettRate (C - 1) :=
    strictMonoOn_bennettRate.monotoneOn (by norm_num) (by simp; linarith) (by linarith)
  have hlog := log_le_maximumRateSlack_mul_rate hC
  have hbound := mul_le_mul_of_nonneg_right hm hgC
  have hcount := mul_le_mul_of_nonneg_right hmono hm0
  apply (treeHeight_unshifted_bennett_upper x n hn hτ (by linarith : 1 ≤ C)).trans
  apply Real.exp_le_exp.mpr
  nlinarith

end Forward

/-- Source A36: one sufficiently large row works simultaneously for every
real C ≥ 2. No cutoff dependent on C is selected. -/
theorem eventually_maximum_uniform_bennett_upper (rows : ℕ → SignSequence)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (rows n))
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / heightScale (rows n) n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ C : ℝ, 2 ≤ C →
      (Forward.treeLaw (rows n) n).real
        {s | C ≤ (Forward.treeHeight s : ℝ) / heightScale (rows n) n} ≤
        Real.exp (-heightScale (rows n) n * bennettRate (C - 1) / 2) := by
  have hd := tendsto_heightScale_atTop rows
    (fun n => (lt_extinctionTime_iff (rows n) n).mp (hτ n))
  have hg : 0 < bennettRate 1 / 4 := by
    exact div_pos (bennettRate_pos (by norm_num)) (by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_log_nat_succ_le_mul_scale hd hlog hg,
    hd.eventually_ge_atTop (4 * maximumRateSlack)] with n hn hN hm
  exact Forward.treeHeight_uniform_bennett_upper_of_slack (rows n) n hn (hτ n) hN hm

end Freezing1
