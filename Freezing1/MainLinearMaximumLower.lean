module

public import Freezing1.ForwardGoodChainSurvival
public import Freezing1.ForwardGoodChainMaximum
public import Freezing1.LinearGoodChainBase
public import Freezing1.MainForwardBlockConcentration
public import Freezing1.MainLinearComponentMaximum
public import Freezing1.LinearMaximumUpper

/-!
# The maximum height in the linear regime

The lower bound combines the actual forward block counts, the component
maximum estimate, and permutation-symmetric growth of the genuine good sets.
Every scale is a canonical prefix of one terminal tree. The initial good set
is the entire active population, with coefficient `c/4`; no independence of
successive blocks or of their counts is assumed. Together with the proved
upper bound this gives Theorem `thm:lineaire` (III).
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Lower-tail convergence from the quantified forms of the source's two
linear-growth assumptions. Every probabilistic chaining input is discharged
by an estimate for the actual forward process. -/
theorem linear_maximum_lower_tendsto_zero_of_bounds (c : LinearRegimeParameter)
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hnear : NearOriginLinear x A (c : ℝ)) (hbulk : BulkLowerBound x)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n).real
      {s | (Forward.treeHeight s : ℝ) / Real.log (n : ℝ) <
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c - η})
      atTop (𝓝 0) := by
  let d : ℝ := ((c : ℝ) + 1) / (2 * (c : ℝ))
  let δ : ℝ := η / (2 * d)
  have hc := c.property.1
  have hd : 0 < d := by dsimp [d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, _hsize, L, hL, ε, hε, hε1, hN⟩ :=
    exists_forward_geometricBlock_fewTallRoots_probability x A c hτ hAinf hnear hδ
  let k₀ : ℕ → ℕ := chainLowerIndex C A
  let K : ℕ → ℕ := chainUpperIndex C ε
  let t : ℝ := (linearPoissonRate c C : ℝ) * (linearHeightFactor c - δ)
  have hC2 : 2 ≤ C := by omega
  have hcuts := eventually_chain_cutoff_bounds C hC hA hAinf hsmall hε hε1
  have hindices : ∀ᶠ n in atTop, k₀ n ≤ K n := hcuts.mono fun _ hn => hn.2.1
  have hwindow : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n), C ^ (k + 1) ≤ n := by
    filter_upwards [hcuts] with n hn
    intro k hk
    obtain ⟨hk0, hkK⟩ := Finset.mem_Ico.mp hk
    simpa only [pow_succ] using (hn.2.2.2.2 k hk0 hkK.le).2.2
  have hN' : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n),
      (Forward.treeLaw (x n) n).real
        {s | (Forward.blockTallCount s (C ^ k) (C ^ (k + 1)) t : ℝ) ≤
          4 * (C ^ k : ℕ)} ≤ L / (C ^ k : ℕ) := by
    filter_upwards [hcuts, hN] with n hn hNn
    intro k hk
    obtain ⟨hk0, hkK⟩ := Finset.mem_Ico.mp hk
    have hwin := hn.2.2.2.2 k hk0 hkK.le
    exact hNn k hwin.1 hwin.2.1
  have hM : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n),
      (Forward.treeLaw (x n) (C ^ (k + 1))).real
        {s | (k : ℝ) ^ 3 < (Forward.componentMaximum s (C ^ k) : ℝ)} ≤
          1 / (k : ℝ) ^ 2 := by
    filter_upwards [hcuts, uniform_geometric_componentMaximum_tail x A c.property.1
      hAinf hnear hbulk hτ C hC.le] with n hn hMn
    intro k hk
    obtain ⟨hk0, hkK⟩ := Finset.mem_Ico.mp hk
    have hwin := hn.2.2.2.2 k hk0 hkK.le
    simpa only [pow_succ] using hMn k hwin.1 hwin.2.2
  have hbase := Forward.eventually_treeLaw_goodSet_base x A c.property.1 hA hAinf
    hsmall hnear C hC2 t hτ
  have hsurv := Forward.goodChain_survival x C hC k₀ K
    (chainLowerIndex_tendsto_atTop C hC hAinf) hindices
    ((c : ℝ) / 4) (by positivity) t L hL.le hτ hwindow hbase hN' hM
  have hspan : Tendsto (fun n : ℕ => (((K n - k₀ n : ℕ) : ℝ) * t) / Real.log (n : ℝ))
      atTop (𝓝 (d * (linearHeightFactor c - δ))) := by
    have hh := (chain_log_span_tendsto_one C hC hAinf hsmall hε).mul_const
      (d * (linearHeightFactor c - δ))
    simp only [one_mul] at hh
    convert hh using 1
    funext n
    dsimp only [K, k₀]
    rw [show t = d * Real.log (C : ℝ) * (linearHeightFactor c - δ) from rfl]
    ring
  have hlower := Forward.maximum_lower_tail_of_goodChain_survival x
    (fun n => C ^ K n) k₀ K C hC.le hindices (fun _ => t)
    (d * (linearHeightFactor c - δ)) hspan hsurv (half_pos hη)
  have hthreshold : d * (linearHeightFactor c - δ) - η / 2 =
      d * linearHeightFactor c - η := by
    dsimp [δ]
    field_simp [ne_of_gt hd]
    ring
  simpa only [hthreshold] using hlower

/-- The exact lower half of Theorem `thm:lineaire` (III), under the literal
nested-limsup and bulk-liminf assumptions of the Introduction. -/
theorem linear_maximum_lower_tendsto_zero (c : LinearRegimeParameter)
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) (hbulk : BulkLiminf x)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n).real
      {s | (Forward.treeHeight s : ℝ) / Real.log (n : ℝ) <
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c - η})
      atTop (𝓝 0) := by
  have hs : ∀ n, PositiveThrough (x n) n := fun n =>
    (lt_extinctionTime_iff (x n) n).mp (hτ n)
  exact linear_maximum_lower_tendsto_zero_of_bounds c x A hA hAinf hsmall
    (fun n => (hτ n).le)
    ((nearOriginLimsup_iff x A hA c.property.1.le c.property.2 hs).mp hnear)
    ((bulkLiminf_iff x hs).mp hbulk) hη

/-- Theorem `thm:lineaire` (III): convergence in probability of the actual
maximum tree height, with the source's complete linear-regime assumptions. -/
theorem linear_maximum_deviation_tendsto_zero (c : LinearRegimeParameter)
    (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (hA : ∀ n, 0 < A n) (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A (c : ℝ)) (hbulk : BulkLiminf x)
    {η : ℝ} (hη : 0 < η) :
    Tendsto (fun n : ℕ => (Forward.treeLaw (x n) n)
      {s | η ≤ |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) -
        (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c|})
      atTop (𝓝 0) := by
  apply (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
  have hh := (linear_maximum_lower_tendsto_zero c x A hA hAinf hsmall hτ hnear hbulk
    (half_pos hη)).add
    (linear_maximum_upper_tendsto_zero c x A hA hAinf hsmall hτ hnear hbulk (half_pos hη))
  simp only [add_zero] at hh
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hh
  intro n
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (measureReal_union_le _ _)
  intro s hs
  change η ≤ |(Forward.treeHeight s : ℝ) / Real.log (n : ℝ) -
    (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c| at hs
  change (Forward.treeHeight s : ℝ) / Real.log (n : ℝ) <
      (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c - η / 2 ∨
    (((c : ℝ) + 1) / (2 * (c : ℝ))) * linearHeightFactor c + η / 2 <
      (Forward.treeHeight s : ℝ) / Real.log (n : ℝ)
  rcases le_abs.mp hs with h | h
  · right; linarith
  · left; linarith

end Freezing1
