module

public import Freezing1.UniformPairDistanceMoments
public import Freezing1.MainLinearUniformHeight
public import Freezing1.CoalescenceLogScale

/-!
# Distance between two uniform vertices in the linear regime

The two vertices are conditionally independent samples from the same actual
forward tree. The distance limit uses the genuine common-history geometry.
Exponential moments of the two heights give every real finite `Lp` limit.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter CanonicalTree
open scoped Topology ENNReal Classical

/-- The geometric defect is negligible on the logarithmic scale, while each
of the two actual height marginals converges to the same constant. -/
theorem linear_pair_distance_deviation_tendsto_zero
    {x : ℕ → SignSequence} {K : ℝ}
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hheight : ∀ δ > 0, Tendsto (fun n => (Forward.uniformHeightLaw (x n) n)
      {k | δ ≤ |(k : ℝ) / Real.log (n : ℝ) - K|}) atTop (𝓝 0))
    (hcoal : ∀ δ > 0, Tendsto (fun n => (ReverseHistory.uniformCoalescenceLaw (x n) n).real
      {k | δ < (k : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (pairCoalescenceLaw (x n) n)
      {z | ε ≤ |(z.2.2.1 : ℝ) / Real.log (n : ℝ) - 2 * K|}) atTop (𝓝 0) := by
  let (n : ℕ) : IsProbabilityMeasure (pairCoalescenceLaw (x n) n) :=
    pairCoalescenceLaw_probability (x n) n (hτ n)
  let (n : ℕ) : IsProbabilityMeasure (ReverseHistory.uniformCoalescenceLaw (x n) n) :=
    ReverseHistory.uniformCoalescenceLaw_probability (x n) n (hτ n)
  have hC : Tendsto (fun n => (ReverseHistory.uniformCoalescenceLaw (x n) n)
      {k | ε / 8 < (k : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
      (hcoal (ε / 8) (by positivity))
  have hsum := ((hheight (ε / 4) (by positivity)).add
    (hheight (ε / 4) (by positivity))).add hC
  simp only [add_zero] at hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop 0] with n hln
  let μ := pairCoalescenceLaw (x n) n
  let E₁ : Set PairCoalescenceData := {z | ε / 4 ≤ |(z.1 : ℝ) / Real.log (n : ℝ) - K|}
  let E₂ : Set PairCoalescenceData := {z | ε / 4 ≤ |(z.2.1 : ℝ) / Real.log (n : ℝ) - K|}
  let E₃ : Set PairCoalescenceData := {z | ε / 8 < (z.2.2.2 : ℝ) / Real.log (n : ℝ)}
  have h1 : μ E₁ = (Forward.uniformHeightLaw (x n) n)
      {k | ε / 4 ≤ |(k : ℝ) / Real.log (n : ℝ) - K|} := by
    rw [← pairCoalescenceLaw_map_first (x n) n (hτ n),
      Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  have h2 : μ E₂ = (Forward.uniformHeightLaw (x n) n)
      {k | ε / 4 ≤ |(k : ℝ) / Real.log (n : ℝ) - K|} := by
    rw [← pairCoalescenceLaw_map_second (x n) n (hτ n),
      Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  have h3 : μ E₃ = (ReverseHistory.uniformCoalescenceLaw (x n) n)
      {k | ε / 8 < (k : ℝ) / Real.log (n : ℝ)} := by
    rw [← pairCoalescenceLaw_map_coalescence (x n) n (hτ n),
      Measure.map_apply (by fun_prop) (by measurability)]
    rfl
  calc
    _ ≤ μ ((E₁ ∪ E₂) ∪ E₃) := by
      apply measure_mono_ae
      filter_upwards [pairCoalescenceLaw_geometry (x n) n (hτ n)] with z hz
      intro hd
      by_contra hnot
      have he1 : |(z.1 : ℝ) / Real.log (n : ℝ) - K| < ε / 4 := by
        have : z ∉ E₁ := fun h => hnot (Or.inl (Or.inl h))
        exact lt_of_not_ge this
      have he2 : |(z.2.1 : ℝ) / Real.log (n : ℝ) - K| < ε / 4 := by
        have : z ∉ E₂ := fun h => hnot (Or.inl (Or.inr h))
        exact lt_of_not_ge this
      have he3 : (z.2.2.2 : ℝ) / Real.log (n : ℝ) ≤ ε / 8 := by
        have : z ∉ E₃ := fun h => hnot (Or.inr h)
        exact le_of_not_gt this
      have hlo := div_nonneg hz.1 hln.le
      have hhi := div_le_div_of_nonneg_right hz.2 hln.le
      simp only [add_div, sub_div, mul_div_assoc] at hlo hhi
      rcases abs_lt.mp he1 with ⟨h1l, h1u⟩
      rcases abs_lt.mp he2 with ⟨h2l, h2u⟩
      rcases le_abs.mp hd with hd | hd <;> linarith
    _ ≤ μ E₁ + μ E₂ + μ E₃ :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = _ := by rw [h1, h2, h3]

/-- Every real finite `Lp` distance limit, with its probabilistic inputs
already stated for the actual sampling laws. -/
theorem linear_uniform_distance_tendsto_Lp_of_scale
    {x : ℕ → SignSequence} {K : ℝ} (hK : 0 < K)
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hscale : Tendsto (fun n : ℕ => heightScale (x n) n / Real.log (n : ℝ)) atTop (𝓝 K))
    (hbulk : BulkLowerBound x)
    (hcoal : ∀ δ > 0, Tendsto (fun n => (ReverseHistory.uniformCoalescenceLaw (x n) n).real
      {k | δ < (k : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 0))
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ) - 2 * K)
      (ENNReal.ofReal r) (forwardPairDataLaw (x n) n)) atTop (𝓝 0) := by
  let (n : ℕ) : IsProbabilityMeasure (pairCoalescenceLaw (x n) n) :=
    pairCoalescenceLaw_probability (x n) n (hτ n).le
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  let B : ℝ := 2 + (Real.exp 2 - 1) * (K + 1)
  have hexp : ∀ᶠ n in atTop,
      mgf (fun z => (z.2.2.1 : ℝ)) (pairCoalescenceLaw (x n) n) 1 ≤
        Real.exp (B * Real.log (n : ℝ)) := by
    filter_upwards [hlog.eventually_ge_atTop 1,
      hscale.eventually (gt_mem_nhds (lt_add_one K))] with n hln hrat
    have hln0 : 0 < Real.log (n : ℝ) := by linarith
    have hm : heightScale (x n) n ≤ (K + 1) * Real.log (n : ℝ) :=
      (div_le_iff₀ hln0).mp hrat.le
    have he : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
    have hmul := mul_le_mul_of_nonneg_right hm he
    calc
      _ ≤ Real.exp 2 * Real.exp (heightScale (x n) n * (Real.exp 2 - 1)) :=
        pairCoalescenceLaw_distance_mgf_le (x n) n (hτ n)
      _ = Real.exp (2 + heightScale (x n) n * (Real.exp 2 - 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; dsimp [B]; nlinarith
  have hmain := centered_tendsto_Lp_of_eventual_exp_bound
    (Z := fun _ (z : PairCoalescenceData) => (z.2.2.1 : ℝ)) (center := 2 * K)
    (fun _ => measurable_of_countable _)
    (fun n θ => pairCoalescenceLaw_integrable_exp_distance (x n) n (hτ n).le θ)
    (fun _ => Eventually.of_forall fun z => Nat.cast_nonneg z.2.2.1)
    hexp hlog
    (fun _ hε => linear_pair_distance_deviation_tendsto_zero (fun n => (hτ n).le)
      (fun _ hδ => linear_uniform_height_deviation_tendsto_zero hK hτ hscale hbulk hδ)
      hcoal hε) hr
  convert hmain using 1
  funext n
  rw [← pairCoalescenceLaw_map_triple (x n) n (hτ n).le,
    eLpNorm_map_measure (by fun_prop) (by fun_prop)]
  rfl

/-- Convergence in probability for the actual pair distance, under the literal
linear-regime hypotheses of the paper. -/
theorem linear_uniform_distance_deviation_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (forwardPairDataLaw (x n) n)
      {z | ε ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c|})
      atTop (𝓝 0) := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hb := (bulkLiminf_iff x hs).mp hbulk
  have hn := (nearOriginLimsup_iff x A hA hc.le hc1 hs).mp hnear
  have hscale := linear_heightScale_tendsto x A hc hc1 hA hAinf hsmall hτ hnear hbulk
  have hh := linear_pair_distance_deviation_tendsto_zero
    (K := (c + 1) / (2 * c)) (fun n => (hτ n).le)
    (fun _ hδ => linear_uniform_height_deviation_tendsto_zero (by positivity) hτ hscale hb hδ)
    (fun _ hδ => ReverseHistory.uniform_coalescence_div_log_tendsto_zero x A
      (fun n => (hτ n).le) hc hAinf hsmall hn hb hδ) hε
  have heq : 2 * ((c + 1) / (2 * c)) = (c + 1) / c := by ring
  rw [heq] at hh
  convert hh using 1
  funext n
  rw [← pairCoalescenceLaw_map_triple (x n) n (hτ n).le,
    Measure.map_apply (by fun_prop) (by measurability)]
  rfl

/-- The distance assertion of Theorem `thm:lineaire` (II), for two conditionally
independent uniform vertices of the same forward tree, including equality. -/
theorem linear_uniform_distance_tendsto_Lp
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n : ℕ => eLpNorm
      (fun z : ℕ × ℕ × ℕ => (z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c)
      (ENNReal.ofReal r) (forwardPairDataLaw (x n) n)) atTop (𝓝 0) := by
  have hs : ∀ n, PositiveThrough (x n) n :=
    fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hb := (bulkLiminf_iff x hs).mp hbulk
  have hn := (nearOriginLimsup_iff x A hA hc.le hc1 hs).mp hnear
  have hh := linear_uniform_distance_tendsto_Lp_of_scale
    (K := (c + 1) / (2 * c)) (by positivity) hτ
    (linear_heightScale_tendsto x A hc hc1 hA hAinf hsmall hτ hnear hbulk) hb
    (fun _ hδ => ReverseHistory.uniform_coalescence_div_log_tendsto_zero x A
      (fun n => (hτ n).le) hc hAinf hsmall hn hb hδ) hr
  have heq : 2 * ((c + 1) / (2 * c)) = (c + 1) / c := by ring
  simpa only [heq] using hh

end Freezing1
