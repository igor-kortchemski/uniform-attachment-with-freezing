module

public import Freezing1.LinearComponentTail

/-!
# Uniform union bounds for geometric-block component populations

The finite signed urn has a uniform exponential moment. Its endpoint plus
one accounts for the paper's permanently active root convention. A union
bound over at most `C^k+1` roots is then at most `1/k^2`, uniformly in the
allowed geometric window. The actual component-law transfer is separate.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

/-- Markov's exponential bound, with the additional distinguished root kept. -/
theorem continuationLaw_root_augmented_tail_le (Z : ℕ → ℤ) (a j : ℕ)
    {β B : ℝ} (hβ : 0 ≤ β)
    (hmgf : (∫ u, Real.exp (β * (u : ℝ)) ∂SignedUrn.continuationLaw Z a j 1) ≤ Real.exp B)
    (q : ℝ) :
    (SignedUrn.continuationLaw Z a j 1).real {u | q < (u : ℝ) + 1} ≤
      Real.exp (B + β - β * q) := by
  calc
    _ ≤ (SignedUrn.continuationLaw Z a j 1).real {u | q - 1 ≤ (u : ℝ)} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro u hu
      change q < (u : ℝ) + 1 at hu
      change q - 1 ≤ (u : ℝ)
      linarith
    _ ≤ Real.exp (-β * (q - 1)) *
        mgf (fun u : ℤ => (u : ℝ)) (SignedUrn.continuationLaw Z a j 1) β :=
      measure_ge_le_exp_mul_mgf _ hβ (SignedUrn.continuationLaw_integrable Z a j 1 _)
    _ ≤ Real.exp (-β * (q - 1)) * Real.exp B :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The exponential decay in the cubic threshold beats both the geometric
number of components and the requested reciprocal-square failure rate. -/
theorem eventually_geometric_exp_cube_le_inv_sq (C : ℕ) (hC : 1 ≤ C)
    {β : ℝ} (hβ : 0 < β) (B : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      ((C ^ k : ℕ) + 1 : ℝ) * Real.exp (B + β - β * (k : ℝ) ^ 3) ≤ 1 / (k : ℝ) ^ 2 := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hpow : Tendsto (fun k : ℕ => β * (k : ℝ) ^ 2) atTop atTop :=
    (tendsto_const_mul_pow_atTop (by norm_num : (2 : ℕ) ≠ 0) hβ).comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun k : ℕ => 2 * ((k : ℝ) ^ 2 * Real.exp (-(k : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp tendsto_natCast_atTop_atTop).const_mul 2
  filter_upwards [eventually_ge_atTop 1,
    hpow.eventually_ge_atTop (Real.log C + 1 + |B + β|),
    hexp.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk hquad hsmall
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hCpow : (1 : ℝ) ≤ (C : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast hC)
  have hpoweq : (C : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log C) := by
    rw [Real.exp_nat_mul, Real.exp_log hC0]
  have hexponent : B + β + (k : ℝ) * Real.log C - β * (k : ℝ) ^ 3 ≤ -(k : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hquad hk0.le
    have hb := mul_le_mul_of_nonneg_right hk1 (abs_nonneg (B + β))
    nlinarith [le_abs_self (B + β)]
  calc
    _ ≤ 2 * ((C : ℝ) ^ k * Real.exp (B + β - β * (k : ℝ) ^ 3)) := by
      rw [Nat.cast_pow]
      nlinarith [Real.exp_pos (B + β - β * (k : ℝ) ^ 3)]
    _ = 2 * Real.exp (B + β + (k : ℝ) * Real.log C - β * (k : ℝ) ^ 3) := by
      rw [hpoweq, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2 * Real.exp (-(k : ℝ)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ ≤ 1 / (k : ℝ) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hk0)).mpr
      nlinarith

/-- A diverging real cutoff eventually forces every permitted geometric
index above any prescribed fixed index. -/
theorem eventually_geometric_index_ge (A : ℕ → ℝ) (hA : Tendsto A atTop atTop)
    (C : ℕ) (hC : 1 ≤ C) (K : ℕ) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) → K ≤ k := by
  filter_upwards [hA.eventually_gt_atTop ((C ^ K : ℕ) : ℝ)] with n hn
  intro k hk
  by_contra hK
  have hle : (C : ℝ) ^ k ≤ (C : ℝ) ^ K :=
    pow_le_pow_right₀ (by exact_mod_cast hC) (by omega)
  rw [← Nat.cast_pow, ← Nat.cast_pow] at hle
  linarith

/-- Actual schedule parameters have a uniform exponential moment for every
block `[a,a*C]` above the original cutoff, including the late bulk. -/
theorem uniform_geometric_urn_exponential_moment
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c) (hbulk : BulkLowerBound x)
    (C : ℕ) (hC : 1 ≤ C) :
    ∃ β > 0, ∃ B : ℝ, ∀ᶠ n in atTop,
      ∀ a : ℕ, A n ≤ (a : ℝ) → a * C ≤ n →
        (∫ u, Real.exp (β * (u : ℝ))
          ∂SignedUrn.continuationLaw (activeCount (x n)) a (a * C - a) 1) ≤ Real.exp B := by
  obtain ⟨d, hd, hwalk⟩ := eventually_linear_lower_above_cutoff x A hc hA hnear hbulk
  refine ⟨linearUrnExponent d C, linearUrnExponent_pos hd (Nat.cast_nonneg C), linearUrnMoment d, ?_⟩
  filter_upwards [hwalk, hA.eventually_gt_atTop 0] with n hwalkn hAn
  intro a hAa han
  have haR : (0 : ℝ) < a := hAn.trans_le hAa
  have ha : 0 < a := by exact_mod_cast haR
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hab : a ≤ a * C := by nlinarith
  have he : a + (a * C - a) = a * C := Nat.add_sub_of_le hab
  apply continuationLaw_exp_le_of_linear_lower (activeCount (x n)) ha hd (Nat.cast_nonneg C)
  · intro i hi
    rw [he] at hi
    have hai := (Finset.mem_Icc.mp hi).1
    exact hwalkn i (hAa.trans (by exact_mod_cast hai)) ((Finset.mem_Icc.mp hi).2.trans han)
  · intro i _
    rw [activeCount_succ]
    cases (x n) (i + 1) <;> simp
  · rw [he]
    have h1 : (activeCount (x n) (a * C) : ℝ) ≤ (plusCount (x n) (a * C) : ℝ) + 1 := by
      exact_mod_cast activeCount_le_plusCount_add_one (x n) (a * C)
    have h2 : (plusCount (x n) (a * C) : ℝ) ≤ ((a * C : ℕ) : ℝ) := by
      exact_mod_cast plusCount_le (x n) (a * C)
    push_cast at h2
    nlinarith

/-- Scalar union estimate for L11, already for the genuine urn parameters.
The transfer to the forest's component maximum is supplied by its kernel law. -/
theorem uniform_geometric_urn_tail_union
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c)
    (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c) (hbulk : BulkLowerBound x)
    (C : ℕ) (hC : 1 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → C ^ k * C ≤ n →
      (((C ^ k : ℕ) : ℝ) + 1) *
        (SignedUrn.continuationLaw (activeCount (x n)) (C ^ k) (C ^ k * C - C ^ k) 1).real
          {u | (k : ℝ) ^ 3 < (u : ℝ) + 1} ≤ 1 / (k : ℝ) ^ 2 := by
  obtain ⟨β, hβ, B, hmoment⟩ := uniform_geometric_urn_exponential_moment x A hc hA hnear hbulk C hC
  obtain ⟨K, hK⟩ := eventually_atTop.mp (eventually_geometric_exp_cube_le_inv_sq C hC hβ B)
  filter_upwards [hmoment, eventually_geometric_index_ge A hA C hC K] with n hn hkn
  intro k hAk hbound
  calc
    _ ≤ (((C ^ k : ℕ) : ℝ) + 1) * Real.exp (B + β - β * (k : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left
        (continuationLaw_root_augmented_tail_le (activeCount (x n)) (C ^ k) (C ^ k * C - C ^ k)
          hβ.le (hn (C ^ k) hAk hbound) _) (by positivity)
    _ ≤ _ := hK k (hkn k hAk)

end Freezing1
