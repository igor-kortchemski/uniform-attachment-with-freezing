module

public import Freezing1.UniformBirthBernoulli
public import Freezing1.UniformBirthConditionalMean

/-!
# The actual random birth-truncated conditional mean

The sum and its mean live on the explicit independent product space from
the joint representation. Conditioning is on its genuine birth coordinate.
The zero-mean row is retained, and the positive-row lower bound is proved.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators ProbabilityTheory

set_option backward.isDefEq.respectTransparency false

def randomSum (x : SignSequence) {n : ℕ} (z : ℕ × (Fin n → ℕ)) : ℝ :=
  (truncatedSum x z.1 z.2 : ℝ)

noncomputable def randomMean (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (z : ℕ × (Fin n → ℕ)) : ℝ := truncatedMean x n h z.1

theorem randomMean_bounds (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (z : ℕ × (Fin n → ℕ)) : 0 ≤ randomMean x n h z ∧ randomMean x n h z ≤ heightScale x n :=
  ⟨truncatedMean_nonneg x n h z.1, truncatedMean_le_heightScale x n h z.1⟩

theorem randomSum_integrable (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    Integrable (randomSum x) (auxiliaryLaw x n h) := by
  have := birthLaw_probability x n h
  have hm : Integrable (truncatedMean x n h) (birthLaw x n) := by
    apply (integrable_const (heightScale x n)).mono' (measurable_of_countable _).aestronglyMeasurable
    apply Eventually.of_forall
    intro b
    simpa only [Real.norm_eq_abs, abs_of_nonneg (truncatedMean_nonneg x n h b)] using
      truncatedMean_le_heightScale x n h b
  apply (integrable_prod_iff (measurable_of_countable (randomSum x)).aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun b => truncatedSum_integrable x n h b)
  · convert hm using 1
    funext b
    simp only [randomSum, Real.norm_eq_abs]
    have he (Y : Fin n → ℕ) : |(truncatedSum x b Y : ℝ)| = (truncatedSum x b Y : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg _)
    simp_rw [he]
    exact integral_truncatedSum x n h b

theorem randomMean_condExp (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    (auxiliaryLaw x n h)[randomSum x | (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[auxiliaryLaw x n h]
      randomMean x n h := by
  have := birthLaw_probability x n h
  have hh := condExp_prod_fst_nat (birthLaw x n) (bernoulliProductLaw (reciprocalParameter x n h))
    (randomSum x) (randomSum_integrable x n h)
  filter_upwards [hh] with z hz
  change ((birthLaw x n).prod (bernoulliProductLaw (reciprocalParameter x n h)))[randomSum x |
    (inferInstance : MeasurableSpace ℕ).comap Prod.fst] z = truncatedMean x n h z.1
  rw [hz]
  exact integral_truncatedSum x n h z.1

theorem uniformVertex_supported (x : SignSequence) (n : ℕ) :
    ∀ᵐ v ∂uniformVertex x n, v ∈ vertexLabels x n := by
  rw [ae_iff]
  simp [uniformVertex, Measure.uniformOfFinset_apply]

theorem birthLaw_le_horizon (x : SignSequence) (n : ℕ) : ∀ᵐ b ∂birthLaw x n, b ≤ n := by
  rw [birthLaw, ae_map_iff (measurable_of_countable _).aemeasurable (by measurability)]
  filter_upwards [uniformVertex_supported x n] with v hv
  exact Reverse.birthTime_le_of_mem hv

theorem auxiliary_birth_le_horizon (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    ∀ᵐ z ∂auxiliaryLaw x n h, z.1 ≤ n := by
  apply ae_of_ae_map (f := Prod.fst) (p := fun b : ℕ => b ≤ n) measurable_fst.aemeasurable
  rw [(auxiliary_birth_hasLaw x n h).map_eq]
  exact birthLaw_le_horizon x n

/-- The total finite-array mean equals the source's exact `h_B` on the
actual birth distribution. -/
theorem randomMean_eq_heightScale_birth (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    ∀ᵐ z ∂auxiliaryLaw x n h, randomMean x n h z = heightScale x z.1 := by
  filter_upwards [auxiliary_birth_le_horizon x n h] with z hz
  exact truncatedMean_eq_heightScale x n h hz

theorem first_step_attachment {x : SignSequence} {n : ℕ} (h : PositiveThrough x n) (hn : 1 ≤ n) :
    x 1 = true := by
  have hs := h 1 hn
  cases hx : x 1 with
  | true => rfl
  | false =>
    have he : activeCount x 1 = 0 := by norm_num [activeCount_succ, hx]
    rw [he] at hs
    omega

theorem birthTime_pos_of_mem {x : SignSequence} {n : ℕ} (h : PositiveThrough x n)
    (hn : 1 ≤ n) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) : 1 ≤ birthTime n v := by
  cases v with
  | inl i => exact hn
  | inr i =>
    have hx : x (i + 1) = false := (Finset.mem_filter.mp (Finset.inr_mem_disjSum.mp hv)).2
    have hi : i ≠ 0 := by
      intro he
      subst i
      have ht := first_step_attachment h hn
      simp only [Nat.zero_add] at hx
      rw [ht] at hx
      contradiction
    exact Nat.one_le_iff_ne_zero.mpr hi

theorem auxiliary_birth_pos (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n) :
    ∀ᵐ z ∂auxiliaryLaw x n h, 1 ≤ z.1 := by
  apply ae_of_ae_map (f := Prod.fst) (p := fun b : ℕ => 1 ≤ b) measurable_fst.aemeasurable
  rw [(auxiliary_birth_hasLaw x n h).map_eq, birthLaw,
    ae_map_iff (measurable_of_countable _).aemeasurable (by measurability)]
  filter_upwards [uniformVertex_supported x n] with v hv
  exact birthTime_pos_of_mem h hn hv

theorem truncatedMean_ge_half (x : SignSequence) (n : ℕ) (h : PositiveThrough x n)
    (hn : 1 ≤ n) {b : ℕ} (hb : 1 ≤ b) : 1 / 2 ≤ truncatedMean x n h b := by
  let i0 : Fin n := ⟨0, by omega⟩
  have hi0 : i0 ∈ Finset.univ.filter (fun i : Fin n => i.val < b) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, i0]
    omega
  have hsingle := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.univ.filter (fun i : Fin n => i.val < b)) =>
      unitInterval.nonneg (Reverse.attachmentParameter x n (horizon_le_extinction h) i)) hi0
  have hp : (Reverse.attachmentParameter x n (horizon_le_extinction h) i0 : ℝ) = 1 / 2 := by
    norm_num [Reverse.attachmentParameter_coe, i0, activeCount_succ, first_step_attachment h hn]
  simpa only [truncatedMean, hp] using hsingle

theorem randomMean_ge_half (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n) :
    ∀ᵐ z ∂auxiliaryLaw x n h, 1 / 2 ≤ randomMean x n h z := by
  filter_upwards [auxiliary_birth_pos x n h hn] with z hz
  exact truncatedMean_ge_half x n h hn hz

@[simp] theorem randomMean_zero (x : SignSequence) (h : PositiveThrough x 0)
    (z : ℕ × (Fin 0 → ℕ)) : randomMean x 0 h z = 0 := by
  simp [randomMean, truncatedMean]

@[simp] theorem randomSum_zero (x : SignSequence) (z : ℕ × (Fin 0 → ℕ)) : randomSum x z = 0 := by
  simp [randomSum, truncatedSum]

end Freezing1.UniformBirth
