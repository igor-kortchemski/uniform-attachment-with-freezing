module

public import Freezing1.ForwardMaximum

/-!
# The height of a uniform vertex of the actual forward tree

The conditional sampling includes active and frozen vertices. Its distribution
is derived from Algorithm 1. The exact mixture over attachment times is a
forward alternative to the reverse birth-time representation.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Empirical average over all vertices, including frozen vertices. -/
noncomputable def vertexMean (s : State) (f : ℕ → ℝ) : ℝ :=
  vertexSum s f / s.vertices.card

theorem uniform_vertices_probability (s : State) (h : s.vertices.Nonempty) :
    IsProbabilityMeasure (Measure.uniformOfFinset s.vertices) := by
  constructor
  rw [Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)

/-- A vertex sampled conditionally uniformly from the whole tree. The empty
fallback is never used under the constructed tree law, which always contains the root. -/
noncomputable def vertexHeightKernel : Kernel State ℕ where
  toFun s := if s.vertices.Nonempty then (Measure.uniformOfFinset s.vertices).map s.height
    else Measure.dirac 0
  measurable' := measurable_from_top

instance vertexHeightKernel_probability (s : State) : IsProbabilityMeasure (vertexHeightKernel s) := by
  change IsProbabilityMeasure (if s.vertices.Nonempty then _ else _)
  split_ifs with h
  · have := uniform_vertices_probability s h
    infer_instance
  · infer_instance

/-- The actual law of the height of a conditionally uniform vertex. -/
noncomputable def uniformHeightLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (treeLaw x n).bind vertexHeightKernel

instance uniformHeightLaw_probability (x : SignSequence) (n : ℕ) :
    IsProbabilityMeasure (uniformHeightLaw x n) :=
  isProbabilityMeasure_bind vertexHeightKernel.measurable.aemeasurable
    (Filter.Eventually.of_forall vertexHeightKernel_probability)

theorem integral_uniform_vertices (s : State) (hs : s.vertices.Nonempty) (f : ℕ → ℝ) :
    (∫ v, f v ∂Measure.uniformOfFinset s.vertices) =
      (∑ v ∈ s.vertices, f v) / s.vertices.card := by
  unfold Measure.uniformOfFinset
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    ring
  · intro v _
    apply Integrable.smul_measure (integrable_dirac (by simp))
    simp [hs.ne_empty]

theorem vertexHeightKernel_integral (s : State) (hs : s.vertices.Nonempty) (f : ℕ → ℝ) :
    (∫ k, f k ∂vertexHeightKernel s) = vertexMean s f := by
  change (∫ k, f k ∂(if s.vertices.Nonempty then _ else _)) = _
  rw [ite_eq_left hs, integral_map (by fun_prop) (by fun_prop), integral_uniform_vertices s hs]
  rfl

theorem vertexHeightKernel_le {n : ℕ} {s : State} (hs : ValidAt n s) :
    vertexHeightKernel s {k | k ≤ n} = 1 := by
  have h : s.vertices.Nonempty := ⟨0, hs.root_mem⟩
  change (if s.vertices.Nonempty then (Measure.uniformOfFinset s.vertices).map s.height
    else Measure.dirac 0) {k | k ≤ n} = 1
  rw [ite_eq_left h, Measure.map_apply (by fun_prop) (by measurability), Measure.uniformOfFinset_apply]
  have hf : s.vertices.filter (fun v => s.height v ≤ n) = s.vertices := by
    apply Finset.filter_eq_self.mpr
    intro v hv
    exact (hs.height_le_id v hv).trans (hs.vertices_le v hv)
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hf]
  exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)

theorem uniformHeightLaw_le (x : SignSequence) (n : ℕ) :
    ∀ᵐ k ∂uniformHeightLaw x n, k ≤ n := by
  apply (ae_iff_prob_eq_one (by measurability)).mpr
  rw [uniformHeightLaw, Measure.bind_apply (by measurability) vertexHeightKernel.measurable.aemeasurable]
  calc
    _ = ∫⁻ _s, (1 : ℝ≥0∞) ∂treeLaw x n := by
      apply lintegral_congr_ae
      filter_upwards [treeLaw_valid x n] with s hs using vertexHeightKernel_le hs
    _ = 1 := by simp

theorem uniformHeightLaw_integrable (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    Integrable f (uniformHeightLaw x n) := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  apply (integrable_const C).mono' (by fun_prop)
  filter_upwards [uniformHeightLaw_le x n] with k hk
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (by omega))

theorem uniformHeightLaw_integral (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformHeightLaw x n) = ∫ s, vertexMean s f ∂treeLaw x n := by
  have hi := uniformHeightLaw_integrable x n f
  unfold uniformHeightLaw at hi ⊢
  have hi' : Integrable f ((vertexHeightKernel ∘ₖ Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [Kernel.comp_apply, Kernel.const_apply] using hi
  have hh := Kernel.integral_comp hi'
  simp only [Kernel.comp_apply, Kernel.const_apply] at hh
  rw [hh]
  apply integral_congr_ae
  filter_upwards [treeLaw_valid x n] with s hs
  exact vertexHeightKernel_integral s ⟨0, hs.root_mem⟩ f

/-- The total vertex count is deterministic before absorption. -/
theorem uniformHeightLaw_integral_eq_vertexSum (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) ≤ extinctionTime x) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformHeightLaw x n) =
      (∫ s, vertexSum s f ∂treeLaw x n) / (plusCount x n + 1 : ℕ) := by
  rw [uniformHeightLaw_integral, ← integral_div]
  apply integral_congr_ae
  filter_upwards [treeLaw_counts x n hτ] with s hs
  simp only [vertexMean, hs.2]

/-- Exact decomposition of a test function's total weight over vertex births. -/
theorem treeLaw_vertexSum_eq_birth_sum (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ s, vertexSum s f ∂treeLaw x n) = f 0 +
      ∑ i ∈ Finset.range n, if x (i + 1) then
        (∫ k, f (k + 1) ∂uniformActiveHeightLaw x i) else 0 := by
  induction n with
  | zero => simp [treeLaw, vertexSum, initial]
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
    rw [treeLaw_vertexSum_succ x n hnτ, ih hnτ, Finset.sum_range_succ]
    rw [uniformActiveHeightLaw_integral x n hnτ]
    ring

/-- Exact forward mixture for the law of a uniform vertex: the root and one
shifted active-height law for each attachment time, all with equal weight. -/
theorem uniformHeightLaw_integral_mixture (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ k, f k ∂uniformHeightLaw x n) =
      (f 0 + ∑ i ∈ Finset.range n, if x (i + 1) then
        (∫ k, f (k + 1) ∂uniformActiveHeightLaw x i) else 0) /
          (plusCount x n + 1 : ℕ) := by
  rw [uniformHeightLaw_integral_eq_vertexSum x n hτ.le,
    treeLaw_vertexSum_eq_birth_sum x n hτ]

theorem heightScale_mono_before_extinction (x : SignSequence) {i n : ℕ}
    (hin : i ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) :
    heightScale x i ≤ heightScale x n := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hin)
  intro j hj _
  have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
  have hs := ((lt_extinctionTime_iff x n).mp hτ) (j + 1) hjn
  have hsR : (0 : ℝ) < activeCount x (j + 1) := by exact_mod_cast hs
  split_ifs <;> positivity

/-- A positive-parameter exponential bound for a uniform vertex. The exact
birth mixture cancels the number of vertices; only the child's extra edge remains. -/
theorem uniformHeightLaw_mgf_upper (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    mgf (fun k : ℕ => (k : ℝ)) (uniformHeightLaw x n) θ ≤
      Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) := by
  let M : ℝ := Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1))
  have hd : 0 ≤ Real.exp θ - 1 := sub_nonneg.mpr (Real.one_le_exp hθ)
  have hh : 0 ≤ heightScale x n := by
    simpa only [heightScale_zero] using heightScale_mono_before_extinction x (Nat.zero_le n) hτ
  have hM : 1 ≤ M := by
    dsimp [M]
    nlinarith [Real.one_le_exp hθ, Real.one_le_exp (mul_nonneg hh hd)]
  have hterm : ∀ i ∈ Finset.range n,
      (if x (i + 1) then
        (∫ k : ℕ, Real.exp (θ * ((k + 1 : ℕ) : ℝ)) ∂uniformActiveHeightLaw x i) else 0) ≤
        if x (i + 1) then M else 0 := by
    intro i hi
    split_ifs
    · have hin := (Finset.mem_range.mp hi).le
      have hiτ : (i : ℕ∞) < extinctionTime x :=
        lt_of_le_of_lt (by exact_mod_cast hin) hτ
      have hmono : Real.exp (heightScale x i * (Real.exp θ - 1)) ≤
          Real.exp (heightScale x n * (Real.exp θ - 1)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
          (heightScale_mono_before_extinction x hin hτ) hd)
      simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add,
        mul_comm _ (Real.exp θ)]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        ((uniformActiveHeightLaw_mgf_le x i hiτ θ).trans hmono) (Real.exp_pos θ).le
    · exact le_rfl
  have hsum : (∑ i ∈ Finset.range n, if x (i + 1) then M else 0) = plusCount x n * M := by
    rw [plusCount, Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases x (i + 1) <;> simp
  change (∫ k : ℕ, Real.exp (θ * (k : ℝ)) ∂uniformHeightLaw x n) ≤ M
  rw [uniformHeightLaw_integral_mixture x n hτ]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (plusCount x n + 1 : ℕ))).mpr
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero]
  calc
    _ ≤ 1 + ∑ i ∈ Finset.range n, if x (i + 1) then M else 0 :=
      add_le_add le_rfl (Finset.sum_le_sum hterm)
    _ = 1 + plusCount x n * M := by rw [hsum]
    _ ≤ M + plusCount x n * M := add_le_add hM le_rfl
    _ = M * (plusCount x n + 1 : ℕ) := by push_cast; ring

end Freezing1.Forward
