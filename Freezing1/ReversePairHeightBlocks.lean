module

public import Freezing1.ReversePairHeightKernel
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Iterating the actual killed two-height kernel

The continuation law is built by binding the original reverse kernels. Its
pair-product bound retains the actual event that the two component roots are
different at the bottom of the block. No conditional independence on that
event is used.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- Bochner integration through a measurable bind, with integrability explicit. -/
theorem integral_bind_of_integrable {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ : Measure α) (K : α → Measure β) (hK : Measurable K)
    {f : β → ℝ} (hf : Integrable f (μ.bind K)) :
    (∫ y, f y ∂μ.bind K) = ∫ x, (∫ y, f y ∂K x) ∂μ := by
  let κ : Kernel α β := ⟨K, hK⟩
  have hi : Integrable f ((κ ∘ₖ Kernel.const Unit μ) ()) := by
    simpa only [κ, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hf
  simpa only [κ, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using
    Kernel.integral_comp hi

theorem integrable_unitInterval_function {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb x).1]; exact (hb x).2

theorem integral_unitInterval_bounds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ (∫ x, f x ∂μ) ∧ (∫ x, f x ∂μ) ≤ 1 := by
  refine ⟨integral_nonneg (fun x => (hb x).1), ?_⟩
  simpa using integral_mono (integrable_unitInterval_function μ hf hb)
    (integrable_const (1 : ℝ)) (fun x => (hb x).2)

/-- Successive independent Bernoulli averaging, in descending paper-step order. -/
noncomputable def blockAverage (p : ℕ → unitInterval) (a : ℕ) :
    ℕ → (ℕ → ℝ) → ℕ → ℝ
  | 0, f, d => f d
  | k + 1, f, d => bernoulliAverage (p (a + k)) (blockAverage p a k f) d

theorem blockAverage_mono (p : ℕ → unitInterval) (a k : ℕ) {f : ℕ → ℝ}
    (hf : Monotone f) : Monotone (blockAverage p a k f) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact bernoulliAverage_mono _ ih

theorem blockAverage_bounds (p : ℕ → unitInterval) (a k : ℕ) {f : ℕ → ℝ}
    (hf : ∀ d, 0 ≤ f d ∧ f d ≤ 1) (d : ℕ) :
    0 ≤ blockAverage p a k f d ∧ blockAverage p a k f d ≤ 1 := by
  induction k generalizing d with
  | zero => exact hf d
  | succ k ih =>
    refine ⟨bernoulliAverage_nonneg _ (fun d => (ih d).1) d, ?_⟩
    change (p (a + k) : ℝ) * blockAverage p a k f (d + 1) +
      (1 - (p (a + k) : ℝ)) * blockAverage p a k f d ≤ 1
    have h1 := mul_le_mul_of_nonneg_left (ih (d + 1)).2 (p (a + k)).2.1
    have h0 := mul_le_mul_of_nonneg_left (ih d).2 (sub_nonneg.mpr (p (a + k)).2.2)
    linarith

namespace Reverse

/-- A harmless zero extension of the actual finite schedule parameters. -/
noncomputable def stepParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : ℕ) : unitInterval :=
  if hi : i < n then attachmentParameter x n hn ⟨i, hi⟩ else 0

theorem stepParameter_of_lt (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {i : ℕ} (hi : i < n) :
    stepParameter x n hn i = attachmentParameter x n hn ⟨i, hi⟩ := by
  simp only [stepParameter, dite_eq_left hi]

/-- Actual continuation from phase `a+k` down to phase `a`. -/
noncomputable def blockLaw (x : SignSequence) (a : ℕ) : ℕ → Forest → Measure Forest
  | 0, F => Measure.dirac F
  | k + 1, F => (transitionLaw x (a + k) F).bind (blockLaw x a k)

instance blockLaw_probability (x : SignSequence) (a k : ℕ) (F : Forest) :
    IsProbabilityMeasure (blockLaw x a k F) := by
  induction k generalizing F with
  | zero => change IsProbabilityMeasure (Measure.dirac F); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall ih)

/-- Product test function, killed as soon as its two component roots coincide. -/
noncomputable def killedProduct (u v : ℕ ⊕ ℕ) (f g : ℕ → ℝ) (F : Forest) : ℝ :=
  if F.root u ≠ F.root v then f (F.depth u) * g (F.depth v) else 0

theorem killedProduct_bounds (u v : ℕ ⊕ ℕ) {f g : ℕ → ℝ}
    (hf : ∀ d, 0 ≤ f d ∧ f d ≤ 1) (hg : ∀ d, 0 ≤ g d ∧ g d ≤ 1)
    (F : Forest) : 0 ≤ killedProduct u v f g F ∧ killedProduct u v f g F ≤ 1 := by
  unfold killedProduct
  split_ifs
  · exact ⟨mul_nonneg (hf _).1 (hg _).1,
      (mul_le_mul (hf _).2 (hg _).2 (hg _).1 zero_le_one).trans_eq (one_mul _)⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- A product supersolution for the true block kernel. The two heights are
not declared independent; trajectories that coalesce are assigned zero. -/
theorem blockLaw_killed_product_le {x : SignSequence} {n a k : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hF : ValidAt x n (a + k) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    {f g : ℕ → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf01 : ∀ d, 0 ≤ f d ∧ f d ≤ 1) (hg01 : ∀ d, 0 ≤ g d ∧ g d ≤ 1) :
    (∫ F', killedProduct u v f g F' ∂blockLaw x a k F) ≤
      killedProduct u v (blockAverage (stepParameter x n hn) a k f)
        (blockAverage (stepParameter x n hn) a k g) F := by
  induction k generalizing F with
  | zero => simp [blockLaw, blockAverage]
  | succ k ih =>
    have hi : a + k < n := by omega
    have hF' : ValidAt x n (a + k + 1) F := by simpa [Nat.add_assoc] using hF
    have hiBind : Integrable (killedProduct u v f g) (blockLaw x a (k + 1) F) :=
      integrable_unitInterval_function _ measurable_from_top (killedProduct_bounds u v hf01 hg01)
    rw [blockLaw, integral_bind_of_integrable _ _ measurable_from_top hiBind]
    have hinner : Integrable (fun F' => ∫ F'', killedProduct u v f g F''
        ∂blockLaw x a k F') (transitionLaw x (a + k) F) :=
      integrable_unitInterval_function _ measurable_from_top fun F' =>
        integral_unitInterval_bounds _ measurable_from_top (killedProduct_bounds u v hf01 hg01)
    have havgF := blockAverage_bounds (stepParameter x n hn) a k hf01
    have havgG := blockAverage_bounds (stepParameter x n hn) a k hg01
    have hiRhs : Integrable (killedProduct u v
        (blockAverage (stepParameter x n hn) a k f)
        (blockAverage (stepParameter x n hn) a k g)) (transitionLaw x (a + k) F) :=
      integrable_unitInterval_function _ measurable_from_top (killedProduct_bounds u v havgF havgG)
    refine (integral_mono_ae hinner hiRhs ?_).trans ?_
    · filter_upwards [transitionLaw_valid hn hi hF',
        transitionLaw_present_depth_support hn hi hF' hu,
        transitionLaw_present_depth_support hn hi hF' hv] with F' hvalid hu' hv'
      exact ih (by omega) hvalid hu'.1 hv'.1
    · have h := (transitionLaw_killed_product_le hn hi hF' hu hv
        (blockAverage_mono _ _ _ hf) (blockAverage_mono _ _ _ hg)
        (fun d => (havgF d).1) (fun d => (havgG d).1)).2
      simpa only [killedProduct, blockAverage, stepParameter_of_lt x n hn hi] using h


/-- Finite product coordinates in the paper block `(a,a+k]`. -/
def blockIndices (n a k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => a ≤ i.val ∧ i.val < a + k

@[simp] theorem blockIndices_zero (n a : ℕ) : blockIndices n a 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [blockIndices, Finset.mem_filter, Finset.mem_univ, true_and, Nat.add_zero] at hi
  omega

theorem blockIndices_not_mem_next (n a k : ℕ) (hi : a + k < n) :
    (⟨a + k, hi⟩ : Fin n) ∉ blockIndices n a k := by
  simp [blockIndices]

theorem blockIndices_succ (n a k : ℕ) (hi : a + k < n) :
    blockIndices n a (k + 1) = insert ⟨a + k, hi⟩ (blockIndices n a k) := by
  ext i
  simp only [blockIndices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Fin.ext_iff]
  omega

/-- The deterministic average is exactly expectation under the explicitly
independent finite Bernoulli product used in the other height laws. -/
theorem blockAverage_eq_integral_partialSum (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a k : ℕ} (hk : a + k ≤ n)
    {f : ℕ → ℝ} (hf : ∀ d, 0 ≤ f d ∧ f d ≤ 1) (d : ℕ) :
    blockAverage (stepParameter x n hn) a k f d =
      ∫ j, f (d + j) ∂bernoulliPartialSumLaw (attachmentParameter x n hn) (blockIndices n a k) := by
  induction k generalizing d with
  | zero => simp [blockAverage]
  | succ k ih =>
    have hi : a + k < n := by omega
    rw [blockIndices_succ n a k hi, bernoulliPartialSumLaw_insert _ _ (blockIndices_not_mem_next n a k hi)]
    have hint : Integrable (fun j => f (d + j))
        ((bernoulliPartialSumLaw (attachmentParameter x n hn) (blockIndices n a k)).bind
          (fun j => bernoulliMeasure (j + 1) j (attachmentParameter x n hn ⟨a + k, hi⟩))) := by
      have hp : IsProbabilityMeasure
          ((bernoulliPartialSumLaw (attachmentParameter x n hn) (blockIndices n a k)).bind
            (fun j => bernoulliMeasure (j + 1) j (attachmentParameter x n hn ⟨a + k, hi⟩))) :=
        isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
          (Filter.Eventually.of_forall fun _ => inferInstance)
      exact integrable_unitInterval_function _ (measurable_of_countable _) (fun j => hf (d + j))
    rw [integral_bind_of_integrable _ _ (measurable_of_countable _) hint]
    simp only [integral_bernoulliMeasure, smul_eq_mul]
    have hint1 : Integrable (fun j => f (d + (j + 1)))
        (bernoulliPartialSumLaw (attachmentParameter x n hn) (blockIndices n a k)) :=
      integrable_unitInterval_function _ (measurable_of_countable _) (fun j => hf _)
    have hint0 : Integrable (fun j => f (d + j))
        (bernoulliPartialSumLaw (attachmentParameter x n hn) (blockIndices n a k)) :=
      integrable_unitInterval_function _ (measurable_of_countable _) (fun j => hf _)
    rw [integral_add (hint1.const_mul _) (hint0.const_mul _), integral_const_mul, integral_const_mul]
    have he : (fun j => f (d + (j + 1))) = fun j => f ((d + 1) + j) := by
      funext j
      congr 1
      omega
    rw [he, ← ih (by omega) (d + 1), ← ih (by omega) d]
    simp only [blockAverage, bernoulliAverage, stepParameter_of_lt x n hn hi]

/-- The same continuation has the exact one-height expectation, used to
identify the comparison factor with the true one-vertex block probability. -/
theorem blockLaw_depth_integral {x : SignSequence} {n a k : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hF : ValidAt x n (a + k) F) {v : ℕ ⊕ ℕ} (hv : v ∈ F.vertices)
    {f : ℕ → ℝ} (hf : ∀ d, 0 ≤ f d ∧ f d ≤ 1) :
    (∫ F', f (F'.depth v) ∂blockLaw x a k F) =
      blockAverage (stepParameter x n hn) a k f (F.depth v) := by
  induction k generalizing F with
  | zero => simp [blockLaw, blockAverage]
  | succ k ih =>
    have hi : a + k < n := by omega
    have hF' : ValidAt x n (a + k + 1) F := by simpa [Nat.add_assoc] using hF
    have hint : Integrable (fun F' => f (F'.depth v)) (blockLaw x a (k + 1) F) :=
      integrable_unitInterval_function _ measurable_from_top (fun F' => hf _)
    rw [blockLaw, integral_bind_of_integrable _ _ measurable_from_top hint]
    have he : (fun F' => ∫ F'', f (F''.depth v) ∂blockLaw x a k F') =ᵐ[transitionLaw x (a + k) F]
        fun F' => blockAverage (stepParameter x n hn) a k f (F'.depth v) := by
      filter_upwards [transitionLaw_valid hn hi hF',
        transitionLaw_present_depth_support hn hi hF' hv] with F' hvalid hv'
      exact ih (by omega) hvalid hv'.1
    rw [integral_congr_ae he]
    have hL : HasLaw (fun F' : Forest => F'.depth v)
        (bernoulliMeasure (F.depth v + 1) (F.depth v)
          (attachmentParameter x n hn ⟨a + k, hi⟩)) (transitionLaw x (a + k) F) := by
      apply hasLaw_nat_succ_of_support measurable_from_top
        ((transitionLaw_present_depth_support hn hi hF' hv).mono fun _ h => h.2)
      rw [transitionLaw_height_increment hn hi hF' hv, attachmentParameter_coe]
    have heq := hL.integral_comp
      (measurable_of_countable (blockAverage (stepParameter x n hn) a k f)).aestronglyMeasurable
    simpa only [Function.comp_def, integral_bernoulliMeasure, smul_eq_mul,
      blockAverage, bernoulliAverage, stepParameter_of_lt x n hn hi] using heq

end Reverse
end Freezing1
