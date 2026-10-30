module

public import Freezing1.SIRCaptureCoefficientLaw
public import Freezing1.SIRFrozenBalls
public import Freezing1.FiniteUniformRestriction

/-! Same-epsilon capture in the native infection-tree history, with genuine conditional uniform sampling. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def prefixCaptureKernel (before last : TreeState) : Measure Bool :=
  if last.tree.vertices.Nonempty then
    (Measure.uniformOfFinset last.tree.vertices).map (fun v => decide (v ∈ before.tree.vertices))
  else Measure.dirac false

instance prefixCaptureKernel_probability (before last : TreeState) :
    IsProbabilityMeasure (prefixCaptureKernel before last) := by
  unfold prefixCaptureKernel
  split_ifs with h
  · have : IsProbabilityMeasure (Measure.uniformOfFinset last.tree.vertices) := by
      constructor
      rw [Measure.uniformOfFinset_apply]
      simp only [Set.mem_univ, Finset.filter_true]
      exact ENNReal.div_self (by exact_mod_cast h.card_pos.ne') (by simp)
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance
  · infer_instance

theorem measurable_prefixCaptureHistoryKernel (n k : ℕ) :
    Measurable (fun H : ℕ → TreeState => prefixCaptureKernel (H k) (H (2 * n + 1))) := by
  let f : TreeState × TreeState → Measure Bool := fun z => prefixCaptureKernel z.1 z.2
  have hf : Measurable f := measurable_of_countable f
  have he : (fun H : ℕ → TreeState => prefixCaptureKernel (H k) (H (2 * n + 1))) =
      f ∘ (fun H : ℕ → TreeState => (H k, H (2 * n + 1))) := rfl
  rw [he]
  exact hf.comp ((measurable_pi_apply k).prodMk (measurable_pi_apply (2 * n + 1)))

noncomputable def actualPrefixCaptureLaw (r : ℝ≥0) (n k : ℕ) : Measure Bool :=
  (treeFullLaw r n).bind (fun H => prefixCaptureKernel (H k) (H (2 * n + 1)))

instance actualPrefixCaptureLaw_probability (r : ℝ≥0) (n k : ℕ) :
    IsProbabilityMeasure (actualPrefixCaptureLaw r n k) :=
  isProbabilityMeasure_bind (measurable_prefixCaptureHistoryKernel n k).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem prefixCaptureKernel_true {before last : TreeState}
    (hsub : before.tree.vertices ⊆ last.tree.vertices) (hne : last.tree.vertices.Nonempty) :
    (prefixCaptureKernel before last).real {true} =
      (before.tree.vertices.card : ℝ) / last.tree.vertices.card := by
  rw [prefixCaptureKernel, ite_eq_left hne,
    map_measureReal_apply (measurable_of_countable _) ((Set.to_countable _).measurableSet),
    FiniteUniform.uniformOfFinset_real]
  have he : last.tree.vertices.filter
      (fun v => v ∈ (fun v => decide (v ∈ before.tree.vertices)) ⁻¹' ({true} : Set Bool)) =
        before.tree.vertices := by
    ext v
    simp only [Finset.mem_filter, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
  rw [he]

theorem retainedFraction_eq_one_sub_uncaptured {a b : ℕ} (hab : a ≤ b) (hb : 0 < b) :
    (a : ℝ) / b = 1 - uncapturedFraction b a := by
  unfold uncapturedFraction
  rw [Nat.cast_sub hab]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  field_simp
  ring

theorem measurable_forwardMissingFraction (n k : ℕ) : Measurable (forwardMissingFraction n k) := by
  let f : Counts × Counts → ℝ := fun z =>
    uncapturedFraction (captureVertexCount n z.2) (captureVertexCount n z.1)
  have hf : Measurable f := measurable_of_countable f
  have he : forwardMissingFraction n k = f ∘ (fun H : ℕ → Counts => (H k, H (2 * n + 1))) := rfl
  rw [he]
  exact hf.comp ((measurable_pi_apply k).prodMk (measurable_pi_apply (2 * n + 1)))

theorem forwardMissingFraction_bounds (n k : ℕ) (H : ℕ → Counts) :
    0 ≤ forwardMissingFraction n k H ∧ forwardMissingFraction n k H ≤ 1 :=
  uncapturedFraction_bounds _ _

theorem forwardMissingFraction_integrable (r : ℝ≥0) (n k : ℕ) :
    Integrable (forwardMissingFraction n k) (countsFullLaw r n) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_forwardMissingFraction n k).aestronglyMeasurable
  exact Eventually.of_forall fun H => by
    rw [Real.norm_eq_abs, abs_of_nonneg (forwardMissingFraction_bounds n k H).1]
    exact (forwardMissingFraction_bounds n k H).2

theorem integral_bool_true (μ : Measure Bool) :
    (∫ b : Bool, (if b = true then (1 : ℝ) else 0) ∂μ) = μ.real {true} := by
  simpa using integral_ite_indicator μ (fun b : Bool => b = true) ((Set.to_countable _).measurableSet)

theorem treeFullLaw_captureKernel_fraction (r : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    ∀ᵐ H ∂treeFullLaw r n,
      (prefixCaptureKernel (H k) (H (2 * n + 1))).real {true} =
        1 - forwardMissingFraction n k (fun j => (H j).counts) := by
  filter_upwards [treeFullLaw_valid r n, treeFullLaw_update r n] with H hv hu
  have hmono : Monotone (fun j => (H j).tree.vertices) := by
    apply monotone_nat_of_le_succ
    intro j
    rcases hu j with h | ⟨sign, u, _, h⟩
    · rw [h]
    · rw [h]
      exact treeStep_vertices_mono _ _ _
  have hne : (H (2 * n + 1)).tree.vertices.Nonempty := ⟨[], (hv _).1.root_mem⟩
  rw [prefixCaptureKernel_true (hmono hk) hne]
  have hp : captureVertexCount n (H k).counts = (H k).tree.vertices.card := by
    have h := (hv k).2
    change n + 1 - (H k).susceptible = _
    omega
  have ht : captureVertexCount n (H (2 * n + 1)).counts = (H (2 * n + 1)).tree.vertices.card := by
    have h := (hv (2 * n + 1)).2
    change n + 1 - (H (2 * n + 1)).susceptible = _
    omega
  change _ = 1 - uncapturedFraction (captureVertexCount n (H (2 * n + 1)).counts)
    (captureVertexCount n (H k).counts)
  rw [hp, ht]
  exact retainedFraction_eq_one_sub_uncaptured (Finset.card_le_card (hmono hk)) hne.card_pos

theorem actualPrefixCaptureLaw_true_eq (r : ℝ≥0) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    (actualPrefixCaptureLaw r n k).real {true} =
      1 - ∫ C, forwardMissingFraction n k C ∂countsFullLaw r n := by
  have hm : Measurable (fun H : ℕ → TreeState => fun j => (H j).counts) :=
    Measurable.of_eval fun j => (measurable_of_countable TreeState.counts).comp (measurable_pi_apply j)
  have hCounts : HasLaw (fun H : ℕ → TreeState => fun j => (H j).counts)
      (countsFullLaw r n) (treeFullLaw r n) := ⟨hm.aemeasurable, map_treeFullLaw_counts r n⟩
  have hiF := hCounts.integrable_fun_comp (forwardMissingFraction_integrable r n k)
  have hb (b : Bool) : 0 ≤ (if b = true then (1 : ℝ) else 0) ∧
      (if b = true then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hi : Integrable (fun b : Bool => if b = true then (1 : ℝ) else 0)
      (actualPrefixCaptureLaw r n k) :=
    integrable_unitInterval_function _ (measurable_of_countable _) hb
  rw [← integral_bool_true]
  change (∫ b : Bool, (if b = true then (1 : ℝ) else 0)
    ∂(treeFullLaw r n).bind (fun H => prefixCaptureKernel (H k) (H (2 * n + 1)))) = _
  rw [integral_bind_of_integrable _ _ (measurable_prefixCaptureHistoryKernel n k) hi]
  have he : (fun H => ∫ b : Bool, (if b = true then (1 : ℝ) else 0)
      ∂prefixCaptureKernel (H k) (H (2 * n + 1))) =ᵐ[treeFullLaw r n]
      (fun H => 1 - forwardMissingFraction n k (fun j => (H j).counts)) := by
    filter_upwards [treeFullLaw_captureKernel_fraction r n k hk] with H hH
    rw [integral_bool_true]
    exact hH
  rw [integral_congr_ae he, integral_sub (integrable_const (1 : ℝ)) hiF,
    integral_const, probReal_univ, one_smul]
  have h := hCounts.integral_comp (measurable_forwardMissingFraction n k).aestronglyMeasurable
  exact congrArg (fun z : ℝ => 1 - z) h

/-- Native actual SIR capture, with the same epsilon in cutoff and error. -/
theorem actualPrefixCaptureLaw_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualPrefixCaptureLaw (rate n) n
        ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊).real {true} := by
  have ht2 : fluidExtinctionTime lam - eps ≤ 2 := by
    have hh := (fluidExtinctionTime_spec hlam).2.1
    linarith only [hh, heps]
  filter_upwards [countsFullLaw_reverseMissing_same_epsilon rate lam hlam hscaled heps hepsT]
    with n hn
  have hk : ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊ ≤ 2 * n + 1 := by
    have h := StoppedCoupling.floor_time_index_le (n := n) (m := 2) ht2
    omega
  rw [actualPrefixCaptureLaw_true_eq _ _ _ hk]
  have hle := integral_mono
    (forwardMissingFraction_integrable (rate n) n ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊)
    (reverseMissingFraction_integrable (rate n) n ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊)
    (fun H => forwardMissingFraction_le_reverse n ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊ H)
  linarith only [hle, hn]

/-- The two Bernoulli observations really come from two independent uniform
terminal vertices, including the diagonal pair. -/
theorem prefixCaptureKernel_prod_actual {before last : TreeState}
    (hne : last.tree.vertices.Nonempty) :
    (prefixCaptureKernel before last).prod (prefixCaptureKernel before last) =
      ((Measure.uniformOfFinset last.tree.vertices).prod
        (Measure.uniformOfFinset last.tree.vertices)).map
          (fun z => (decide (z.1 ∈ before.tree.vertices), decide (z.2 ∈ before.tree.vertices))) := by
  have : IsProbabilityMeasure (Measure.uniformOfFinset last.tree.vertices) := by
    constructor
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    exact ENNReal.div_self (by exact_mod_cast hne.card_pos.ne') (by simp)
  rw [prefixCaptureKernel, ite_eq_left hne,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem measurable_prefixCapturePairHistoryKernel (n k : ℕ) :
    Measurable (fun H : ℕ → TreeState =>
      (prefixCaptureKernel (H k) (H (2 * n + 1))).prod
        (prefixCaptureKernel (H k) (H (2 * n + 1)))) := by
  let f : TreeState × TreeState → Measure (Bool × Bool) := fun z =>
    (prefixCaptureKernel z.1 z.2).prod (prefixCaptureKernel z.1 z.2)
  have hf : Measurable f := measurable_of_countable f
  have he : (fun H : ℕ → TreeState =>
      (prefixCaptureKernel (H k) (H (2 * n + 1))).prod
        (prefixCaptureKernel (H k) (H (2 * n + 1)))) =
      f ∘ (fun H : ℕ → TreeState => (H k, H (2 * n + 1))) := rfl
  rw [he]
  exact hf.comp ((measurable_pi_apply k).prodMk (measurable_pi_apply (2 * n + 1)))

noncomputable def actualPrefixCapturePairLaw (r : ℝ≥0) (n k : ℕ) : Measure (Bool × Bool) :=
  (treeFullLaw r n).bind fun H =>
    (prefixCaptureKernel (H k) (H (2 * n + 1))).prod
      (prefixCaptureKernel (H k) (H (2 * n + 1)))

instance actualPrefixCapturePairLaw_probability (r : ℝ≥0) (n k : ℕ) :
    IsProbabilityMeasure (actualPrefixCapturePairLaw r n k) :=
  isProbabilityMeasure_bind (measurable_prefixCapturePairHistoryKernel n k).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem actualPrefixCapturePairLaw_map_fst (r : ℝ≥0) (n k : ℕ) :
    (actualPrefixCapturePairLaw r n k).map Prod.fst = actualPrefixCaptureLaw r n k := by
  rw [actualPrefixCapturePairLaw,
    Measure.map_bind (measurable_prefixCapturePairHistoryKernel n k).aemeasurable
      measurable_fst.aemeasurable]
  have he : (fun H : ℕ → TreeState =>
      ((prefixCaptureKernel (H k) (H (2 * n + 1))).prod
        (prefixCaptureKernel (H k) (H (2 * n + 1)))).map Prod.fst) =
      (fun H => prefixCaptureKernel (H k) (H (2 * n + 1))) := by
    funext H
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [he]
  rfl

theorem actualPrefixCapturePairLaw_map_snd (r : ℝ≥0) (n k : ℕ) :
    (actualPrefixCapturePairLaw r n k).map Prod.snd = actualPrefixCaptureLaw r n k := by
  rw [actualPrefixCapturePairLaw,
    Measure.map_bind (measurable_prefixCapturePairHistoryKernel n k).aemeasurable
      measurable_snd.aemeasurable]
  have he : (fun H : ℕ → TreeState =>
      ((prefixCaptureKernel (H k) (H (2 * n + 1))).prod
        (prefixCaptureKernel (H k) (H (2 * n + 1)))).map Prod.snd) =
      (fun H => prefixCaptureKernel (H k) (H (2 * n + 1))) := by
    funext H
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [he]
  rfl

theorem actualPrefixCapturePairLaw_true_marginals (r : ℝ≥0) (n k : ℕ) :
    (actualPrefixCapturePairLaw r n k).real {z | z.1 = true} =
        (actualPrefixCaptureLaw r n k).real {true} ∧
      (actualPrefixCapturePairLaw r n k).real {z | z.2 = true} =
        (actualPrefixCaptureLaw r n k).real {true} := by
  constructor
  · rw [← actualPrefixCapturePairLaw_map_fst,
      map_measureReal_apply measurable_fst ((Set.to_countable _).measurableSet)]
    rfl
  · rw [← actualPrefixCapturePairLaw_map_snd,
      map_measureReal_apply measurable_snd ((Set.to_countable _).measurableSet)]
    rfl

theorem actualPrefixCapturePairLaw_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      let k := ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊
      1 - eps ≤ (actualPrefixCapturePairLaw (rate n) n k).real {z | z.1 = true} ∧
        (actualPrefixCapturePairLaw (rate n) n k).real {z | z.1 = true} =
          (actualPrefixCapturePairLaw (rate n) n k).real {z | z.2 = true} := by
  filter_upwards [actualPrefixCaptureLaw_same_epsilon rate lam hlam hscaled heps hepsT] with n hn
  have hm := actualPrefixCapturePairLaw_true_marginals (rate n) n
    ⌊(n : ℝ) * (fluidExtinctionTime lam - eps)⌋₊
  exact ⟨by rwa [hm.1], hm.1.trans hm.2.symm⟩

end Freezing1.SIR
