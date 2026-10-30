module

public import Freezing1.MainLinearDistance
public import Freezing1.FiniteUniformPairs
public import Mathlib.Probability.Independence.Basic

/-!
# Sampled distance matrices of the forward tree (linear regime)

For `k` points drawn independently and uniformly from the vertices of the *same*
forward tree $T_n$, the sampling kernel records the $k\times k$ matrix of graph
distances. This is the object used by the Gromov-weak (distance-matrix)
topology of Elek-Tardos and Janson.

* `sampleKernel k s` is the law of that matrix for a fixed state `s`, and
  `sampleLaw x n k` averages it over the actual forward tree law.
* `linear_sampled_distance_matrix_tendsto_zero` : under the hypotheses of
  Theorem `thm:lineaire`, for every `k` and every $\varepsilon>0$,
  $\mathbb P(\max_{i,j}|D_{ij}/\ln n-\tfrac{c+1}{c}\mathbf 1_{i\ne j}|\ge\varepsilon)\to0$.
  The diagonal is identically zero; every off-diagonal pair has exactly the pair
  law `forwardPairDataLaw`, so coincidences $V_i=V_j$ are included.
* `starMatrix a k` is the sampled distance matrix of `k` independent points of
  the long dendron $\Upsilon_{\delta_a}$ (dictionary entry, see the notes).
-/

@[expose] public section

namespace Freezing1.LinearBush

open MeasureTheory ProbabilityTheory Filter CanonicalTree
open scoped Topology ENNReal Classical

/-! ### The limit object -/

/-- Distance matrix of `k` points of the long dendron $\Upsilon_\nu$ whose
heights (distances to the root) are `h`. Two distinct sampled points branch at
the root, hence are at distance `h i + h j`; the diagonal is zero. -/
def longDendronMatrix {k : ℕ} (h : Fin k → ℝ) : Fin k → Fin k → ℝ :=
  fun i j => if i = j then 0 else h i + h j

/-- Sampled distance matrix of `k` independent points of $\Upsilon_{\delta_a}$:
every height is `a`, so all distinct pairs are at distance `2a`. -/
def starMatrix (a : ℝ) (k : ℕ) : Fin k → Fin k → ℝ :=
  fun i j => if i = j then 0 else 2 * a

theorem starMatrix_eq_longDendronMatrix (a : ℝ) (k : ℕ) :
    starMatrix a k = longDendronMatrix (fun _ : Fin k => a) := by
  funext i j
  simp only [starMatrix, longDendronMatrix]
  split_ifs <;> ring

/-- Law of the sampled distance matrix of `k` iid points of $\Upsilon_\nu$:
the heights are iid with law `ν`. -/
noncomputable def longDendronSampleLaw (ν : Measure ℝ) (k : ℕ) : Measure (Fin k → Fin k → ℝ) :=
  (Measure.pi fun _ : Fin k => ν).map longDendronMatrix

/-- For $\nu=\delta_a$ the sampled matrix law is the Dirac mass at the star matrix. -/
theorem longDendronSampleLaw_dirac (a : ℝ) (k : ℕ) :
    longDendronSampleLaw (Measure.dirac a) k = Measure.dirac (starMatrix a k) := by
  have hpi : (Measure.pi fun _ : Fin k => (Measure.dirac a : Measure ℝ)) =
      Measure.dirac (fun _ : Fin k => a) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
    simp only [Set.indicator, Set.mem_pi, Set.mem_univ, forall_true_left]
    simp only [Measure.dirac_apply' _ (hs _), Set.indicator]
    by_cases h : ∀ i, a ∈ s i
    · simp [h]
    · push Not at h
      obtain ⟨i, hi⟩ := h
      simp only [Finset.prod_ite_zero]
      simp
  have hmeas : Measurable (longDendronMatrix : (Fin k → ℝ) → Fin k → Fin k → ℝ) := by
    unfold longDendronMatrix
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    by_cases hij : i = j
    · simp [hij]
    · simp only [hij, ite_false]
      exact ((measurable_pi_apply i).add (measurable_pi_apply j))
  rw [longDendronSampleLaw, hpi, Measure.map_dirac' hmeas, ← starMatrix_eq_longDendronMatrix]

/-! ### Finite uniform measures -/

instance instIsFiniteMeasureUniformOfFinset {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (A : Finset α) :
    IsFiniteMeasure (Measure.uniformOfFinset A) := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · have : Measure.uniformOfFinset (∅ : Finset α) = 0 := by simp [Measure.uniformOfFinset]
    rw [this]
    infer_instance
  · have := FiniteUniform.uniformOfFinset_probability hA
    infer_instance

/-! ### The sampling kernel and its law -/

/-- The law of the `k × k` graph-distance matrix of `k` independent uniform vertices
of the fixed state `s`. -/
noncomputable def sampleKernel (k : ℕ) (s : Forward.State) : Measure (Fin k → Fin k → ℕ) :=
  (Measure.pi fun _ : Fin k => Measure.uniformOfFinset s.vertices).map
    (fun v i j => s.graph.dist (v i) (v j))

/-- The law of the sampled distance matrix of the forward tree `T_n`: sample the actual
tree, then `k` conditionally independent uniform vertices of that same tree. -/
noncomputable def sampleLaw (x : SignSequence) (n k : ℕ) : Measure (Fin k → Fin k → ℕ) :=
  (Forward.treeLaw x n).bind (sampleKernel k)

theorem measurable_sampleMatrix (k : ℕ) (s : Forward.State) :
    Measurable (fun (v : Fin k → ℕ) (i j : Fin k) => s.graph.dist (v i) (v j)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have h := (measurable_of_countable (fun p : ℕ × ℕ => s.graph.dist p.1 p.2)).comp
    ((measurable_pi_apply (X := fun _ : Fin k => ℕ) i).prodMk (measurable_pi_apply j))
  exact h

theorem sampleKernel_probability {k : ℕ} {s : Forward.State} (hs : s.vertices.Nonempty) :
    IsProbabilityMeasure (sampleKernel k s) := by
  have := FiniteUniform.uniformOfFinset_probability hs
  unfold sampleKernel
  infer_instance

theorem sampleLaw_probability (x : SignSequence) (n k : ℕ) :
    IsProbabilityMeasure (sampleLaw x n k) := by
  unfold sampleLaw
  refine isProbabilityMeasure_bind measurable_from_top.aemeasurable ?_
  filter_upwards [Forward.treeLaw_valid x n] with s hs
  exact sampleKernel_probability ⟨0, hs.root_mem⟩

/-! ### Two coordinates of a product of uniform samples -/

/-- Two distinct coordinates of an iid sample are independent, each with the common law. -/
theorem pi_pair_map {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    (Measure.pi fun _ : Fin k => μ).map (fun v => (v i, v j)) = μ.prod μ := by
  have hind := iIndepFun_pi (μ := fun _ : Fin k => μ) (X := fun _ => (id : α → α))
    (fun _ => aemeasurable_id)
  have h2 := (hind.indepFun hij).map_prod_eq_prod_map_map
    ((measurable_pi_apply i).aemeasurable) ((measurable_pi_apply j).aemeasurable)
  have hi : (Measure.pi fun _ : Fin k => μ).map (fun v => v i) = μ :=
    (measurePreserving_eval (fun _ : Fin k => μ) i).map_eq
  have hj : (Measure.pi fun _ : Fin k => μ).map (fun v => v j) = μ :=
    (measurePreserving_eval (fun _ : Fin k => μ) j).map_eq
  simpa only [id, hi, hj] using h2

theorem sampleKernel_pair_apply {k : ℕ} {s : Forward.State} (hs : s.vertices.Nonempty)
    {i j : Fin k} (hij : i ≠ j) (T : Set ℕ) :
    sampleKernel k s {D | D i j ∈ T} =
      ∫⁻ u, (Measure.uniformOfFinset s.vertices) {v | s.graph.dist u v ∈ T}
        ∂(Measure.uniformOfFinset s.vertices) := by
  have := FiniteUniform.uniformOfFinset_probability hs
  have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | D i j ∈ T} :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) (MeasurableSet.of_discrete (s := T))
  rw [sampleKernel, Measure.map_apply (measurable_sampleMatrix k s) hmeas]
  have h1 : (fun (v : Fin k → ℕ) (i j : Fin k) => s.graph.dist (v i) (v j)) ⁻¹'
        {D | D i j ∈ T} =
      (fun v : Fin k → ℕ => (v i, v j)) ⁻¹' {p : ℕ × ℕ | s.graph.dist p.1 p.2 ∈ T} := rfl
  rw [h1, ← Measure.map_apply ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    (MeasurableSet.of_discrete), pi_pair_map _ hij,
    Measure.prod_apply (MeasurableSet.of_discrete)]
  rfl

theorem sampleKernel_diag_apply {k : ℕ} (s : Forward.State) (i : Fin k) {T : Set ℕ}
    (hT : 0 ∉ T) : sampleKernel k s {D | D i i ∈ T} = 0 := by
  have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | D i i ∈ T} :=
    ((measurable_pi_apply i).comp (measurable_pi_apply i)) (MeasurableSet.of_discrete (s := T))
  rw [sampleKernel, Measure.map_apply (measurable_sampleMatrix k s) hmeas]
  have : (fun (v : Fin k → ℕ) (i j : Fin k) => s.graph.dist (v i) (v j)) ⁻¹'
      {D : Fin k → Fin k → ℕ | D i i ∈ T} = ∅ := by
    ext v
    simp [hT]
  rw [this, measure_empty]

theorem forwardPairKernel_event (s : Forward.State) (T : Set ℕ) :
    forwardPairKernel s {z | z.2.2 ∈ T} =
      ∫⁻ u, (Measure.uniformOfFinset s.vertices) {v | s.graph.dist u v ∈ T}
        ∂(Measure.uniformOfFinset s.vertices) := by
  unfold forwardPairKernel
  rw [Measure.bind_apply MeasurableSet.of_discrete
    (measurable_of_countable _).aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete]
  rfl

theorem sampleLaw_pair_apply (x : SignSequence) (n k : ℕ) {i j : Fin k} (hij : i ≠ j)
    (T : Set ℕ) :
    sampleLaw x n k {D | D i j ∈ T} = forwardPairDataLaw x n {z | z.2.2 ∈ T} := by
  have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | D i j ∈ T} :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)) (MeasurableSet.of_discrete (s := T))
  unfold sampleLaw forwardPairDataLaw
  rw [Measure.bind_apply hmeas measurable_from_top.aemeasurable,
    Measure.bind_apply MeasurableSet.of_discrete measurable_from_top.aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [Forward.treeLaw_valid x n] with s hs
  rw [sampleKernel_pair_apply ⟨0, hs.root_mem⟩ hij, forwardPairKernel_event]

theorem sampleLaw_diag_apply (x : SignSequence) (n k : ℕ) (i : Fin k) {T : Set ℕ}
    (hT : 0 ∉ T) : sampleLaw x n k {D | D i i ∈ T} = 0 := by
  have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | D i i ∈ T} :=
    ((measurable_pi_apply i).comp (measurable_pi_apply i)) (MeasurableSet.of_discrete (s := T))
  unfold sampleLaw
  rw [Measure.bind_apply hmeas measurable_from_top.aemeasurable]
  simp [sampleKernel_diag_apply _ i hT]

/-! ### Convergence of the rescaled distance matrix -/

/-- Union bound: the matrix deviation is controlled by the pair-distance deviation. -/
theorem sampleLaw_deviation_le (x : SignSequence) (n k : ℕ) {ε L α : ℝ} (hε : 0 < ε)
    (a : Fin k → Fin k → ℝ) (ha : ∀ i j : Fin k, i ≠ j → a i j = α)
    (hd : ∀ i : Fin k, a i i = 0) :
    sampleLaw x n k {D | ∃ i j, ε ≤ |(D i j : ℝ) / L - a i j|} ≤
      ∑ _p : Fin k × Fin k, forwardPairDataLaw x n {z | ε ≤ |(z.2.2 : ℝ) / L - α|} := by
  let T : Fin k × Fin k → Set ℕ := fun p => {d | ε ≤ |(d : ℝ) / L - a p.1 p.2|}
  calc sampleLaw x n k {D | ∃ i j, ε ≤ |(D i j : ℝ) / L - a i j|}
      ≤ sampleLaw x n k (⋃ p : Fin k × Fin k, {D | D p.1 p.2 ∈ T p}) := by
        apply measure_mono
        rintro D ⟨i, j, h⟩
        exact Set.mem_iUnion.2 ⟨(i, j), h⟩
    _ ≤ ∑ p : Fin k × Fin k, sampleLaw x n k {D | D p.1 p.2 ∈ T p} :=
        measure_iUnion_fintype_le _ _
    _ ≤ _ := by
        refine Finset.sum_le_sum fun p _ => ?_
        by_cases hp : p.1 = p.2
        · rcases p with ⟨i, j⟩
          dsimp only at hp
          subst hp
          have h0 : 0 ∉ T (i, i) := by
            simp only [T, Set.mem_ofPred_eq, Nat.cast_zero, zero_div, hd, sub_zero,
              abs_zero, not_le]
            exact hε
          rw [sampleLaw_diag_apply x n k i h0]
          exact zero_le
        · rw [sampleLaw_pair_apply x n k hp (T p)]
          have : T p = {d : ℕ | ε ≤ |(d : ℝ) / L - α|} := by
            simp only [T, ha _ _ hp]
          rw [this]
          rfl

/-- **Sampled distance matrices (linear regime).** Under the hypotheses of Theorem
`thm:lineaire`, for every number `k` of sampled vertices and every $\varepsilon>0$, the
probability that some entry of the rescaled distance matrix $D_{ij}/\ln n$ of `k`
independent uniform vertices of $T_n$ is at distance $\ge\varepsilon$ from the
entry of the star matrix $\frac{c+1}{c}\mathbf 1_{i\ne j}$ tends to zero. -/
theorem linear_sampled_distance_matrix_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => sampleLaw (x n) n k
      {D | ∃ i j, ε ≤ |(D i j : ℝ) / Real.log (n : ℝ) - starMatrix ((c + 1) / (2 * c)) k i j|})
      atTop (𝓝 0) := by
  have hpair := linear_uniform_distance_deviation_tendsto_zero x A hc hc1 hA hAinf hsmall hτ
    hnear hbulk hε
  have hsum : Tendsto (fun n : ℕ => ∑ _p : Fin k × Fin k, forwardPairDataLaw (x n) n
      {z | ε ≤ |(z.2.2 : ℝ) / Real.log (n : ℝ) - (c + 1) / c|}) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin k × Fin k)) (fun _ _ => hpair)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  refine sampleLaw_deviation_le (x n) n k hε _ (fun i j hij => ?_) (fun i => by simp [starMatrix])
  simp only [starMatrix, hij, ite_false]
  field_simp

end Freezing1.LinearBush
