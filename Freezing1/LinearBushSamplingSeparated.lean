module

public import Freezing1.LinearBushSamplingMatrix

/-!
# Separated samples in the linear regime

Fix $0<c\le1$ and a scale $r<\frac{c+1}{c}$. For every number `k` of sampled
vertices, with probability tending to one the `k` independent uniform vertices of
$T_n$ are pairwise at rescaled distance $>r$, i.e. at graph distance
$>r\ln n$. Consequently $T_n/\ln n$ has `k` points that are pairwise $r$-separated,
with probability tending to one (a state-level statement, `PackingAtLeast`).

* `SeparatedMatrix L r D` : all off-diagonal entries of `D / L` exceed `r`.
* `PackingAtLeast s L r k` : the state `s` has `k` vertices pairwise at graph
  distance $>rL$ (the packing number of `s` rescaled by `L` is at least `k`).
* `linear_separated_sample_tendsto_one` : $\mathbb P(\text{sample separated})\to1$.
* `linear_packingAtLeast_tendsto_one` : the same for the tree law, via the union
  bound of the sampled distance matrices.
-/

@[expose] public section

namespace Freezing1.LinearBush

open MeasureTheory ProbabilityTheory Filter CanonicalTree
open scoped Topology ENNReal Classical

/-- All off-diagonal entries of the matrix `D / L` exceed `r`. -/
def SeparatedMatrix (L r : ℝ) {k : ℕ} (D : Fin k → Fin k → ℕ) : Prop :=
  ∀ i j, i ≠ j → r < (D i j : ℝ) / L

/-- The state `s` contains `k` vertices which are pairwise at rescaled graph distance
`> r` (graph distance divided by `L`). -/
def PackingAtLeast (s : Forward.State) (L r : ℝ) (k : ℕ) : Prop :=
  ∃ v : Fin k → ℕ, (∀ i, v i ∈ s.vertices) ∧
    ∀ i j, i ≠ j → r < (s.graph.dist (v i) (v j) : ℝ) / L

theorem uniform_notMem_null (s : Forward.State) :
    (Measure.uniformOfFinset s.vertices) {u | u ∉ s.vertices} = 0 := by
  rw [Measure.uniformOfFinset_apply]
  simp

/-- A state without a separated family of `k` vertices never produces a separated sample. -/
theorem sampleKernel_separated_eq_zero {k : ℕ} {s : Forward.State} {L r : ℝ}
    (hnot : ¬ PackingAtLeast s L r k) :
    sampleKernel k s {D | SeparatedMatrix L r D} = 0 := by
  have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | SeparatedMatrix L r D} :=
    MeasurableSet.of_discrete
  unfold sampleKernel
  rw [Measure.map_apply (measurable_sampleMatrix k s) hmeas]
  refine measure_mono_null (t := ⋃ i : Fin k, (Function.eval i) ⁻¹' {u | u ∉ s.vertices}) ?_ ?_
  · intro v hv
    by_contra hnot'
    simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_ofPred_eq,
      not_exists, not_not] at hnot'
    exact hnot ⟨v, hnot', hv⟩
  · exact measure_iUnion_null fun i => Measure.pi_eval_preimage_null _ (uniform_notMem_null s)

/-- **Separated samples.** Under the hypotheses of Theorem `thm:lineaire`, for every `k`
and every $r<\frac{c+1}{c}$, the probability that `k` independent uniform vertices of
$T_n$ are pairwise at graph distance $>r\ln n$ tends to one. -/
theorem linear_separated_sample_tendsto_one
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    (k : ℕ) {r : ℝ} (hr : r < (c + 1) / c) :
    Tendsto (fun n : ℕ => sampleLaw (x n) n k
      {D | SeparatedMatrix (Real.log (n : ℝ)) r D}) atTop (𝓝 1) := by
  have hε : 0 < (c + 1) / c - r := sub_pos.mpr hr
  have hE := linear_sampled_distance_matrix_tendsto_zero x A hc hc1 hA hAinf hsmall hτ hnear hbulk
    k hε
  have hlow : Tendsto (fun n : ℕ => 1 - sampleLaw (x n) n k
      {D | ∃ i j, (c + 1) / c - r ≤
        |(D i j : ℝ) / Real.log (n : ℝ) - starMatrix ((c + 1) / (2 * c)) k i j|}) atTop (𝓝 1) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) hE (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · have := sampleLaw_probability (x n) n k
    set E : Set (Fin k → Fin k → ℕ) := {D | ∃ i j, (c + 1) / c - r ≤
        |(D i j : ℝ) / Real.log (n : ℝ) - starMatrix ((c + 1) / (2 * c)) k i j|} with hEdef
    have hsub : {D : Fin k → Fin k → ℕ | SeparatedMatrix (Real.log (n : ℝ)) r D}ᶜ ⊆ E := by
      intro D hD
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, SeparatedMatrix, not_forall,
        not_lt] at hD
      obtain ⟨i, j, hij, hle⟩ := hD
      refine ⟨i, j, ?_⟩
      have hs : starMatrix ((c + 1) / (2 * c)) k i j = (c + 1) / c := by
        simp only [starMatrix, hij, ite_false]
        field_simp
      rw [hs]
      have : (D i j : ℝ) / Real.log (n : ℝ) - (c + 1) / c ≤ -((c + 1) / c - r) := by linarith
      calc (c + 1) / c - r ≤ -((D i j : ℝ) / Real.log (n : ℝ) - (c + 1) / c) := by linarith
        _ ≤ _ := neg_le_abs _
    have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | SeparatedMatrix (Real.log (n : ℝ)) r D} :=
      MeasurableSet.of_discrete
    have h1 : sampleLaw (x n) n k
        {D : Fin k → Fin k → ℕ | SeparatedMatrix (Real.log (n : ℝ)) r D}ᶜ ≤
        sampleLaw (x n) n k E := measure_mono hsub
    have h2 := prob_compl_eq_one_sub (μ := sampleLaw (x n) n k) hmeas
    calc 1 - sampleLaw (x n) n k E ≤ 1 - sampleLaw (x n) n k
          {D : Fin k → Fin k → ℕ | SeparatedMatrix (Real.log (n : ℝ)) r D}ᶜ :=
        tsub_le_tsub_left h1 _
      _ = _ := by rw [h2, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]
  · have := sampleLaw_probability (x n) n k
    exact prob_le_one

/-- A separated sample forces a separated family of vertices of the tree. -/
theorem sampleLaw_separated_le_treeLaw (x : SignSequence) (n k : ℕ) (L r : ℝ) :
    sampleLaw x n k {D | SeparatedMatrix L r D} ≤
      Forward.treeLaw x n {s | PackingAtLeast s L r k} := by
  have hmeas : MeasurableSet {D : Fin k → Fin k → ℕ | SeparatedMatrix L r D} :=
    MeasurableSet.of_discrete
  have hpack : MeasurableSet {s : Forward.State | PackingAtLeast s L r k} :=
    MeasurableSet.of_discrete
  unfold sampleLaw
  rw [Measure.bind_apply hmeas measurable_from_top.aemeasurable,
    ← lintegral_indicator_one hpack]
  refine lintegral_mono_ae ?_
  filter_upwards [Forward.treeLaw_valid x n] with s hs
  by_cases h : PackingAtLeast s L r k
  · have := sampleKernel_probability (k := k) ⟨0, hs.root_mem⟩
    simp only [Set.indicator, Set.mem_ofPred_eq, h, ite_true, Pi.one_apply]
    exact prob_le_one
  · rw [sampleKernel_separated_eq_zero h]
    exact zero_le

/-- **Packing of the rescaled tree (state level).** Under the hypotheses of Theorem
`thm:lineaire`, for every `k` and every $r<\frac{c+1}{c}$, with probability tending to one
the forward tree $T_n$ contains `k` vertices pairwise at graph distance $>r\ln n$. -/
theorem linear_packingAtLeast_tendsto_one
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    (k : ℕ) {r : ℝ} (hr : r < (c + 1) / c) :
    Tendsto (fun n : ℕ => Forward.treeLaw (x n) n
      {s | PackingAtLeast s (Real.log (n : ℝ)) r k}) atTop (𝓝 1) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    (linear_separated_sample_tendsto_one x A hc hc1 hA hAinf hsmall hτ hnear hbulk k hr)
    tendsto_const_nhds (fun n => sampleLaw_separated_le_treeLaw (x n) n k _ _)
    (fun _ => prob_le_one)

end Freezing1.LinearBush
