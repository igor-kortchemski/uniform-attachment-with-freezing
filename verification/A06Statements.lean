module

public import Freezing1.LinearBushGHTree

/-!
Probe for source obligation A06 (tex line 357): sampled distance matrices (the
distance-matrix / Gromov-weak topology used for dendrons) converge to the star matrix of the
long dendron $\Upsilon_{\delta_{(c+1)/(2c)}}$, and $T_n/\ln n$ is not tight for the
Gromov-Hausdorff topology (hence not for Gromov-Hausdorff-Prokhorov).

The sampled matrices are expanded into the actual forward tree law, followed by `k`
independent uniform vertices conditional on that same tree (`Measure.pi`). Events on
`GHSpace` are phrased through sets of forward states, so no measurable structure on
`GHSpace` is needed.
-/

open MeasureTheory Filter GromovHausdorff
open scoped Topology Classical

namespace Freezing1.StatementAudit

/-- (A) Sampled distance matrices. -/
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((Forward.treeLaw (x n) n).bind fun s =>
        (Measure.pi fun _ : Fin k => Measure.uniformOfFinset s.vertices).map
          (fun v i j => s.graph.dist (v i) (v j)))
      {D | ∃ i j, ε ≤ |(D i j : ℝ) / Real.log (n : ℝ) -
        (if i = j then 0 else (c + 1) / c)|}) atTop (𝓝 0) := by
  have h := LinearBush.linear_sampled_distance_matrix_tendsto_zero x A hcpos hcle hApos hAinf
    hAsmall hsurvive hnear hbulk k hε
  simp only [LinearBush.starMatrix_linear hcpos.ne'] at h
  exact h

/-- (A) The limit object: the sampled matrix law of the long dendron with `ν = δ_a`. -/
example (a : ℝ) (k : ℕ) :
    (Measure.pi fun _ : Fin k => (Measure.dirac a : Measure ℝ)).map
      (fun h : Fin k → ℝ => fun i j : Fin k => if i = j then (0 : ℝ) else h i + h j) =
    Measure.dirac (fun i j : Fin k => if i = j then (0 : ℝ) else 2 * a) :=
  LinearBush.longDendronSampleLaw_dirac a k

/-- (B2) `k` sampled vertices are pairwise `r ln n`-separated with probability → 1. -/
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    (k : ℕ) (r : ℝ) (hr : r < (c + 1) / c) :
    Tendsto (fun n : ℕ =>
      ((Forward.treeLaw (x n) n).bind fun s =>
        (Measure.pi fun _ : Fin k => Measure.uniformOfFinset s.vertices).map
          (fun v i j => s.graph.dist (v i) (v j)))
      {D | ∀ i j, i ≠ j → r < (D i j : ℝ) / Real.log (n : ℝ)}) atTop (𝓝 1) :=
  LinearBush.linear_separated_sample_tendsto_one x A hcpos hcle hApos hAinf hAsmall hsurvive
    hnear hbulk k hr

/-- (B2) The tree has `k` pairwise `r ln n`-separated vertices with probability → 1. -/
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    (k : ℕ) (r : ℝ) (hr : r < (c + 1) / c) :
    Tendsto (fun n : ℕ => Forward.treeLaw (x n) n
      {s | ∃ v : Fin k → ℕ, (∀ i, v i ∈ s.vertices) ∧
        ∀ i j, i ≠ j → r < (s.graph.dist (v i) (v j) : ℝ) / Real.log (n : ℝ)})
      atTop (𝓝 1) :=
  LinearBush.linear_packingAtLeast_tendsto_one x A hcpos hcle hApos hAinf hAsmall hsurvive
    hnear hbulk k hr

/-- (B1) Deterministic: uniformly bounded packing numbers on compacts of `GHSpace`. -/
example {K : Set GHSpace} (hK : IsCompact K) (r : ℝ) (hr : 0 < r) :
    ∃ M : ℕ, ∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X],
      toGHSpace X ∈ K → ∀ (m : ℕ) (f : Fin m → X),
        (∀ i j, i ≠ j → r < dist (f i) (f j)) → m ≤ M :=
  LinearBush.exists_packingNumberLE_of_isCompact hK hr

/-- (B) Non-tightness: every compact subset of `GHSpace` has asymptotically zero probability. -/
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop)
    {K : Set GHSpace} (hK : IsCompact K) :
    Tendsto (fun n : ℕ => Forward.treeLaw (x n) n
      {s | LinearBush.scaledGH n s ∈ K}) atTop (𝓝 0) :=
  LinearBush.linear_scaledGH_mem_isCompact_tendsto_zero x A hcpos hcle hApos hAinf hAsmall
    hsurvive hnear hbulk hK

/-- The rescaled tree is the actual compact metric space: vertex set of the state with
distance `graph.dist / ln n`. -/
example (s : Forward.State) (L : ℝ) [Fact (LinearBush.IsConnectedState s)] [Fact (0 < L)]
    (u v : LinearBush.ScaledVertices s L) : dist u v = (s.graph.dist u.1 v.1 : ℝ) / L := rfl

/-- (B) Non-tightness, conclusion form: no compact set carries mass `≥ 1/2` eventually. -/
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop) :
    ¬ ∃ K : Set GHSpace, IsCompact K ∧
      ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ Forward.treeLaw (x n) n {s | LinearBush.scaledGH n s ∈ K} :=
  LinearBush.linear_not_tight x A hcpos hcle hApos hAinf hAsmall hsurvive hnear hbulk

/-- (B) Non-tightness of the laws on `GHSpace` with the Borel σ-algebra. -/
example (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ)
    (hcpos : 0 < c) (hcle : c ≤ 1) (hApos : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hAsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hsurvive : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : Tendsto
      (fun ε : ℝ => limsup (fun n => nearOriginMaximum x A c ε n) atTop)
      (𝓝[>] 0) (𝓝 0))
    (hbulk : ∀ ε : ℝ, 0 < ε → ε < 1 →
      0 < liminf (fun n => bulkMinimum x ε n) atTop) :
    letI : MeasurableSpace GHSpace := borel GHSpace
    ¬ IsTightMeasureSet
      (Set.range fun n : ℕ => (Forward.treeLaw (x n) n).map (LinearBush.scaledGH n)) :=
  LinearBush.linear_not_isTightMeasureSet x A hcpos hcle hApos hAinf hAsmall hsurvive hnear hbulk

end Freezing1.StatementAudit

#print axioms Freezing1.LinearBush.linear_sampled_distance_matrix_tendsto_zero
#print axioms Freezing1.LinearBush.longDendronSampleLaw_dirac
#print axioms Freezing1.LinearBush.linear_separated_sample_tendsto_one
#print axioms Freezing1.LinearBush.linear_packingAtLeast_tendsto_one
#print axioms Freezing1.LinearBush.exists_packingNumberLE_of_isCompact
#print axioms Freezing1.LinearBush.packingAtMost_of_scaledGH_mem
#print axioms Freezing1.LinearBush.linear_packingAtMost_tendsto_zero
#print axioms Freezing1.LinearBush.linear_scaledGH_mem_isCompact_tendsto_zero
#print axioms Freezing1.LinearBush.linear_event_in_compact_tendsto_zero
#print axioms Freezing1.LinearBush.linear_not_tight
#print axioms Freezing1.LinearBush.linear_not_isTightMeasureSet
#print axioms Freezing1.LinearBush.starMatrix_linear
#print axioms Freezing1.LinearBush.sampleLaw_probability
