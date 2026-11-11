# A06: sampled distance matrices and non-tightness of $T_n/\ln n$ (linear regime)

Source obligation A06, `attachement-uniforme-1-final.tex` line 357:

> $(T_n/\ln n)_n$ is not tight for the Gromov-Hausdorff-Prokhorov topology. However, for the
> topology considered in [ET21, Jan21], $T_n/\ln n$ converges to the long dendron $\Upsilon_\nu$
> (notation of [Jan21, Example 3.12]) with $\nu$ the Dirac mass at $(c+1)/(2c)$.

The setting is Theorem `thm:lineaire` (tex lines 316-340): $0<c\le1$, $A_n\to\infty$,
$A_n=o(\ln n)$, `NearOriginLimsup x A c`, `BulkLiminf x`, and survival $\tau>n$
(`hτ : ∀ n, (n : ℕ∞) < extinctionTime (x n)`). The proved input is T04.II,
`Freezing1.linear_uniform_distance_deviation_tendsto_zero` (file `Freezing1/MainLinearDistance.lean`):
for two conditionally independent uniform vertices of the same forward tree, $d/\ln n\to(c+1)/c$ in
probability, with law `CanonicalTree.forwardPairDataLaw (x n) n`.

Everything below lives in the new files (no existing file was edited):

| File | Content |
| --- | --- |
| `Freezing1/LinearBushSamplingMatrix.lean` | limit object, sampling kernel/law, part (A) |
| `Freezing1/LinearBushSamplingSeparated.lean` | separated samples, part (B2) |
| `Freezing1/LinearBushGHPacking.lean` | deterministic packing bound on compacts of `GHSpace`, part (B1) |
| `Freezing1/LinearBushGHTree.lean` | rescaled tree as a compact metric space, `scaledGH`, final non-tightness |
| `verification/A06Statements.lean`, `verification/a06-statements.log` | statement probe and its log |

All names are in the namespace `Freezing1.LinearBush`.

## 1. What "the cited topology" is, and what is formalized

* **[ET21, Jan21] topology.** Elek-Tardos and Janson consider convergence of trees (and of
  random trees) through *sampling*: a (random) tree converges when, for every $k$, the joint law of the
  $k\times k$ matrix of mutual distances between $k$ independent uniform points converges
  (Gromov-weak / distance-matrix topology for dendrons). The rescaling by $\ln n$ is
  applied to the metric before sampling. This is what part (A) formalizes: the *sampled distance
  matrix* of $T_n/\ln n$ converges, for every $k$, in probability (hence in distribution) to a
  deterministic matrix.
* **Limit object, dictionary entry (not formalized dendron theory).** For the long dendron
  $\Upsilon_\nu$ we use the sampled matrix of $k$ independent points: their heights are i.i.d. with
  law $\nu$, distinct points branch at the root, so
  $D_{ij}=h_i+h_j$ for $i\ne j$ and $D_{ii}=0$ (`longDendronMatrix`). For
  $\nu=\delta_a$ all heights equal $a$ and the matrix is the *star matrix*
  $2a(\mathbf 1_{i\ne j})$ (`starMatrix a k`); `longDendronSampleLaw_dirac` proves that the sampled
  matrix law of $\Upsilon_{\delta_a}$ (iid heights `ν = δ_a`) is the Dirac mass at `starMatrix a k`.
  With $a=(c+1)/(2c)$ the off-diagonal entries are $(c+1)/c$ (`starMatrix_linear`).
  **Caveat.** The identification "sampled matrix of $\Upsilon_{\delta_a}$ equals
  `starMatrix a k`" is a *dictionary entry*: it is not derived from a formalized definition of
  dendrons and I did not have the text of [Jan21, Example 3.12] at hand. It is the reading forced by
  the paper's own parametrization: in Theorem `thm:lineaire` (II) the rescaled height of a uniform
  vertex tends to $(c+1)/(2c)=a$ and the distance of two uniform vertices to $2a$, so in the
  limit object two independent points are at distance $2a$. No claim of Lean-level convergence "to the
  dendron $\Upsilon_\nu$ in Janson's topology" is made; only convergence of every sampled distance
  matrix to `starMatrix a k` is.
* **Gromov-Hausdorff-Prokhorov (GHP).** Not formalized. Part (B) proves non-tightness in the
  Gromov-Hausdorff topology (Mathlib's `GromovHausdorff.GHSpace`). Non-tightness in GHP follows from it
  on paper: the map forgetting the measure (and the root, if pointed) is $1$-Lipschitz from GHP to
  GH, since $d_{GH}\le d_{GHP}$ on the underlying spaces; a compact $K'$ of the GHP space carrying mass
  $\ge 1/2$ eventually would have a compact image $K$ in `GHSpace` with the same property,
  contradicting `linear_not_tight`. This continuity argument is a remark, not a Lean theorem.

## 2. Exact exported statements

Common hypotheses (copied from `linear_uniform_distance_deviation_tendsto_zero`):
`(x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
(hAinf : Tendsto A atTop atTop) (hsmall : Tendsto (fun n => A n / Real.log n) atTop (𝓝 0))
(hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n)) (hnear : NearOriginLimsup x A c)
(hbulk : BulkLiminf x)` ("(H)" below).

### Part (A), `LinearBushSamplingMatrix.lean`

```lean
noncomputable def sampleKernel (k : ℕ) (s : Forward.State) : Measure (Fin k → Fin k → ℕ) :=
  (Measure.pi fun _ : Fin k => Measure.uniformOfFinset s.vertices).map
    (fun v i j => s.graph.dist (v i) (v j))
noncomputable def sampleLaw (x : SignSequence) (n k : ℕ) : Measure (Fin k → Fin k → ℕ) :=
  (Forward.treeLaw x n).bind (sampleKernel k)
def starMatrix (a : ℝ) (k : ℕ) : Fin k → Fin k → ℝ := fun i j => if i = j then 0 else 2 * a

theorem linear_sampled_distance_matrix_tendsto_zero (H) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => sampleLaw (x n) n k
      {D | ∃ i j, ε ≤ |(D i j : ℝ) / Real.log (n : ℝ) -
        starMatrix ((c + 1) / (2 * c)) k i j|}) atTop (𝓝 0)
```

The event is exactly $\max_{i,j}|D_{ij}/\ln n-\tfrac{c+1}{c}\mathbf 1_{i\ne j}|\ge\varepsilon$. Proof: the
diagonal is identically zero ($\mathbb P(D_{ii}\neq0)=0$, `sampleKernel_diag_apply`); for $i\ne j$
the law of $(V_i,V_j)$ under `Measure.pi` is the product of two uniform laws
(`pi_pair_map`, via `iIndepFun_pi` and `measurePreserving_eval`), hence the event for $D_{ij}$ has
exactly the probability of the same event under `forwardPairDataLaw`
(`sampleLaw_pair_apply`, which includes the coincidence $V_i=V_j$); union bound over the $k^2$
pairs (`sampleLaw_deviation_le`) and `linear_uniform_distance_deviation_tendsto_zero`.
Supporting: `instIsFiniteMeasureUniformOfFinset` (new instance: uniform measures on finsets are finite,
needed for `Measure.pi`), `sampleKernel_probability`, `sampleLaw_probability`,
`longDendronMatrix`, `longDendronSampleLaw`, `longDendronSampleLaw_dirac`.
A version with the supremum norm of the matrix on `Fin k → Fin k → ℝ` was not included (the
ambient instance diamond `Pi.normedRing` / `Pi.seminormedGroup` made the statement time out); the
`∃ i j` form is the literal max-entry statement.

### Part (B2), `LinearBushSamplingSeparated.lean`

```lean
def SeparatedMatrix (L r : ℝ) {k : ℕ} (D : Fin k → Fin k → ℕ) : Prop :=
  ∀ i j, i ≠ j → r < (D i j : ℝ) / L
def PackingAtLeast (s : Forward.State) (L r : ℝ) (k : ℕ) : Prop :=
  ∃ v : Fin k → ℕ, (∀ i, v i ∈ s.vertices) ∧ ∀ i j, i ≠ j → r < (s.graph.dist (v i) (v j) : ℝ) / L

theorem linear_separated_sample_tendsto_one (H) (k : ℕ) {r : ℝ} (hr : r < (c + 1) / c) :
    Tendsto (fun n => sampleLaw (x n) n k {D | SeparatedMatrix (Real.log n) r D}) atTop (𝓝 1)
theorem linear_packingAtLeast_tendsto_one (H) (k : ℕ) {r : ℝ} (hr : r < (c + 1) / c) :
    Tendsto (fun n => Forward.treeLaw (x n) n {s | PackingAtLeast s (Real.log n) r k}) atTop (𝓝 1)
```

Proof: the complement of the separated event is contained in the part-(A) event with
$\varepsilon=(c+1)/c-r$, so its probability tends to $0$ and the law is a probability measure;
a state without $k$ pairwise-separated vertices gives probability $0$ to a separated sample
(`sampleKernel_separated_eq_zero`, using `Measure.pi_eval_preimage_null`: the sampled vertices lie
a.s. in `s.vertices`), whence `sampleLaw_separated_le_treeLaw`. The scale $r$ may be any real
$<(c+1)/c$ (in particular $r=(c+1)/(2c)$); only $r>0$ is meaningful for packing.

### Part (B1), `LinearBushGHPacking.lean` (pure Mathlib, no project import)

```lean
def IsSeparatedFamily {X : Type u} [PseudoMetricSpace X] (r : ℝ) {m : ℕ} (f : Fin m → X) : Prop :=
  ∀ i j, i ≠ j → r < dist (f i) (f j)
def PackingNumberLE (X : Type u) [PseudoMetricSpace X] (r : ℝ) (M : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → X), IsSeparatedFamily r f → m ≤ M

theorem exists_packingNumberLE_of_isCompact {K : Set GHSpace} (hK : IsCompact K) {r : ℝ}
    (hr : 0 < r) :
    ∃ M : ℕ, ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X],
      toGHSpace X ∈ K → PackingNumberLE X r M
```

Proof: finite $r/4$-net of $K$ (`finite_cover_balls_of_compact`); for $X$ with class within
$r/4$ of a net point $q$, `ghDist_eq_hausdorffDist` gives isometric embeddings of $X$ and `q.Rep`
into $\ell^\infty$ at Hausdorff distance $<r/4$, so an $r$-separated family of $X$ yields an
$r/2$-separated family in `q.Rep` (`exists_separated_family_of_ghDist_lt`), of cardinality at most the number of
$r/4$-balls covering the compact `q.Rep` (`exists_packingNumberLE_of_compactSpace`). $M$ is the maximum over the net.

### Part (B), `LinearBushGHTree.lean`

```lean
def ScaledVertices (s : Forward.State) (L : ℝ) : Type := {v : ℕ // v ∈ s.vertices}
-- for [Fact (IsConnectedState s)] [Fact (0 < L)]: MetricSpace with dist u v = graph.dist u.1 v.1 / L,
-- Fintype, hence CompactSpace; Nonempty (root).
noncomputable def scaledGH (n : ℕ) (s : Forward.State) : GHSpace   -- toGHSpace (ScaledVertices s (log n)),
                                                                   -- junk value if not connected or log n ≤ 0
def PackingAtMost (s : Forward.State) (L r : ℝ) (M : ℕ) : Prop := ¬ PackingAtLeast s L r (M + 1)

theorem linear_packingAtMost_tendsto_zero (H) {r : ℝ} (hr : r < (c + 1) / c) (M : ℕ) :
    Tendsto (fun n => Forward.treeLaw (x n) n {s | PackingAtMost s (Real.log n) r M}) atTop (𝓝 0)
theorem linear_scaledGH_mem_isCompact_tendsto_zero (H) {K : Set GHSpace} (hK : IsCompact K) :
    Tendsto (fun n => Forward.treeLaw (x n) n {s | scaledGH n s ∈ K}) atTop (𝓝 0)
theorem linear_event_in_compact_tendsto_zero (H) {K : Set GHSpace} (hK : IsCompact K)
    (E : ℕ → Set Forward.State) (hE : ∀ n, E n ⊆ {s | scaledGH n s ∈ K}) :
    Tendsto (fun n => Forward.treeLaw (x n) n (E n)) atTop (𝓝 0)
theorem linear_not_tight (H) :
    ¬ ∃ K : Set GHSpace, IsCompact K ∧
      ∀ᶠ n in atTop, 1 / 2 ≤ Forward.treeLaw (x n) n {s | scaledGH n s ∈ K}
theorem linear_not_isTightMeasureSet (H) :   -- Borel σ-algebra on GHSpace
    letI : MeasurableSpace GHSpace := borel GHSpace
    ¬ IsTightMeasureSet (Set.range fun n : ℕ => (Forward.treeLaw (x n) n).map (scaledGH n))
```

`Forward.State` carries the discrete σ-algebra (`MeasurableSpace State := ⊤`), so every event
of states is measurable and no measurable structure on `GHSpace` is needed in the first four
statements. The metric on `ScaledVertices` uses the ambient `s.graph.dist`; the triangle inequality
comes from `Reachable.dist_triangle_left` and reachability from the root in connected states
(`ValidAt.reachable`, via `isConnectedState_of_validAt`). The chain: deterministic
`packingAtMost_of_scaledGH_mem` (connected state, $\ln n>0$, class in $K$ implies `PackingAtMost s (log n) r M`
for the $M$ of B1 with $r=(c+1)/(2c)$) plus `linear_packingAtMost_tendsto_zero`.

## 3. Evidence

Direct checks (`lake env lean -DautoImplicit=false Freezing1/File.lean`, run from the repository root),
all with exit status 0 and empty output (no warnings, no `sorry`):

| File | direct check | lines |
| --- | --- | --- |
| `Freezing1/LinearBushSamplingMatrix.lean` | exit 0 | 265 |
| `Freezing1/LinearBushSamplingSeparated.lean` | exit 0 | 150 |
| `Freezing1/LinearBushGHPacking.lean` | exit 0 | 119 |
| `Freezing1/LinearBushGHTree.lean` | exit 0 | 247 |
| `verification/A06Statements.lean` | exit 0, log in `verification/a06-statements.log` | 165 |

Artifacts of the four new modules were built only through the serialized builder
(`bl.sh Freezing1.LinearBushSamplingMatrix`, then `...SamplingSeparated` together with `...GHPacking`,
then `...GHTree`); all builds ended with `Build completed successfully`. `#print axioms` of every export
(`linear_sampled_distance_matrix_tendsto_zero`, `longDendronSampleLaw_dirac`,
`linear_separated_sample_tendsto_one`, `linear_packingAtLeast_tendsto_one`,
`exists_packingNumberLE_of_isCompact`, `packingAtMost_of_scaledGH_mem`,
`linear_packingAtMost_tendsto_zero`, `linear_scaledGH_mem_isCompact_tendsto_zero`,
`linear_event_in_compact_tendsto_zero`, `linear_not_tight`, `linear_not_isTightMeasureSet`,
`starMatrix_linear`, `sampleLaw_probability`) reports exactly `propext`, `Classical.choice`,
`Quot.sound`. The probe `verification/A06Statements.lean` restates each headline theorem with the
measure expanded (`(Forward.treeLaw (x n) n).bind fun s => (Measure.pi ...).map ...`) and the
hypotheses `hnear`, `hbulk` unfolded as in `verification/MainLinearDistanceStatement.lean`; the
star-matrix entries are rewritten to `if i = j then 0 else (c + 1) / c` via `starMatrix_linear`.

## 4. Not covered / caveats

* GHP is not formalized; only GH. The deduction GHP-non-tight from GH-non-tight is the
  one-line continuity remark in section 1.
* Convergence of $T_n/\ln n$ "to $\Upsilon_\nu$" is formalized only as convergence in probability
  of every sampled distance matrix to the deterministic star matrix; the dictionary entry
  "star matrix $=$ sampled matrix of $\Upsilon_{\delta_a}$" is an identification with Janson's Example 3.12,
  not a derivation from a formal definition of dendrons or of Janson's topology. Convergence in
  probability to a constant implies convergence in distribution, so the sampling convergence
  required by the distance-matrix topology follows; this implication is standard and not restated in Lean.
* Part (A) concerns the unordered/sampled matrices of the *forward* tree `Forward.treeLaw`
  (the object the T04 distance theorem is about), with independent vertices drawn conditionally on
  the same tree, including repetitions.
* The paper's "for $n\ge1$" is replaced by asymptotics in $n$; for $n\le1$ the rescaling
  $\ln n$ vanishes and `scaledGH` returns a junk value, which does not affect any limit statement.
* Hypotheses are exactly those of T04.II (no extra assumption); in particular $r$ in the
  packing statements can be any real below $(c+1)/c$ (the scale $(c+1)/(2c)$ is used internally for compacts).
