module

public import Freezing1.LinearBushSamplingSeparated
public import Freezing1.LinearBushGHPacking
public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Non-tightness of $T_n/\ln n$ in the Gromov-Hausdorff topology (linear regime)

The vertex set `ScaledVertices s L` of a connected forward state `s`, with the
metric $d(u,v)=d_{\mathrm{graph}}(u,v)/L$, is a finite (hence compact) metric
space; `scaledGH n s` is its class in Mathlib's `GromovHausdorff.GHSpace` for
$L=\ln n$ (a fixed junk value for states that are not connected or $n\le1$).

Since the Gromov-Hausdorff-Prokhorov distance dominates the Gromov-Hausdorff
distance, non-tightness in `GHSpace` implies non-tightness for the pointed
Gromov-Hausdorff-Prokhorov topology (forgetting the measure is continuous); only
the Gromov-Hausdorff statement is formalized here.

The statements below avoid any measurable structure on `GHSpace`: events are
sets of forward states (a discrete measurable space), e.g.
`{s | scaledGH n s ∈ K}` for a compact `K ⊆ GHSpace`.

* `linear_packingAtMost_tendsto_zero` : for every `M` and $r<\frac{c+1}{c}$, the
  probability that the packing number of $T_n/\ln n$ at scale `r` is at most `M`
  tends to zero.
* `linear_scaledGH_mem_isCompact_tendsto_zero` : for every compact `K`,
  $\mathbb P(T_n/\ln n\in K)\to0$.
* `linear_not_tight` : no compact set carries mass $\ge 1/2$ eventually.
-/

@[expose] public section

namespace Freezing1.LinearBush

open MeasureTheory ProbabilityTheory Filter CanonicalTree GromovHausdorff
open scoped Topology ENNReal Classical

/-- The star matrix of the long dendron $\Upsilon_{\delta_a}$ with $a=\frac{c+1}{2c}$ has
off-diagonal entries $\frac{c+1}{c}$. -/
theorem starMatrix_linear {c : ℝ} (hc : c ≠ 0) (k : ℕ) (i j : Fin k) :
    starMatrix ((c + 1) / (2 * c)) k i j = if i = j then 0 else (c + 1) / c := by
  simp only [starMatrix]
  split_ifs
  · rfl
  · field_simp

/-- A forward state is connected on its vertex set (it contains the root and every vertex is
reachable from it). Valid states are connected. -/
def IsConnectedState (s : Forward.State) : Prop :=
  0 ∈ s.vertices ∧ ∀ v ∈ s.vertices, s.graph.Reachable 0 v

theorem isConnectedState_of_validAt {n : ℕ} {s : Forward.State} (h : Forward.ValidAt n s) :
    IsConnectedState s :=
  ⟨h.root_mem, h.reachable⟩

/-- The vertex set of `s`, to be equipped with the metric `graph distance / L`. -/
def ScaledVertices (s : Forward.State) (_L : ℝ) : Type :=
  {v : ℕ // v ∈ s.vertices}

instance (s : Forward.State) (L : ℝ) : Fintype (ScaledVertices s L) :=
  inferInstanceAs (Fintype {v : ℕ // v ∈ s.vertices})

instance (s : Forward.State) (L : ℝ) [Fact (IsConnectedState s)] :
    Nonempty (ScaledVertices s L) :=
  ⟨⟨0, (Fact.out : IsConnectedState s).1⟩⟩

theorem scaledVertices_reachable {s : Forward.State} {L : ℝ} (hc : IsConnectedState s)
    (u v : ScaledVertices s L) : s.graph.Reachable u.1 v.1 :=
  (hc.2 u.1 u.2).symm.trans (hc.2 v.1 v.2)

/-- The rescaled tree $T/L$: vertices with distance $d_{\mathrm{graph}}/L$. -/
noncomputable instance instMetricSpaceScaledVertices (s : Forward.State) (L : ℝ)
    [hc : Fact (IsConnectedState s)] [hL : Fact (0 < L)] : MetricSpace (ScaledVertices s L) where
  dist u v := (s.graph.dist u.1 v.1 : ℝ) / L
  dist_self u := by simp
  dist_comm u v := by rw [SimpleGraph.dist_comm]
  dist_triangle u v w := by
    have h := (scaledVertices_reachable hc.out u v).dist_triangle_left w.1
    have h' : (s.graph.dist u.1 w.1 : ℝ) ≤ s.graph.dist u.1 v.1 + s.graph.dist v.1 w.1 := by
      exact_mod_cast h
    rw [← add_div]
    exact div_le_div_of_nonneg_right h' hL.out.le
  eq_of_dist_eq_zero {u v} h := by
    have h0 : (s.graph.dist u.1 v.1 : ℝ) = 0 := by
      have := hL.out.ne'
      simpa [this] using h
    have h1 : s.graph.dist u.1 v.1 = 0 := by exact_mod_cast h0
    exact Subtype.ext ((scaledVertices_reachable hc.out u v).dist_eq_zero_iff.mp h1)

theorem scaledVertices_dist {s : Forward.State} {L : ℝ} [Fact (IsConnectedState s)]
    [Fact (0 < L)] (u v : ScaledVertices s L) :
    dist u v = (s.graph.dist u.1 v.1 : ℝ) / L := rfl

/-- The Gromov-Hausdorff class of the rescaled tree $T/\ln n$ (a junk value if the state is not
connected or if $\ln n\le0$). -/
noncomputable def scaledGH (n : ℕ) (s : Forward.State) : GHSpace :=
  if h : IsConnectedState s ∧ 0 < Real.log (n : ℝ) then
    have : Fact (IsConnectedState s) := ⟨h.1⟩
    have : Fact (0 < Real.log (n : ℝ)) := ⟨h.2⟩
    toGHSpace (ScaledVertices s (Real.log (n : ℝ)))
  else default

/-- The packing number of `s` rescaled by `L` is at most `M` at scale `r`. -/
def PackingAtMost (s : Forward.State) (L r : ℝ) (M : ℕ) : Prop :=
  ¬ PackingAtLeast s L r (M + 1)

/-- Deterministic half: a connected state whose rescaled class lies in `K` has packing number at
most `M` at scale `r`, where `M` is the uniform bound for `K`. -/
theorem packingAtMost_of_scaledGH_mem {K : Set GHSpace} {r : ℝ} {M : ℕ}
    (hM : ∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X],
      toGHSpace X ∈ K → PackingNumberLE X r M)
    {n : ℕ} {s : Forward.State} (hs : IsConnectedState s) (hL : 0 < Real.log (n : ℝ))
    (hK : scaledGH n s ∈ K) : PackingAtMost s (Real.log (n : ℝ)) r M := by
  have hcond : IsConnectedState s ∧ 0 < Real.log (n : ℝ) := ⟨hs, hL⟩
  have : Fact (IsConnectedState s) := ⟨hs⟩
  have : Fact (0 < Real.log (n : ℝ)) := ⟨hL⟩
  rw [scaledGH, dite_eq_left_of_eq_true (eq_true hcond)] at hK
  rintro ⟨v, hv, hsep⟩
  let f : Fin (M + 1) → ScaledVertices s (Real.log (n : ℝ)) := fun i => ⟨v i, hv i⟩
  have hf : IsSeparatedFamily r f := fun i j hij => hsep i j hij
  exact absurd (hM (ScaledVertices s (Real.log (n : ℝ))) hK (M + 1) f hf) (by omega)

/-- **Packing numbers blow up.** Under the hypotheses of Theorem `thm:lineaire`, for every
$r<\frac{c+1}{c}$ and every `M`, the probability that the packing number of $T_n/\ln n$ at
scale `r` is at most `M` tends to zero. -/
theorem linear_packingAtMost_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {r : ℝ} (hr : r < (c + 1) / c) (M : ℕ) :
    Tendsto (fun n : ℕ => Forward.treeLaw (x n) n
      {s | PackingAtMost s (Real.log (n : ℝ)) r M}) atTop (𝓝 0) := by
  have h1 := linear_packingAtLeast_tendsto_one x A hc hc1 hA hAinf hsmall hτ hnear hbulk
    (M + 1) hr
  have h2 : Tendsto (fun n : ℕ => 1 - Forward.treeLaw (x n) n
      {s | PackingAtLeast s (Real.log (n : ℝ)) r (M + 1)}) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.sub (tendsto_const_nhds (x := (1 : ℝ≥0∞))) h1
      (Or.inl ENNReal.one_ne_top)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => zero_le) (fun n => le_of_eq ?_)
  have hmeas : MeasurableSet {s : Forward.State |
      PackingAtLeast s (Real.log (n : ℝ)) r (M + 1)} := MeasurableSet.of_discrete
  have := prob_compl_eq_one_sub (μ := Forward.treeLaw (x n) n) hmeas
  exact this

/-- **Non-tightness in the Gromov-Hausdorff space (event form).** Under the hypotheses of
Theorem `thm:lineaire`, for every compact `K ⊆ GHSpace`, the probability that the rescaled tree
$T_n/\ln n$ has Gromov-Hausdorff class in `K` tends to zero. -/
theorem linear_scaledGH_mem_isCompact_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {K : Set GHSpace} (hK : IsCompact K) :
    Tendsto (fun n : ℕ => Forward.treeLaw (x n) n {s | scaledGH n s ∈ K}) atTop (𝓝 0) := by
  have hr0 : 0 < (c + 1) / (2 * c) := by positivity
  have hr : (c + 1) / (2 * c) < (c + 1) / c := by
    have : (c + 1) / (2 * c) = ((c + 1) / c) / 2 := by field_simp
    have hpos : 0 < (c + 1) / c := by positivity
    rw [this]
    linarith
  obtain ⟨M, hM⟩ := exists_packingNumberLE_of_isCompact.{0} hK hr0
  have hlim := linear_packingAtMost_tendsto_zero x A hc hc1 hA hAinf hsmall hτ hnear hbulk hr M
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  refine measure_mono_ae ?_
  filter_upwards [Forward.treeLaw_valid (x n) n] with s hs hsK
  exact packingAtMost_of_scaledGH_mem hM (isConnectedState_of_validAt hs) hn hsK

/-- Every event of states whose rescaled class lies in a compact set has vanishing
probability: the sequence $T_n/\ln n$ escapes every compact subset of `GHSpace`. -/
theorem linear_event_in_compact_tendsto_zero
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    {K : Set GHSpace} (hK : IsCompact K) (E : ℕ → Set Forward.State)
    (hE : ∀ n, E n ⊆ {s | scaledGH n s ∈ K}) :
    Tendsto (fun n : ℕ => Forward.treeLaw (x n) n (E n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (linear_scaledGH_mem_isCompact_tendsto_zero x A hc hc1 hA hAinf hsmall hτ hnear hbulk hK)
    (fun _ => zero_le) (fun n => measure_mono (hE n))

/-- **Not tight.** No compact subset of `GHSpace` carries probability $\ge 1/2$ for all large
`n`; in particular the sequence of laws of $T_n/\ln n$ is not tight. -/
theorem linear_not_tight
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) :
    ¬ ∃ K : Set GHSpace, IsCompact K ∧
      ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ Forward.treeLaw (x n) n {s | scaledGH n s ∈ K} := by
  rintro ⟨K, hK, hev⟩
  have h0 := linear_scaledGH_mem_isCompact_tendsto_zero x A hc hc1 hA hAinf hsmall hτ hnear hbulk hK
  have hlt : ∀ᶠ n : ℕ in atTop, Forward.treeLaw (x n) n {s | scaledGH n s ∈ K} < 1 / 2 :=
    h0.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n, h1, h2⟩ := (hev.and hlt).exists
  exact absurd h2 (not_lt.mpr h1)

/-- **Not tight (law form).** The laws of $T_n/\ln n$ on `GHSpace` (with its Borel
σ-algebra) do not form a tight family: the measures are the push-forwards of the tree law
under `scaledGH n`. -/
theorem linear_not_isTightMeasureSet
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) :
    letI : MeasurableSpace GHSpace := borel GHSpace
    ¬ IsTightMeasureSet (Set.range fun n : ℕ => (Forward.treeLaw (x n) n).map (scaledGH n)) := by
  let _ : MeasurableSpace GHSpace := borel GHSpace
  have : BorelSpace GHSpace := ⟨rfl⟩
  intro htight
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  obtain ⟨K, hK, hle⟩ := htight (1 / 2) (by norm_num)
  refine linear_not_tight x A hc hc1 hA hAinf hsmall hτ hnear hbulk ⟨K, hK, Eventually.of_forall fun n => ?_⟩
  have h1 := hle _ ⟨n, rfl⟩
  have hmeasf : Measurable (scaledGH n) := measurable_from_top
  rw [Measure.map_apply hmeasf hK.isClosed.measurableSet.compl] at h1
  have hmeasK : MeasurableSet {s : Forward.State | scaledGH n s ∈ K} := MeasurableSet.of_discrete
  have h2 := prob_compl_eq_one_sub (μ := Forward.treeLaw (x n) n) hmeasK
  have h3 : scaledGH n ⁻¹' Kᶜ = {s : Forward.State | scaledGH n s ∈ K}ᶜ := by
    ext s; simp
  rw [h3, h2] at h1
  have hle1 : Forward.treeLaw (x n) n {s : Forward.State | scaledGH n s ∈ K} ≤ 1 := prob_le_one
  rw [one_div]
  calc (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
    _ ≤ 1 - (1 - Forward.treeLaw (x n) n {s : Forward.State | scaledGH n s ∈ K}) :=
        tsub_le_tsub_left (by simpa [one_div] using h1) _
    _ = _ := ENNReal.sub_sub_cancel ENNReal.one_ne_top hle1

end Freezing1.LinearBush
