module

public import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Packing numbers are uniformly bounded on compact subsets of the Gromov-Hausdorff space

For a metric space `X` and $r>0$, an *$r$-separated family* of `m` points is a map
`f : Fin m → X` with $d(f_i,f_j)>r$ for $i\ne j$. The packing number of `X` at
scale `r` is at most `M` when there is no $r$-separated family of more than `M`
points (`PackingNumberLE`).

The main result `exists_packingNumberLE_of_isCompact` is deterministic: for every
compact $K\subseteq$ `GHSpace` and every $r>0$ there is `M` such that **every**
compact metric space whose isometry class lies in `K` has packing number at most
`M` at scale `r`. The proof compares with a finite $r/4$-net of `K`: a space at
Gromov-Hausdorff distance $<r/4$ from a net element `q` sends an $r$-separated
family to an $r/2$-separated family in `q`, whose size is bounded by the number
of $r/4$-balls needed to cover the compact representative of `q`.
-/

@[expose] public section

namespace Freezing1.LinearBush

open GromovHausdorff Set Metric

universe u v

/-- `f` is an `r`-separated family: distinct indices are at distance `> r`. -/
def IsSeparatedFamily {X : Type u} [PseudoMetricSpace X] (r : ℝ) {m : ℕ} (f : Fin m → X) :
    Prop :=
  ∀ i j, i ≠ j → r < dist (f i) (f j)

/-- The packing number of `X` at scale `r` is at most `M`: no `r`-separated family has more
than `M` points. -/
def PackingNumberLE (X : Type u) [PseudoMetricSpace X] (r : ℝ) (M : ℕ) : Prop :=
  ∀ (m : ℕ) (f : Fin m → X), IsSeparatedFamily r f → m ≤ M

theorem exists_packingNumberLE_of_compactSpace (Y : Type v) [MetricSpace Y] [CompactSpace Y]
    {e : ℝ} (he : 0 < e) : ∃ N : ℕ, PackingNumberLE Y (2 * e) N := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact (isCompact_univ (X := Y)) he
  refine ⟨ht.toFinset.card, fun m f hf => ?_⟩
  have hex : ∀ i, ∃ y : ht.toFinset, f i ∈ ball (y : Y) e := by
    intro i
    have := hcov (mem_univ (f i))
    simp only [mem_iUnion] at this
    obtain ⟨y, hy, hfy⟩ := this
    exact ⟨⟨y, ht.mem_toFinset.mpr hy⟩, hfy⟩
  choose φ hφ using hex
  have hinj : Function.Injective φ := by
    intro i j hij
    by_contra hne
    have h1 := hφ i
    have h2 := hφ j
    rw [hij] at h1
    have := dist_triangle_right (f i) (f j) (φ j : Y)
    have h3 := mem_ball.mp h1
    have h4 := mem_ball.mp h2
    have h5 := hf i j hne
    linarith
  have := Fintype.card_le_of_injective φ hinj
  simpa using this

/-- An `r`-separated family in `X` transfers to a family in `Y` that is separated by
`r - 2δ`, when the Gromov-Hausdorff distance of `X` and `Y` is below `δ`. -/
theorem exists_separated_family_of_ghDist_lt {X : Type u} [MetricSpace X] [CompactSpace X]
    [Nonempty X] {Y : Type v} [MetricSpace Y] [CompactSpace Y] [Nonempty Y] {δ r : ℝ}
    (hd : ghDist X Y < δ) {m : ℕ} {f : Fin m → X} (hf : IsSeparatedFamily r f) :
    ∃ g : Fin m → Y, IsSeparatedFamily (r - 2 * δ) g := by
  obtain ⟨Φ, Ψ, hΦ, hΨ, hgh⟩ := ghDist_eq_hausdorffDist X Y
  have hfin : hausdorffEDist (range Φ) (range Ψ) ≠ ⊤ :=
    hausdorffEDist_ne_top_of_nonempty_of_bounded (range_nonempty _) (range_nonempty _)
      (isCompact_range hΦ.continuous).isBounded (isCompact_range hΨ.continuous).isBounded
  have hex : ∀ i, ∃ y : Y, dist (Φ (f i)) (Ψ y) < δ := by
    intro i
    obtain ⟨z, ⟨y, rfl⟩, hz⟩ := exists_dist_lt_of_hausdorffDist_lt (mem_range_self (f i))
      (hgh ▸ hd) hfin
    exact ⟨y, hz⟩
  choose g hg using hex
  refine ⟨g, fun i j hij => ?_⟩
  have h1 := hg i
  have h2 := hg j
  have h3 := hf i j hij
  rw [← hΦ.dist_eq] at h3
  rw [← hΨ.dist_eq]
  have := dist_triangle4 (Φ (f i)) (Ψ (g i)) (Ψ (g j)) (Φ (f j))
  rw [dist_comm (Ψ (g j)) (Φ (f j))] at this
  linarith

/-- **Uniform packing bound on compacts of `GHSpace`.** For every compact
$K\subseteq$ `GHSpace` and every $r>0$ there is `M` such that every nonempty compact
metric space whose Gromov-Hausdorff class lies in `K` has packing number at most `M`
at scale `r`. -/
theorem exists_packingNumberLE_of_isCompact {K : Set GHSpace} (hK : IsCompact K) {r : ℝ}
    (hr : 0 < r) :
    ∃ M : ℕ, ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X],
      toGHSpace X ∈ K → PackingNumberLE X r M := by
  obtain ⟨t, -, ht, hcov⟩ := finite_cover_balls_of_compact hK (show 0 < r / 4 by positivity)
  have hN : ∀ q : GHSpace, ∃ N : ℕ, PackingNumberLE q.Rep (2 * (r / 4)) N :=
    fun q => exists_packingNumberLE_of_compactSpace q.Rep (by positivity)
  choose N hN using hN
  refine ⟨ht.toFinset.sup N, fun X _ _ _ hX m f hf => ?_⟩
  have := hcov hX
  simp only [mem_iUnion] at this
  obtain ⟨q, hq, hXq⟩ := this
  have hdist : ghDist X q.Rep < r / 4 := by
    have : ghDist X q.Rep = dist (toGHSpace X) q := by
      rw [ghDist, q.toGHSpace_rep]
    rw [this]
    exact mem_ball.mp hXq
  obtain ⟨g, hg⟩ := exists_separated_family_of_ghDist_lt hdist hf
  have hg' : IsSeparatedFamily (2 * (r / 4)) g := by
    intro i j hij
    have := hg i j hij
    linarith
  exact (hN q m g hg').trans (Finset.le_sup (f := N) (ht.mem_toFinset.mpr hq))

end Freezing1.LinearBush
