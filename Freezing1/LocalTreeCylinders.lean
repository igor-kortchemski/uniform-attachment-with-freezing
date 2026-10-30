module

public import Freezing1.ForwardLocalTree
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Local-ball cylinders determine weak convergence

The sets prescribing one complete radius ball are clopen. Coherence makes
their nonempty intersections single cylinders, and they form a neighborhood
basis. Consequently convergence of these actual cylinder probabilities is
sufficient for weak convergence on the local-tree space.
-/

@[expose] public section

namespace Freezing1.LocalTree

open Filter MeasureTheory Set
open scoped Topology Classical

/-- The full radius-r ball, including all of its labels, is prescribed. -/
def cylinder (r : ℕ) (B : Ball) : Set Tree := {T | T.val r = B}

theorem cylinder_isClopen (r : ℕ) (B : Ball) : IsClopen (cylinder r B) :=
  (isClopen_discrete ({B} : Set Ball)).preimage
    ((continuous_apply r).comp continuous_subtype_val)

theorem cylinder_lower_eq {r q : ℕ} (hrq : r ≤ q) {T U : Tree}
    (h : T.val q = U.val q) : T.val r = U.val r := by
  rw [← T.restrict_ball hrq, ← U.restrict_ball hrq, h]

theorem exists_cylinder_subset_of_isOpen {u : Set Tree} (hu : IsOpen u)
    {T : Tree} (hT : T ∈ u) :
    ∃ r, cylinder r (T.val r) ⊆ u := by
  by_contra hn
  simp only [not_exists, Set.not_subset] at hn
  choose U hU hnot using hn
  have hlim : Tendsto U atTop (𝓝 T) := by
    apply (tendsto_iff_balls _ _).mpr
    intro r
    filter_upwards [eventually_ge_atTop r] with n hn
    exact cylinder_lower_eq hn (hU n)
  obtain ⟨n, hn⟩ := (hlim.eventually (hu.mem_nhds hT)).exists
  exact hnot n hn

def cylinders : Set (Set Tree) := {s | ∃ r B, s = cylinder r B}

theorem cylinders_isPiSystem : IsPiSystem cylinders := by
  intro s hs t ht hst
  obtain ⟨r, B, rfl⟩ := hs
  obtain ⟨q, C, rfl⟩ := ht
  obtain ⟨U, hUr, hUq⟩ := hst
  rcases le_total r q with hrq | hqr
  · refine ⟨q, C, ?_⟩
    ext T
    constructor
    · exact fun h => h.2
    · intro hT
      refine ⟨?_, hT⟩
      change T.val r = B
      exact (cylinder_lower_eq hrq (hT.trans hUq.symm)).trans hUr
  · refine ⟨r, B, ?_⟩
    ext T
    constructor
    · exact fun h => h.1
    · intro hT
      refine ⟨hT, ?_⟩
      change T.val q = C
      exact (cylinder_lower_eq hqr (hT.trans hUr.symm)).trans hUq

theorem tendsto_probabilityMeasure_of_cylinders
    {μ : ℕ → ProbabilityMeasure Tree} {ν : ProbabilityMeasure Tree}
    (h : ∀ r B, Tendsto (fun n => μ n (cylinder r B)) atTop (𝓝 (ν (cylinder r B)))) :
    Tendsto μ atTop (𝓝 ν) := by
  apply cylinders_isPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨r, B, rfl⟩
    exact (cylinder_isClopen r B).isOpen.measurableSet
  · intro u hu T hT
    obtain ⟨r, hr⟩ := exists_cylinder_subset_of_isOpen hu hT
    exact ⟨cylinder r (T.val r), ⟨r, T.val r, rfl⟩,
      (cylinder_isClopen r (T.val r)).isOpen.mem_nhds rfl, hr⟩
  · rintro s ⟨r, B, rfl⟩
    exact h r B

end Freezing1.LocalTree
