module

public import Freezing1.PlaneTreeLocalTopology
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Complete finite-ball cylinders determine weak plane-tree convergence

The balls are the actual finite Ulam--Harris vertex sets. Their discrete
values give clopen cylinders, a neighbourhood basis, and a pi-system.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open Filter MeasureTheory Set
open scoped Topology Classical

abbrev Ball := Finset Address

instance : TopologicalSpace Ball := ⊥
instance : DiscreteTopology Ball := ⟨rfl⟩
instance : PolishSpace Ball := inferInstance
instance : MeasurableSpace Ball := borel Ball
instance : BorelSpace Ball := ⟨rfl⟩

theorem tendsto_ball {ι : Type*} {l : Filter ι} {S : ι → Tree} {T : Tree}
    (hS : Tendsto S l (𝓝 T)) (h : ℕ) :
    Tendsto (fun i => ball (S i) h) l (𝓝 (ball T h)) := by
  rw [nhds_discrete, tendsto_pure]
  exact (tendsto_iff_balls S T).mp hS h

theorem continuous_ball (h : ℕ) : Continuous (fun T : Tree => ball T h) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact tendsto_ball (S := id) (l := 𝓝 T) tendsto_id h

theorem measurable_ball (h : ℕ) : Measurable (fun T : Tree => ball T h) :=
  (continuous_ball h).measurable

def restrictBall (h : ℕ) (B : Ball) : Ball := B.filter (fun u => u.length ≤ h)

theorem restrictBall_ball {r q : ℕ} (hrq : r ≤ q) (T : Tree) :
    restrictBall r (ball T q) = ball T r := by
  ext u
  simp only [restrictBall, Finset.mem_filter, mem_ball]
  constructor
  · rintro ⟨⟨hu, _⟩, hlen⟩
    exact ⟨hu, hlen⟩
  · rintro ⟨hu, hlen⟩
    exact ⟨⟨hu, hlen.trans hrq⟩, hlen⟩

/-- A full radius-r Ulam--Harris ball is prescribed. -/
def cylinder (r : ℕ) (B : Ball) : Set Tree := {T | ball T r = B}

theorem cylinder_isClopen (r : ℕ) (B : Ball) : IsClopen (cylinder r B) :=
  (isClopen_discrete ({B} : Set Ball)).preimage (continuous_ball r)

theorem cylinder_lower_eq {r q : ℕ} (hrq : r ≤ q) {T U : Tree}
    (he : ball T q = ball U q) : ball T r = ball U r := by
  rw [← restrictBall_ball hrq T, ← restrictBall_ball hrq U, he]

theorem exists_cylinder_subset_of_isOpen {u : Set Tree} (hu : IsOpen u)
    {T : Tree} (hT : T ∈ u) :
    ∃ r, cylinder r (ball T r) ⊆ u := by
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

theorem mem_nhds_iff_exists_cylinder (T : Tree) (u : Set Tree) :
    u ∈ 𝓝 T ↔ ∃ r, cylinder r (ball T r) ⊆ u := by
  constructor
  · intro hu
    obtain ⟨v, hvu, hv, hTv⟩ := mem_nhds_iff.mp hu
    obtain ⟨r, hr⟩ := exists_cylinder_subset_of_isOpen hv hTv
    exact ⟨r, hr.trans hvu⟩
  · rintro ⟨r, hr⟩
    exact Filter.mem_of_superset ((cylinder_isClopen r (ball T r)).isOpen.mem_nhds rfl) hr

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
      change ball T r = B
      exact (cylinder_lower_eq hrq (hT.trans hUq.symm)).trans hUr
  · refine ⟨r, B, ?_⟩
    ext T
    constructor
    · exact fun h => h.1
    · intro hT
      refine ⟨hT, ?_⟩
      change ball T q = C
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
    exact ⟨cylinder r (ball T r), ⟨r, ball T r, rfl⟩,
      (cylinder_isClopen r (ball T r)).isOpen.mem_nhds rfl, hr⟩
  · rintro s ⟨r, B, rfl⟩
    exact h r B

end Freezing1.PlaneTree
