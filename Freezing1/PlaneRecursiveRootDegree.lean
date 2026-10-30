module

public import Freezing1.ForwardDegreeLimits
public import Freezing1.ForwardPlaneLaw

/-!
# Root degree escapes in the genuine recursive plane tree

The all-attachment process is projected from the already verified forward
construction. Its root remains active, so the active-and-bounded-degree
estimate gives escape above every fixed degree threshold.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Topology Classical

theorem ValidAt.birthChildren_root {n : ℕ} {s : State} (hs : ValidAt n s) :
    birthChildren s 0 = s.vertices.filter (fun v => s.graph.Adj 0 v) := by
  ext v
  simp only [birthChildren, Finset.mem_filter]
  constructor
  · rintro ⟨hv, hv0, hp⟩
    exact ⟨hv, hp ▸ hs.parent_adj v hv hv0⟩
  · rintro ⟨hv, ha⟩
    have hv0 : v ≠ 0 := by intro he; subst v; exact s.graph.irrefl ha
    have hh : s.height v = 1 := by
      rw [hs.height_eq_dist v hv, s.graph.dist_eq_one_iff_adj.mpr ha]
    have hph : s.height (s.parent v) = 0 := by
      have := hs.height_parent v hv hv0
      omega
    have hp : s.parent v = 0 := by
      rw [hs.height_eq_dist _ (hs.parent_mem v hv)] at hph
      exact ((hs.reachable _ (hs.parent_mem v hv)).dist_eq_zero_iff.mp hph).symm
    exact ⟨hv, hv0, hp⟩

theorem ValidAt.toPlaneState_rootDegree {n : ℕ} {s : State} (hs : ValidAt n s) :
    PlaneForward.childCount s.toPlaneState [] = rootDegree s := by
  rw [← planeAddress_zero s, toPlaneState_childCount hs hs.root_mem,
    hs.birthChildren_root]
  rfl

theorem treeLaw_allAttachment_root_active (n : ℕ) :
    ∀ᵐ s ∂treeLaw (fun _ => true) n, 0 ∈ s.active := by
  apply treeLaw_ae_induction (fun _ => true) (fun _ s => 0 ∈ s.active)
  · simp [initial]
  · intro _ _ hs _; exact hs
  · intro k s hs v hv
    simp [step, hv, attach, hs]

theorem treeLaw_allAttachment_bounded_degree_tendsto_zero (d : ℕ) :
    Tendsto (fun n => (treeLaw (fun _ => true) n).real {s | rootDegree s ≤ d})
      atTop (𝓝 0) := by
  have ht : extinctionTime (fun _ => true) = ⊤ := by
    apply (extinctionTime_eq_top_iff _).mpr
    intro n
    simp only [activeCount, ↓reduceIte, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    omega
  have h := treeLaw_active_bounded_degree_tendsto_zero (fun _ => true) ht d
  apply h.congr
  intro n
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [treeLaw_allAttachment_root_active n] with s hs
  simp only [hs, true_and]

end Freezing1.Forward

namespace Freezing1.PlaneForward

open Filter MeasureTheory
open scoped Topology Classical

theorem allAttachment_bounded_root_children_tendsto_zero (d : ℕ) :
    Tendsto (fun k => ((fullLaw 1 initial).map (fun H => H k)).real
      {s | childCount s [] ≤ d}) atTop (𝓝 0) := by
  have h := Forward.treeLaw_allAttachment_bounded_degree_tendsto_zero d
  apply h.congr
  intro k
  rw [← ForwardAnnealed.map_treeLaw_toPlaneState, ForwardAnnealed.treeLaw_one_parameter]
  simp only [Measure.real]
  rw [Measure.map_apply Forward.measurable_toPlaneState (by trivial)]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [Forward.treeLaw_valid (fun _ => true) k] with s hs
  change (Forward.rootDegree s ≤ d) = (childCount s.toPlaneState [] ≤ d)
  rw [hs.toPlaneState_rootDegree]

end Freezing1.PlaneForward
