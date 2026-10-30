module

public import Freezing1.CanonicalUniformSampling
public import Freezing1.CanonicalGraphDistance
public import Freezing1.RootedForestCoalescence
public import Freezing1.ReverseHistory

/-!
# Joint heights and distance of two uniform vertices

Both vertices are sampled independently conditional on the same actual tree.
Canonical coordinates preserve their entire triple of two heights and one
graph distance. The common-history law can therefore be used without changing
the dependence between these three observables or excluding the diagonal.
-/

@[expose] public section

namespace Freezing1.CanonicalTree

open MeasureTheory
open scoped Classical ENNReal

noncomputable def forwardPairKernel (s : Forward.State) : Measure (ℕ × ℕ × ℕ) :=
  (Measure.uniformOfFinset s.vertices).bind fun u =>
    (Measure.uniformOfFinset s.vertices).map fun v => (s.height u, s.height v, s.graph.dist u v)

noncomputable def reversePairKernel (F : Reverse.Forest) : Measure (ℕ × ℕ × ℕ) :=
  (Measure.uniformOfFinset F.vertices).bind fun u =>
    (Measure.uniformOfFinset F.vertices).map fun v => (F.depth u, F.depth v, F.graph.dist u v)

noncomputable def forwardPairDataLaw (x : SignSequence) (n : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  (Forward.treeLaw x n).bind forwardPairKernel

noncomputable def reversePairDataLaw (x : SignSequence) (n : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  (Reverse.treeLaw x n).bind reversePairKernel

theorem uniform_pair_coordinates {F : ReverseStamped.Forest}
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v)
    (hconn : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices, F.forest.graph.Reachable u v) :
    forwardPairKernel (reverseState F) = reversePairKernel F.forest := by
  have hae : ∀ᵐ u ∂Measure.uniformOfFinset F.forest.vertices, u ∈ F.forest.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  unfold forwardPairKernel reversePairKernel
  simp_rw [← uniform_reverse_coordinates hinj]
  rw [Measure.bind_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [hae] with u hu
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [hae] with v hv
  simp only [Function.comp_def, (reverseState_vertex_data hinj hu).2.1,
    (reverseState_vertex_data hinj hv).2.1,
    reverseState_graph_dist hinj hu hv (hconn u hu v hv)]

theorem reachable_of_one_root (F : Reverse.Forest) (hroot : F.roots.card = 1)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    F.graph.Reachable u v := by
  apply (F.root_eq_iff_reachable hu hv).mp
  exact (Finset.card_le_one.mp hroot.le) _ (F.root_mem_roots hu) _ (F.root_mem_roots hv)

/-- T05 transports the complete joint sample, not only its three marginals. -/
theorem forwardPairDataLaw_eq_reverse (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    forwardPairDataLaw x n = reversePairDataLaw x n := by
  unfold forwardPairDataLaw reversePairDataLaw
  rw [← reverseStateLaw_eq_forward_treeLaw x n hn, reverseStateLaw,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
    ← ReverseStamped.map_treeLaw x n,
    Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseStamped.treeLaw_canonical_ids x n hn,
    ReverseStamped.lawAfter_forest_valid x n n hn le_rfl] with F hF hvalid
  have hroot : F.forest.roots.card = 1 := by simpa using hvalid.roots_card
  exact uniform_pair_coordinates hF.1 (fun _ hu _ hv => reachable_of_one_root F.forest hroot hu hv)

/-- The same joint sample on the coherent reverse history, whose deterministic
terminal label set is sampled independently twice. -/
noncomputable def historyPairDataLaw (x : SignSequence) (n : ℕ) : Measure (ℕ × ℕ × ℕ) :=
  (ReverseHistory.fullLaw x n).bind fun H =>
    (uniformVertex x n).bind fun u => (uniformVertex x n).map fun v =>
      (H.current.depth u, H.current.depth v, H.current.graph.dist u v)

theorem reversePairDataLaw_eq_history (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    reversePairDataLaw x n = historyPairDataLaw x n := by
  have hm : (ReverseHistory.fullLaw x n).map ReverseHistory.History.current = Reverse.treeLaw x n :=
    ReverseHistory.map_lawAfter_current x n n
  unfold reversePairDataLaw historyPairDataLaw
  rw [← hm, Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [ReverseHistory.lawAfter_current_valid x n n hn le_rfl] with H hH
  have hv : H.current.vertices = vertexLabels x n := by
    simpa only [Nat.sub_self, Reverse.phaseLabels_zero] using hH.vertices_eq
  simp only [reversePairKernel, hv, uniformVertex]

theorem forwardPairDataLaw_eq_history (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) :
    forwardPairDataLaw x n = historyPairDataLaw x n :=
  (forwardPairDataLaw_eq_reverse x n hn).trans (reversePairDataLaw_eq_history x n hn)

end Freezing1.CanonicalTree
