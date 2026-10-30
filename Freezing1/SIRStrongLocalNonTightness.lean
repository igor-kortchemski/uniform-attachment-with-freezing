module

public import Freezing1.SIRTreeWordMixture
public import Freezing1.SIRFrozenBalls
public import Freezing1.PlaneRecursiveRootDegree
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.Order.Compact

/-!
# Strong-rate terminal infection trees are not locally tight

Every fixed early prefix approaches the genuine recursive tree. Attachments
only increase the root's child count, so terminal root degrees escape to
infinity in probability. Since degree is continuous in the local topology,
this prevents tightness of the actual embedded terminal tree laws.

The model here is the verified embedded SIR chain. Identification with a
continuous-time Poisson infection construction is a separate obligation.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory
open scoped Topology ENNReal NNReal Classical

theorem TreeState.Update.vertices_subset {z w : TreeState} (hu : z.Update w) :
    z.tree.vertices ⊆ w.tree.vertices := by
  rcases hu with rfl | ⟨sign, u, _, rfl⟩
  · exact Finset.Subset.refl _
  · exact treeStep_vertices_mono z sign u

theorem root_children_mono {s t : PlaneForward.State}
    (h : s.vertices ⊆ t.vertices) :
    PlaneForward.childCount s [] ≤ PlaneForward.childCount t [] := by
  apply Finset.card_le_card
  intro a ha
  exact Finset.mem_filter.mpr ⟨h (Finset.mem_filter.mp ha).1,
    (Finset.mem_filter.mp ha).2⟩

theorem root_children_mono_of_updates {H : ℕ → TreeState}
    (hu : ∀ k, (H k).Update (H (k + 1))) :
    Monotone (fun k => PlaneForward.childCount (H k).tree []) := by
  apply monotone_nat_of_le_succ
  intro k
  exact root_children_mono (hu k).vertices_subset

theorem terminal_bounded_degree_le_prefix (rate : ℝ≥0) (n k d : ℕ)
    (hk : k ≤ 2 * n + 1) :
    (embeddedTerminalTreeLaw rate n : Measure PlaneTree.Tree).real
      {T | PlaneTree.degree T ≤ d} ≤
    ((treeFullLaw rate n).map (fun H => (H k).tree)).real
      {s | PlaneForward.childCount s [] ≤ d} := by
  have hm : Measurable (fun H : ℕ → TreeState =>
      PlaneForward.shape (H (2 * n + 1)).tree) :=
    (measurable_of_countable (fun z : TreeState => PlaneForward.shape z.tree)).comp
      (measurable_pi_apply _)
  have hd : MeasurableSet {T : PlaneTree.Tree | PlaneTree.degree T ≤ d} :=
    PlaneTree.continuous_degree.measurable (measurableSet_Iic (a := d))
  have hm' : Measurable (fun H : ℕ → TreeState => (H k).tree) :=
    (measurable_of_countable (fun z : TreeState => z.tree)).comp (measurable_pi_apply k)
  change ((treeFullLaw rate n).map _).real _ ≤ _
  simp only [Measure.real]
  rw [Measure.map_apply hm hd, Measure.map_apply hm' (by trivial)]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [treeFullLaw_valid rate n, treeFullLaw_update rate n] with H hv hu hD
  have hm := root_children_mono_of_updates hu hk
  have hshape := (hv (2 * n + 1)).1.shape_offspring
  change PlaneTree.degree (PlaneForward.shape (H (2 * n + 1)).tree) ≤ d at hD
  change (PlaneForward.shape (H (2 * n + 1)).tree).val [] ≤ d at hD
  rw [hshape] at hD
  exact hm.trans hD

theorem terminal_bounded_degree_tendsto_zero (rate : ℕ → ℝ≥0)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) (d : ℕ) :
    Tendsto (fun n => (embeddedTerminalTreeLaw (rate n) n : Measure PlaneTree.Tree).real
      {T | PlaneTree.degree T ≤ d}) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun n => ha.trans_le measureReal_nonneg
  · intro ε hε
    have hr := PlaneForward.allAttachment_bounded_root_children_tendsto_zero d
    obtain ⟨k, hk⟩ := (hr.eventually (gt_mem_nhds (show 0 < ε / 2 by linarith))).exists
    have hc := treeFullLaw_plane_events_tendsto_strong rate hl k
      (show 0 < ε / 2 by linarith)
    filter_upwards [hc, eventually_ge_atTop k] with n hn hnk
    have hcmp := hn {s | PlaneForward.childCount s [] ≤ d}
    have hpre : ((treeFullLaw (rate n) n).map (fun H => (H k).tree)).real
        {s | PlaneForward.childCount s [] ≤ d} < ε := by
      have := (abs_lt.mp hcmp).2
      linarith
    exact (terminal_bounded_degree_le_prefix (rate n) n k d (by omega)).trans_lt hpre

end Freezing1.SIR

namespace Freezing1.PlaneTree

open Filter MeasureTheory
open scoped Topology ENNReal Classical

theorem not_tight_of_bounded_degree_tendsto_zero (μ : ℕ → ProbabilityMeasure Tree)
    (h : ∀ d : ℕ, Tendsto (fun n => (μ n : Measure Tree).real
      {T | degree T ≤ d}) atTop (𝓝 0)) :
    ¬IsTightMeasureSet (Set.range fun n => (μ n : Measure Tree)) := by
  intro ht
  obtain ⟨K, hK, hKμ⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp ht
      (1 / 2) (by norm_num)
  obtain ⟨d, hd⟩ := (hK.image continuous_degree).bddAbove
  obtain ⟨n, hn⟩ := ((h d).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))).exists
  have hcomp : (μ n : Measure Tree).real Kᶜ ≤ 1 / 2 := by
    have he := ENNReal.toReal_mono (show (1 / 2 : ℝ≥0∞) ≠ ⊤ by norm_num)
      (hKμ _ ⟨n, rfl⟩)
    norm_num at he
    exact he
  have hcover : (Set.univ : Set Tree) ⊆ {T | degree T ≤ d} ∪ Kᶜ := by
    intro T _
    by_cases hT : T ∈ K
    · exact Or.inl (hd ⟨T, hT, rfl⟩)
    · exact Or.inr hT
  have he := (measureReal_mono hcover (measure_ne_top (μ n : Measure Tree) _)).trans
    (measureReal_union_le _ _)
  simp only [Measure.real, measure_univ, ENNReal.toReal_one] at he
  simp only [Measure.real] at hn hcomp
  linarith

end Freezing1.PlaneTree

namespace Freezing1.SIR

open Filter MeasureTheory
open scoped NNReal

/-- T06.II for the genuine embedded infection-tree chain. -/
theorem embeddedTerminalTreeLaw_not_tight (rate : ℕ → ℝ≥0)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) :
    ¬IsTightMeasureSet (Set.range fun n =>
      (embeddedTerminalTreeLaw (rate n) n : Measure PlaneTree.Tree)) :=
  PlaneTree.not_tight_of_bounded_degree_tendsto_zero _
    (terminal_bounded_degree_tendsto_zero rate hl)

end Freezing1.SIR
