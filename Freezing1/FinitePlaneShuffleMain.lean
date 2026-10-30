module

public import Freezing1.FinitePlaneShuffleLaw
public import Freezing1.FinitePlaneShuffleUnordered
public import Freezing1.FinitePlaneConditionedUniform
public import Mathlib.Probability.Kernel.Defs

/-!
# The uniform plane reordering leaves the uniform law on finite plane trees invariant

`shuffleLaw T` is the law of the uniform random plane reordering of `T` as a measure on plane
trees; it is a Markov kernel. The uniform law on finite plane trees with `m` vertices is
invariant under it, and consequently (source Examples, second bullet, with the plane order chosen
uniformly at random) the iid-sign tree conditioned on the extinction time $2m-1$, reordered
uniformly at random, is a uniform plane tree with `m` vertices.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- The law of the uniform random plane reordering of a plane tree, as a measure on plane trees.
(On trees with infinitely many vertices this is the Dirac mass at the tree itself.) -/
noncomputable def shuffleLaw (T : Tree) : Measure Tree := (shufflePMF T).toMeasure

instance shuffleLaw_isProbabilityMeasure (T : Tree) : IsProbabilityMeasure (shuffleLaw T) :=
  inferInstanceAs (IsProbabilityMeasure (shufflePMF T).toMeasure)

theorem shuffleLaw_apply (T : Tree) {S : Set Tree} (hS : MeasurableSet S) :
    shuffleLaw T S = ∑' U, S.indicator (shufflePMF T) U :=
  PMF.toMeasure_apply _ hS

theorem shuffleLaw_of_not_finite {T : Tree} (hT : ¬FiniteVertices T) :
    shuffleLaw T = Measure.dirac T := by
  rw [shuffleLaw, shufflePMF_of_not_finite hT, PMF.toMeasure_pure]

/-- On a finite class the reordering law is the finite sum over the class. -/
theorem shuffleLaw_apply_class {m : ℕ} (T : FinitePlaneClass m) {S : Set Tree}
    (hS : MeasurableSet S) :
    shuffleLaw T.val S = ∑ U : FinitePlaneClass m, S.indicator (shufflePMF T.val) U.val := by
  rw [shuffleLaw_apply T.val hS]
  have hsupp : Function.support (fun U : Tree => S.indicator (shufflePMF T.val) U) ⊆
      {U : Tree | FiniteVertices U ∧ finiteVertexCount U = m} := by
    intro U hU
    have h2 : shufflePMF T.val U ≠ 0 := fun h => hU (by simp [Set.indicator_apply, h])
    obtain ⟨h3, h4⟩ := finiteVertices_of_shufflePMF T.property.1 h2
    exact ⟨h3, h4.trans T.property.2⟩
  calc ∑' U : Tree, S.indicator (shufflePMF T.val) U
      = ∑' U : {U : Tree // FiniteVertices U ∧ finiteVertexCount U = m},
          S.indicator (shufflePMF T.val) U.val :=
        (tsum_subtype_eq_of_support_subset (f := fun U : Tree => S.indicator (shufflePMF T.val) U)
          (s := {U : Tree | FiniteVertices U ∧ finiteVertexCount U = m}) hsupp).symm
    _ = ∑ U : FinitePlaneClass m, S.indicator (shufflePMF T.val) U.val := tsum_fintype _

/-- Reordering a tree of the class gives a tree of the class, almost surely. -/
theorem shuffleLaw_finitePlaneSet {m : ℕ} (T : FinitePlaneClass m) :
    shuffleLaw T.val (finitePlaneSet m) = 1 := by
  rw [shuffleLaw, (shufflePMF T.val).toMeasure_apply_eq_one_iff (measurableSet_finitePlaneSet m)]
  intro S hS
  obtain ⟨h1, h2⟩ := finiteVertices_of_shufflePMF T.property.1 hS
  exact ⟨h1, h2.trans T.property.2⟩

/-- A leaf has only one plane order. -/
theorem shufflePMF_leaf : shufflePMF leaf = PMF.pure leaf := by
  ext S
  by_cases hS : degree S = 0
  · rw [shufflePMF_apply_eq finiteVertices_leaf (d := 0) degree_leaf hS,
      eq_leaf_of_degree_zero hS]
    simp
  · rw [shufflePMF_apply_of_degree_ne finiteVertices_leaf (by simpa using hS)]
    have : S ≠ leaf := fun h => hS (by rw [h]; rfl)
    simp [PMF.pure_apply, this]

/-! ### Measurability: `shuffleLaw` is a Markov kernel -/

theorem countable_finiteVertices : {T : Tree | FiniteVertices T}.Countable := by
  have h : {T : Tree | FiniteVertices T} = ⋃ m : ℕ, finitePlaneSet m := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, finitePlaneSet]
    exact ⟨fun hT => ⟨_, hT, rfl⟩, fun ⟨_, hT, _⟩ => hT⟩
  rw [h]
  exact Set.countable_iUnion fun m => (finitePlaneSet_finite m).countable

theorem measurable_shuffleLaw : Measurable shuffleLaw := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  refine measurable_of_restrict_of_restrict_compl measurableSet_finiteVertices ?_ ?_
  · have : Countable {T : Tree | FiniteVertices T} := countable_finiteVertices.to_subtype
    exact measurable_of_countable _
  · have h : ({T : Tree | FiniteVertices T}ᶜ.domRestrict fun T => shuffleLaw T s) =
        fun T => s.indicator (fun _ => (1 : ℝ≥0∞)) T.val := by
      funext T
      have hT : ¬FiniteVertices T.val := T.property
      show shuffleLaw T.val s = s.indicator (fun _ => (1 : ℝ≥0∞)) T.val
      rw [shuffleLaw_of_not_finite hT, Measure.dirac_apply' _ hs]
      rfl
    rw [h]
    exact (measurable_const.indicator hs).comp measurable_subtype_coe

/-- The uniform random plane reordering as a Markov kernel on plane trees. -/
noncomputable def shuffleKernel : ProbabilityTheory.Kernel Tree Tree :=
  ⟨shuffleLaw, measurable_shuffleLaw⟩

/-! ### Invariance of the uniform law -/

/-- The uniform law on the finite plane trees with `m` vertices is invariant under the
uniform random plane reordering. -/
theorem finitePlaneUniform_bind_shuffleLaw (m : ℕ) :
    (finitePlaneUniform m).bind shuffleLaw = finitePlaneUniform m := by
  ext S hS
  rw [Measure.bind_apply hS measurable_shuffleLaw.aemeasurable, finitePlaneUniform_apply m hS]
  unfold finitePlaneUniform
  rw [lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]
  congr 1
  calc ∑ T : FinitePlaneClass m, shuffleLaw T.val S
      = ∑ T : FinitePlaneClass m, ∑ U : FinitePlaneClass m,
          S.indicator (shufflePMF T.val) U.val :=
        Finset.sum_congr rfl fun T _ => shuffleLaw_apply_class T hS
    _ = ∑ U : FinitePlaneClass m, ∑ T : FinitePlaneClass m,
          S.indicator (shufflePMF T.val) U.val := Finset.sum_comm
    _ = ∑ U : FinitePlaneClass m, (if U.val ∈ S then (1 : ℝ≥0∞) else 0) := by
        refine Finset.sum_congr rfl fun U _ => ?_
        by_cases hU : U.val ∈ S
        · simp only [Set.indicator_of_mem hU, hU, ↓reduceIte]
          exact sum_shuffleMatrix_column U
        · simp [hU]
    _ = ((Finset.univ.filter fun T : FinitePlaneClass m => T.val ∈ S).card : ℝ≥0∞) := by
        rw [Finset.sum_boole]

end Freezing1.PlaneTree

namespace Freezing1.ForwardAnnealed

open MeasureTheory ProbabilityTheory PlaneTree PlaneForward
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Source Examples, second bullet, with a uniformly random plane order. For the iid-sign
chronological plane tree (success probability `p ∈ (0,1)`, the symmetric case being `p = 1/2`),
conditionally on the first extinction time being `2m-1`, the terminal tree after an independent
uniform random reordering of the children of every vertex has the uniform law on all finite plane
trees with `m` vertices. -/
theorem iid_signs_conditioned_extinction_uniform_plane_shuffled (p : unitInterval)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw p PlaneForward.initial {H | ExtinctionTimeIs (2 * m - 1) H} ∧
      (((PlaneForward.fullLaw p PlaneForward.initial)[|{H | ExtinctionTimeIs (2 * m - 1) H}]).map
          PlaneForward.chainLimit).bind shuffleLaw = finitePlaneUniform m := by
  obtain ⟨hpos, hlaw⟩ := iid_signs_conditioned_extinction_uniform_plane p hp0 hp1 m hm
  refine ⟨hpos, ?_⟩
  rw [hlaw]
  exact finitePlaneUniform_bind_shuffleLaw m

end Freezing1.ForwardAnnealed
