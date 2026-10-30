module

import Freezing1.FinitePlaneShuffleMain

open MeasureTheory ProbabilityTheory
open Freezing1
open scoped Classical ENNReal

noncomputable section

/-! Authored exact-type restatement for the A03 uniform plane-reordering step
(source lines 271-274, second bullet: "when the plane order ... is chosen uniformly at random"). -/

-- The source's symmetric success probability, as an element of the unit interval.
def halfP : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

private theorem halfP_pos : 0 < (halfP : ℝ) := by simp [halfP]
private theorem halfP_lt : (halfP : ℝ) < 1 := by simp [halfP]; norm_num

/-! ### The definition: independent uniform permutation of the children at every vertex -/

-- The random reordering of a plane tree, as a PMF, as a measure, and as a Markov kernel.
example : PlaneTree.Tree → PMF PlaneTree.Tree := PlaneTree.shufflePMF
example : PlaneTree.Tree → Measure PlaneTree.Tree := PlaneTree.shuffleLaw
example : Measurable PlaneTree.shuffleLaw := PlaneTree.measurable_shuffleLaw
example : Kernel PlaneTree.Tree PlaneTree.Tree := PlaneTree.shuffleKernel

-- The defining recursion for a tree with finitely many vertices: shuffle every child subtree
-- independently (independent product `piFin`), then apply one uniform permutation of the children.
example (T : PlaneTree.Tree) (hT : PlaneTree.FiniteVertices T) :
    PlaneTree.shufflePMF T =
      (PlaneTree.uniformPerm (PlaneTree.degree T)).bind fun σ =>
        (PlaneTree.piFin (PlaneTree.degree T) fun i : Fin (PlaneTree.degree T) =>
            PlaneTree.shufflePMF (PlaneTree.child T ((i : ℕ) + 1))).map
          fun A => PlaneTree.ofChildren fun i => A (σ i) :=
  PlaneTree.shufflePMF_of_finite hT

-- The independent product has the product mass function; the permutation is uniform.
example {α : Type} (n : ℕ) (μ : Fin n → PMF α) (f : Fin n → α) :
    PlaneTree.piFin n μ f = ∏ i, μ i (f i) := PlaneTree.piFin_apply n μ f

example (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    PlaneTree.uniformPerm d σ = (Fintype.card (Equiv.Perm (Fin d)) : ℝ≥0∞)⁻¹ :=
  PlaneTree.uniformPerm_apply d σ

-- `ofChildren` rebuilds a plane tree from the ordered list of its children.
example (T : PlaneTree.Tree) :
    PlaneTree.ofChildren (fun i : Fin (PlaneTree.degree T) => PlaneTree.child T ((i : ℕ) + 1)) = T :=
  PlaneTree.ofChildren_child_eq T rfl

-- Infinite trees are junk: reordering is the identity.
example (T : PlaneTree.Tree) (hT : ¬PlaneTree.FiniteVertices T) :
    PlaneTree.shuffleLaw T = Measure.dirac T := PlaneTree.shuffleLaw_of_not_finite hT

-- One-level transition mass between trees with root degree d (permutations at the root and
-- independent shuffles of the d child subtrees).
example {T S : PlaneTree.Tree} (hT : PlaneTree.FiniteVertices T) {d : ℕ}
    (hdT : PlaneTree.degree T = d) (hdS : PlaneTree.degree S = d) :
    PlaneTree.shufflePMF T S = (Fintype.card (Equiv.Perm (Fin d)) : ℝ≥0∞)⁻¹ *
      ∑ σ : Equiv.Perm (Fin d), ∏ j : Fin d,
        PlaneTree.shufflePMF (PlaneTree.child T ((j : ℕ) + 1))
          (PlaneTree.child S (((σ.symm j : Fin d) : ℕ) + 1)) :=
  PlaneTree.shufflePMF_apply_eq hT hdT hdS

-- Different root degrees are never reached.
example {T S : PlaneTree.Tree} (hT : PlaneTree.FiniteVertices T)
    (h : PlaneTree.degree S ≠ PlaneTree.degree T) : PlaneTree.shufflePMF T S = 0 :=
  PlaneTree.shufflePMF_apply_of_degree_ne hT h

example : PlaneTree.shufflePMF PlaneTree.leaf = PMF.pure PlaneTree.leaf :=
  PlaneTree.shufflePMF_leaf

/-! ### Preserved vertex count, total mass one, symmetry, doubly stochastic -/

example (T : PlaneTree.Tree) : IsProbabilityMeasure (PlaneTree.shuffleLaw T) := inferInstance

-- The reordering of a finite tree has finitely many vertices, with the same count.
example {T S : PlaneTree.Tree} (hT : PlaneTree.FiniteVertices T)
    (h : PlaneTree.shufflePMF T S ≠ 0) :
    PlaneTree.FiniteVertices S ∧ PlaneTree.finiteVertexCount S = PlaneTree.finiteVertexCount T :=
  PlaneTree.finiteVertices_of_shufflePMF hT h

example (m : ℕ) (T : PlaneTree.FinitePlaneClass m) :
    PlaneTree.shuffleLaw T.val (PlaneTree.finitePlaneSet m) = 1 :=
  PlaneTree.shuffleLaw_finitePlaneSet T

-- The kernel is symmetric on finite trees.
example (n : ℕ) (T S : PlaneTree.Tree) (hn : PlaneTree.finiteVertexCount T = n)
    (hT : PlaneTree.FiniteVertices T) (hS : PlaneTree.FiniteVertices S) :
    PlaneTree.shufflePMF T S = PlaneTree.shufflePMF S T :=
  PlaneTree.shufflePMF_symm n T S hn hT hS

-- Rows and columns of the transition matrix on the finite class sum to one.
example (m : ℕ) (T : PlaneTree.FinitePlaneClass m) :
    ∑ S : PlaneTree.FinitePlaneClass m, PlaneTree.shufflePMF T.val S.val = 1 :=
  PlaneTree.sum_shuffleMatrix_row T

example (m : ℕ) (S : PlaneTree.FinitePlaneClass m) :
    ∑ T : PlaneTree.FinitePlaneClass m, PlaneTree.shufflePMF T.val S.val = 1 :=
  PlaneTree.sum_shuffleMatrix_column S

/-! ### The law depends only on the unordered tree -/

example {T T' : PlaneTree.Tree} (h : PlaneTree.SameUnordered T T')
    (hT : PlaneTree.FiniteVertices T) : PlaneTree.shufflePMF T = PlaneTree.shufflePMF T' :=
  h.shufflePMF_eq hT

example {T : PlaneTree.Tree} (hT : PlaneTree.FiniteVertices T)
    (σ : Equiv.Perm (Fin (PlaneTree.degree T))) :
    PlaneTree.shufflePMF (PlaneTree.ofChildren fun i : Fin (PlaneTree.degree T) =>
        PlaneTree.child T (((σ i : Fin (PlaneTree.degree T)) : ℕ) + 1)) =
      PlaneTree.shufflePMF T :=
  PlaneTree.shufflePMF_ofChildren_perm hT σ

/-! ### Export (a): invariance of the uniform law -/

example (m : ℕ) (_hm : 1 ≤ m) :
    (PlaneTree.finitePlaneUniform m).bind PlaneTree.shuffleLaw = PlaneTree.finitePlaneUniform m :=
  PlaneTree.finitePlaneUniform_bind_shuffleLaw m

/-! ### Export (b): the source statement with a uniformly random plane order -/

example (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw halfP PlaneForward.initial
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H} ∧
      (((PlaneForward.fullLaw halfP PlaneForward.initial)[|
          {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H}]).map
            PlaneForward.chainLimit).bind PlaneTree.shuffleLaw =
        PlaneTree.finitePlaneUniform m :=
  ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_shuffled halfP halfP_pos
    halfP_lt m hm

-- General success probability p in (0,1).
example (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (m : ℕ) (hm : 1 ≤ m) :
    0 < PlaneForward.fullLaw p PlaneForward.initial
        {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H} ∧
      (((PlaneForward.fullLaw p PlaneForward.initial)[|
          {H | PlaneForward.ExtinctionTimeIs (2 * m - 1) H}]).map
            PlaneForward.chainLimit).bind PlaneTree.shuffleLaw =
        PlaneTree.finitePlaneUniform m :=
  ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_shuffled p hp0 hp1 m hm

end

#print axioms Freezing1.PlaneTree.shufflePMF
#print axioms Freezing1.PlaneTree.shufflePMF_of_finite
#print axioms Freezing1.PlaneTree.piFin_apply
#print axioms Freezing1.PlaneTree.ofChildren_child_eq
#print axioms Freezing1.PlaneTree.shufflePMF_apply_eq
#print axioms Freezing1.PlaneTree.finiteVertices_of_shufflePMF
#print axioms Freezing1.PlaneTree.shufflePMF_symm
#print axioms Freezing1.PlaneTree.sum_shuffleMatrix_row
#print axioms Freezing1.PlaneTree.sum_shuffleMatrix_column
#print axioms Freezing1.PlaneTree.measurable_shuffleLaw
#print axioms Freezing1.PlaneTree.SameUnordered.shufflePMF_eq
#print axioms Freezing1.PlaneTree.shufflePMF_ofChildren_perm
#print axioms Freezing1.PlaneTree.finitePlaneUniform_bind_shuffleLaw
#print axioms Freezing1.ForwardAnnealed.iid_signs_conditioned_extinction_uniform_plane_shuffled
