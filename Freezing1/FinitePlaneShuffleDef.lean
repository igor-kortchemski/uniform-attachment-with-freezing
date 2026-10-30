module

public import Freezing1.FinitePlaneConditionalBounds
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The uniform random reordering of the children of a finite plane tree

A plane tree is rebuilt from the list of its (subtrees of its) children by repeated `graft`
(`ofList`, `ofChildren`). The uniform random plane order of a finite plane tree is the recursive
random tree `shufflePMF`: shuffle the subtree of each child independently
(an independent product `piFin` of the child laws), then apply one uniformly random
permutation of $\{1,\dots,d\}$ to the list of the $d$ children. Hence the permutation at every
vertex is uniform, and permutations at distinct vertices (and the shuffles of distinct subtrees)
are independent.

Infinite trees are junk: `shufflePMF` is the Dirac mass at the tree itself unless the tree
has finitely many vertices.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-! ### Rebuilding a tree from its list of children -/

/-- The plane tree whose root has the given list of subtrees as children, in this order. -/
def ofList : List Tree → Tree
  | [] => leaf
  | A :: L => graft A (ofList L)

/-- The plane tree whose root has the children `A 0, A 1, …, A (d-1)` in this order. -/
def ofChildren {d : ℕ} (A : Fin d → Tree) : Tree := ofList (List.ofFn A)

@[simp] theorem ofChildren_zero (A : Fin 0 → Tree) : ofChildren A = leaf := by
  simp [ofChildren, ofList]

theorem ofChildren_succ {d : ℕ} (A : Fin (d + 1) → Tree) :
    ofChildren A = graft (A 0) (ofChildren fun i => A i.succ) := by
  simp [ofChildren, List.ofFn_succ, ofList]

@[simp] theorem degree_ofChildren {d : ℕ} (A : Fin d → Tree) : degree (ofChildren A) = d := by
  induction d with
  | zero => simp
  | succ d ih => rw [ofChildren_succ, degree_graft, ih]

theorem child_ofChildren {d : ℕ} (A : Fin d → Tree) (i : Fin d) :
    child (ofChildren A) ((i : ℕ) + 1) = A i := by
  induction d with
  | zero => exact i.elim0
  | succ d ih =>
    rw [ofChildren_succ]
    cases i using Fin.cases with
    | zero => simp [child_one_graft]
    | succ j =>
      have h := (child_succ_graft (A 0) (ofChildren fun i => A i.succ) (j := (j : ℕ) + 1)
        (by omega)).trans (ih (fun i => A i.succ) j)
      simpa only [Fin.val_succ] using h

/-- Every tree of degree `d` is rebuilt from the list of its `d` children. -/
theorem ofChildren_child_eq {d : ℕ} :
    ∀ T : Tree, degree T = d → ofChildren (fun i : Fin d => child T ((i : ℕ) + 1)) = T := by
  induction d with
  | zero =>
    intro T hT
    rw [eq_leaf_of_degree_zero hT]
    simp
  | succ d ih =>
    intro T hT
    have hpos : 0 < degree T := by omega
    have key := graft_child_dropFirst hpos
    have hdd : degree (dropFirst T) = d := by rw [degree_dropFirst]; omega
    have h1 : (fun i : Fin d => child T (((i.succ : Fin (d + 1)) : ℕ) + 1)) =
        fun i : Fin d => child (dropFirst T) ((i : ℕ) + 1) := by
      funext i
      rw [child_dropFirst T (by omega), Fin.val_succ]
    rw [ofChildren_succ]
    simp only [Fin.val_zero, zero_add]
    rw [h1, ih (dropFirst T) hdd]
    exact key

theorem ofChildren_eq_iff {d : ℕ} (A : Fin d → Tree) (S : Tree) :
    ofChildren A = S ↔ degree S = d ∧ ∀ i : Fin d, A i = child S ((i : ℕ) + 1) := by
  constructor
  · rintro rfl
    exact ⟨degree_ofChildren A, fun i => (child_ofChildren A i).symm⟩
  · rintro ⟨hd, h⟩
    have : A = fun i : Fin d => child S ((i : ℕ) + 1) := funext h
    rw [this]
    exact ofChildren_child_eq S hd

theorem finiteVertices_ofChildren {d : ℕ} {A : Fin d → Tree} (h : ∀ i, FiniteVertices (A i)) :
    FiniteVertices (ofChildren A) := by
  induction d with
  | zero => simpa using finiteVertices_leaf
  | succ d ih =>
    rw [ofChildren_succ]
    exact finiteVertices_graft (h 0) (ih fun i => h i.succ)

theorem finiteVertexCount_ofChildren {d : ℕ} {A : Fin d → Tree} (h : ∀ i, FiniteVertices (A i)) :
    finiteVertexCount (ofChildren A) = 1 + ∑ i, finiteVertexCount (A i) := by
  induction d with
  | zero => simp [finiteVertexCount_leaf]
  | succ d ih =>
    rw [ofChildren_succ, finiteVertexCount_graft (h 0) (finiteVertices_ofChildren fun i => h i.succ),
      ih (fun i => h i.succ), Fin.sum_univ_succ]
    omega

/-- The vertex count of a finite plane tree is one plus the counts of its child subtrees. -/
theorem finiteVertexCount_eq_one_add_sum {T : Tree} (hT : FiniteVertices T) :
    finiteVertexCount T =
      1 + ∑ i : Fin (degree T), finiteVertexCount (child T ((i : ℕ) + 1)) := by
  have h := finiteVertexCount_ofChildren (A := fun i : Fin (degree T) => child T ((i : ℕ) + 1))
    (fun i => finiteVertices_child hT ⟨by omega, by omega⟩)
  rwa [ofChildren_child_eq T rfl] at h

theorem finiteVertices_of_children {T : Tree}
    (h : ∀ i : Fin (degree T), FiniteVertices (child T ((i : ℕ) + 1))) : FiniteVertices T := by
  have := finiteVertices_ofChildren (A := fun i : Fin (degree T) => child T ((i : ℕ) + 1)) h
  rwa [ofChildren_child_eq T rfl] at this

/-! ### Independent products and the uniform permutation law -/

/-- The independent product of `n` probability mass functions. -/
noncomputable def piFin {α : Type} : (n : ℕ) → (Fin n → PMF α) → PMF (Fin n → α)
  | 0, _ => PMF.pure (fun i => i.elim0)
  | n + 1, μ => (μ 0).bind fun a =>
      (piFin n fun i => μ i.succ).map fun g => (Fin.cons a g : Fin (n + 1) → α)

theorem piFin_apply {α : Type} (n : ℕ) (μ : Fin n → PMF α) (f : Fin n → α) :
    piFin n μ f = ∏ i, μ i (f i) := by
  induction n with
  | zero =>
    have : f = fun i => i.elim0 := funext fun i => i.elim0
    simp [piFin, PMF.pure_apply, this]
  | succ n ih =>
    rw [piFin, PMF.bind_apply, Fin.prod_univ_succ]
    rw [tsum_eq_single (f 0)]
    · rw [PMF.map_apply, tsum_eq_single (Fin.tail f), ih]
      · have : f = Fin.cons (f 0) (Fin.tail f) := (Fin.cons_self_tail f).symm
        rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
        rfl
      · intro g hg
        split_ifs with hf
        · exfalso
          apply hg
          have := congrArg Fin.tail hf
          simpa using this.symm
        · rfl
    · intro a ha
      have h0 : (PMF.map (fun g => (Fin.cons a g : Fin (n + 1) → α))
          (piFin n fun i => μ i.succ)) f = 0 := by
        rw [PMF.map_apply]
        refine ENNReal.tsum_eq_zero.mpr fun g => ?_
        split_ifs with hf
        · exfalso
          have h := congrFun hf 0
          simp only [Fin.cons_zero] at h
          exact ha h.symm
        · rfl
      rw [h0, mul_zero]

/-- The uniform probability mass function on the permutations of `{0, …, d-1}`. -/
noncomputable def uniformPerm (d : ℕ) : PMF (Equiv.Perm (Fin d)) :=
  PMF.ofFintype (fun _ => (Fintype.card (Equiv.Perm (Fin d)) : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (by simp))

theorem uniformPerm_apply (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    uniformPerm d σ = (Fintype.card (Equiv.Perm (Fin d)) : ℝ≥0∞)⁻¹ := rfl

/-! ### The random reordering -/

/-- The random plane reordering of a plane tree. For a tree with finitely many vertices and
`d` children at the root: the subtree of each child is reordered by `shufflePMF`, the `d`
reordered subtrees being independent (`piFin`); then a uniformly random permutation `σ` of the
`d` children is applied (the `i`-th child of the result is the `σ i`-th reordered subtree), and
the tree is rebuilt with `ofChildren`. For a tree with infinitely many vertices (junk case) the
result is the tree itself. -/
noncomputable def shufflePMF (T : Tree) : PMF Tree :=
  if hT : FiniteVertices T then
    (uniformPerm (degree T)).bind fun σ =>
      (piFin (degree T) fun i : Fin (degree T) => shufflePMF (child T ((i : ℕ) + 1))).map
        fun A => ofChildren fun i => A (σ i)
  else PMF.pure T
termination_by finiteVertexCount T
decreasing_by
  exact finiteVertexCount_child_lt hT ⟨by omega, by have := i.isLt; omega⟩

theorem shufflePMF_of_not_finite {T : Tree} (hT : ¬FiniteVertices T) :
    shufflePMF T = PMF.pure T := by
  rw [shufflePMF]
  split_ifs
  rfl

theorem shufflePMF_of_finite {T : Tree} (hT : FiniteVertices T) :
    shufflePMF T = (uniformPerm (degree T)).bind fun σ =>
      (piFin (degree T) fun i : Fin (degree T) => shufflePMF (child T ((i : ℕ) + 1))).map
        fun A => ofChildren fun i => A (σ i) := by
  rw [shufflePMF]
  split_ifs
  rfl

end Freezing1.PlaneTree
