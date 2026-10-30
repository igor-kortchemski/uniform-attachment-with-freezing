module

public import Freezing1.FinitePlaneShuffleLaw

/-!
# The random reordering only depends on the unordered tree

Two plane trees are the same unordered rooted tree (`SameUnordered`) when their root degrees agree
and their child subtrees match up to a permutation of the children, recursively. The law of the
uniform random reordering of a finite plane tree is the same for all plane trees representing the
same unordered tree. Hence "reorder uniformly at random" is a well defined operation on the
unordered tree, independent of the plane order used to represent it (for instance the chronological
one).
-/

@[expose] public section

namespace Freezing1.PlaneTree

open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- `SameUnordered T T'`: the plane trees `T` and `T'` are the same rooted tree once the order of
the children is forgotten (at every vertex there is a permutation of the children carrying the
child subtrees of `T` to those of `T'`, recursively). -/
inductive SameUnordered : Tree → Tree → Prop
  | intro {T T' : Tree} {d : ℕ} (σ : Equiv.Perm (Fin d)) (hT : degree T = d) (hT' : degree T' = d)
      (h : ∀ j : Fin d,
        SameUnordered (child T ((j : ℕ) + 1)) (child T' (((σ j : Fin d) : ℕ) + 1))) :
      SameUnordered T T'

theorem SameUnordered.finiteVertices : ∀ {T T' : Tree}, SameUnordered T T' →
    FiniteVertices T → FiniteVertices T' := by
  intro T T' h
  induction h with
  | intro σ hdT hdT' h ih =>
    intro hT
    apply finiteVertices_of_children_lt
    intro i hi
    rw [hdT'] at hi
    have hj := (σ.symm ⟨i, hi⟩).isLt
    have := ih (σ.symm ⟨i, hi⟩)
      (finiteVertices_child hT ⟨by omega, by omega⟩)
    simpa using this

theorem SameUnordered.refl_of_finite :
    ∀ (n : ℕ) (T : Tree), finiteVertexCount T = n → FiniteVertices T → SameUnordered T T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hn hT
    refine SameUnordered.intro (Equiv.refl (Fin (degree T))) rfl rfl fun j => ?_
    have hj : 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ degree T :=
      ⟨by omega, by have := j.isLt; omega⟩
    exact ih _ (hn ▸ finiteVertexCount_child_lt hT hj) _ rfl (finiteVertices_child hT hj)

/-- The random reordering of a finite plane tree has the same law for all plane trees that
represent the same unordered tree. -/
theorem SameUnordered.shufflePMF_eq : ∀ {T T' : Tree}, SameUnordered T T' →
    FiniteVertices T → shufflePMF T = shufflePMF T' := by
  intro T T' h
  induction h with
  | intro σ hdT hdT' h ih =>
    rename_i T T' d
    intro hT
    have hT' : FiniteVertices T' := (SameUnordered.intro σ hdT hdT' h).finiteVertices hT
    ext S
    by_cases hdS : degree S = d
    · rw [shufflePMF_apply_eq hT hdT hdS, shufflePMF_apply_eq hT' hdT' hdS]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ fun τ => ?_
      refine Eq.trans ?_ (Equiv.prod_comp σ (fun k : Fin d =>
        shufflePMF (child T' ((k : ℕ) + 1))
          (child S ((((Equiv.mulLeft σ τ).symm k : Fin d) : ℕ) + 1))))
      refine Finset.prod_congr rfl fun j _ => ?_
      have hj : 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ degree T :=
        ⟨by omega, by have := j.isLt; omega⟩
      have hs : ((Equiv.mulLeft σ τ).symm (σ j) : Fin d) = τ.symm j := by
        simp [Equiv.Perm.mul_def]
      rw [ih j (finiteVertices_child hT hj), hs]
    · rw [shufflePMF_apply_of_degree_ne hT (by rw [hdT]; exact hdS),
        shufflePMF_apply_of_degree_ne hT' (by rw [hdT']; exact hdS)]

/-- Permuting the list of children of the root of a finite plane tree does not change the law
of its random reordering. -/
theorem shufflePMF_ofChildren_perm {T : Tree} (hT : FiniteVertices T)
    (σ : Equiv.Perm (Fin (degree T))) :
    shufflePMF (ofChildren fun i : Fin (degree T) => child T (((σ i : Fin (degree T)) : ℕ) + 1)) =
      shufflePMF T := by
  have h : SameUnordered T (ofChildren fun i : Fin (degree T) =>
      child T (((σ i : Fin (degree T)) : ℕ) + 1)) := by
    refine SameUnordered.intro σ.symm rfl (degree_ofChildren _) fun j => ?_
    have hj : 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ degree T :=
      ⟨by omega, by have := j.isLt; omega⟩
    rw [child_ofChildren]
    simp only [Equiv.apply_symm_apply]
    exact SameUnordered.refl_of_finite _ _ rfl (finiteVertices_child hT hj)
  exact (SameUnordered.shufflePMF_eq h hT).symm

end Freezing1.PlaneTree
