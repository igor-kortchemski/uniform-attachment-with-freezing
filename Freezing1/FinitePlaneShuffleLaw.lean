module

public import Freezing1.FinitePlaneShuffleDef

/-!
# The reordering kernel preserves the vertex count and is symmetric

For finite plane trees $T,S$ with $d$ root children, the transition mass of the random
reordering is
$$K(T,S)=\frac1{d!}\sum_{\sigma\in\mathfrak S_d}\prod_{j}K(T_j,S_{\sigma^{-1}j}),$$
where $T_j,S_k$ are the child subtrees (and $K(T,S)=0$ if the root degrees differ). From this
formula, by induction on the vertex count, the reordering preserves the vertex count and finiteness
and the kernel is symmetric, $K(T,S)=K(S,T)$. Symmetry gives the doubly stochastic property on
each class of plane trees with a fixed number of vertices.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem finiteVertexCount_eq_one_add_sum_range {T : Tree} (hT : FiniteVertices T) :
    finiteVertexCount T =
      1 + ∑ i ∈ Finset.range (degree T), finiteVertexCount (child T (i + 1)) := by
  rw [finiteVertexCount_eq_one_add_sum hT, Finset.sum_range]

theorem finiteVertices_of_children_lt {T : Tree}
    (h : ∀ i, i < degree T → FiniteVertices (child T (i + 1))) : FiniteVertices T :=
  finiteVertices_of_children fun i => h i i.isLt

/-! ### The one-step formula for the transition mass -/

/-- The transition mass of the reordering between two trees with the same root degree `d`. -/
theorem shufflePMF_apply_eq {T S : Tree} (hT : FiniteVertices T) {d : ℕ} (hdT : degree T = d)
    (hdS : degree S = d) :
    shufflePMF T S = (Fintype.card (Equiv.Perm (Fin d)) : ℝ≥0∞)⁻¹ *
      ∑ σ : Equiv.Perm (Fin d), ∏ j : Fin d,
        shufflePMF (child T ((j : ℕ) + 1)) (child S (((σ.symm j : Fin d) : ℕ) + 1)) := by
  subst hdT
  rw [shufflePMF_of_finite hT, PMF.bind_apply, tsum_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [uniformPerm_apply, PMF.map_apply,
    tsum_eq_single (fun j => child S (((σ.symm j : Fin (degree T)) : ℕ) + 1))]
  · rw [piFin_apply]
    have h : S = ofChildren fun i => (fun j => child S (((σ.symm j : Fin (degree T)) : ℕ) + 1)) (σ i) := by
      symm
      rw [ofChildren_eq_iff]
      exact ⟨hdS, fun i => by simp⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  · intro A hA
    have h : ¬ S = ofChildren fun i => A (σ i) := by
      intro h
      apply hA
      obtain ⟨-, h2⟩ := (ofChildren_eq_iff _ _).mp h.symm
      funext j
      have := h2 (σ.symm j)
      simpa using this
    rw [ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- Reordering preserves the root degree. -/
theorem shufflePMF_apply_of_degree_ne {T S : Tree} (hT : FiniteVertices T)
    (h : degree S ≠ degree T) : shufflePMF T S = 0 := by
  rw [shufflePMF_of_finite hT, PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.mpr fun σ => ?_
  have : (PMF.map (fun A : Fin (degree T) → Tree => ofChildren fun i => A (σ i))
      (piFin (degree T) fun i : Fin (degree T) => shufflePMF (child T ((i : ℕ) + 1)))) S = 0 := by
    rw [PMF.map_apply]
    refine ENNReal.tsum_eq_zero.mpr fun A => ?_
    have hn : ¬ S = ofChildren fun i => A (σ i) := by
      intro hS
      apply h
      rw [hS, degree_ofChildren]
    rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
  rw [this, mul_zero]

/-! ### Finiteness and vertex count are preserved -/

theorem shufflePMF_support :
    ∀ (n : ℕ) (T S : Tree), finiteVertexCount T = n → FiniteVertices T →
      shufflePMF T S ≠ 0 → FiniteVertices S ∧ finiteVertexCount S = n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T S hn hT hne
    by_cases hd : degree S = degree T
    · rw [shufflePMF_apply_eq hT rfl hd] at hne
      obtain ⟨-, hsum⟩ := mul_ne_zero_iff.mp hne
      obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
      have hprod := Finset.prod_ne_zero_iff.mp hσ
      have hch : ∀ j : Fin (degree T),
          FiniteVertices (child S (((σ.symm j : Fin (degree T)) : ℕ) + 1)) ∧
          finiteVertexCount (child S (((σ.symm j : Fin (degree T)) : ℕ) + 1)) =
            finiteVertexCount (child T ((j : ℕ) + 1)) := by
        intro j
        have hj : 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ degree T := ⟨by omega, by have := j.isLt; omega⟩
        exact ih (finiteVertexCount (child T ((j : ℕ) + 1)))
          (hn ▸ finiteVertexCount_child_lt hT hj) (child T ((j : ℕ) + 1)) _ rfl
          (finiteVertices_child hT hj) (hprod j (Finset.mem_univ _))
      have hch' : ∀ k : Fin (degree T),
          FiniteVertices (child S ((k : ℕ) + 1)) ∧
          finiteVertexCount (child S ((k : ℕ) + 1)) =
            finiteVertexCount (child T (((σ k : Fin (degree T)) : ℕ) + 1)) := by
        intro k
        simpa using hch (σ k)
      have hSfin : FiniteVertices S := by
        apply finiteVertices_of_children_lt
        intro i hi
        rw [hd] at hi
        exact (hch' ⟨i, hi⟩).1
      refine ⟨hSfin, ?_⟩
      rw [finiteVertexCount_eq_one_add_sum_range hSfin, hd, Finset.sum_range, ← hn,
        finiteVertexCount_eq_one_add_sum_range hT, Finset.sum_range]
      congr 1
      calc ∑ k : Fin (degree T), finiteVertexCount (child S ((k : ℕ) + 1))
          = ∑ k : Fin (degree T), finiteVertexCount (child T (((σ k : Fin (degree T)) : ℕ) + 1)) :=
            Finset.sum_congr rfl fun k _ => (hch' k).2
        _ = ∑ j : Fin (degree T), finiteVertexCount (child T ((j : ℕ) + 1)) :=
            Equiv.sum_comp σ (fun j : Fin (degree T) => finiteVertexCount (child T ((j : ℕ) + 1)))
    · exact absurd (shufflePMF_apply_of_degree_ne hT hd) hne

/-- Reordering a finite plane tree gives a finite plane tree with the same number of vertices. -/
theorem finiteVertices_of_shufflePMF {T S : Tree} (hT : FiniteVertices T)
    (h : shufflePMF T S ≠ 0) : FiniteVertices S ∧ finiteVertexCount S = finiteVertexCount T :=
  shufflePMF_support _ T S rfl hT h

/-! ### Symmetry of the transition mass -/

theorem shufflePMF_symm :
    ∀ (n : ℕ) (T S : Tree), finiteVertexCount T = n → FiniteVertices T → FiniteVertices S →
      shufflePMF T S = shufflePMF S T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T S hn hT hS
    by_cases hd : degree S = degree T
    · obtain ⟨d, hdT⟩ : ∃ d, degree T = d := ⟨_, rfl⟩
      have hdS : degree S = d := hd.trans hdT
      rw [shufflePMF_apply_eq hT hdT hdS, shufflePMF_apply_eq hS hdS hdT]
      congr 1
      have hK : ∀ (j k : Fin d), shufflePMF (child T ((j : ℕ) + 1)) (child S ((k : ℕ) + 1)) =
          shufflePMF (child S ((k : ℕ) + 1)) (child T ((j : ℕ) + 1)) := by
        intro j k
        have hj : 1 ≤ (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ degree T :=
          ⟨by omega, by have := j.isLt; omega⟩
        have hk : 1 ≤ (k : ℕ) + 1 ∧ (k : ℕ) + 1 ≤ degree S :=
          ⟨by omega, by have := k.isLt; omega⟩
        exact ih (finiteVertexCount (child T ((j : ℕ) + 1))) (hn ▸ finiteVertexCount_child_lt hT hj)
          _ _ rfl (finiteVertices_child hT hj) (finiteVertices_child hS hk)
      calc ∑ σ : Equiv.Perm (Fin d), ∏ j : Fin d,
            shufflePMF (child T ((j : ℕ) + 1)) (child S (((σ.symm j : Fin d) : ℕ) + 1))
          = ∑ σ : Equiv.Perm (Fin d), ∏ j : Fin d,
            shufflePMF (child S (((σ.symm j : Fin d) : ℕ) + 1)) (child T ((j : ℕ) + 1)) :=
            Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun j _ => hK _ _
        _ = ∑ σ : Equiv.Perm (Fin d), ∏ k : Fin d,
            shufflePMF (child S ((k : ℕ) + 1)) (child T (((σ k : Fin d) : ℕ) + 1)) := by
            refine Finset.sum_congr rfl fun σ _ => ?_
            rw [← Equiv.prod_comp σ]
            simp
        _ = ∑ σ : Equiv.Perm (Fin d), ∏ k : Fin d,
            shufflePMF (child S ((k : ℕ) + 1)) (child T (((σ.symm k : Fin d) : ℕ) + 1)) := by
            refine Fintype.sum_equiv (Equiv.inv _) _ _ fun σ => ?_
            simp [Equiv.Perm.inv_def]
    · rw [shufflePMF_apply_of_degree_ne hT hd, shufflePMF_apply_of_degree_ne hS (Ne.symm hd)]

/-! ### Transition matrix on the class of finite plane trees with `m` vertices -/

/-- The transition mass of the random reordering between two trees of the class. -/
noncomputable def shuffleMatrix (m : ℕ) (T S : FinitePlaneClass m) : ℝ≥0∞ :=
  shufflePMF T.val S.val

theorem shuffleMatrix_symm {m : ℕ} (T S : FinitePlaneClass m) :
    shuffleMatrix m T S = shuffleMatrix m S T :=
  shufflePMF_symm _ T.val S.val rfl T.property.1 S.property.1

/-- Rows of the transition matrix sum to one: the reordering of a tree of the class is a
probability measure on the class. -/
theorem sum_shuffleMatrix_row {m : ℕ} (T : FinitePlaneClass m) :
    ∑ S : FinitePlaneClass m, shuffleMatrix m T S = 1 := by
  have hsupp : Function.support (fun S : Tree => shufflePMF T.val S) ⊆
      {S : Tree | FiniteVertices S ∧ finiteVertexCount S = m} := by
    intro S hS
    obtain ⟨h1, h2⟩ := finiteVertices_of_shufflePMF T.property.1 hS
    exact ⟨h1, h2.trans T.property.2⟩
  have h2 : ∑' S : {S : Tree // FiniteVertices S ∧ finiteVertexCount S = m},
      shufflePMF T.val S.val = ∑' S : Tree, shufflePMF T.val S :=
    tsum_subtype_eq_of_support_subset (f := fun S : Tree => shufflePMF T.val S)
      (s := {S : Tree | FiniteVertices S ∧ finiteVertexCount S = m}) hsupp
  calc ∑ S : FinitePlaneClass m, shuffleMatrix m T S
      = ∑' S : FinitePlaneClass m, shufflePMF T.val S.val := (tsum_fintype _).symm
    _ = ∑' S : Tree, shufflePMF T.val S := h2
    _ = 1 := (shufflePMF T.val).tsum_coe

/-- The transition matrix of the random reordering on the finite class of plane trees with `m`
vertices is doubly stochastic: columns also sum to one. -/
theorem sum_shuffleMatrix_column {m : ℕ} (S : FinitePlaneClass m) :
    ∑ T : FinitePlaneClass m, shuffleMatrix m T S = 1 := by
  rw [← sum_shuffleMatrix_row S]
  exact Finset.sum_congr rfl fun T _ => shuffleMatrix_symm T S

end Freezing1.PlaneTree
