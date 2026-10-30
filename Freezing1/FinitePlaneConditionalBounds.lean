module

public import Freezing1.FinitePlaneConditionalGeometry
public import Mathlib.Data.Finset.Card

/-! Finite plane trees of a prescribed actual vertex count form a finite class. -/

@[expose] public section

namespace Freezing1.PlaneTree

open Set
open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem finiteVertexCount_child_lt {T : Tree} (hT : FiniteVertices T) {j : ℕ}
    (hj : 1 ≤ j ∧ j ≤ degree T) : finiteVertexCount (child T j) < finiteVertexCount T := by
  let C := List.cons j '' {u : Address | Present (child T j) u}
  have hfin : C.Finite := (finiteVertices_child hT hj).image (List.cons j)
  have hroot : ([] : Address) ∉ C := by rintro ⟨u, _, h⟩; cases h
  have hsub : insert [] C ⊆ {u : Address | Present T u} := by
    rintro u (rfl | ⟨v, hv, rfl⟩)
    · exact present_nil T
    · exact (present_cons T j v).mpr ⟨hj.1, hj.2, hv⟩
  have hc := Set.ncard_le_ncard hsub hT
  rw [Set.ncard_insert_of_notMem hroot hfin] at hc
  have he : C.ncard = finiteVertexCount (child T j) :=
    Set.ncard_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
  rw [he] at hc
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hc

theorem degree_le_finiteVertexCount {T : Tree} (hT : FiniteVertices T) :
    degree T ≤ finiteVertexCount T := by
  let C : Finset Address := (Finset.range (degree T)).image (fun j => [j + 1])
  have hsub : (C : Set Address) ⊆ {u : Address | Present T u} := by
    intro u hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hu
    exact (present_cons T (j + 1) []).mpr ⟨by omega, by
      have hh := Finset.mem_range.mp hj
      omega, trivial⟩
  have hc : C.card = degree T := by
    simp only [C]
    rw [Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
    simp
  have hle := Set.ncard_le_ncard hsub hT
  rw [Set.ncard_coe_finset, hc] at hle
  exact hle

theorem offspring_le_finiteVertexCount {T : Tree} (hT : FiniteVertices T) (u : Address) :
    T.val u ≤ finiteVertexCount T := by
  induction u generalizing T with
  | nil => exact degree_le_finiteVertexCount hT
  | cons j u ih =>
    by_cases hj : 1 ≤ j ∧ j ≤ degree T
    · change (child T j).val u ≤ finiteVertexCount T
      exact (ih (finiteVertices_child hT hj)).trans (finiteVertexCount_child_le hT hj)
    · change (child T j).val u ≤ finiteVertexCount T
      rw [child_eq_leaf_of_absent T j hj, leaf_offspring]
      exact Nat.zero_le _

theorem length_lt_finiteVertexCount {T : Tree} (hT : FiniteVertices T) {u : Address}
    (hu : Present T u) : u.length < finiteVertexCount T := by
  induction u generalizing T with
  | nil => exact finiteVertexCount_pos hT
  | cons j u ih =>
    obtain ⟨hj, hdeg, htail⟩ := (present_cons T j u).mp hu
    have hchild := ih (finiteVertices_child hT ⟨hj, hdeg⟩) htail
    have hcount := finiteVertexCount_child_lt hT ⟨hj, hdeg⟩
    simp only [List.length_cons]
    omega

theorem address_entries_le_finiteVertexCount {T : Tree} (hT : FiniteVertices T) {u : Address}
    (hu : Present T u) : ∀ j ∈ u, j ≤ finiteVertexCount T := by
  induction u generalizing T with
  | nil => simp
  | cons j u ih =>
    obtain ⟨hj, hdeg, htail⟩ := (present_cons T j u).mp hu
    have hhead := hdeg.trans (degree_le_finiteVertexCount hT)
    have htail' := ih (finiteVertices_child hT ⟨hj, hdeg⟩) htail
    intro i hi
    rcases List.mem_cons.mp hi with rfl | hi
    · exact hhead
    · exact (htail' i hi).trans (finiteVertexCount_child_le hT ⟨hj, hdeg⟩)

def boundedAddresses (B : ℕ) : ℕ → Finset Address
  | 0 => {[]}
  | h + 1 => insert [] (((Finset.range (B + 1)) ×ˢ boundedAddresses B h).image
      (fun p => p.1 :: p.2))

theorem mem_boundedAddresses (B h : ℕ) (u : Address) :
    u ∈ boundedAddresses B h ↔ u.length ≤ h ∧ ∀ j ∈ u, j ≤ B := by
  induction h generalizing u with
  | zero => cases u <;> simp [boundedAddresses]
  | succ h ih =>
    cases u with
    | nil => simp [boundedAddresses]
    | cons j u =>
      simp [boundedAddresses, ih, List.length_cons]
      tauto

theorem present_mem_boundedAddresses {T : Tree} (hT : FiniteVertices T) {m : ℕ}
    (hm : finiteVertexCount T ≤ m) {u : Address} (hu : Present T u) :
    u ∈ boundedAddresses m m :=
  (mem_boundedAddresses m m u).mpr
    ⟨(length_lt_finiteVertexCount hT hu).le.trans hm,
      fun j hj => (address_entries_le_finiteVertexCount hT hu j hj).trans hm⟩

abbrev FinitePlaneClass (m : ℕ) := {T : Tree // FiniteVertices T ∧ finiteVertexCount T = m}

noncomputable def finitePlaneCoordinates (m : ℕ) (T : FinitePlaneClass m) :
    (u : boundedAddresses m m) → Fin (m + 1) :=
  fun u => ⟨T.val.val u.val, by
    have h := offspring_le_finiteVertexCount T.property.1 u.val
    rw [T.property.2] at h
    omega⟩

theorem finitePlaneCoordinates_injective (m : ℕ) : Function.Injective (finitePlaneCoordinates m) := by
  intro T S he
  apply Subtype.ext
  apply Subtype.ext
  funext u
  by_cases hu : u ∈ boundedAddresses m m
  · exact congrArg Fin.val (congrFun he ⟨u, hu⟩)
  · have hnT : ¬Present T.val u := fun hp => hu
      (present_mem_boundedAddresses T.property.1 T.property.2.le hp)
    have hnS : ¬Present S.val u := fun hp => hu
      (present_mem_boundedAddresses S.property.1 S.property.2.le hp)
    rw [not_present_offspring_zero T.val u hnT, not_present_offspring_zero S.val u hnS]

noncomputable instance finitePlaneClass_fintype (m : ℕ) : Fintype (FinitePlaneClass m) :=
  Fintype.ofInjective (finitePlaneCoordinates m) (finitePlaneCoordinates_injective m)

def star : ℕ → Tree
  | 0 => leaf
  | m + 1 => graft leaf (star m)

theorem finiteVertices_star (m : ℕ) : FiniteVertices (star m) := by
  induction m with
  | zero => exact finiteVertices_leaf
  | succ m ih => exact finiteVertices_graft finiteVertices_leaf ih

theorem finiteVertexCount_star (m : ℕ) : finiteVertexCount (star m) = m + 1 := by
  induction m with
  | zero => exact finiteVertexCount_leaf
  | succ m ih =>
    rw [star, finiteVertexCount_graft finiteVertices_leaf (finiteVertices_star m),
      finiteVertexCount_leaf, ih]
    omega

theorem finitePlaneClass_nonempty {m : ℕ} (hm : 0 < m) : Nonempty (FinitePlaneClass m) :=
  ⟨⟨star (m - 1), finiteVertices_star _, by rw [finiteVertexCount_star]; omega⟩⟩

end Freezing1.PlaneTree
