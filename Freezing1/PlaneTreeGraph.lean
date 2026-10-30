module

public import Freezing1.PlaneTreeLabellings
public import Freezing1.LocalTreeGraph
public import Mathlib.Data.Nat.Pairing

/-!
# Genuine graph realization of every locally finite plane shape

Natural address codes are auxiliary vertex IDs only. They are not the
tree's actual incoming-edge labels. Existing finite-ball graph theorems
then supply connectedness, acyclicity, local finiteness and exact distances.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open scoped Classical

def addressCode (u : Address) : ℕ := u.foldl (fun a j => Nat.pair a j + 1) 0

@[simp] theorem addressCode_nil : addressCode [] = 0 := rfl

theorem addressCode_append_singleton (u : Address) (j : ℕ) :
    addressCode (u ++ [j]) = Nat.pair (addressCode u) j + 1 := by
  simp [addressCode, List.foldl_append]

theorem addressCode_lt_append (u : Address) (j : ℕ) :
    addressCode u < addressCode (u ++ [j]) := by
  rw [addressCode_append_singleton]
  exact Nat.lt_succ_of_le (Nat.left_le_pair _ _)

theorem addressCode_eq_zero_iff (u : Address) : addressCode u = 0 ↔ u = [] := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u j _ => simp [addressCode_append_singleton]

theorem addressCode_injective : Function.Injective addressCode := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro v he
    exact ((addressCode_eq_zero_iff v).mp he.symm).symm
  | append_singleton u j ih =>
    intro v he
    induction v using List.reverseRecOn with
    | nil => simp [addressCode_append_singleton] at he
    | append_singleton v k _ =>
      rw [addressCode_append_singleton, addressCode_append_singleton] at he
      have hp := Nat.pair_eq_pair.mp (Nat.add_right_cancel he)
      rw [ih hp.1, hp.2]

theorem exists_append_singleton_of_ne_nil (u : Address) (hu : u ≠ []) :
    ∃ v : Address, ∃ j : ℕ, u = v ++ [j] := by
  induction u using List.reverseRecOn with
  | nil => exact (hu rfl).elim
  | append_singleton u j _ => exact ⟨u, j, rfl⟩

def auxiliaryRecord (u : Address) : LocalTree.VertexRecord :=
  ⟨addressCode u, addressCode u.dropLast, u.length, none⟩

theorem auxiliaryRecord_injective : Function.Injective auxiliaryRecord := by
  intro u v he
  exact addressCode_injective (congrArg LocalTree.VertexRecord.birth he)

noncomputable def auxiliaryBall (T : Tree) (h : ℕ) : LocalTree.Ball :=
  (ball T h).image auxiliaryRecord

theorem auxiliaryBall_valid (T : Tree) (h : ℕ) : LocalTree.ValidBall h (auxiliaryBall T h) := by
  constructor
  · refine ⟨auxiliaryRecord [], Finset.mem_image.mpr ⟨[], (mem_ball _ _ _).mpr ⟨present_nil T, by simp⟩, rfl⟩, rfl⟩
  · intro r hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    exact (mem_ball _ _ _).mp hu |>.2
  · intro r hr s hs he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have huv := addressCode_injective he
    subst v
    rfl
  · intro r hr he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu0 := (addressCode_eq_zero_iff u).mp he
    subst u
    exact ⟨rfl, rfl⟩
  · intro r hr he
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hu0 : u ≠ [] := by
      intro hh
      subst u
      exact he rfl
    obtain ⟨v, j, rfl⟩ := exists_append_singleton_of_ne_nil u hu0
    obtain ⟨hp, hlen⟩ := (mem_ball _ _ _).mp hu
    have hvp : Present T v := present_of_prefix ⟨[j], rfl⟩ hp
    have hvl : v.length ≤ h := by simp only [List.length_append, List.length_singleton] at hlen; omega
    refine ⟨auxiliaryRecord v, Finset.mem_image.mpr ⟨v, (mem_ball _ _ _).mpr ⟨hvp, hvl⟩, rfl⟩, ?_, ?_, ?_⟩
    · simp [auxiliaryRecord]
    · simp [auxiliaryRecord]
    · exact addressCode_lt_append v j

theorem auxiliaryBall_restrict (T : Tree) (h : ℕ) :
    LocalTree.restrict h (auxiliaryBall T (h + 1)) = auxiliaryBall T h := by
  ext r
  simp only [LocalTree.restrict, Finset.mem_filter]
  constructor
  · rintro ⟨hr, hlen⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    refine Finset.mem_image.mpr ⟨u, (mem_ball _ _ _).mpr ?_, rfl⟩
    exact ⟨((mem_ball _ _ _).mp hu).1, hlen⟩
  · intro hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hr
    have hh := (mem_ball _ _ _).mp hu
    exact ⟨Finset.mem_image.mpr ⟨u, (mem_ball _ _ _).mpr ⟨hh.1, by omega⟩, rfl⟩, hh.2⟩

noncomputable def auxiliaryTree (T : Tree) : LocalTree.Tree :=
  ⟨auxiliaryBall T, fun h => ⟨auxiliaryBall_valid T h, auxiliaryBall_restrict T h⟩⟩

abbrev GraphVertex (T : Tree) := LocalTree.Vertex (auxiliaryTree T)

noncomputable def graph (T : Tree) := LocalTree.graph (auxiliaryTree T)

theorem graph_isTree (T : Tree) : (graph T).IsTree := LocalTree.graph_isTree _

noncomputable instance graph_locallyFinite (T : Tree) : (graph T).LocallyFinite :=
  LocalTree.graph_locallyFinite _

noncomputable def vertexOfAddress (T : Tree) (u : {u : Address // Present T u}) : GraphVertex T :=
  ⟨auxiliaryRecord u.val, ⟨u.val.length,
    Finset.mem_image.mpr ⟨u.val, (mem_ball _ _ _).mpr ⟨u.property, le_rfl⟩, rfl⟩⟩⟩

theorem vertexOfAddress_injective (T : Tree) : Function.Injective (vertexOfAddress T) := by
  intro u v he
  apply Subtype.ext
  exact auxiliaryRecord_injective (congrArg Subtype.val he)

theorem vertexOfAddress_surjective (T : Tree) : Function.Surjective (vertexOfAddress T) := by
  intro v
  obtain ⟨h, hv⟩ := v.property
  obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hv
  refine ⟨⟨u, ((mem_ball _ _ _).mp hu).1⟩, ?_⟩
  exact Subtype.ext he

noncomputable def addressEquiv (T : Tree) : {u : Address // Present T u} ≃ GraphVertex T :=
  Equiv.ofBijective (vertexOfAddress T) ⟨vertexOfAddress_injective T, vertexOfAddress_surjective T⟩

theorem graph_dist_address (T : Tree) (u : {u : Address // Present T u}) :
    (graph T).dist (LocalTree.root (auxiliaryTree T)) (vertexOfAddress T u) = u.val.length :=
  (LocalTree.height_eq_dist _ _).symm

end Freezing1.PlaneTree
