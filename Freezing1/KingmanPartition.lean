module

public import Freezing1.UniformRootPair

/-!
# The jump chain of Kingman's coalescent on set partitions

A partition is given by its family of blocks. One Kingman jump chooses an
ordered pair of distinct blocks uniformly, equivalently an unordered pair
uniformly, and replaces them by their union. This module specifies that
kernel on its own, without any forest, and proves that it acts on genuine
partitions of a fixed finite set, removes exactly one block, and gives each
unordered pair of blocks the mass $1/\binom{m}{2}$. No holding times are
introduced.
-/

@[expose] public section

namespace Freezing1.Kingman

open MeasureTheory
open scoped ENNReal Classical

/-- A family of blocks; being a genuine partition is the separate predicate
`Blocks.IsPartitionOf`. -/
@[ext] structure Blocks (V : Type*) where
  family : Finset (Finset V)

namespace Blocks

variable {V : Type*} [DecidableEq V]

instance : MeasurableSpace (Blocks V) := ⊤
instance : DiscreteMeasurableSpace (Blocks V) := ⟨fun _ => trivial⟩

/-- The discrete partition into singletons. -/
def discrete (s : Finset V) : Blocks V := ⟨s.image fun v => {v}⟩

/-- Replace two blocks by their union. -/
def merge (P : Blocks V) (A B : Finset V) : Blocks V :=
  ⟨insert (A ∪ B) ((P.family.erase A).erase B)⟩

/-- The family is a set partition of `s`: nonempty, pairwise disjoint blocks covering `s`. -/
structure IsPartitionOf (P : Blocks V) (s : Finset V) : Prop where
  nonempty : ∀ B ∈ P.family, B.Nonempty
  disjoint : ∀ B ∈ P.family, ∀ C ∈ P.family, B ≠ C → Disjoint B C
  subset : ∀ B ∈ P.family, B ⊆ s
  cover : ∀ v ∈ s, ∃ B ∈ P.family, v ∈ B

theorem discrete_isPartitionOf (s : Finset V) : (discrete s).IsPartitionOf s where
  nonempty := by
    intro B hB
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    exact Finset.singleton_nonempty v
  disjoint := by
    intro B hB C hC hne
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hC
    simpa [Finset.disjoint_singleton] using hne
  subset := by
    intro B hB
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hB
    simpa using hv
  cover := fun v hv => ⟨{v}, Finset.mem_image.mpr ⟨v, hv, rfl⟩, Finset.mem_singleton_self v⟩

theorem discrete_card (s : Finset V) : (discrete s).family.card = s.card :=
  Finset.card_image_of_injective _ (fun _ _ h => by simpa using h)

section Merge

variable {P : Blocks V} {s : Finset V} {A B : Finset V}

theorem merge_comm (P : Blocks V) (A B : Finset V) : P.merge A B = P.merge B A := by
  simp only [merge, Finset.union_comm A B, Finset.erase_right_comm]

theorem union_notMem (hP : P.IsPartitionOf s) (hA : A ∈ P.family) (hB : B ∈ P.family)
    (hAB : A ≠ B) : A ∪ B ∉ P.family := by
  intro hU
  have hAne := hP.nonempty A hA
  have hBne := hP.nonempty B hB
  by_cases hUA : A ∪ B = A
  · have hBA : B ⊆ A := Finset.union_eq_left.mp hUA
    have := hP.disjoint B hB A hA (Ne.symm hAB)
    obtain ⟨b, hb⟩ := hBne
    exact Finset.disjoint_left.mp this hb (hBA hb)
  · have := hP.disjoint A hA (A ∪ B) hU (Ne.symm hUA)
    obtain ⟨a, ha⟩ := hAne
    exact Finset.disjoint_left.mp this ha (Finset.mem_union_left _ ha)

theorem merge_card (hP : P.IsPartitionOf s) (hA : A ∈ P.family) (hB : B ∈ P.family)
    (hAB : A ≠ B) : (P.merge A B).family.card + 1 = P.family.card := by
  have hU : A ∪ B ∉ (P.family.erase A).erase B := fun h =>
    union_notMem hP hA hB hAB (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hBe : B ∈ P.family.erase A := Finset.mem_erase.mpr ⟨Ne.symm hAB, hB⟩
  change (insert (A ∪ B) ((P.family.erase A).erase B)).card + 1 = _
  rw [Finset.card_insert_of_notMem hU, Finset.card_erase_of_mem hBe,
    Finset.card_erase_of_mem hA]
  have : 2 ≤ P.family.card := by
    have h1 : ({A, B} : Finset (Finset V)) ⊆ P.family := by
      intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact hA
      · rw [Finset.mem_singleton.mp hX]; exact hB
    have := Finset.card_le_card h1
    rwa [Finset.card_pair hAB] at this
  omega

theorem merge_isPartitionOf (hP : P.IsPartitionOf s) (hA : A ∈ P.family) (hB : B ∈ P.family)
    (hAB : A ≠ B) : (P.merge A B).IsPartitionOf s where
  nonempty := by
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact (hP.nonempty A hA).mono Finset.subset_union_left
    · exact hP.nonempty C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
  disjoint := by
    intro C hC D hD hCD
    have key : ∀ X ∈ (P.family.erase A).erase B, Disjoint X (A ∪ B) := by
      intro X hX
      have hXB := (Finset.mem_erase.mp hX).1
      have hXA := (Finset.mem_erase.mp (Finset.mem_erase.mp hX).2).1
      have hXP := (Finset.mem_erase.mp (Finset.mem_erase.mp hX).2).2
      exact Finset.disjoint_union_right.mpr
        ⟨hP.disjoint X hXP A hA hXA, hP.disjoint X hXP B hB hXB⟩
    rcases Finset.mem_insert.mp hC with rfl | hC'
    · rcases Finset.mem_insert.mp hD with rfl | hD'
      · exact absurd rfl hCD
      · exact (key D hD').symm
    · rcases Finset.mem_insert.mp hD with rfl | hD'
      · exact key C hC'
      · exact hP.disjoint C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC')) D
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hD')) hCD
  subset := by
    intro C hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact Finset.union_subset (hP.subset A hA) (hP.subset B hB)
    · exact hP.subset C (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hC))
  cover := by
    intro v hv
    obtain ⟨C, hC, hvC⟩ := hP.cover v hv
    by_cases hCA : C = A
    · subst hCA
      exact ⟨C ∪ B, Finset.mem_insert_self _ _, Finset.mem_union_left _ hvC⟩
    · by_cases hCB : C = B
      · subst hCB
        exact ⟨A ∪ C, Finset.mem_insert_self _ _, Finset.mem_union_right _ hvC⟩
      · exact ⟨C, Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hCB, Finset.mem_erase.mpr ⟨hCA, hC⟩⟩), hvC⟩

/-- Two merges of a partition agree exactly for the same unordered pair of blocks. -/
theorem merge_eq_merge_iff (hP : P.IsPartitionOf s) {C D : Finset V}
    (hA : A ∈ P.family) (hB : B ∈ P.family) (hC : C ∈ P.family) (hD : D ∈ P.family)
    (hAB : A ≠ B) (hCD : C ≠ D) :
    P.merge A B = P.merge C D ↔ (A = C ∧ B = D) ∨ (A = D ∧ B = C) := by
  constructor
  · intro h
    have hmem : A ∪ B ∈ (P.merge C D).family := by
      rw [← h]; exact Finset.mem_insert_self _ _
    rcases Finset.mem_insert.mp hmem with hU | hU
    · -- A ∪ B = C ∪ D
      have hsub : ∀ X ∈ P.family, ∀ a ∈ X, a ∈ C ∪ D → X = C ∨ X = D := by
        intro X hX a haX haCD
        rcases Finset.mem_union.mp haCD with haC | haD
        · left
          by_contra hne
          exact Finset.disjoint_left.mp (hP.disjoint X hX C hC hne) haX haC
        · right
          by_contra hne
          exact Finset.disjoint_left.mp (hP.disjoint X hX D hD hne) haX haD
      obtain ⟨a, ha⟩ := hP.nonempty A hA
      obtain ⟨b, hb⟩ := hP.nonempty B hB
      have haCD : a ∈ C ∪ D := hU ▸ Finset.mem_union_left _ ha
      have hbCD : b ∈ C ∪ D := hU ▸ Finset.mem_union_right _ hb
      rcases hsub A hA a ha haCD with rfl | rfl <;> rcases hsub B hB b hb hbCD with rfl | rfl
      · exact absurd rfl hAB
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · exact absurd rfl hAB
    · exact absurd (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hU))
        (union_notMem hP hA hB hAB)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact merge_comm P A B

end Merge

end Blocks

/-- One Kingman jump: an ordered pair of distinct blocks, chosen uniformly, is merged.
With fewer than two blocks the partition is unchanged. -/
noncomputable def mergeLaw {V : Type*} [DecidableEq V] (P : Blocks V) : Measure (Blocks V) :=
  if 2 ≤ P.family.card then
    ((P.family.offDiag.card : ℝ≥0∞)⁻¹) • ∑ q ∈ P.family.offDiag, Measure.dirac (P.merge q.1 q.2)
  else Measure.dirac P

variable {V : Type*} [DecidableEq V]

theorem mergeLaw_apply (P : Blocks V) (hP : 2 ≤ P.family.card) (S : Set (Blocks V)) :
    mergeLaw P S =
      (P.family.offDiag.card : ℝ≥0∞)⁻¹ *
        ∑ q ∈ P.family.offDiag, S.indicator 1 (P.merge q.1 q.2) := by
  rw [mergeLaw, ite_eq_left hP, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  simp only [Measure.dirac_apply' _ (MeasurableSet.of_discrete (s := S))]

omit [DecidableEq V] in
theorem offDiag_card_ne_zero {P : Blocks V} (hP : 2 ≤ P.family.card) :
    (P.family.offDiag.card : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (offDiag_nonempty_of_two_le_card hP).card_pos.ne'

/-- A one-step event holding at every legal merge has full probability. -/
theorem mergeLaw_apply_eq_one {P : Blocks V} (hP : 2 ≤ P.family.card) {S : Set (Blocks V)}
    (hS : ∀ q ∈ P.family.offDiag, P.merge q.1 q.2 ∈ S) : mergeLaw P S = 1 := by
  rw [mergeLaw_apply P hP, Finset.sum_congr rfl (fun q hq => Set.indicator_of_mem (hS q hq) 1)]
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (offDiag_card_ne_zero hP) (ENNReal.natCast_ne_top _)

instance mergeLaw_isProbabilityMeasure (P : Blocks V) : IsProbabilityMeasure (mergeLaw P) := by
  by_cases hP : 2 ≤ P.family.card
  · exact ⟨mergeLaw_apply_eq_one hP (S := Set.univ) (fun _ _ => Set.mem_univ _)⟩
  · unfold mergeLaw
    rw [ite_eq_right hP]
    infer_instance

/-- The jump chain stays on genuine partitions of the same set and loses exactly one block. -/
theorem mergeLaw_ae_partition {s : Finset V} {P : Blocks V} (hP : P.IsPartitionOf s)
    (h2 : 2 ≤ P.family.card) :
    ∀ᵐ Q ∂mergeLaw P, Q.IsPartitionOf s ∧ Q.family.card + 1 = P.family.card := by
  apply (ae_iff_prob_eq_one (measurable_from_top (f := fun Q : Blocks V =>
      Q.IsPartitionOf s ∧ Q.family.card + 1 = P.family.card))).mpr
  apply mergeLaw_apply_eq_one h2
  intro q hq
  obtain ⟨hq1, hq2, hq3⟩ := Finset.mem_offDiag.mp hq
  exact ⟨Blocks.merge_isPartitionOf hP hq1 hq2 hq3, Blocks.merge_card hP hq1 hq2 hq3⟩

/-- Each unordered pair of distinct blocks is merged with probability `1 / choose(m, 2)`. -/
theorem mergeLaw_unordered {s : Finset V} {P : Blocks V} (hP : P.IsPartitionOf s)
    {A B : Finset V} (hA : A ∈ P.family) (hB : B ∈ P.family) (hAB : A ≠ B) :
    mergeLaw P {P.merge A B} = ((P.family.card.choose 2 : ℕ) : ℝ≥0∞)⁻¹ := by
  have h2 : 2 ≤ P.family.card := by
    have h1 : ({A, B} : Finset (Finset V)) ⊆ P.family := by
      intro X hX
      rcases Finset.mem_insert.mp hX with rfl | hX
      · exact hA
      · rw [Finset.mem_singleton.mp hX]; exact hB
    have := Finset.card_le_card h1
    rwa [Finset.card_pair hAB] at this
  have hsub : ({(A, B), (B, A)} : Finset (Finset V × Finset V)) ⊆ P.family.offDiag := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact Finset.mem_offDiag.mpr ⟨hA, hB, hAB⟩
    · rw [Finset.mem_singleton.mp hq]
      exact Finset.mem_offDiag.mpr ⟨hB, hA, Ne.symm hAB⟩
  have hne : ((A, B) : Finset V × Finset V) ≠ (B, A) := fun h => hAB (congrArg Prod.fst h)
  have hsum : ∑ q ∈ P.family.offDiag, ({P.merge A B} : Set (Blocks V)).indicator 1
      (P.merge q.1 q.2) = (2 : ℝ≥0∞) := by
    rw [← Finset.sum_subset hsub, Finset.sum_pair hne]
    · simp only [Set.indicator_of_mem (Set.mem_singleton _),
        Blocks.merge_comm P B A, Pi.one_apply]
      norm_num
    · intro q hq hqn
      obtain ⟨C, D⟩ := q
      obtain ⟨hC, hD, hCD⟩ := Finset.mem_offDiag.mp hq
      apply Set.indicator_of_notMem
      intro hmem
      have := (Blocks.merge_eq_merge_iff hP hC hD hA hB hCD hAB).mp hmem
      apply hqn
      simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
      exact this
  rw [mergeLaw_apply P h2, hsum, card_offDiag_eq_mul_pred]
  have hm : P.family.card * (P.family.card - 1) = 2 * P.family.card.choose 2 := by
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self P.family.card
    rw [Nat.choose_two_right]
    omega
  rw [hm]
  push_cast
  rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  generalize (((P.family.card.choose 2 : ℕ)) : ℝ≥0∞)⁻¹ = c
  rw [show (2⁻¹ * c * 2 : ℝ≥0∞) = c * (2⁻¹ * 2) by ring,
    ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

end Freezing1.Kingman
