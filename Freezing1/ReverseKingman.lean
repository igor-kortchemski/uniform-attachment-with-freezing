module

public import Freezing1.KingmanPartition
public import Freezing1.ReverseHistory
public import Freezing1.RootedForestCoalescence

/-!
# The all-positive reverse forest projects onto Kingman's jump chain

The component partition of an actual rooted forest is a genuine partition of
its vertex set, and an actual uniform ordered-root join projects exactly to the
uniform merge of two blocks. For the all-positive schedule the whole actual
reverse history, forgetting trees and keeping only component partitions, has
the law of the Kingman jump chain started from the discrete partition of the
$n+1$ original labels. No holding times are involved.
-/

@[expose] public section

namespace Freezing1.Kingman

open MeasureTheory
open scoped ENNReal Classical

section Forest

variable {V : Type*} [DecidableEq V]

/-- The component of the root `r`. -/
def component (F : RootedForest V) (r : V) : Finset V :=
  F.vertices.filter fun v => F.root v = r

theorem mem_component {F : RootedForest V} {r v : V} :
    v ∈ component F r ↔ v ∈ F.vertices ∧ F.root v = r := Finset.mem_filter

theorem mem_component_self {F : RootedForest V} {r : V} (hr : r ∈ F.roots) :
    r ∈ component F r :=
  mem_component.mpr ⟨(RootedForest.mem_roots.mp hr).1, (RootedForest.mem_roots.mp hr).2⟩

theorem component_injOn (F : RootedForest V) : Set.InjOn (component F) F.roots := by
  intro r hr r' hr' h
  have : r ∈ component F r' := h ▸ mem_component_self hr
  exact ((RootedForest.mem_roots.mp hr).2).symm.trans (mem_component.mp this).2

/-- The family of component vertex sets of a rooted forest. -/
def Blocks.ofForest (F : RootedForest V) : Blocks V := ⟨F.roots.image (component F)⟩

theorem ofForest_card (F : RootedForest V) : (Blocks.ofForest F).family.card = F.roots.card :=
  Finset.card_image_of_injOn (component_injOn F)

theorem ofForest_isPartitionOf (F : RootedForest V) :
    (Blocks.ofForest F).IsPartitionOf F.vertices where
  nonempty := by
    intro B hB
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hB
    exact ⟨r, mem_component_self hr⟩
  disjoint := by
    intro B hB C hC hne
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.mp hC
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact hne (by rw [(mem_component.mp hv).2.symm.trans (mem_component.mp hv').2])
  subset := by
    intro B hB
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hB
    exact fun v hv => (mem_component.mp hv).1
  cover := fun v hv => ⟨component F (F.root v),
    Finset.mem_image.mpr ⟨F.root v, F.root_mem_roots hv, rfl⟩, mem_component.mpr ⟨hv, rfl⟩⟩

theorem ofForest_isolated (s : Finset V) :
    Blocks.ofForest (RootedForest.isolated s) = Blocks.discrete s := by
  have hroots : (RootedForest.isolated s).roots = s := by
    ext v
    simp [RootedForest.isolated]
  have hcomp : ∀ r ∈ s, component (RootedForest.isolated s) r = {r} := by
    intro r hr
    ext v
    rw [mem_component, Finset.mem_singleton]
    change v ∈ s ∧ v = r ↔ v = r
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hr, h⟩⟩
  unfold Blocks.ofForest Blocks.discrete
  rw [hroots]
  congr 1
  exact Finset.image_congr (fun r hr => hcomp r hr)

/-- A legal ordered join sends the union of the two components to a single block and leaves
the other blocks unchanged. -/
theorem ofForest_joinChoice (F : RootedForest V) {p : V × V} (hp : p ∈ F.roots.offDiag) :
    Blocks.ofForest (F.joinChoice p) =
      (Blocks.ofForest F).merge (component F p.1) (component F p.2) := by
  obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
  have hroot : ∀ v, (F.joinChoice p).root v = if F.root v = p.2 then p.1 else F.root v :=
    fun v => RootedForest.joinChoice_root F hp v
  have hvert : (F.joinChoice p).vertices = F.vertices := by
    simp only [RootedForest.joinChoice, dite_eq_left hp, RootedForest.join_vertices]
  have hroots : (F.joinChoice p).roots = F.roots.erase p.2 := by
    simp only [RootedForest.joinChoice, dite_eq_left hp]
    exact RootedForest.join_roots F ha hb hab
  have hcomp : ∀ r ∈ F.roots.erase p.2, component (F.joinChoice p) r =
      if r = p.1 then component F p.1 ∪ component F p.2 else component F r := by
    intro r hr
    have hrb : r ≠ p.2 := (Finset.mem_erase.mp hr).1
    ext v
    rw [mem_component, hvert, hroot]
    by_cases hra : r = p.1
    · subst hra
      rw [ite_eq_left rfl, Finset.mem_union, mem_component, mem_component]
      by_cases hv : F.root v = p.2
      · simp [hv]
        tauto
      · simp [hv]
    · rw [ite_eq_right hra, mem_component]
      by_cases hv : F.root v = p.2
      · simp [hv, Ne.symm hra]
        tauto
      · simp [hv]
  ext C
  simp only [Blocks.ofForest, Blocks.merge, hroots, Finset.mem_image, Finset.mem_insert,
    Finset.mem_erase]
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : r ∈ F.roots.erase p.2 := Finset.mem_erase.mpr hr
    by_cases hra : r = p.1
    · left
      rw [hcomp r hr', ite_eq_left hra]
    · right
      rw [hcomp r hr', ite_eq_right hra]
      refine ⟨?_, ?_, r, hr.2, rfl⟩
      · intro h
        exact hr.1 (component_injOn F hr.2 hb h)
      · intro h
        exact hra (component_injOn F hr.2 ha h)
  · rintro (rfl | ⟨hCb, hCa, r, hr, rfl⟩)
    · refine ⟨p.1, ⟨hab, ha⟩, ?_⟩
      rw [hcomp p.1 (Finset.mem_erase.mpr ⟨hab, ha⟩), ite_eq_left rfl]
    · have hrb : r ≠ p.2 := fun h => hCb (h ▸ rfl)
      have hra : r ≠ p.1 := fun h => hCa (h ▸ rfl)
      refine ⟨r, ⟨hrb, hr⟩, ?_⟩
      rw [hcomp r (Finset.mem_erase.mpr ⟨hrb, hr⟩), ite_eq_right hra]

end Forest

section OneStep

variable {V : Type*} [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- One actual uniform ordered-root join projects exactly to one Kingman merge of the
component partition. -/
theorem joinLaw_map_blocks (F : RootedForest V) (hF : 2 ≤ F.roots.card) :
    F.joinLaw.map Blocks.ofForest = mergeLaw (Blocks.ofForest F) := by
  have hP : 2 ≤ (Blocks.ofForest F).family.card := by rw [ofForest_card]; exact hF
  have hm1 : Measurable F.joinChoice := measurable_of_countable _
  have hm2 : Measurable (Blocks.ofForest : RootedForest V → Blocks V) := measurable_from_top
  ext S hS
  rw [Measure.map_apply hm2 hS, mergeLaw_apply _ hP, RootedForest.joinLaw, ite_eq_left hF,
    Measure.map_apply hm1 (hm2 hS), uniformRootPair, Measure.uniformOfFinset,
    Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (hm1 (hm2 hS))]
  rw [← Finset.mul_sum]
  have hcard : (Blocks.ofForest F).family.offDiag.card = F.roots.offDiag.card := by
    rw [card_offDiag_eq_mul_pred, card_offDiag_eq_mul_pred, ofForest_card]
  rw [hcard]
  congr 1
  refine (Finset.sum_bij (fun p _ => (component F p.1, component F p.2)) ?_ ?_ ?_ ?_)
  · intro p hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    refine Finset.mem_offDiag.mpr ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, ?_⟩
    intro h
    exact hab (component_injOn F ha hb h)
  · intro p hp q hq h
    obtain ⟨hpa, hpb, _⟩ := Finset.mem_offDiag.mp hp
    obtain ⟨hqa, hqb, _⟩ := Finset.mem_offDiag.mp hq
    have h1 := component_injOn F hpa hqa (congrArg Prod.fst h)
    have h2 := component_injOn F hpb hqb (congrArg Prod.snd h)
    exact Prod.ext h1 h2
  · intro q hq
    obtain ⟨hq1, hq2, hq3⟩ := Finset.mem_offDiag.mp hq
    obtain ⟨r1, hr1, h1⟩ := Finset.mem_image.mp hq1
    obtain ⟨r2, hr2, h2⟩ := Finset.mem_image.mp hq2
    refine ⟨(r1, r2), Finset.mem_offDiag.mpr ⟨hr1, hr2, ?_⟩, Prod.ext h1 h2⟩
    intro h
    have h' : r1 = r2 := h
    exact hq3 (by rw [← h1, ← h2, h'])
  · intro p hp
    simp only [Set.indicator, Set.mem_preimage, Pi.one_apply, ofForest_joinChoice F hp]

end OneStep

end Freezing1.Kingman
