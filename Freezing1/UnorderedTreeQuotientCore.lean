module

public import Freezing1.UnorderedFiniteIsoBridge
public import Freezing1.PlaneFiniteBallIso
public import Freezing1.LocalTopologyVariants

/-!
# Assembly of the actual forgetting-order quotient and its local topology

This internal assembly takes the precise finite-isomorphism reflection
lemma as an explicit proof input. The final source consumer must supply
its proved instance; these conditional helpers alone do not complete A20.

The carrier is an actual quotient by root/parent/label-preserving vertex
bijections. Its wrapper allows the local metric topology to be specified
explicitly, without inheriting an unproved property of a generic quotient
topology from a typeclass.
-/

@[expose] public section

namespace Freezing1.UnorderedLocal

open BinaryBijection Filter
open scoped Topology Classical

abbrev PlaneSource := PlaneLabelled.Tree (Option ℕ) ℕ

structure Tree where
  val : Quotient (PlaneLabelled.unorderedSetoid (Option ℕ) ℕ)

theorem Tree.ext {S T : Tree} (hh : S.val = T.val) : S = T := by
  cases S
  cases T
  cases hh
  rfl

def ofPlane (T : PlaneSource) : Tree := ⟨Quotient.mk _ T⟩

theorem ofPlane_eq_iff (S T : PlaneSource) :
    ofPlane S = ofPlane T ↔ Nonempty (PlaneLabelled.UnorderedIso S T) := by
  change Tree.mk (Quotient.mk _ S) = Tree.mk (Quotient.mk _ T) ↔ _
  rw [Tree.mk.injEq, Quotient.eq]
  rfl

theorem exists_plane_representative (T : Tree) : ∃ P : PlaneSource, ofPlane P = T := by
  refine ⟨T.val.out, Tree.ext ?_⟩
  exact Quotient.out_eq T.val

def FiniteIsoReflection : Prop :=
  ∀ s t : Rooted, Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) → s.UnorderedEq t

theorem finiteClasses_eq_iff_actualIso (H : FiniteIsoReflection) (s t : Rooted) :
    ofRooted s = ofRooted t ↔ Nonempty (PlaneLabelled.UnorderedIso s.toPlaneLabelled t.toPlaneLabelled) :=
  ⟨fun he => ((ofRooted_eq_iff s t).mp he).nonempty_unorderedIso,
    fun he => (ofRooted_eq_iff s t).mpr (H s t he)⟩

theorem tower_eq_of_iso (H : FiniteIsoReflection) {S T : PlaneSource}
    (e : PlaneLabelled.UnorderedIso S T) : PlaneLabelled.toBallTower S = PlaneLabelled.toBallTower T := by
  apply Subtype.ext
  funext h
  exact (ofRooted_eq_iff _ _).mpr (H _ _ ⟨e.finiteRootedIso h⟩)

theorem planeTower_surjective (H : FiniteIsoReflection) : Function.Surjective PlaneLabelled.toBallTower := by
  intro B
  obtain ⟨T, r, hrep, hiso⟩ := exists_finiteIso_realization B
  refine ⟨T, Subtype.ext (funext (fun h => ?_))⟩
  exact ((ofRooted_eq_iff _ _).mpr (H _ _ (hiso h))).trans (hrep h)

noncomputable def towerMap (H : FiniteIsoReflection) (T : Tree) : BallTower :=
  Quotient.lift PlaneLabelled.toBallTower
    (fun (S T : PlaneSource) (he : Nonempty (PlaneLabelled.UnorderedIso S T)) => by
      obtain ⟨e⟩ := he
      exact tower_eq_of_iso H e) T.val

@[simp] theorem towerMap_ofPlane (H : FiniteIsoReflection) (T : PlaneSource) :
    towerMap H (ofPlane T) = PlaneLabelled.toBallTower T := rfl

theorem towerMap_injective (H : FiniteIsoReflection) : Function.Injective (towerMap H) := by
  intro S T
  rcases S with ⟨S⟩
  rcases T with ⟨T⟩
  refine Quotient.inductionOn₂ S T (fun P Q he => ?_)
  exact (ofPlane_eq_iff P Q).mpr (PlaneLabelled.nonempty_unorderedIso_of_tower_eq P Q he)

theorem towerMap_surjective (H : FiniteIsoReflection) : Function.Surjective (towerMap H) := by
  intro B
  obtain ⟨T, hT⟩ := planeTower_surjective H B
  exact ⟨ofPlane T, hT⟩

noncomputable def treeTowerEquiv (H : FiniteIsoReflection) : Tree ≃ BallTower :=
  Equiv.ofBijective (towerMap H) ⟨towerMap_injective H, towerMap_surjective H⟩

@[instance_reducible] noncomputable def topology (H : FiniteIsoReflection) : TopologicalSpace Tree :=
  TopologicalSpace.induced (towerMap H) inferInstance

theorem polishSpace_topology (H : FiniteIsoReflection) : @PolishSpace Tree (topology H) :=
  (treeTowerEquiv H).polishSpace_induced

theorem completeSeparableMetric_topology (H : FiniteIsoReflection) :
    @LocalTopologyVariants.HasCompleteSeparableMetric Tree (topology H) := by
  let : TopologicalSpace Tree := topology H
  have : PolishSpace Tree := polishSpace_topology H
  exact LocalTopologyVariants.hasCompleteSeparableMetric _

noncomputable def finiteTrunc (H : FiniteIsoReflection) (T : Tree) (h : ℕ) : FiniteTree :=
  (towerMap H T).val h

@[simp] theorem finiteTrunc_ofPlane (H : FiniteIsoReflection) (T : PlaneSource) (h : ℕ) :
    finiteTrunc H (ofPlane T) h = ofRooted (PlaneLabelled.finiteRooted T h) := rfl

theorem quotient_tendsto_iff_balls (H : FiniteIsoReflection) {ι : Type*} {l : Filter ι}
    (S : ι → Tree) (T : Tree) :
    Tendsto S l (@nhds Tree (topology H) T) ↔
      ∀ h, ∀ᶠ i in l, finiteTrunc H (S i) h = finiteTrunc H T h := by
  rw [topology, nhds_induced, tendsto_comap_iff]
  exact tendsto_iff_balls (fun i => towerMap H (S i)) (towerMap H T)

theorem quotient_tendsto_iff_positive_balls (H : FiniteIsoReflection) {ι : Type*} {l : Filter ι}
    (S : ι → Tree) (T : Tree) :
    Tendsto S l (@nhds Tree (topology H) T) ↔
      ∀ h, 1 ≤ h → ∀ᶠ i in l, finiteTrunc H (S i) h = finiteTrunc H T h := by
  rw [quotient_tendsto_iff_balls H]
  constructor
  · exact fun hc h _ => hc h
  · intro hc h
    by_cases hh : 1 ≤ h
    · exact hc h hh
    · have hz : h = 0 := by omega
      subst h
      filter_upwards [hc 1 le_rfl] with i hi
      have he := congrArg (truncate 0) hi
      simpa only [finiteTrunc, BallTower.truncate_ball _ (by omega : 0 ≤ 1)] using he

end Freezing1.UnorderedLocal
