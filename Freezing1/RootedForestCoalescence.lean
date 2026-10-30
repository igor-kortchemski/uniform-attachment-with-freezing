module

public import Freezing1.RootedForestLaw
public import Freezing1.UniformRootPair

/-!
# One-step coalescence in the actual reverse kernel

This verifies the conditional hazard used in Lemma `loi du temps de coalescence`.
It is a statement about the actual uniform ordered-root merge, not the full
joint-history product law. Distinct components have hazard `1 / choose(S, 2)`;
vertices already in the same component remain together with probability one.
In particular the distinct-component formula must not be applied to `u = v`.
-/

@[expose] public section

namespace Freezing1.RootedForest

open MeasureTheory
open scoped ENNReal Classical

variable {V : Type*} [DecidableEq V]

/-- Equality of stored component roots is actual connectivity in the forest graph. -/
theorem root_eq_iff_reachable (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    F.root u = F.root v ↔ F.graph.Reachable u v := by
  constructor
  · intro h
    obtain ⟨pu, _⟩ := F.exists_root_walk hu
    obtain ⟨pv, _⟩ := F.exists_root_walk hv
    have hru : F.graph.Reachable (F.root u) u := ⟨pu⟩
    have hrv : F.graph.Reachable (F.root v) v := ⟨pv⟩
    rw [h] at hru
    exact hru.symm.trans hrv
  · rintro ⟨p⟩
    exact F.root_eq_of_walk p

/-- The actual ordered merge sends every vertex in the second component to
its first root and leaves all other component labels unchanged. -/
theorem joinChoice_root (F : RootedForest V) {p : V × V}
    (hp : p ∈ F.roots.offDiag) (v : V) :
    (F.joinChoice p).root v = if F.root v = p.2 then p.1 else F.root v := by
  simp only [joinChoice, dite_eq_left hp, join]

/-- An actual merge never separates vertices already in one component. -/
theorem joinChoice_root_eq_of_eq (F : RootedForest V) {u v : V}
    (h : F.root u = F.root v) (p : V × V) :
    (F.joinChoice p).root u = (F.joinChoice p).root v := by
  by_cases hp : p ∈ F.roots.offDiag
  · rw [joinChoice_root F hp, joinChoice_root F hp, h]
  · simpa only [joinChoice, dite_eq_right hp] using h

/-- Two previously different components merge exactly when their two roots
are the chosen pair, in either order. -/
theorem joinChoice_root_eq_iff (F : RootedForest V) {u v : V}
    (huv : F.root u ≠ F.root v) {p : V × V} (hp : p ∈ F.roots.offDiag) :
    (F.joinChoice p).root u = (F.joinChoice p).root v ↔
      p = (F.root u, F.root v) ∨ p = (F.root v, F.root u) := by
  rw [joinChoice_root F hp, joinChoice_root F hp]
  rcases p with ⟨a, b⟩
  simp only [Prod.mk.injEq]
  by_cases hu : F.root u = b <;> by_cases hv : F.root v = b <;>
    simp_all <;> aesop

variable [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- For two existing different components, the actual forest event is exactly
the corresponding unordered-root event under the sampling measure. -/
theorem joinLaw_coalescence_eq_uniformRootPair (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    F.joinLaw.real {F' | F'.root u = F'.root v} =
      (uniformRootPair F.roots).real
        {p | p = (F.root u, F.root v) ∨ p = (F.root v, F.root u)} := by
  have hF : 2 ≤ F.roots.card :=
    (show F.roots.Nontrivial from
      ⟨F.root u, F.root_mem_roots hu, F.root v, F.root_mem_roots hv, huv⟩).two_le_card
  have hf : F.roots.offDiag.filter (fun p => (F.joinChoice p).root u = (F.joinChoice p).root v) =
      F.roots.offDiag.filter (fun p => p = (F.root u, F.root v) ∨ p = (F.root v, F.root u)) := by
    apply Finset.filter_congr
    intro p hp
    exact joinChoice_root_eq_iff F huv hp
  change (F.joinLaw {F' | F'.root u = F'.root v}).toReal = _
  rw [joinLaw_apply F hF]
  simp only [Set.mem_ofPred_eq]
  rw [hf]
  simp only [uniformRootPair, Measure.real, Measure.uniformOfFinset_apply, Set.mem_ofPred_eq]

/-- Exact one-step coalescence hazard for two distinct components. -/
theorem joinLaw_coalescence (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    F.joinLaw.real {F' | F'.root u = F'.root v} = 1 / (F.roots.card.choose 2 : ℝ) := by
  rw [joinLaw_coalescence_eq_uniformRootPair F hu hv huv]
  exact uniformRootPair_coalescence F.roots (F.root_mem_roots hu) (F.root_mem_roots hv) huv

/-- Equivalent ordered-pair normalization of the same actual hazard. -/
theorem joinLaw_coalescence_mul (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    F.joinLaw.real {F' | F'.root u = F'.root v} =
      2 / ((F.roots.card : ℝ) * ((F.roots.card : ℝ) - 1)) := by
  rw [joinLaw_coalescence_eq_uniformRootPair F hu hv huv]
  exact uniformRootPair_unordered F.roots (F.root_mem_roots hu) (F.root_mem_roots hv) huv

/-- Components that have already coalesced stay together, including the
identity kernel used when fewer than two roots exist. -/
theorem joinLaw_coalescence_of_eq (F : RootedForest V) {u v : V}
    (huv : F.root u = F.root v) :
    F.joinLaw.real {F' | F'.root u = F'.root v} = 1 := by
  have hae : ∀ᵐ F' ∂F.joinLaw, F'.root u = F'.root v := by
    by_cases hF : 2 ≤ F.roots.card
    · apply F.joinLaw_ae hF
      intro p _
      exact F.joinChoice_root_eq_of_eq huv p
    · simp only [joinLaw, ite_eq_right hF]
      simpa using huv
  have he := (ae_iff_prob_eq_one measurable_from_top).mp hae
  change (F.joinLaw {F' | F'.root u = F'.root v}).toReal = 1
  rw [he, ENNReal.toReal_one]

/-- The one-step survival factor appearing in the source's product formula. -/
theorem joinLaw_noncoalescence (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    F.joinLaw.real {F' | F'.root u ≠ F'.root v} =
      1 - 1 / (F.roots.card.choose 2 : ℝ) := by
  change F.joinLaw.real ({F' | F'.root u = F'.root v}ᶜ) = _
  rw [probReal_compl_eq_one_sub (by trivial), joinLaw_coalescence F hu hv huv]

/-- The same hazard stated using actual graph connectivity, not just the
component-root representation. -/
theorem joinLaw_connectivity_coalescence (F : RootedForest V) {u v : V}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    F.joinLaw.real {F' | F'.graph.Reachable u v} = 1 / (F.roots.card.choose 2 : ℝ) := by
  have hF : 2 ≤ F.roots.card :=
    (show F.roots.Nontrivial from
      ⟨F.root u, F.root_mem_roots hu, F.root v, F.root_mem_roots hv, huv⟩).two_le_card
  have he : F.joinLaw.real {F' | F'.root u = F'.root v} =
      F.joinLaw.real {F' | F'.graph.Reachable u v} := by
    apply measureReal_congr
    filter_upwards [F.joinLaw_vertices hF] with F' hvertices
    exact propext (F'.root_eq_iff_reachable (by rwa [hvertices]) (by rwa [hvertices]))
  rw [← he, joinLaw_coalescence F hu hv huv]

end Freezing1.RootedForest
