module

public import Freezing1.ForwardForestRootOrbit
public import Freezing1.ForwardForestStarConvention

/-!
# The source's bare all-star forest as a genuine coarsening

The root clocks and their true activity are erased before root names are
forgotten. This is coarser than the augmented forest used for full-state
reconstruction. It retains all descendant data and the source's marked-root
activity convention.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def slotStarForest (m : ℕ) (F : State) : State :=
  { F with
    active := F.active ∪ Finset.range m
    frozenAt := fun v => if v < m then none else F.frozenAt v }

theorem slotStarForest_relabel {m : ℕ} {e : Equiv.Perm ℕ}
    (he : RootPermutation m e) (F : State) :
    slotStarForest m (F.relabel e) = (slotStarForest m F).relabel e := by
  apply State.ext_data
  · rfl
  · change F.active.image e ∪ Finset.range m = (F.active ∪ Finset.range m).image e
    rw [Finset.image_union, he.image_range]
  · rfl
  · rfl
  · rfl
  · funext v
    have hmem : e.symm v < m ↔ v < m := by
      have hh : e.symm v ∈ Finset.range m ↔ v ∈ Finset.range m := by
        conv_rhs => rw [← he.image_range]
        simp only [Finset.mem_image]
        constructor
        · intro hv
          exact ⟨e.symm v, hv, e.apply_symm_apply v⟩
        · rintro ⟨r, hr, hrv⟩
          simpa only [← hrv, Equiv.symm_apply_apply] using hr
      simpa only [Finset.mem_range] using hh
    change (if v < m then none else F.frozenAt (e.symm v)) =
      if e.symm v < m then none else F.frozenAt (e.symm v)
    simp only [hmem]

noncomputable def starErasedCoarsening (m : ℕ) : RootErasedForest m → RootErasedForest m :=
  Quotient.map (slotStarForest m) (by
    rintro F G ⟨e, he, hG⟩
    exact ⟨e, he, by rw [hG, slotStarForest_relabel he]⟩)

noncomputable def bareSlotOrbit (m : ℕ) (F : State) : RootErasedForest m :=
  starErasedCoarsening m (eraseRootNames m F)

theorem bareSlotOrbit_eq (m : ℕ) (F : State) :
    bareSlotOrbit m F = eraseRootNames m (slotStarForest m F) := rfl

theorem bareSlotOrbit_relabel {m : ℕ} {e : Equiv.Perm ℕ} (he : RootPermutation m e) (F : State) :
    bareSlotOrbit m (F.relabel e) = bareSlotOrbit m F := by
  unfold bareSlotOrbit
  rw [eraseRootNames_relabel he]

/-- The coarsening agrees exactly with applying the source's star convention
to the actual cut forest and then renaming its old roots. -/
theorem slotStarForest_actual (s : State) (a : ℕ) :
    slotStarForest (cutRoots s a).card (slotForest s a) =
      (starForest s a).relabel (rootNormalizer a (cutRoots s a)) := by
  let e := rootNormalizer a (cutRoots s a)
  have hroots : (cutRoots s a).image e = Finset.range (cutRoots s a).card :=
    rootNormalizer_image a (cutRoots s a) (fun r hr => ((mem_cutRoots s a r).mp hr).2)
  apply State.ext_data
  · rfl
  · change s.active.image e ∪ Finset.range (cutRoots s a).card = (s.active ∪ cutRoots s a).image e
    rw [Finset.image_union, hroots]
  · rfl
  · rfl
  · rfl
  · funext v
    have hmem : e.symm v ∈ cutRoots s a ↔ v < (cutRoots s a).card := by
      rw [← Finset.mem_range, ← hroots]
      simp only [Finset.mem_image]
      constructor
      · intro hv
        exact ⟨e.symm v, hv, e.apply_symm_apply v⟩
      · rintro ⟨r, hr, hrv⟩
        simpa only [← hrv, Equiv.symm_apply_apply] using hr
    change (if v < (cutRoots s a).card then none else (forestCut s a).frozenAt (e.symm v)) =
      if e.symm v ∈ cutRoots s a then none else (forestCut s a).frozenAt (e.symm v)
    simp only [hmem]

/-- The source's complete bare forest, after erasing old names and clocks,
is independent of the entire past tree under the actual law. -/
theorem indepFun_prefix_bareForest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun t => truncateAt t a)
      (fun t => bareSlotOrbit (activeCount x a).toNat (slotForest t a)) (treeLaw x b) := by
  have hh := (indepFun_prefix_slotForest x hab hb).comp (φ := fun q : State => q)
    (ψ := bareSlotOrbit (activeCount x a).toNat) measurable_id measurable_from_top
  simpa only [Function.comp_def] using hh

end Freezing1.Forward
