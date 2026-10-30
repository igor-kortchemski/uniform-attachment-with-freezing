module

public import Freezing1.FiniteMultisetSampling
public import Freezing1.Path
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Root tags and heights in the actual active population

The abstract state is a multiset of pairs (initial root, block height), with
one occurrence for every active vertex. A uniform occurrence is selected;
attachment adds its child and freezing removes that occurrence. Empty states
are absorbing. The map from actual trees is established in a separate module.
-/

@[expose] public section

namespace Freezing1.TaggedPopulation

open MeasureTheory
open scoped Classical ENNReal

abbrev State := Multiset (ℕ × ℕ)

instance : MeasurableSpace State := ⊤

noncomputable def initial (roots : Finset ℕ) : State :=
  roots.val.map (fun r => (r, 0))

noncomputable def step (m : State) (sign : Bool) (v : ℕ × ℕ) : State :=
  if sign then (v.1, v.2 + 1) ::ₘ m else m.erase v

noncomputable def transitionLaw (m : State) (sign : Bool) : Measure State :=
  if m = 0 then Measure.dirac m else (multisetUniform m).map (step m sign)

instance transitionLaw_probability (m : State) (sign : Bool) :
    IsProbabilityMeasure (transitionLaw m sign) := by
  unfold transitionLaw
  split_ifs with hm
  · infer_instance
  · let : IsProbabilityMeasure (multisetUniform m) := multisetUniform_isProbabilityMeasure m hm
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr
      inferInstance

noncomputable def relabel (e : Equiv.Perm ℕ) (m : State) : State :=
  m.map (fun v => (e v.1, v.2))

@[simp] theorem relabel_card (e : Equiv.Perm ℕ) (m : State) :
    (relabel e m).card = m.card := Multiset.card_map _ _

@[simp] theorem relabel_eq_zero (e : Equiv.Perm ℕ) (m : State) :
    relabel e m = 0 ↔ m = 0 := Multiset.map_eq_zero

theorem relabel_step (e : Equiv.Perm ℕ) (m : State) (sign : Bool) (v : ℕ × ℕ) :
    relabel e (step m sign v) = step (relabel e m) sign (e v.1, v.2) := by
  cases sign
  · simp only [step, Bool.false_eq_true, ↓reduceIte, relabel]
    apply Multiset.map_erase
    intro u w he
    have h1 : e u.1 = e w.1 := congrArg Prod.fst he
    have h2 := congrArg (fun z : ℕ × ℕ => z.2) he
    exact Prod.ext (e.injective h1) h2
  · simp [step, relabel]

/-- Root relabeling commutes with the entire genuine occurrence-selection
kernel, including removals and repeated identical particles. -/
theorem map_transitionLaw_relabel (e : Equiv.Perm ℕ) (m : State) (sign : Bool) :
    (transitionLaw m sign).map (relabel e) = transitionLaw (relabel e m) sign := by
  by_cases hm : m = 0
  · subst m
    simp [transitionLaw, relabel]
  · have hme : relabel e m ≠ 0 := by simpa using hm
    simp only [transitionLaw, hm, hme, ite_false]
    rw [Measure.map_map measurable_from_top (measurable_of_countable _)]
    change (multisetUniform m).map (fun v => relabel e (step m sign v)) =
      (multisetUniform (m.map (fun v => (e v.1, v.2)))).map (step (relabel e m) sign)
    rw [← map_multisetUniform m (fun v => (e v.1, v.2)) (measurable_of_countable _),
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext v
    exact relabel_step e m sign v

noncomputable def continuationLaw (x : SignSequence) : ℕ → ℕ → State → Measure State
  | _, 0, m => Measure.dirac m
  | a, k + 1, m => (transitionLaw m (x (a + 1))).bind (continuationLaw x (a + 1) k)

instance continuationLaw_probability (x : SignSequence) (a k : ℕ) (m : State) :
    IsProbabilityMeasure (continuationLaw x a k m) := by
  induction k generalizing a m with
  | zero => change IsProbabilityMeasure (Measure.dirac m); infer_instance
  | succ k ih =>
    change IsProbabilityMeasure ((transitionLaw _ _).bind _)
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall fun t => ih (a + 1) t)

theorem map_continuationLaw_relabel (x : SignSequence) (a k : ℕ)
    (e : Equiv.Perm ℕ) (m : State) :
    (continuationLaw x a k m).map (relabel e) =
      continuationLaw x a k (relabel e m) := by
  induction k generalizing a m with
  | zero => simp [continuationLaw]
  | succ k ih =>
    rw [continuationLaw, Measure.map_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    calc
      _ = (transitionLaw m (x (a + 1))).bind
          (fun t => continuationLaw x (a + 1) k (relabel e t)) := by
        congr 1
        funext t
        exact ih (a + 1) t
      _ = ((transitionLaw m (x (a + 1))).map (relabel e)).bind
          (continuationLaw x (a + 1) k) := by
        rw [Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      _ = _ := by rw [map_transitionLaw_relabel, continuationLaw]

theorem relabel_initial (e : Equiv.Perm ℕ) (roots : Finset ℕ) :
    relabel e (initial roots) = initial (roots.image e) := by
  unfold relabel initial
  rw [Finset.image_val_of_injOn (e.injective.injOn), Multiset.map_map, Multiset.map_map]
  rfl

/-- The future tagged population is invariant under every permutation of
the initial root set. This is a proved kernel symmetry. -/
theorem continuationLaw_initial_invariant (x : SignSequence) (a k : ℕ)
    (roots : Finset ℕ) (e : Equiv.Perm ℕ) (he : roots.image e = roots) :
    (continuationLaw x a k (initial roots)).map (relabel e) =
      continuationLaw x a k (initial roots) := by
  rw [map_continuationLaw_relabel, relabel_initial, he]

end Freezing1.TaggedPopulation
