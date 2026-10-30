module

public import Freezing1.ForwardForestCutLaw
public import Freezing1.ForwardForestRelabel
public import Freezing1.FiniteRootSlots
public import Mathlib.Probability.Independence.Basic

/-!
# The full forest in anonymous old-root slots

Only old root IDs are replaced, by canonical slots. Every future edge/birth
ID and freezing time stays unchanged. The resulting full forest has a law
depending only on the deterministic population at the cut, and its joint law
with the whole earlier tree is a product. Further erasure of slot names is
needed for the source's conditional uniform matching formulation.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem relabel_forestInitial (e : Equiv.Perm ℕ) (roots : Finset ℕ) :
    (forestInitial roots).relabel e = forestInitial (roots.image e) := by
  apply State.ext_data
  · rfl
  · rfl
  · ext u v
    simp [State.relabel, forestInitial]
  · funext v
    simp [State.relabel, forestInitial]
  · rfl
  · rfl

noncomputable def rootNormalizer (a : ℕ) (roots : Finset ℕ) : Equiv.Perm ℕ :=
  Classical.choose (exists_canonical_root_relabel a (roots.filter fun r => r ≤ a)
    (fun _ hr => (Finset.mem_filter.mp hr).2))

theorem rootNormalizer_future (a : ℕ) (roots : Finset ℕ) (t : ℕ) (ht : a < t) :
    rootNormalizer a roots t = t :=
  (Classical.choose_spec (exists_canonical_root_relabel a (roots.filter fun r => r ≤ a)
    (fun _ hr => (Finset.mem_filter.mp hr).2))).2 t ht

theorem rootNormalizer_image (a : ℕ) (roots : Finset ℕ) (hb : ∀ r ∈ roots, r ≤ a) :
    roots.image (rootNormalizer a roots) = Finset.range roots.card := by
  have hh := (Classical.choose_spec (exists_canonical_root_relabel a (roots.filter fun r => r ≤ a)
    (fun _ hr => (Finset.mem_filter.mp hr).2))).1
  have he : roots.filter (fun r => r ≤ a) = roots := Finset.filter_eq_self.mpr hb
  unfold rootNormalizer
  simpa only [he] using hh

noncomputable def slotForest (s : State) (a : ℕ) : State :=
  (forestCut s a).relabel (rootNormalizer a (cutRoots s a))

noncomputable def forestSlotLaw (x : SignSequence) (a k m : ℕ) : Measure State :=
  continuationLaw x a k (forestInitial (Finset.range m))

instance forestSlotLaw_probability (x : SignSequence) (a k m : ℕ) :
    IsProbabilityMeasure (forestSlotLaw x a k m) := by
  unfold forestSlotLaw
  infer_instance

theorem continuationLaw_slotForest {x : SignSequence} {a k : ℕ} {s : State}
    (hs : HasHistory x a s) (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    (continuationLaw x a k s).map (fun t => slotForest t a) =
      forestSlotLaw x a k s.active.card := by
  have hroots : ∀ᵐ t ∂continuationLaw x a k s, cutRoots t a = s.active := by
    filter_upwards [continuationLaw_truncate_self hs hτ] with t ht
    exact congrArg State.active ht
  calc
    _ = (continuationLaw x a k s).map
        (fun t => (forestCut t a).relabel (rootNormalizer a s.active)) := by
      apply Measure.map_congr
      filter_upwards [hroots] with t ht
      simp only [slotForest, ht]
    _ = ((continuationLaw x a k s).map (fun t => forestCut t a)).map
        (State.relabel (rootNormalizer a s.active)) := by
      rw [Measure.map_map measurable_from_top measurable_from_top]
      rfl
    _ = _ := by
      rw [continuationLaw_forestCut_at_cut hs.current hτ,
        map_continuationLaw_relabel x a k _ _ (rootNormalizer_future a s.active),
        relabel_forestInitial,
        rootNormalizer_image a s.active (fun r hr => hs.current.valid.vertices_le r
          (hs.current.valid.active_subset hr))]
      rfl

/-- Exact full-prefix/full-forest product law under the original tree law. -/
theorem treeLaw_prefix_slotForest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    (treeLaw x b).map (fun t => (truncateAt t a, slotForest t a)) =
      (treeLaw x a).prod (forestSlotLaw x a (b - a) (activeCount x a).toNat) := by
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  rw [Measure.prod_eq_of_sfinite]
  calc
    _ = ((treeLaw x a).bind (continuationLaw x a (b - a))).map
        (fun t => (truncateAt t a, slotForest t a)) := by
      rw [← treeLaw_add_eq_bind_continuation, he]
    _ = (treeLaw x a).bind (fun s =>
        (continuationLaw x a (b - a) s).map (fun t => (truncateAt t a, slotForest t a))) := by
      rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    _ = _ := by
      apply Measure.bind_congr_right
      filter_upwards [treeLaw_hasHistory x a haτ] with s hs
      have hcard : s.active.card = (activeCount x a).toNat := by
        have hh := congrArg Int.toNat hs.current.count
        simpa only [Int.toNat_natCast] using hh
      calc
        _ = (continuationLaw x a (b - a) s).map (fun t => (s, slotForest t a)) := by
          apply Measure.map_congr
          filter_upwards [continuationLaw_truncate_self hs hτ] with t ht
          rw [ht]
        _ = ((continuationLaw x a (b - a) s).map (fun t => slotForest t a)).map (Prod.mk s) := by
          rw [Measure.map_map measurable_from_top measurable_from_top]
          rfl
        _ = _ := by rw [continuationLaw_slotForest hs hτ, hcard]

theorem treeLaw_slotForest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    (treeLaw x b).map (fun t => slotForest t a) =
      forestSlotLaw x a (b - a) (activeCount x a).toNat := by
  have hh := congrArg (fun μ : Measure (State × State) => μ.map Prod.snd)
    (treeLaw_prefix_slotForest x hab hb)
  rw [Measure.map_map measurable_snd measurable_from_top, Measure.map_snd_prod, measure_univ, one_smul] at hh
  exact hh

/-- A47/A51 independence of the whole anonymously coded forest, not merely
the already identified pair of block statistics. -/
theorem indepFun_prefix_slotForest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun t => truncateAt t a) (fun t => slotForest t a) (treeLaw x b) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable).mpr
  rw [treeLaw_prefix_slotForest x hab hb, treeLaw_slotForest x hab hb]
  congr 1
  have hh := congrArg (fun μ : Measure (State × State) => μ.map Prod.fst)
    (treeLaw_prefix_slotForest x hab hb)
  rw [Measure.map_map measurable_fst measurable_from_top, Measure.map_fst_prod, measure_univ, one_smul] at hh
  exact hh.symm

theorem forestSlotLaw_relabel_invariant (x : SignSequence) (a k m : ℕ)
    (e : Equiv.Perm ℕ) (he : ∀ t : ℕ, a < t → e t = t)
    (hroots : (Finset.range m).image e = Finset.range m) :
    (forestSlotLaw x a k m).map (State.relabel e) = forestSlotLaw x a k m := by
  rw [forestSlotLaw, map_continuationLaw_relabel x a k e _ he, relabel_forestInitial, hroots]

end Freezing1.Forward
