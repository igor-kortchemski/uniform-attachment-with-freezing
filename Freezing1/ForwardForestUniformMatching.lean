module

public import Freezing1.ForwardForestRootOrbit
public import Freezing1.ForwardForestReconstruction

/-!
# Exact independent uniform matching of the complete augmented forest

The earlier tree, a fresh anonymous forest, and a true uniform permutation
are sampled by explicit original laws. The joint identity retains the erased
forest and the complete terminal state. Compatibility is supplied by the
actual forest-law bridge and reconstruction theorem, not assumed.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def reconstructSlotForest (x : SignSequence) (a b : ℕ) (past F : State) : State :=
  reconstructForest x a b past (F.relabel (rootNormalizer a past.active).symm)

theorem reconstructSlotForest_actual {x : SignSequence} {a b : ℕ} {s : State}
    (hs : HasHistory x b s) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    reconstructSlotForest x a b (truncateAt s a) (slotForest s a) = s := by
  unfold reconstructSlotForest slotForest
  change reconstructForest x a b (truncateAt s a)
    (((forestCut s a).relabel (rootNormalizer a (cutRoots s a))).relabel
      (rootNormalizer a (cutRoots s a)).symm) = s
  rw [State.relabel_trans, Equiv.self_trans_symm, State.relabel_refl]
  exact reconstructForest_actual hs hb

theorem treeLaw_prefix_erasedForest_terminal (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    let m := (activeCount x a).toNat
    (treeLaw x b).map (fun t => (truncateAt t a, eraseRootNames m (slotForest t a), t)) =
      (treeLaw x a).bind (fun past => (forestSlotLaw x a (b - a) m).map
        (fun F => (past, eraseRootNames m F, reconstructSlotForest x a b past F))) := by
  dsimp only
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  calc
    _ = ((treeLaw x a).bind (continuationLaw x a (b - a))).map
        (fun t => (truncateAt t a, eraseRootNames (activeCount x a).toNat (slotForest t a), t)) := by
      rw [← treeLaw_add_eq_bind_continuation, he]
    _ = (treeLaw x a).bind (fun past => (continuationLaw x a (b - a) past).map
        (fun t => (truncateAt t a, eraseRootNames (activeCount x a).toNat (slotForest t a), t))) := by
      rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    _ = _ := by
      apply Measure.bind_congr_right
      filter_upwards [treeLaw_hasHistory x a haτ] with past hpast
      have hcard : past.active.card = (activeCount x a).toNat := by
        have hh := congrArg Int.toNat hpast.current.count
        simpa only [Int.toNat_natCast] using hh
      calc
        _ = (continuationLaw x a (b - a) past).map (fun t =>
            (past, eraseRootNames (activeCount x a).toNat (slotForest t a),
              reconstructSlotForest x a b past (slotForest t a))) := by
          apply Measure.map_congr
          filter_upwards [continuationLaw_truncate_self hpast hτ,
            continuationLaw_hasHistory hpast hτ] with t ht hs
          have hsb : HasHistory x b t := by simpa only [he] using hs
          rw [← ht, reconstructSlotForest_actual hsb hb]
        _ = ((continuationLaw x a (b - a) past).map (fun t => slotForest t a)).map
            (fun F => (past, eraseRootNames (activeCount x a).toNat F, reconstructSlotForest x a b past F)) := by
          rw [Measure.map_map measurable_from_top measurable_from_top]
          rfl
        _ = _ := by rw [continuationLaw_slotForest hpast hτ, hcard]

/-- The genuine full terminal state is reconstructed by an independent
uniform bijection of all old roots. The earlier tree is the lower-cut tree.
The augmented erased forest retains root freezing clocks; its source
all-star coarsening is handled separately. -/
theorem treeLaw_uniform_root_matching (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    let m := (activeCount x a).toNat
    (treeLaw x b).map (fun t => (truncateAt t a, eraseRootNames m (slotForest t a), t)) =
      (treeLaw x a).bind (fun past => (forestSlotLaw x a (b - a) m).bind
        (fun F => (uniformPermutationLaw (Fin m)).map
          (fun σ => (past, eraseRootNames m F,
            reconstructSlotForest x a b past (F.relabel (rootSlotPermutation m σ)))))) := by
  dsimp only
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hm : (activeCount x a).toNat ≤ a + 1 := by
    have hnon := activeCount_nonneg_of_le_extinctionTime haτ
    have hu := activeCount_le_plusCount_add_one x a
    have hp := plusCount_le x a
    omega
  rw [treeLaw_prefix_erasedForest_terminal x hab hb]
  apply Measure.bind_congr_right
  exact Eventually.of_forall (fun past => by
    dsimp only
    conv_lhs => rw [← forestSlotLaw_uniform_root_permutation x a (b - a) (activeCount x a).toNat hm]
    rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    congr 1
    funext F
    rw [Measure.map_map measurable_from_top measurable_from_top]
    congr 1
    funext σ
    dsimp only [Function.comp_def]
    rw [eraseRootNames_relabel (rootSlotPermutation_bounded _ σ)])

theorem indepFun_prefix_erasedForest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun t => truncateAt t a)
      (fun t => eraseRootNames (activeCount x a).toNat (slotForest t a)) (treeLaw x b) := by
  exact (indepFun_prefix_slotForest x hab hb).comp measurable_id measurable_from_top

end Freezing1.Forward
