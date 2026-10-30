module

public import Freezing1.ForwardForestUniformMatching
public import Freezing1.ForwardForestStarOrbit
public import Freezing1.UniformPairDistance

/-! Genuine measure-preserving root-rematching actions on actual terminal trees. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

def CompatibleSlotForest (x : SignSequence) (a b : ℕ) (past F : State) : Prop :=
  CompatibleForest x a b past (F.relabel (rootNormalizer a past.active).symm)

theorem unslot_slotForest (s : State) (a : ℕ) :
    (slotForest s a).relabel (rootNormalizer a (truncateAt s a).active).symm = forestCut s a := by
  change ((forestCut s a).relabel (rootNormalizer a (cutRoots s a))).relabel
    (rootNormalizer a (cutRoots s a)).symm = _
  rw [State.relabel_trans, Equiv.self_trans_symm, State.relabel_refl]

theorem compatibleSlotForest_actual {x : SignSequence} {a b : ℕ} {s : State}
    (hs : HasHistory x b s) : CompatibleSlotForest x a b (truncateAt s a) (slotForest s a) :=
  ⟨s, hs, rfl, (unslot_slotForest s a).symm⟩

theorem reconstructSlotForest_spec {x : SignSequence} {a b : ℕ} {past F : State}
    (hc : CompatibleSlotForest x a b past F) :
    HasHistory x b (reconstructSlotForest x a b past F) ∧
      truncateAt (reconstructSlotForest x a b past F) a = past ∧
      slotForest (reconstructSlotForest x a b past F) a = F := by
  have hh := reconstructForest_spec hc
  refine ⟨hh.1, hh.2.1, ?_⟩
  have hroots : cutRoots (reconstructSlotForest x a b past F) a = past.active :=
    congrArg State.active hh.2.1
  have hcut : forestCut (reconstructSlotForest x a b past F) a =
      F.relabel (rootNormalizer a past.active).symm := hh.2.2
  unfold slotForest
  rw [hroots, hcut, State.relabel_trans, Equiv.symm_trans_self, State.relabel_refl]

theorem forestSlotLaw_ae_compatible {x : SignSequence} {a k : ℕ} {past : State}
    (hpast : HasHistory x a past) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) :
    ∀ᵐ F ∂forestSlotLaw x a k past.active.card, CompatibleSlotForest x a (a + k) past F := by
  rw [← continuationLaw_slotForest hpast hn]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [continuationLaw_hasHistory hpast hn, continuationLaw_truncate_self hpast hn]
    with q hq hprefix
  rw [← hprefix]
  exact compatibleSlotForest_actual hq

theorem active_card_le_time_succ {a : ℕ} {past : State} (hpast : ValidAt a past) :
    past.active.card ≤ a + 1 := by
  have hsub : past.active ⊆ Finset.range (a + 1) := by
    intro r hr
    exact Finset.mem_range.mpr (by have := hpast.vertices_le r (hpast.active_subset hr); omega)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

theorem forestSlotLaw_ae_compatible_permuted {x : SignSequence} {a k m : ℕ} {past : State}
    (hpast : HasHistory x a past) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    (hcard : past.active.card = m) (σ : Equiv.Perm (Fin m)) :
    ∀ᵐ F ∂forestSlotLaw x a k m,
      CompatibleSlotForest x a (a + k) past (F.relabel (rootSlotPermutation m σ)) := by
  have hm : m ≤ a + 1 := by rw [← hcard]; exact active_card_le_time_succ hpast.current.valid
  have hc : ∀ᵐ F ∂forestSlotLaw x a k m, CompatibleSlotForest x a (a + k) past F := by
    rw [← hcard]
    exact forestSlotLaw_ae_compatible hpast hn
  have hh : ∀ᵐ F ∂(forestSlotLaw x a k m).map (State.relabel (rootSlotPermutation m σ)),
      CompatibleSlotForest x a (a + k) past F := by
    rw [forestSlotLaw_root_permutation x a k m hm]
    exact hc
  exact (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mp hh

theorem forestSlotLaw_map_reconstruct {x : SignSequence} {a k m : ℕ} {past : State}
    (hpast : HasHistory x a past) (hn : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x)
    (hcard : past.active.card = m) :
    (forestSlotLaw x a k m).map (reconstructSlotForest x a (a + k) past) =
      continuationLaw x a k past := by
  rw [← hcard, ← continuationLaw_slotForest hpast hn,
    Measure.map_map measurable_from_top measurable_from_top]
  calc
    _ = (continuationLaw x a k past).map id := by
      apply Measure.map_congr
      filter_upwards [continuationLaw_hasHistory hpast hn, continuationLaw_truncate_self hpast hn]
        with q hq hprefix
      dsimp only [Function.comp_def]
      rw [← hprefix, reconstructSlotForest_actual hq hn]
      rfl
    _ = _ := Measure.map_id

noncomputable def rematchState (x : SignSequence) (a b : ℕ)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) (s : State) : State :=
  reconstructSlotForest x a b (truncateAt s a)
    ((slotForest s a).relabel (rootSlotPermutation (activeCount x a).toNat σ))

/-- Every fixed rematching is characterized on actual supported terminal
states, including preservation of the whole earlier tree and the full forest. -/
theorem rematchState_ae_spec (x : SignSequence) {a b : ℕ} (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
    ∀ᵐ q ∂treeLaw x b, HasHistory x b (rematchState x a b σ q) ∧
      truncateAt (rematchState x a b σ q) a = truncateAt q a ∧
      slotForest (rematchState x a b σ q) a =
        (slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ) := by
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hn : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  have hμ : treeLaw x b = (treeLaw x a).bind (continuationLaw x a (b - a)) := by
    rw [← treeLaw_add_eq_bind_continuation, he]
  rw [hμ]
  apply ae_bind_of_ae measurable_from_top.aemeasurable (by trivial)
  filter_upwards [treeLaw_hasHistory x a haτ] with past hpast
  have hcard : past.active.card = (activeCount x a).toNat := by
    have hh := congrArg Int.toNat hpast.current.count
    simpa only [Int.toNat_natCast] using hh
  have hc : ∀ᵐ q ∂continuationLaw x a (b - a) past,
      CompatibleSlotForest x a (a + (b - a)) past
        ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ)) := by
    have hh := forestSlotLaw_ae_compatible_permuted hpast hn hcard σ
    have hslot := continuationLaw_slotForest hpast hn
    rw [hcard] at hslot
    rw [← hslot] at hh
    have hmeas : AEMeasurable (fun q : State => slotForest q a)
        (continuationLaw x a (b - a) past) := measurable_from_top.aemeasurable
    exact (ae_map_iff hmeas (p := fun F : State => CompatibleSlotForest x a (a + (b - a)) past
      (F.relabel (rootSlotPermutation (activeCount x a).toNat σ))) (by trivial)).mp hh
  filter_upwards [hc, continuationLaw_truncate_self hpast hn] with q hq hprefix
  have hq' : CompatibleSlotForest x a b past
      ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ)) := by
    simpa only [he] using hq
  dsimp only [rematchState]
  rw [hprefix]
  exact reconstructSlotForest_spec hq'

/-- The actual terminal law is preserved by each fixed root bijection. -/
theorem map_treeLaw_rematchState (x : SignSequence) {a b : ℕ} (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
    (treeLaw x b).map (rematchState x a b σ) = treeLaw x b := by
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hn : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  calc
    _ = ((treeLaw x a).bind (continuationLaw x a (b - a))).map (rematchState x a b σ) := by
      rw [← treeLaw_add_eq_bind_continuation, he]
    _ = (treeLaw x a).bind (fun past => (continuationLaw x a (b - a) past).map
        (rematchState x a b σ)) := by
      rw [Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    _ = (treeLaw x a).bind (continuationLaw x a (b - a)) := by
      apply Measure.bind_congr_right
      filter_upwards [treeLaw_hasHistory x a haτ] with past hpast
      have hcard : past.active.card = (activeCount x a).toNat := by
        have hh := congrArg Int.toNat hpast.current.count
        simpa only [Int.toNat_natCast] using hh
      have hm := active_card_le_time_succ hpast.current.valid
      rw [hcard] at hm
      calc
        _ = (continuationLaw x a (b - a) past).map (fun q => reconstructSlotForest x a b past
            ((slotForest q a).relabel (rootSlotPermutation (activeCount x a).toNat σ))) := by
          apply Measure.map_congr
          filter_upwards [continuationLaw_truncate_self hpast hn] with q hq
          simp only [rematchState, hq]
        _ = ((forestSlotLaw x a (b - a) (activeCount x a).toNat).map
            (State.relabel (rootSlotPermutation (activeCount x a).toNat σ))).map
              (reconstructSlotForest x a b past) := by
          have hslot := continuationLaw_slotForest hpast hn
          rw [hcard] at hslot
          rw [← hslot,
            Measure.map_map measurable_from_top measurable_from_top,
            Measure.map_map measurable_from_top measurable_from_top]
          rfl
        _ = continuationLaw x a (b - a) past := by
          rw [forestSlotLaw_root_permutation x a (b - a) _ hm]
          simpa only [he] using forestSlotLaw_map_reconstruct hpast hn hcard
    _ = _ := by rw [← treeLaw_add_eq_bind_continuation, he]

noncomputable def pastBareForest (x : SignSequence) (a : ℕ) (q : State) :
    State × RootErasedForest (activeCount x a).toNat :=
  (truncateAt q a, bareSlotOrbit (activeCount x a).toNat (slotForest q a))

theorem pastBareForest_rematchState (x : SignSequence) {a b : ℕ} (hab : a ≤ b)
    (hb : (b : ℕ∞) ≤ extinctionTime x) (σ : Equiv.Perm (Fin (activeCount x a).toNat)) :
    (fun q => pastBareForest x a (rematchState x a b σ q)) =ᵐ[treeLaw x b] pastBareForest x a := by
  filter_upwards [rematchState_ae_spec x hab hb σ] with q hq
  unfold pastBareForest
  rw [hq.2.1, hq.2.2, bareSlotOrbit_relabel (rootSlotPermutation_bounded _ σ)]

end Freezing1.Forward
