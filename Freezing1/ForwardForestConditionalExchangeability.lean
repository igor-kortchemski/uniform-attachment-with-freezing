module

public import Freezing1.ForwardForestRematchingAction
public import Freezing1.ConditionalInvariantAverage

/-! Actual conditional exchangeability under every lower-root bijection. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Relabelling the future subtrees by a fixed permutation of the lower
active roots preserves every conditional integrable observation given the
whole earlier tree. The root action is the supported actual reconstruction,
not a hypothetical independently sampled family of component trees. -/
theorem condExp_rematchState_given_prefix (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) {f : State → ℝ}
    (hf : Integrable f (treeLaw x b)) :
    (treeLaw x b)[(fun q => f (rematchState x a b σ q)) |
      MeasurableSpace.comap (fun q => truncateAt q a) inferInstance] =ᵐ[treeLaw x b]
      (treeLaw x b)[f | MeasurableSpace.comap (fun q => truncateAt q a) inferInstance] := by
  apply condExp_comp_of_preserving_observation (show Measurable (fun q => truncateAt q a) from measurable_from_top)
    (show MeasurePreserving (rematchState x a b σ) (treeLaw x b) (treeLaw x b) from
      ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩) _ hf
  exact (rematchState_ae_spec x hab hb σ).mono fun _ hq => hq.2.1

/-- Conditional exchangeability remains valid after observing the complete
unlabelled bare forest as well as the earlier tree. -/
theorem condExp_rematchState_given_past_forest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) {f : State → ℝ}
    (hf : Integrable f (treeLaw x b)) :
    (treeLaw x b)[(fun q => f (rematchState x a b σ q)) |
      MeasurableSpace.comap (pastBareForest x a) inferInstance] =ᵐ[treeLaw x b]
      (treeLaw x b)[f | MeasurableSpace.comap (pastBareForest x a) inferInstance] :=
  condExp_comp_of_preserving_observation measurable_from_top
    ⟨measurable_from_top, map_treeLaw_rematchState x hab hb σ⟩
    (pastBareForest_rematchState x hab hb σ) hf

theorem condExp_rematching_event_given_prefix (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (σ : Equiv.Perm (Fin (activeCount x a).toNat)) (A : Set State) :
    (treeLaw x b)[(fun q => if rematchState x a b σ q ∈ A then (1 : ℝ) else 0) |
      MeasurableSpace.comap (fun q => truncateAt q a) inferInstance] =ᵐ[treeLaw x b]
      (treeLaw x b)[(fun q => if q ∈ A then (1 : ℝ) else 0) |
        MeasurableSpace.comap (fun q => truncateAt q a) inferInstance] := by
  apply condExp_rematchState_given_prefix x hab hb σ
    (f := fun q => if q ∈ A then (1 : ℝ) else 0)
  apply Integrable.of_bound measurable_from_top.aestronglyMeasurable 1
  exact ae_of_all _ (fun q => by split_ifs <;> norm_num)

end Freezing1.Forward
