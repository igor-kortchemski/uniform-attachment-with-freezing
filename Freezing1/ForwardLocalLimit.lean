module

public import Freezing1.ForwardLocalStability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The measurable local limit on the genuine infinite trajectory

Coordinate stabilization produces a coherent locally finite tree. The
resulting limit is almost everywhere measurable and its law is the weak
limit of the actual finite tree laws. Values on exceptional trajectories
are assigned the initial tree.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology Classical

namespace LocalTree

theorem exists_limit_of_balls_stabilize (T : ℕ → Tree)
    (hs : ∀ h, ∃ a, ∀ n ≥ a, (T n).val h = (T a).val h) :
    ∃ t : Tree, Tendsto T atTop (𝓝 t) := by
  choose a ha using hs
  let B : ℕ → Ball := fun h => (T (a h)).val h
  have hB : ValidSequence B := by
    intro h
    refine ⟨(T (a h)).property h |>.1, ?_⟩
    let n := max (a h) (a (h + 1))
    have hh := ha h n (le_max_left _ _)
    have hh' := ha (h + 1) n (le_max_right _ _)
    change restrict h ((T (a (h + 1))).val (h + 1)) = (T (a h)).val h
    rw [← hh', ← hh]
    exact (T n).property h |>.2
  refine ⟨⟨B, hB⟩, (tendsto_iff_balls _ _).mpr ?_⟩
  intro h
  exact eventually_atTop.mpr ⟨a h, ha h⟩

end LocalTree

namespace ForwardInfiniteHistory

open Forward

theorem measurable_localTree_eval (n : ℕ) :
    Measurable (fun H : History => localTreeOfState (H n)) :=
  (show Measurable localTreeOfState from measurable_from_top).comp (measurable_pi_apply n)

noncomputable def localLimit (H : History) : LocalTree.Tree :=
  if h : ∃ t : LocalTree.Tree,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)
  then h.choose else localTreeOfState initial

theorem tendsto_localLimit_of_exists {H : History}
    (h : ∃ t : LocalTree.Tree, Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) :
    Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  simp only [localLimit, dite_eq_left h]
  exact h.choose_spec

theorem fullLaw_tendsto_localLimit (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x)) :
    ∀ᵐ H ∂fullLaw x,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  filter_upwards [fullLaw_valid x, fullLaw_all_balls_stabilize x hτ hdiv]
    with H hv hs
  apply tendsto_localLimit_of_exists
  apply LocalTree.exists_limit_of_balls_stabilize
  intro h
  obtain ⟨a, ha⟩ := hs h
  refine ⟨a, fun n hn => ?_⟩
  simp only [(hv n).localTreeOfState_balls, (hv a).localTreeOfState_balls]
  exact ha n hn

theorem aemeasurable_localLimit_of_ae_tendsto (x : SignSequence)
    (hc : ∀ᵐ H ∂fullLaw x,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H))) :
    AEMeasurable localLimit (fullLaw x) :=
  aemeasurable_of_tendsto_metrizable_ae'
    (fun n => (measurable_localTree_eval n).aemeasurable)
    hc

theorem aemeasurable_localLimit (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x)) :
    AEMeasurable localLimit (fullLaw x) :=
  aemeasurable_localLimit_of_ae_tendsto x (fullLaw_tendsto_localLimit x hτ hdiv)

noncomputable def localLimitLaw (x : SignSequence) : ProbabilityMeasure LocalTree.Tree :=
  ProbabilityMeasure.map (⟨fullLaw x, inferInstance⟩ : ProbabilityMeasure History) localLimit

noncomputable def localProbabilityLaw (x : SignSequence) (n : ℕ) :
    ProbabilityMeasure LocalTree.Tree := ⟨localTreeLaw x n, inferInstance⟩

theorem map_eval_localTree (x : SignSequence) (n : ℕ) :
    (fullLaw x).map (fun H : History => localTreeOfState (H n)) = localTreeLaw x n := by
  rw [localTreeLaw, ← map_eval x n, Measure.map_map measurable_from_top (measurable_pi_apply n)]
  rfl

theorem tendsto_localProbabilityLaw_of_ae_tendsto (x : SignSequence)
    (hc : ∀ᵐ H ∂fullLaw x,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H))) :
    Tendsto (localProbabilityLaw x) atTop (𝓝 (localLimitLaw x)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hlim := tendsto_integral_filter_of_norm_le_const (μ := fullLaw x)
    (F := fun n H => f (localTreeOfState (H n))) (f := fun H => f (localLimit H))
    (Eventually.of_forall fun n =>
      (f.continuous.measurable.comp (measurable_localTree_eval n)).aestronglyMeasurable)
    ⟨‖f‖, Eventually.of_forall fun _ => Eventually.of_forall fun H => f.norm_coe_le_norm _⟩
    (hc.mono fun H hH =>
      (f.continuous.tendsto _).comp hH)
  have hleft : ∀ n, (∫ t, f t ∂(localProbabilityLaw x n : Measure LocalTree.Tree)) =
      ∫ H, f (localTreeOfState (H n)) ∂fullLaw x := by
    intro n
    change (∫ t, f t ∂localTreeLaw x n) = _
    rw [← map_eval_localTree]
    exact integral_map (measurable_localTree_eval n).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  have hright : (∫ t, f t ∂(localLimitLaw x : Measure LocalTree.Tree)) =
      ∫ H, f (localLimit H) ∂fullLaw x :=
    integral_map (aemeasurable_localLimit_of_ae_tendsto x hc)
      f.continuous.measurable.aestronglyMeasurable
  simpa only [hleft, hright] using hlim

theorem tendsto_localProbabilityLaw_of_ae_exists (x : SignSequence)
    (hc : ∀ᵐ H ∂fullLaw x, ∃ t : LocalTree.Tree,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)) :
    Tendsto (localProbabilityLaw x) atTop (𝓝 (localLimitLaw x)) :=
  tendsto_localProbabilityLaw_of_ae_tendsto x
    (hc.mono fun _ hH => tendsto_localLimit_of_exists hH)

theorem tendsto_localProbabilityLaw (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x)) :
    Tendsto (localProbabilityLaw x) atTop (𝓝 (localLimitLaw x)) :=
  tendsto_localProbabilityLaw_of_ae_tendsto x (fullLaw_tendsto_localLimit x hτ hdiv)

end ForwardInfiniteHistory
end Freezing1
