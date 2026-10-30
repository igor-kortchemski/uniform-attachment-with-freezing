module

public import Freezing1.ForwardDegreeBounds
public import Freezing1.ForwardLifetimeCriterion
public import Freezing1.AttachmentReciprocalSeries

/-!
# The root-degree obstruction to local convergence

The joint probability of continued activity and bounded degree vanishes.
When the freezing reciprocal series converges, root activity has a strictly
positive limit, so the actual marginal degree laws are not tight. This
argument uses finite-horizon laws and does not assume an infinite coupling.
-/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Topology BigOperators ENNReal Classical

theorem treeLaw_active_bounded_degree_tendsto_zero (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (d : ℕ) :
    Tendsto (fun n => (treeLaw x n).real {s | 0 ∈ s.active ∧ rootDegree s ≤ d})
      atTop (𝓝 0) := by
  have hγ : 0 < 1 - Real.exp (-1) := by
    have hh : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  have hscaled := (tendsto_sum_attachmentHazard_atTop x hτ).const_mul_atTop hγ
  have hneg := tendsto_neg_atTop_atBot.comp hscaled
  change Tendsto (fun n => -((1 - Real.exp (-1)) *
    ∑ i ∈ Finset.range n, attachmentHazard x i)) atTop atBot at hneg
  have harg : Tendsto (fun n => (d : ℝ) + (Real.exp (-1) - 1) *
      ∑ i ∈ Finset.range n, attachmentHazard x i) atTop atBot := by
    have hh := (tendsto_const_nhds (x := (d : ℝ))).add_atBot hneg
    convert hh using 1
    funext n
    ring
  have he := Real.tendsto_exp_atBot.comp harg
  simp only [Function.comp_def] at he
  apply squeeze_zero (fun _ => measureReal_nonneg) _ he
  intro n
  simpa only [one_mul, attachmentHazard] using
    treeLaw_active_bounded_degree_le x n d (by simp [hτ]) (θ := 1) (by norm_num)

theorem treeLaw_active_bounded_degree_tendsto_zero_ennreal (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (d : ℕ) :
    Tendsto (fun n => (treeLaw x n) {s | 0 ∈ s.active ∧ rootDegree s ≤ d})
      atTop (𝓝 0) :=
  (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp
    (treeLaw_active_bounded_degree_tendsto_zero x hτ d)

theorem treeLaw_root_survival_tendsto_of_summable (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hs : Summable (printedFreezingReciprocal x)) :
    Tendsto (fun n => (treeLaw x n).real {s | 0 ∈ s.active}) atTop
      (𝓝 (Real.exp (∑' i, Real.log (1 - freezingHazard x i)))) := by
  have hh := tendsto_survivalProduct_of_summable (freezingHazard_lt_one x hτ)
    ((summable_freezingHazard_iff x hτ).mpr hs)
  convert hh using 1
  funext n
  rw [treeLaw_root_survival_product x n (by simp [hτ])]
  simpa only [Nat.zero_add, Nat.Ico_zero_eq_range] using vertexSurvivalFactor_product x 0 n

/-- A convergent freezing series leaves a uniform positive amount of mass
above every fixed degree threshold, eventually in time. -/
theorem rootDegree_not_tight_of_summable_freezing (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hs : Summable (printedFreezingReciprocal x)) :
    ∃ δ > 0, ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (treeLaw x n).real {s | d < rootDegree s} := by
  let p := Real.exp (∑' i, Real.log (1 - freezingHazard x i))
  have hp : 0 < p := Real.exp_pos _
  refine ⟨p / 2, by positivity, ?_⟩
  intro d
  have hh := (treeLaw_root_survival_tendsto_of_summable x hτ hs).sub
    (treeLaw_active_bounded_degree_tendsto_zero x hτ d)
  simp only [sub_zero] at hh
  filter_upwards [hh.eventually (lt_mem_nhds (show p / 2 < p by linarith))] with n hn
  have hsub : {s : State | 0 ∈ s.active} ⊆
      {s | d < rootDegree s} ∪ {s | 0 ∈ s.active ∧ rootDegree s ≤ d} := by
    intro s hs
    by_cases hd : d < rootDegree s
    · exact Or.inl hd
    · exact Or.inr ⟨hs, Nat.le_of_not_gt hd⟩
  have hbound := (measureReal_mono hsub (measure_ne_top (treeLaw x n) _)).trans
    (measureReal_union_le _ _)
  linarith

end Freezing1.Forward
