module

public import Freezing1.PlaneGraftLimit
public import Freezing1.PlaneFirstStep
public import Freezing1.PlaneGeometricBienayme

/-!
# The Introduction's iid-sign geometric Bienaymé limit (T02)

The actual chronological plane-tree laws satisfy an exact first-step
mixture. The grafted chain converges to a graft of independent copies of
the same actual limit. Uniqueness of the weak limit yields the geometric
branching fixed point, including p=0 and finite extinction.
-/

@[expose] public section

namespace Freezing1.ForwardAnnealed

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable def leafProbabilityLaw : ProbabilityMeasure PlaneTree.Tree :=
  ⟨Measure.dirac PlaneTree.leaf, inferInstance⟩

theorem planeProbabilityLaw_succ_eq_mix (p : unitInterval) (n : ℕ) :
    planeProbabilityLaw p (n + 1) =
      probabilityMix p (PlaneForward.graftProbabilityLaw p n) leafProbabilityLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [planeProbabilityLaw_eq_chainShape, PlaneForward.firstStep_shapeLaw]
  rfl

theorem planeLimitLaw_eq_mix (p : unitInterval) (hp : (p : ℝ) < 1) :
    planeLimitLaw p = probabilityMix p (PlaneForward.graftLimitLaw p) leafProbabilityLaw := by
  have hactual := (tendsto_planeProbabilityLaw p hp).comp (tendsto_add_atTop_nat 1)
  have hmix := tendsto_probabilityMix p
    (PlaneForward.tendsto_graftProbabilityLaw p hp)
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => leafProbabilityLaw) atTop (𝓝 leafProbabilityLaw))
  apply tendsto_nhds_unique (f := fun n => probabilityMix p
    (PlaneForward.graftProbabilityLaw p n) leafProbabilityLaw) ?_ hmix
  simpa only [Function.comp_def, planeProbabilityLaw_succ_eq_mix] using hactual

theorem planeLimitLaw_fixedPoint (p : unitInterval) (hp : (p : ℝ) < 1) :
    (planeLimitLaw p : Measure PlaneTree.Tree) =
      ENNReal.ofReal (1 - (p : ℝ)) • Measure.dirac PlaneTree.leaf +
      ENNReal.ofReal (p : ℝ) •
        ((planeLimitLaw p : Measure PlaneTree.Tree).prod (planeLimitLaw p)).map
          (fun q => PlaneTree.graft q.1 q.2) := by
  have h := congrArg (fun μ : ProbabilityMeasure PlaneTree.Tree => (μ : Measure PlaneTree.Tree))
    (planeLimitLaw_eq_mix p hp)
  change (planeLimitLaw p : Measure PlaneTree.Tree) =
    unitInterval.toNNReal p • (PlaneForward.graftLimitLaw p : Measure PlaneTree.Tree) +
    unitInterval.toNNReal (unitInterval.symm p) • Measure.dirac PlaneTree.leaf at h
  rw [ENNReal.smul_def, ENNReal.smul_def,
    ← @ENNReal.ofReal_coe_nnreal (unitInterval.toNNReal p),
    ← @ENNReal.ofReal_coe_nnreal (unitInterval.toNNReal (unitInterval.symm p))] at h
  change (planeLimitLaw p : Measure PlaneTree.Tree) =
    ENNReal.ofReal (p : ℝ) •
      ((planeLimitLaw p : Measure PlaneTree.Tree).prod (planeLimitLaw p)).map
        (fun q => PlaneTree.graft q.1 q.2) +
    ENNReal.ofReal (1 - (p : ℝ)) • Measure.dirac PlaneTree.leaf at h
  rw [add_comm] at h
  exact h

theorem planeLimitLaw_isBienayme (p : unitInterval) (hp : (p : ℝ) < 1) :
    PlaneTree.IsBienayme (planeLimitLaw p) (geometricMeasure (unitInterval.symm p)) :=
  PlaneTree.isBienayme_geometric_of_fixedPoint p hp (planeLimitLaw p)
    (planeLimitLaw_fixedPoint p hp)

theorem planeLimitLaw_eq_geometricBienaymeLaw (p : unitInterval) (hp : (p : ℝ) < 1) :
    (planeLimitLaw p : Measure PlaneTree.Tree) = PlaneTree.geometricBienaymeLaw p :=
  (planeLimitLaw_isBienayme p hp).eq_bienaymeLaw

theorem planeLimitLaw_offspring_mass (p : unitInterval) (hp : (p : ℝ) < 1) (k : ℕ) :
    (planeLimitLaw p : Measure PlaneTree.Tree) {T | PlaneTree.degree T = k} =
      ENNReal.ofReal ((1 - (p : ℝ)) * (p : ℝ) ^ k) := by
  have h := PlaneTree.firstChildStructure.degree_measure_of_fixedPoint
    (planeLimitLaw p : Measure PlaneTree.Tree)
    (ENNReal.ofReal (1 - (p : ℝ))) (ENNReal.ofReal (p : ℝ))
    (planeLimitLaw_fixedPoint p hp) k
  change (planeLimitLaw p : Measure PlaneTree.Tree) {T | PlaneTree.degree T = k} =
    ENNReal.ofReal (1 - (p : ℝ)) * ENNReal.ofReal (p : ℝ) ^ k at h
  rw [h, ← ENNReal.ofReal_pow p.2.1,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr p.2.2)]

/-- T02 for the actual iid-sign process, with the source's chronological
ordering and the measurable pathwise limit on its genuine probability space. -/
theorem iid_signs_geometric_local_limit (p : unitInterval) (hp : (p : ℝ) < 1) :
    (∀ᵐ H ∂fullLaw p,
      Tendsto (fun n => LocalTree.toPlaneTree (Forward.localTreeOfState (H n))) atTop
        (𝓝 (planeLimit H))) ∧
      (fullLaw p).map planeLimit = PlaneTree.geometricBienaymeLaw p := by
  refine ⟨fullLaw_tendsto_planeLimit p hp, ?_⟩
  rw [← planeLimitLaw_eq_map p hp, planeLimitLaw_eq_geometricBienaymeLaw p hp]

end Freezing1.ForwardAnnealed
