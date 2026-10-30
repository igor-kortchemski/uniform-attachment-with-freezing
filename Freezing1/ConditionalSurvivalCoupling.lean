module

public import Freezing1.ConditionalSurvivalCouplingMixture
public import Freezing1.ConditionalSurvivalCouplingUniform
public import Mathlib.Probability.Independence.InfinitePi

/-!
# One common coupling of all finite-survival conditional laws

Every conditional row has its exact law. All rows eventually equal the
same whole survivor path almost surely. No independence between rows is
asserted or required.
-/

@[expose] public section

namespace Freezing1.ConditionalSurvival

open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

structure System (Ω : Type*) [MeasurableSpace Ω] where
  law : Measure Ω
  probability : IsProbabilityMeasure law
  event : ℕ → Set Ω
  measurable : ∀ n, MeasurableSet (event n)
  antitone : Antitone event
  positive : law (⋂ j, event j) ≠ 0

variable {Ω : Type*} [MeasurableSpace Ω]

instance (D : System Ω) : IsProbabilityMeasure D.law := D.probability

noncomputable def System.survivorLaw (D : System Ω) : Measure Ω := D.law[|⋂ j, D.event j]

instance (D : System Ω) : IsProbabilityMeasure D.survivorLaw :=
  cond_isProbabilityMeasure D.positive

noncomputable def System.residualLaw (D : System Ω) (n : ℕ) : Measure Ω :=
  conditionalOr D.law (D.event n \ ⋂ j, D.event j) D.survivorLaw

instance (D : System Ω) (n : ℕ) : IsProbabilityMeasure (D.residualLaw n) := by
  unfold System.residualLaw
  infer_instance

abbrev Space (Ω : Type*) := ℝ × Ω × (ℕ → Ω)

noncomputable def System.couplingLaw (D : System Ω) : Measure (Space Ω) :=
  unitLaw.prod (D.survivorLaw.prod (Measure.infinitePi D.residualLaw))

instance (D : System Ω) : IsProbabilityMeasure D.couplingLaw := by
  unfold System.couplingLaw
  infer_instance

def System.survivor (_D : System Ω) (z : Space Ω) : Ω := z.2.1

noncomputable def System.row (D : System Ω) (n : ℕ) (z : Space Ω) : Ω :=
  if z.1 ≤ weight D.law D.event n then z.2.1 else z.2.2 n

theorem System.measurable_survivor (D : System Ω) : Measurable D.survivor :=
  measurable_fst.comp measurable_snd

theorem System.measurable_row (D : System Ω) (n : ℕ) : Measurable (D.row n) :=
  Measurable.ite (measurableSet_le measurable_fst measurable_const)
    (measurable_fst.comp measurable_snd)
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))

theorem System.map_survivor (D : System Ω) :
    D.couplingLaw.map D.survivor = D.survivorLaw := by
  have hs : HasLaw Prod.snd (D.survivorLaw.prod (Measure.infinitePi D.residualLaw))
      D.couplingLaw := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [System.couplingLaw, Measure.map_snd_prod, measure_univ, one_smul]
  have hb : HasLaw Prod.fst D.survivorLaw
      (D.survivorLaw.prod (Measure.infinitePi D.residualLaw)) := by
    refine ⟨measurable_fst.aemeasurable, ?_⟩
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact (hb.fun_comp hs).map_eq

theorem System.map_row (D : System Ω) (n : ℕ) :
    D.couplingLaw.map (D.row n) = D.law[|D.event n] := by
  have hcoord : (Measure.infinitePi D.residualLaw).map (fun z => z n) = D.residualLaw n :=
    (measurePreserving_eval_infinitePi D.residualLaw n).map_eq
  have hinner : (D.survivorLaw.prod (Measure.infinitePi D.residualLaw)).map
      (fun z => (z.1, z.2 n)) = D.survivorLaw.prod (D.residualLaw n) := by
    change (D.survivorLaw.prod (Measure.infinitePi D.residualLaw)).map
      (Prod.map id (fun z => z n)) = _
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_pi_apply n), Measure.map_id, hcoord]
  have hf : D.couplingLaw.map (fun z : Space Ω => (z.1, z.2.1, z.2.2 n)) =
      unitLaw.prod (D.survivorLaw.prod (D.residualLaw n)) := by
    change (unitLaw.prod (D.survivorLaw.prod (Measure.infinitePi D.residualLaw))).map
      (Prod.map id (fun z : Ω × (ℕ → Ω) => (z.1, z.2 n))) = _
    rw [← Measure.map_prod_map _ _ (f := id) (g := fun z : Ω × (ℕ → Ω) => (z.1, z.2 n))
      measurable_id
      (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd)),
      Measure.map_id, hinner]
  calc
    _ = (D.couplingLaw.map (fun z : Space Ω => (z.1, z.2.1, z.2.2 n))).map
        (chooseRow (weight D.law D.event n)) := by
      exact (Measure.map_map
        (f := fun z : Space Ω => (z.1, z.2.1, z.2.2 n))
        (g := chooseRow (weight D.law D.event n)) (measurable_chooseRow _)
        (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
          ((measurable_pi_apply n).comp (measurable_snd.comp measurable_snd))))).symm
    _ = ENNReal.ofReal (weight D.law D.event n) • D.survivorLaw +
        (1 - ENNReal.ofReal (weight D.law D.event n)) • D.residualLaw n := by
      rw [hf, map_chooseRow _ _ (weight_mem D.law D.event D.positive n).1
        (weight_mem D.law D.event D.positive n).2]
    _ = _ := by
      rw [← residual_weight D.law D.event D.measurable D.positive n,
        ofReal_weight D.law D.event D.positive n]
      exact (conditional_mixture D.law (MeasurableSet.iInter D.measurable)
        (iInter_subset D.event n) D.positive D.survivorLaw).symm

/-- The single uniform threshold makes every row eventually use the same
entire survivor sample, rather than only a common finite prefix. -/
theorem System.eventually_row_eq_survivor (D : System Ω) :
    ∀ᵐ z ∂D.couplingLaw, ∀ᶠ n in atTop, D.row n z = D.survivor z := by
  have hu : ∀ᵐ z ∂D.couplingLaw, z.1 < 1 := by
    apply ae_of_ae_map (f := Prod.fst) (p := fun u : ℝ => u < 1) measurable_fst.aemeasurable
    rw [System.couplingLaw, Measure.map_fst_prod, measure_univ, one_smul]
    exact unitLaw_ae_lt_one
  filter_upwards [hu] with z hz
  have hn := (weight_tendsto_one D.law D.event D.measurable D.antitone D.positive).eventually
    (lt_mem_nhds hz)
  exact hn.mono fun n h => by simp only [System.row, ite_eq_left h.le, System.survivor]

theorem System.survivor_mem (D : System Ω) :
    ∀ᵐ z ∂D.couplingLaw, D.survivor z ∈ ⋂ n, D.event n := by
  apply ae_of_ae_map (f := D.survivor) (p := fun x => x ∈ ⋂ n, D.event n)
    D.measurable_survivor.aemeasurable
  rw [D.map_survivor]
  exact ae_cond_mem (MeasurableSet.iInter D.measurable)

theorem System.rows_mem (D : System Ω) :
    ∀ᵐ z ∂D.couplingLaw, ∀ n, D.row n z ∈ D.event n := by
  apply ae_all_iff.mpr
  intro n
  apply ae_of_ae_map (f := D.row n) (p := fun x => x ∈ D.event n) (D.measurable_row n).aemeasurable
  rw [D.map_row]
  exact ae_cond_mem (D.measurable n)

/-- Any almost sure original property passes to the common survivor. -/
theorem System.survivor_property (D : System Ω) {P : Ω → Prop} (hP : ∀ᵐ x ∂D.law, P x) :
    ∀ᵐ z ∂D.couplingLaw, P (D.survivor z) := by
  apply ae_of_ae_map (f := D.survivor) (p := P) D.measurable_survivor.aemeasurable
  rw [D.map_survivor]
  exact cond_absolutelyContinuous.ae_le hP

end Freezing1.ConditionalSurvival
