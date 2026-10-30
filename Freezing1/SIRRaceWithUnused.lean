module

public import Freezing1.SIRPreassignedResiduals

/-!
# A genuine clock race with untouched unused arrays

After a designated live winner, the old residuals and the unused coordinates
are independent with their original exponential laws. Any injective
rate-preserving selection of these coordinates therefore gives the exact
next-clock law. This is the probabilistic counterpart of the proved static
array deletion and activation identities.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def untouchedClockProject {L U J : Type*} (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U))
    (z : ({j : L // j ≠ i} → ℝ) × (U → ℝ)) : J → ℝ :=
  fun j => Sum.elim z.1 z.2 (pick j)

theorem measurable_untouchedClockProject {L U J : Type*} (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U)) : Measurable (untouchedClockProject i pick) := by
  apply Measurable.of_eval
  intro j
  cases hp : pick j with
  | inl k => simpa only [untouchedClockProject, hp, Sum.elim_inl, Function.comp_def]
      using (measurable_pi_apply k).comp measurable_fst
  | inr u => simpa only [untouchedClockProject, hp, Sum.elim_inr, Function.comp_def]
      using (measurable_pi_apply u).comp measurable_snd

theorem unused_and_residual_projection_law {L U J : Type*}
    [Fintype L] [Fintype U] [Fintype J]
    (rateL : L → ℝ) (hL : ∀ j, 0 < rateL j)
    (rateU : U → ℝ) (hU : ∀ j, 0 < rateU j) (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U)) (hpick : Function.Injective pick) :
    ((Measure.pi (fun j : {j : L // j ≠ i} => expMeasure (rateL j))).prod
      (Measure.pi (fun j : U => expMeasure (rateU j)))).map
        (untouchedClockProject i pick) =
      Measure.pi (fun j => expMeasure (Sum.elim
        (fun k : {j : L // j ≠ i} => rateL k) rateU (pick j))) := by
  let rate : ({j : L // j ≠ i} ⊕ U) → ℝ :=
    Sum.elim (fun k : {j : L // j ≠ i} => rateL k) rateU
  have hrate : ∀ k, 0 < rate k := by
    intro k
    cases k with
    | inl k => exact hL k
    | inr k => exact hU k
  have : ∀ k, IsProbabilityMeasure (expMeasure (rate k)) :=
    fun k => isProbabilityMeasure_expMeasure (hrate k)
  have hcombine : ((Measure.pi (fun j : {j : L // j ≠ i} => expMeasure (rateL j))).prod
      (Measure.pi (fun j : U => expMeasure (rateU j)))).map
      (fun z : ({j : L // j ≠ i} → ℝ) × (U → ℝ) => Sum.elim z.1 z.2) =
      Measure.pi (fun k => expMeasure (rate k)) :=
    (measurePreserving_sumPiEquivProdPi_symm (fun k => expMeasure (rate k))).map_eq
  have hm : Measurable (fun z : ({j : L // j ≠ i} → ℝ) × (U → ℝ) =>
      Sum.elim z.1 z.2) :=
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : {j : L // j ≠ i} ⊕ U => ℝ)).symm.measurable
  have hp : Measurable (fun t : ({j : L // j ≠ i} ⊕ U) → ℝ => fun j => t (pick j)) :=
    Measurable.of_eval fun j => measurable_pi_apply (pick j)
  calc
    _ = (((Measure.pi (fun j : {j : L // j ≠ i} => expMeasure (rateL j))).prod
        (Measure.pi (fun j : U => expMeasure (rateU j)))).map
        (fun z : ({j : L // j ≠ i} → ℝ) × (U → ℝ) => Sum.elim z.1 z.2)).map
        (fun t : ({j : L // j ≠ i} ⊕ U) → ℝ => fun j => t (pick j)) := by
      rw [Measure.map_map hp hm]
      rfl
    _ = _ := by
      rw [hcombine, independent_clock_coordinate_projection rate hrate pick hpick]

noncomputable def raceWithUnused {L U J : Type*} [Fintype L] [Nonempty L] (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U))
    (z : (L → ℝ) × (U → ℝ)) : ℝ × (J → ℝ) :=
  (earliestClock z.1, untouchedClockProject i pick
    (fun j : {j : L // j ≠ i} => z.1 j - earliestClock z.1, z.2))

/-- The winner, actual minimum time, and next selected clocks have their
factorized law under the actual independent live/unused product. -/
theorem exponential_race_with_unused_projection {L U J : Type*}
    [Fintype L] [Nonempty L] [Fintype U] [Fintype J]
    (rateL : L → ℝ) (hL : ∀ j, 0 < rateL j)
    (rateU : U → ℝ) (hU : ∀ j, 0 < rateU j) (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U)) (hpick : Function.Injective pick) :
    (((Measure.pi (fun j => expMeasure (rateL j))).prod
      (Measure.pi (fun j => expMeasure (rateU j)))).restrict
        (clockWins i ×ˢ univ)).map (raceWithUnused i pick) =
      ENNReal.ofReal (rateL i / ∑ j, rateL j) •
        ((expMeasure (∑ j, rateL j)).prod
          (Measure.pi (fun j => expMeasure (Sum.elim
            (fun k : {j : L // j ≠ i} => rateL k) rateU (pick j))))) := by
  have : ∀ j, IsProbabilityMeasure (expMeasure (rateL j)) :=
    fun j => isProbabilityMeasure_expMeasure (hL j)
  have : ∀ j, IsProbabilityMeasure (expMeasure (rateU j)) :=
    fun j => isProbabilityMeasure_expMeasure (hU j)
  have : IsProbabilityMeasure (expMeasure (∑ j, rateL j)) :=
    isProbabilityMeasure_expMeasure (Finset.sum_pos (fun j _ => hL j) Finset.univ_nonempty)
  let f : (L → ℝ) → ℝ × ({j : L // j ≠ i} → ℝ) := fun t =>
    (earliestClock t, fun j => t j - earliestClock t)
  have hmf : Measurable f := measurable_earliestClock.prodMk
    (Measurable.of_eval fun j => (measurable_pi_apply (j : L)).sub measurable_earliestClock)
  have hmG : Measurable (Prod.map f (id : (U → ℝ) → _)) := hmf.prodMap measurable_id
  have hmP : Measurable (Prod.map (id : ℝ → ℝ) (untouchedClockProject i pick)) :=
    measurable_id.prodMap (measurable_untouchedClockProject i pick)
  have hG :
      ((((Measure.pi (fun j => expMeasure (rateL j))).prod
        (Measure.pi (fun j => expMeasure (rateU j)))).restrict
          (clockWins i ×ˢ univ)).map (Prod.map f id)) =
      ENNReal.ofReal (rateL i / ∑ j, rateL j) •
        (((expMeasure (∑ j, rateL j)).prod
          (Measure.pi (fun j : {j : L // j ≠ i} => expMeasure (rateL j)))).prod
            (Measure.pi (fun j => expMeasure (rateU j)))) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hmap := Measure.map_prod_map
      ((Measure.pi (fun j => expMeasure (rateL j))).restrict (clockWins i))
      (Measure.pi (fun j => expMeasure (rateU j))) hmf
      (show Measurable (id : (U → ℝ) → _) from measurable_id)
    rw [← hmap, independent_exponential_winner_minimum_residual_law rateL hL i,
      Measure.map_id, Measure.prod_smul_left]
  calc
    _ = (((((Measure.pi (fun j => expMeasure (rateL j))).prod
        (Measure.pi (fun j => expMeasure (rateU j)))).restrict
          (clockWins i ×ˢ univ)).map (Prod.map f id)).map
          MeasurableEquiv.prodAssoc).map
            (Prod.map id (untouchedClockProject i pick)) := by
      rw [Measure.map_map hmP MeasurableEquiv.prodAssoc.measurable,
        Measure.map_map (hmP.comp MeasurableEquiv.prodAssoc.measurable) hmG]
      rfl
    _ = _ := by
      rw [hG, Measure.map_smul _ MeasurableEquiv.prodAssoc.measurable.aemeasurable,
        Measure.prodAssoc_prod, Measure.map_smul _ hmP.aemeasurable,
        ← Measure.map_prod_map _ _ measurable_id (measurable_untouchedClockProject i pick),
        Measure.map_id, unused_and_residual_projection_law rateL hL rateU hU i pick hpick]

def designatedRaceWithUnused {L U J : Type*} (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U))
    (z : (L → ℝ) × (U → ℝ)) : ℝ × (J → ℝ) :=
  (z.1 i, untouchedClockProject i pick (fun j : {j : L // j ≠ i} => z.1 j - z.1 i, z.2))

theorem exponential_designated_race_with_unused_projection {L U J : Type*}
    [Fintype L] [Fintype U] [Fintype J]
    (rateL : L → ℝ) (hL : ∀ j, 0 < rateL j)
    (rateU : U → ℝ) (hU : ∀ j, 0 < rateU j) (i : L)
    (pick : J → ({j : L // j ≠ i} ⊕ U)) (hpick : Function.Injective pick) :
    (((Measure.pi (fun j => expMeasure (rateL j))).prod
      (Measure.pi (fun j => expMeasure (rateU j)))).restrict
        (clockWins i ×ˢ univ)).map (designatedRaceWithUnused i pick) =
      ENNReal.ofReal (rateL i / ∑ j, rateL j) •
        ((expMeasure (∑ j, rateL j)).prod
          (Measure.pi (fun j => expMeasure (Sum.elim
            (fun k : {j : L // j ≠ i} => rateL k) rateU (pick j))))) := by
  have : Nonempty L := ⟨i⟩
  rw [← exponential_race_with_unused_projection rateL hL rateU hU i pick hpick]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem ((measurableSet_clockWins i).prod MeasurableSet.univ)] with z hz
  simp only [raceWithUnused, clockWins_earliestClock hz.1]
  rfl

end Freezing1.SIR
