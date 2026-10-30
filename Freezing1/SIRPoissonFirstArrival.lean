module

public import Freezing1.SIRExponentialRace
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# First arrivals of a Poisson contact process

A locally finite simple counting path is represented by its positive,
strictly increasing, divergent arrival sequence. Its first coordinate is
proved to be the actual first positive-count time. Poisson counting
marginals imply its exponential law; that law is not a premise.
-/

@[expose] public section

namespace Freezing1.SIR.PoissonContact

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

def ArrivalPath := {a : ℕ → ℝ // 0 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop}

instance : MeasurableSpace ArrivalPath := inferInstanceAs (MeasurableSpace {a : ℕ → ℝ //
  0 < a 0 ∧ StrictMono a ∧ Tendsto a atTop atTop})

def first (a : ArrivalPath) : ℝ := a.1 0

theorem first_pos (a : ArrivalPath) : 0 < first a := a.2.1

theorem measurable_coordinate (k : ℕ) : Measurable (fun a : ArrivalPath => a.1 k) :=
  (measurable_pi_apply k).comp measurable_subtype_coe

theorem measurable_first : Measurable first := measurable_coordinate 0

theorem exists_later (a : ArrivalPath) (t : ℝ) : ∃ k : ℕ, t < a.1 k :=
  (a.2.2.2.eventually_gt_atTop t).exists

/-- The number of arrivals at or before `t`. -/
noncomputable def count (a : ArrivalPath) (t : ℝ) : ℕ := Nat.find (exists_later a t)

theorem count_eq_iff (a : ArrivalPath) (t : ℝ) (k : ℕ) :
    count a t = k ↔ t < a.1 k ∧ ∀ j < k, ¬t < a.1 j :=
  Nat.find_eq_iff (exists_later a t)

theorem count_eq_zero_iff (a : ArrivalPath) (t : ℝ) : count a t = 0 ↔ t < first a :=
  Nat.find_eq_zero (exists_later a t)

theorem count_pos_iff (a : ArrivalPath) (t : ℝ) : 0 < count a t ↔ first a ≤ t := by
  rw [Nat.pos_iff_ne_zero, ne_eq, count_eq_zero_iff, not_lt]

/-- This explicitly identifies the first coordinate with the counting
process's first contact, including its value at the jump time. -/
theorem positive_count_times (a : ArrivalPath) : {t : ℝ | 0 < count a t} = Ici (first a) := by
  ext t
  exact count_pos_iff a t

theorem count_monotone (a : ArrivalPath) : Monotone (count a) := by
  intro s t hst
  apply Nat.find_min'
  exact hst.trans_lt (Nat.find_spec (exists_later a t))

theorem arrival_le_iff_lt_count (a : ArrivalPath) (t : ℝ) (j : ℕ) :
    a.1 j ≤ t ↔ j < count a t := by
  constructor
  · intro hj
    by_contra hn
    have hcountj : count a t ≤ j := by omega
    have hmono := a.2.2.1.monotone hcountj
    have hnext := Nat.find_spec (exists_later a t)
    change t < a.1 (count a t) at hnext
    linarith
  · intro hj
    exact le_of_not_gt (Nat.find_min (exists_later a t) hj)

theorem measurable_count (t : ℝ) : Measurable (fun a : ArrivalPath => count a t) := by
  apply measurable_to_countable'
  intro k
  have he : (fun a : ArrivalPath => count a t) ⁻¹' {k} =
      {a : ArrivalPath | t < a.1 k} ∩ ⋂ j : ℕ, {a : ArrivalPath | j < k → ¬t < a.1 j} := by
    ext a
    simp only [mem_preimage, mem_singleton_iff, count_eq_iff, mem_inter_iff, mem_iInter,
      mem_ofPred_eq]
  rw [he]
  apply (measurableSet_lt measurable_const (measurable_coordinate k)).inter
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j < k
  · simpa only [hj, true_implies, not_lt] using
      measurableSet_le (measurable_coordinate j) measurable_const
  · simp only [hj, false_implies, ofPred_true]
    exact MeasurableSet.univ

/-- The exact marginal specification used from a rate-`r` Poisson process.
No exponential waiting-time law is part of this specification. -/
def HasPoissonCounts (nu : Measure ArrivalPath) (r : ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, nu.map (fun a => count a (t : ℝ)) = poissonMeasure (r * t)

theorem first_law (nu : Measure ArrivalPath) [IsProbabilityMeasure nu]
    (r : ℝ≥0) (hr : 0 < r) (hcounts : HasPoissonCounts nu r) :
    nu.map first = expMeasure (r : ℝ) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have := isProbabilityMeasure_expMeasure hrR
  have htail : ∀ x : ℝ, (nu.map first) (Ioi x) = expMeasure (r : ℝ) (Ioi x) := by
    intro x
    rw [Measure.map_apply measurable_first measurableSet_Ioi]
    by_cases hx : 0 ≤ x
    · have he : first ⁻¹' Ioi x = (fun a : ArrivalPath => count a x) ⁻¹' {0} := by
        ext a
        simp only [mem_preimage, mem_Ioi, mem_singleton_iff]
        exact (count_eq_zero_iff a x).symm
      rw [he, ← Measure.map_apply (measurable_count x) (measurableSet_singleton 0),
        show nu.map (fun a => count a x) = poissonMeasure (r * ⟨x, hx⟩) from hcounts ⟨x, hx⟩,
        poissonMeasure_singleton, expMeasure_Ioi_of_nonneg hrR hx]
      simp
      rfl
    · have hx0 : x < 0 := by linarith
      have he : first ⁻¹' Ioi x = univ := by
        ext a
        simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
        exact hx0.trans (first_pos a)
      rw [he, measure_univ, expMeasure_Ioi_of_neg hrR hx0]
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, cdf_eq_real]
  apply congrArg ENNReal.toReal
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _), measure_univ, measure_univ, htail]

end Freezing1.SIR.PoissonContact
