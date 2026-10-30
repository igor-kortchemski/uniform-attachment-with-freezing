module

public import Freezing1.SIRPoissonExistenceSums
public import Freezing1.SIRPoissonFirstArrival

/-!
# A Poisson arrival path with exponential waiting times

The arrival path of a rate-`r` Poisson process is built from independent
exponential waiting times: its `k`-th arrival is the sum of the first `k + 1`
waiting times. This is an `ArrivalPath` outside a null set of waiting
sequences, where a fixed fallback path is used. The counting variable at time
`t` has the Poisson law of mean `r t`, so this is an explicit probability
measure on `ArrivalPath` with Poisson counting marginals.
-/

@[expose] public section

namespace Freezing1.SIR.PoissonExistence

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

/-- Waiting sequences with positive entries and divergent partial sums. -/
def good : Set (ℕ → ℝ) := {E | (∀ i, 0 < E i) ∧ ∀ M : ℕ, ∃ k, (M : ℝ) < S k E}

theorem measurableSet_good : MeasurableSet good := by
  have : good = (⋂ i : ℕ, {E : ℕ → ℝ | 0 < E i}) ∩ ⋂ M : ℕ, ⋃ k : ℕ, {E : ℕ → ℝ | (M : ℝ) < S k E} := by
    ext E
    simp only [good, mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_iUnion]
  rw [this]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    (MeasurableSet.iInter fun M => MeasurableSet.iUnion fun k =>
      measurableSet_lt measurable_const (measurable_S k))

theorem waiting_ae_good {r : ℝ} (hr : 0 < r) : ∀ᵐ E ∂waiting r, E ∈ good := by
  have h1 : ∀ᵐ E ∂waiting r, ∀ i, 0 < E i := ae_all_iff.2 (waiting_ae_pos hr)
  have h2 : ∀ᵐ E ∂waiting r, ∀ M : ℕ, ∃ k, (M : ℝ) < S k E :=
    ae_all_iff.2 fun M => waiting_ae_exists_gt hr M
  filter_upwards [h1, h2] with E hE1 hE2 using ⟨hE1, hE2⟩

theorem S_mono {E : ℕ → ℝ} (hE : ∀ i, 0 < E i) : Monotone (fun k => S k E) :=
  monotone_nat_of_le_succ fun k => by
    rw [S_succ]
    linarith [hE k]

/-- Arrival times from waiting times; a fixed fallback path off the good set. -/
noncomputable def pathFun (E : ℕ → ℝ) (k : ℕ) : ℝ :=
  if E ∈ good then S (k + 1) E else (k : ℝ) + 1

theorem pathFun_of_mem {E : ℕ → ℝ} (hE : E ∈ good) (k : ℕ) : pathFun E k = S (k + 1) E := by
  simp only [pathFun, hE, ite_true]

theorem pathFun_of_notMem {E : ℕ → ℝ} (hE : E ∉ good) (k : ℕ) : pathFun E k = (k : ℝ) + 1 := by
  simp only [pathFun, hE, ite_false]

theorem pathFun_spec (E : ℕ → ℝ) :
    0 < pathFun E 0 ∧ StrictMono (pathFun E) ∧ Tendsto (pathFun E) atTop atTop := by
  by_cases hE : E ∈ good
  · obtain ⟨hpos, hdiv⟩ := id hE
    have hsm : StrictMono (pathFun E) := by
      refine strictMono_nat_of_lt_succ fun k => ?_
      rw [pathFun_of_mem hE, pathFun_of_mem hE, S_succ (k + 1)]
      linarith [hpos (k + 1)]
    refine ⟨?_, hsm, tendsto_atTop_atTop_of_monotone hsm.monotone fun b => ?_⟩
    · rw [pathFun_of_mem hE]
      simpa [S] using hpos 0
    · obtain ⟨M, hM⟩ := exists_nat_ge b
      obtain ⟨k, hk⟩ := hdiv M
      refine ⟨k, ?_⟩
      rw [pathFun_of_mem hE]
      exact (hM.trans hk.le).trans (S_mono hpos (Nat.le_succ k))
  · have hf : pathFun E = fun k : ℕ => (k : ℝ) + 1 := funext (pathFun_of_notMem hE)
    rw [hf]
    refine ⟨by simp, ?_, ?_⟩
    · exact fun a b hab => by simpa using hab
    · exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-- The arrival path attached to a waiting sequence. -/
noncomputable def pathOf (E : ℕ → ℝ) : PoissonContact.ArrivalPath :=
  ⟨pathFun E, pathFun_spec E⟩

theorem pathOf_apply {E : ℕ → ℝ} (hE : E ∈ good) (k : ℕ) :
    (pathOf E).1 k = S (k + 1) E :=
  pathFun_of_mem hE k

theorem measurable_pathOf : Measurable pathOf := by
  refine Measurable.subtype_mk (measurable_pi_iff.2 fun k => ?_)
  exact Measurable.ite measurableSet_good (measurable_S (k + 1)) measurable_const

theorem count_pathOf_eq_iff {E : ℕ → ℝ} (hE : E ∈ good) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    PoissonContact.count (pathOf E) t = k ↔ S k E ≤ t ∧ t < S (k + 1) E := by
  rw [PoissonContact.count_eq_iff]
  simp only [pathOf_apply hE]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    cases k with
    | zero => simpa [S] using ht
    | succ k => exact not_lt.1 (h2 k (Nat.lt_succ_self k))
  · rintro ⟨h1, h2⟩
    exact ⟨h2, fun j hj => not_lt.2 ((S_mono hE.1 (Nat.succ_le_of_lt hj)).trans h1)⟩

theorem waiting_count_eq {r : ℝ} (hr : 0 < r) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    waiting r {E | PoissonContact.count (pathOf E) t = k} = ENNReal.ofReal (pmass r k t) := by
  have := isProbabilityMeasure_waiting hr
  have hB : MeasurableSet {E : ℕ → ℝ | S (k + 1) E ≤ t} :=
    measurableSet_le (measurable_S (k + 1)) measurable_const
  have hgood := waiting_ae_good hr
  have hC : {E : ℕ → ℝ | PoissonContact.count (pathOf E) t = k} =ᵐ[waiting r]
      ({E : ℕ → ℝ | S k E ≤ t} \ {E : ℕ → ℝ | S (k + 1) E ≤ t}) := by
    refine eventuallyEqSet_iff.2 (hgood.mono fun E hE => ?_)
    simp only [mem_ofPred_eq, Set.mem_sdiff, count_pathOf_eq_iff hE ht k, not_le]
  have hAB : {E : ℕ → ℝ | S k E ≤ t} ∩ {E : ℕ → ℝ | S (k + 1) E ≤ t} =ᵐ[waiting r]
      {E : ℕ → ℝ | S (k + 1) E ≤ t} := by
    refine eventuallyEqSet_iff.2 (hgood.mono fun E hE => ?_)
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_right_iff_imp]
    exact fun h => (S_mono hE.1 (Nat.le_succ k)).trans h
  have hfin : tail r (k + 1) t ≠ ∞ := by
    rw [← waiting_sum_le_eq_tail hr (k + 1) t]
    exact measure_ne_top _ _
  have h1 := measure_sdiff_add_inter ({E : ℕ → ℝ | S k E ≤ t}) hB (μ := waiting r)
  rw [measure_congr hAB, waiting_sum_le_eq_tail hr k t, waiting_sum_le_eq_tail hr (k + 1) t,
    tail_eq_add k ht] at h1
  rw [measure_congr hC]
  exact (ENNReal.add_left_inj hfin).1 h1

/-- Non-vacuity of the Poisson counting hypothesis on arrival paths. -/
theorem exists_hasPoissonCounts (r : ℝ≥0) (hr : 0 < r) :
    ∃ nu : Measure PoissonContact.ArrivalPath, IsProbabilityMeasure nu ∧
      PoissonContact.HasPoissonCounts nu r := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have := isProbabilityMeasure_waiting hr'
  refine ⟨(waiting (r : ℝ)).map pathOf, inferInstance, ?_⟩
  intro t
  refine Measure.ext_of_singleton fun k => ?_
  have hc : MeasurableSet ((fun a : PoissonContact.ArrivalPath => PoissonContact.count a (t : ℝ)) ⁻¹' {k}) :=
    (PoissonContact.measurable_count (t : ℝ)) (measurableSet_singleton k)
  rw [Measure.map_apply (PoissonContact.measurable_count (t : ℝ)) (measurableSet_singleton k),
    Measure.map_apply measurable_pathOf hc, poissonMeasure_singleton]
  have hset : pathOf ⁻¹' ((fun a : PoissonContact.ArrivalPath => PoissonContact.count a (t : ℝ)) ⁻¹' {k}) =
      {E | PoissonContact.count (pathOf E) (t : ℝ) = k} := rfl
  rw [hset, waiting_count_eq hr' (NNReal.coe_nonneg t) k]
  simp only [pmass, NNReal.coe_mul]
