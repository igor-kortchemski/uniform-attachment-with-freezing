module

public import Freezing1.SIRBiasedWalkMonotone
public import Freezing1.PlaneFiniteExtinction

/-!
# Actual extinction at and below the critical attachment probability

Monotone coupling compares the walk with every slightly supercritical walk.
Its already proved exact extinction odds approach one. This gives critical
recurrence and subcritical extinction without an assumed random-walk theorem.
-/

@[expose] public section

namespace Freezing1.SIR.BiasedWalk

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

def everZero : Set (ℕ → ℕ) := {H | ∃ k, H k = 0}

theorem measurableSet_everZero : MeasurableSet everZero := by
  unfold everZero
  apply measurableSet_setOfPred.mpr
  exact Measurable.exists fun k => measurable_pi_apply k |>.eq measurable_const

theorem supercritical_extinction_le_everZero {p q : unitInterval} (hpq : p ≤ q)
    (hq : (1 : ℝ) / 2 < q) :
    ENNReal.ofReal ((1 - (q : ℝ)) / (q : ℝ)) ≤ fullLaw p everZero := by
  apply le_of_tendsto (zero_probability_tendsto q hq)
  exact Filter.Eventually.of_forall fun k => (zero_probability_antitone hpq k).trans
    (measure_mono (fun H hH => ⟨k, hH⟩))

/-- The true probability of ever reaching the absorbing state is one,
including p=0 and the critical endpoint p=1/2. -/
theorem everZero_probability_eq_one (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    fullLaw p everZero = 1 := by
  by_contra hne
  have hlt : fullLaw p everZero < 1 := lt_of_le_of_ne prob_le_one hne
  let g : ℝ := (fullLaw p).real everZero
  have hg0 : 0 ≤ g := measureReal_nonneg
  have hg1 : g < 1 := by
    change (fullLaw p).real everZero < 1
    rw [measureReal_def]
    have hh := ENNReal.toReal_lt_toReal (measure_ne_top (fullLaw p) everZero)
      (by simp : (1 : ℝ≥0∞) ≠ ⊤) |>.mpr hlt
    simpa only [ENNReal.toReal_one] using hh
  let delta : ℝ := (1 - g) / 2
  have hd0 : 0 < delta := by dsimp [delta]; linarith
  have hd1 : delta < 1 := by dsimp [delta]; linarith
  have hden : 0 < 2 - delta := by linarith
  let q : unitInterval := ⟨1 / (2 - delta), ⟨by positivity,
    (div_le_one hden).mpr (by linarith)⟩⟩
  have hq : (1 : ℝ) / 2 < q := by
    change 1 / 2 < 1 / (2 - delta)
    apply (lt_div_iff₀ hden).mpr
    nlinarith
  have hpq : p ≤ q := by
    exact_mod_cast hp.trans hq.le
  have hodds : (1 - (q : ℝ)) / (q : ℝ) = 1 - delta := by
    change (1 - 1 / (2 - delta)) / (1 / (2 - delta)) = 1 - delta
    field_simp
    ring
  have hb := ENNReal.toReal_mono (measure_ne_top (fullLaw p) everZero)
    (supercritical_extinction_le_everZero hpq hq)
  rw [hodds, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - delta)] at hb
  change 1 - delta ≤ g at hb
  dsimp [delta] at hb
  linarith

theorem fullLaw_everZero_ae (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    ∀ᵐ H ∂fullLaw p, ∃ k, H k = 0 :=
  (mem_ae_iff_prob_eq_one measurableSet_everZero).mpr (everZero_probability_eq_one p hp)

end Freezing1.SIR.BiasedWalk

namespace Freezing1.PlaneForward

open Filter MeasureTheory ProbabilityTheory PlaneTree
open scoped ENNReal NNReal Classical Topology

/-- The actual iid plane genealogy becomes completely frozen almost surely
in both subcritical and critical regimes. -/
theorem fullLaw_ever_absorbed_ae_of_le_half (p : unitInterval) (hp : (p : ℝ) ≤ 1 / 2) :
    ∀ᵐ H ∂fullLaw p initial, ∃ k, (H k).active.card = 0 := by
  have hh := SIR.BiasedWalk.fullLaw_everZero_ae p hp
  rw [← SIR.map_planeFullLaw_activeCard p] at hh
  have hm : Measurable (fun H : ℕ → State => fun k => (H k).active.card) :=
    Measurable.of_eval fun k => (measurable_of_countable (fun s : State => s.active.card)).comp
      (measurable_pi_apply k)
  exact ae_of_ae_map (f := fun H : ℕ → State => fun k => (H k).active.card)
    (p := fun C : ℕ → ℕ => ∃ k, C k = 0) hm.aemeasurable hh

/-- The whole limiting tree is finite almost surely at and below criticality. -/
theorem planeLimitLaw_finite_probability_of_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) :
    (ForwardAnnealed.planeLimitLaw p : Measure Tree) {T | FiniteVertices T} = 1 := by
  have hp1 : (p : ℝ) < 1 := by linarith
  have hf : ∀ᵐ H ∂fullLaw p initial, FiniteVertices (chainLimit H) := by
    filter_upwards [fullLaw_finite_chainLimit_iff_absorbed p hp1,
      fullLaw_ever_absorbed_ae_of_le_half p hp] with H hH hext
    exact hH.mpr hext
  have hm : ∀ᵐ T ∂(fullLaw p initial).map chainLimit, FiniteVertices T :=
    (ae_map_iff (aemeasurable_chainLimit p hp1) measurableSet_finiteVertices).mpr hf
  rw [map_fullLaw_chainLimit p hp1] at hm
  exact (mem_ae_iff_prob_eq_one measurableSet_finiteVertices).mp hm

theorem geometricBienayme_finite_probability_of_le_half (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) :
    geometricBienaymeLaw p {T | FiniteVertices T} = 1 := by
  rw [← ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw p (by linarith)]
  exact planeLimitLaw_finite_probability_of_le_half p hp

end Freezing1.PlaneForward
