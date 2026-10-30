module

public import Freezing1.SIRPoissonFirstArrival

/-!
# A contact-path carrier including the empty process

The extra point is the path with no arrivals at any time. Positive simple
arrival paths retain their original meaning. Zero Poisson intensity forces
the empty path almost surely; emptiness is proved from counting marginals.
-/

@[expose] public section

namespace Freezing1.SIR.PoissonContact

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical Topology

def OptionalPath := Unit ⊕ ArrivalPath

instance : MeasurableSpace OptionalPath := inferInstanceAs (MeasurableSpace (Unit ⊕ ArrivalPath))

def emptyPath : OptionalPath := Sum.inl ()

noncomputable def optionalCount (a : OptionalPath) (t : ℝ) : ℕ :=
  Sum.elim (fun _ => 0) (fun p => count p t) a

@[simp] theorem optionalCount_empty (t : ℝ) : optionalCount emptyPath t = 0 := rfl

@[simp] theorem optionalCount_arrivals (a : ArrivalPath) (t : ℝ) :
    optionalCount (Sum.inr a) t = count a t := rfl

theorem measurable_optionalCount (t : ℝ) : Measurable (fun a => optionalCount a t) :=
  measurable_const.sumElim (measurable_count t)

def HasOptionalPoissonCounts (nu : Measure OptionalPath) (r : ℝ≥0) : Prop :=
  ∀ t : ℝ≥0, nu.map (fun a => optionalCount a (t : ℝ)) = poissonMeasure (r * t)

theorem hasOptionalPoissonCounts_arrivals (nu : Measure ArrivalPath) (r : ℝ≥0)
    (h : HasPoissonCounts nu r) : HasOptionalPoissonCounts (nu.map Sum.inr) r := by
  intro t
  rw [Measure.map_map (measurable_optionalCount t) measurable_inr]
  exact h t

theorem optionalPath_eq_empty_of_counts_zero (a : OptionalPath)
    (h : ∀ k : ℕ, optionalCount a k = 0) : a = emptyPath := by
  cases a with
  | inl u => cases u; rfl
  | inr a =>
    have hle : first a ≤ (⌈first a⌉₊ : ℝ) := Nat.le_ceil _
    have hp : 0 < count a (⌈first a⌉₊ : ℝ) := (count_pos_iff _ _).mpr hle
    have hz := h ⌈first a⌉₊
    change count a (⌈first a⌉₊ : ℝ) = 0 at hz
    omega

theorem HasOptionalPoissonCounts.empty_ae {nu : Measure OptionalPath}
    [IsProbabilityMeasure nu] (h : HasOptionalPoissonCounts nu 0) :
    ∀ᵐ a ∂nu, a = emptyPath := by
  have hz : ∀ k : ℕ, ∀ᵐ a ∂nu, optionalCount a k = 0 := by
    intro k
    apply (mem_ae_iff_prob_eq_one
      (measurableSet_eq_fun (measurable_optionalCount k) measurable_const)).mpr
    change nu ((fun a => optionalCount a (k : ℝ)) ⁻¹' {0}) = 1
    have hk : nu.map (fun a => optionalCount a (k : ℝ)) = poissonMeasure 0 := by
      simpa using h (k : ℝ≥0)
    rw [← Measure.map_apply (measurable_optionalCount k) (measurableSet_singleton 0),
      hk, poissonMeasure_singleton]
    simp
  filter_upwards [ae_all_iff.mpr hz] with a ha
  exact optionalPath_eq_empty_of_counts_zero a ha

theorem HasOptionalPoissonCounts.law_eq_dirac_empty {nu : Measure OptionalPath}
    [IsProbabilityMeasure nu] (h : HasOptionalPoissonCounts nu 0) :
    nu = Measure.dirac emptyPath := by
  have hh : HasLaw (id : OptionalPath → OptionalPath) (Measure.dirac emptyPath) nu :=
    hasLaw_dirac_of_ae_eq h.empty_ae
  simpa only [Measure.map_id] using hh.map_eq

theorem poisson_zero_eq_dirac : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro k
  rw [poissonMeasure_singleton]
  cases k <;> simp

theorem hasOptionalPoissonCounts_empty :
    HasOptionalPoissonCounts (Measure.dirac emptyPath) 0 := by
  intro t
  rw [Measure.map_dirac' (measurable_optionalCount t), optionalCount_empty,
    zero_mul, poisson_zero_eq_dirac]

theorem hasOptionalPoissonCounts_zero_iff (nu : Measure OptionalPath) [IsProbabilityMeasure nu] :
    HasOptionalPoissonCounts nu 0 ↔ nu = Measure.dirac emptyPath :=
  ⟨HasOptionalPoissonCounts.law_eq_dirac_empty,
    fun he => he ▸ hasOptionalPoissonCounts_empty⟩

end Freezing1.SIR.PoissonContact
