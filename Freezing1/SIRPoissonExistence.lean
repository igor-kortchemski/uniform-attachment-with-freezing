module

public import Freezing1.SIRPoissonExistenceProcess
public import Freezing1.SIRPhysicalLaws

/-!
# Non-vacuity of the physical Poisson SIR data

The hypothesis `PoissonSIRData` of the physical SIR theorems is satisfiable
for every positive rate: independent rate-one exponential recovery periods and
independent rate-`rate` Poisson arrival paths, one per ordered pair of
individuals, live on one product probability space. For rate zero the
hypothesis is unsatisfiable, because an arrival path tends to infinity, so
its count cannot be zero at every time; the physical theorems therefore use
`0 < rate`, which is the hypothesis of the existence theorem.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Zero-rate Poisson counts are impossible for an arrival path. -/
theorem PoissonContact.not_hasPoissonCounts_zero (nu : Measure PoissonContact.ArrivalPath)
    [IsProbabilityMeasure nu] : ¬ PoissonContact.HasPoissonCounts nu 0 := by
  intro h
  have hN : ∀ N : ℕ, ∀ᵐ a ∂nu, PoissonContact.count a ((N : ℝ≥0) : ℝ) = 0 := by
    intro N
    have hz : (poissonMeasure ((0 : ℝ≥0) * (N : ℝ≥0))) {0}ᶜ = 0 := by
      rw [zero_mul, prob_compl_eq_zero_iff (measurableSet_singleton 0), poissonMeasure_singleton]
      simp
    have hnull : nu ((fun a => PoissonContact.count a ((N : ℝ≥0) : ℝ)) ⁻¹' {0}ᶜ) = 0 := by
      rw [← Measure.map_apply (PoissonContact.measurable_count ((N : ℝ≥0) : ℝ))
        (measurableSet_singleton 0).compl, h (N : ℝ≥0)]
      exact hz
    exact (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun a ha => by simpa using ha
  have hall : ∀ᵐ a ∂nu, ∀ N : ℕ, PoissonContact.count a ((N : ℝ≥0) : ℝ) = 0 := ae_all_iff.2 hN
  obtain ⟨a, ha⟩ := hall.exists
  obtain ⟨N, hNa⟩ := exists_nat_ge (PoissonContact.first a)
  have := (PoissonContact.count_pos_iff a ((N : ℝ≥0) : ℝ)).2 (by simpa using hNa)
  rw [ha N] at this
  exact lt_irrefl 0 this

/-- The hypothesis `PoissonSIRData` cannot hold at rate zero. -/
theorem PoissonSIRData.false_of_rate_zero {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (n : ℕ) (X : (c : ClockSlot n) → Ω → ClockDatum c) :
    ¬ PoissonSIRData mu n 0 X := fun h =>
  PoissonContact.not_hasPoissonCounts_zero _ (h.contact_counts 0 0)

/-- Non-vacuity of `PoissonSIRData`: for every population size and every positive contact rate
there are a probability space and clock data satisfying the hypothesis of the physical SIR
theorems. -/
theorem PoissonSIRData.exists_data (n : ℕ) (rate : ℝ≥0) (hrate : 0 < rate) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (mu : Measure Ω) (_ : IsProbabilityMeasure mu)
      (X : (c : ClockSlot n) → Ω → ClockDatum c), PoissonSIRData mu n rate X := by
  obtain ⟨nu, hnu, hcounts⟩ := PoissonExistence.exists_hasPoissonCounts rate hrate
  let law : (c : ClockSlot n) → Measure (ClockDatum c) := fun c =>
    match c with
    | (_, none) => (expMeasure 1 : Measure ℝ)
    | (_, some _) => nu
  have hlaw : ∀ c, IsProbabilityMeasure (law c) := by
    rintro ⟨v, w⟩
    cases w with
    | none => exact isProbabilityMeasure_expMeasure one_pos
    | some w => exact hnu
  refine ⟨(c : ClockSlot n) → ClockDatum c, inferInstance, Measure.pi law, inferInstance,
    fun c ω => ω c, ?_, ?_, ?_, ?_⟩
  · exact fun c => measurable_pi_apply c
  · exact iIndepFun_pi (X := fun (c : ClockSlot n) (x : ClockDatum c) => x)
      (μ := law) fun c => aemeasurable_id
  · intro v
    exact (measurePreserving_eval law (v, none)).map_eq
  · intro v w
    change PoissonContact.HasPoissonCounts
      (Measure.map (Function.eval (v, some w)) (Measure.pi law)) rate
    rw [(measurePreserving_eval law (v, some w)).map_eq]
    exact hcounts

/-- Exact range of non-vacuity: `PoissonSIRData` is satisfiable precisely for positive rates. -/
theorem PoissonSIRData.exists_data_iff (n : ℕ) (rate : ℝ≥0) :
    (∃ (Ω : Type) (_ : MeasurableSpace Ω) (mu : Measure Ω) (_ : IsProbabilityMeasure mu)
      (X : (c : ClockSlot n) → Ω → ClockDatum c), PoissonSIRData mu n rate X) ↔ 0 < rate := by
  refine ⟨?_, PoissonSIRData.exists_data n rate⟩
  rintro ⟨Ω, _, mu, _, X, h⟩
  by_contra hr
  have h0 : rate = 0 := le_antisymm (not_lt.mp hr) bot_le
  subst h0
  exact PoissonSIRData.false_of_rate_zero mu n X h

/-- The sequence-level shape of the hypothesis `hdata` of the physical SIR theorems is satisfiable
along every rate sequence that is eventually positive. -/
theorem PoissonSIRData.exists_family (rate : ℕ → ℝ≥0) (hpos : ∀ᶠ n in atTop, 0 < rate n) :
    ∃ (Ω : ℕ → Type) (_ : ∀ n, MeasurableSpace (Ω n)) (mu : (n : ℕ) → Measure (Ω n))
      (_ : ∀ n, IsProbabilityMeasure (mu n)) (X : (n : ℕ) → (c : ClockSlot n) → Ω n → ClockDatum c),
      ∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n) := by
  have key : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (mu : Measure Ω)
      (_ : IsProbabilityMeasure mu) (X : (c : ClockSlot n) → Ω → ClockDatum c),
      0 < rate n → PoissonSIRData mu n (rate n) X := by
    intro n
    by_cases hn : 0 < rate n
    · obtain ⟨Ω, hΩ, mu, hmu, X, hX⟩ := PoissonSIRData.exists_data n (rate n) hn
      exact ⟨Ω, hΩ, mu, hmu, X, fun _ => hX⟩
    · have : ∀ c : ClockSlot n, Nonempty (ClockDatum c) := by
        rintro ⟨v, w⟩
        cases w with
        | none => exact ⟨(0 : ℝ)⟩
        | some w => exact ⟨PoissonExistence.pathOf (fun _ => 0)⟩
      exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance,
        fun c _ => Classical.choice (this c), fun h => absurd h hn⟩
  choose Ω hΩ mu hmu X hX using key
  exact ⟨Ω, hΩ, mu, hmu, X, hpos.mono fun n hn => hX n hn⟩

end Freezing1.SIR
