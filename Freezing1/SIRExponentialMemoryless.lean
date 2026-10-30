module

public import Freezing1.SIRExponentialWinner

/-!
# Residual exponential clocks after a genuine finite race

Memorylessness is stated as an equality of restricted pushforward measures,
so its event probability and residual law are proved together. No conditional
memorylessness statement is assumed as a premise.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem exponential_residual_law {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) :
    ((expMeasure r).restrict (Ioi s)).map (fun t : ℝ => t - s) =
      ENNReal.ofReal (Real.exp (-(r * s))) • expMeasure r := by
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hm : Measurable (fun t : ℝ => t - s) := measurable_id.sub_const s
  have : IsFiniteMeasure (ENNReal.ofReal (Real.exp (-(r * s))) • expMeasure r) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  have hu : (((expMeasure r).restrict (Ioi s)).map (fun t : ℝ => t - s)) univ =
      (ENNReal.ofReal (Real.exp (-(r * s))) • expMeasure r) univ := by
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact expMeasure_Ioi_of_nonneg hr hs
  have ht : ∀ x : ℝ,
      (((expMeasure r).restrict (Ioi s)).map (fun t : ℝ => t - s)) (Ioi x) =
        (ENNReal.ofReal (Real.exp (-(r * s))) • expMeasure r) (Ioi x) := by
    intro x
    rw [Measure.map_apply hm measurableSet_Ioi,
      Measure.restrict_apply (measurableSet_Ioi.preimage hm)]
    by_cases hx : 0 ≤ x
    · have he : (fun t : ℝ => t - s) ⁻¹' Ioi x ∩ Ioi s = Ioi (s + x) := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_Ioi]
        constructor
        · intro h; linarith [h.1]
        · intro h; constructor <;> linarith
      rw [he, expMeasure_Ioi_of_nonneg hr (add_nonneg hs hx),
        Measure.smul_apply, smul_eq_mul, expMeasure_Ioi_of_nonneg hr hx,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      ring
    · have hx' : x < 0 := lt_of_not_ge hx
      have he : (fun t : ℝ => t - s) ⁻¹' Ioi x ∩ Ioi s = Ioi s := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_Ioi]
        constructor
        · exact fun h => h.2
        · intro h; constructor <;> linarith
      rw [he, expMeasure_Ioi_of_nonneg hr hs, Measure.smul_apply, smul_eq_mul,
        expMeasure_Ioi_of_neg hr hx', mul_one]
  apply Measure.ext_of_Iic
  intro x
  rw [← compl_Ioi, measure_compl measurableSet_Ioi (measure_ne_top _ _),
    measure_compl measurableSet_Ioi (measure_ne_top _ _), hu, ht]

theorem independent_exponential_residual_law {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) {s : ℝ} (hs : 0 ≤ s) :
    ((Measure.pi (fun j => expMeasure (rate j))).restrict {t | ∀ j, s < t j}).map
      (fun t : ι → ℝ => fun j => t j - s) =
      ENNReal.ofReal (Real.exp (-((∑ j, rate j) * s))) •
        Measure.pi (fun j => expMeasure (rate j)) := by
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  have : ∀ j, IsFiniteMeasure
      (ENNReal.ofReal (Real.exp (-(rate j * s))) • expMeasure (rate j)) := by
    intro j
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  have he : {t : ι → ℝ | ∀ j, s < t j} = Set.pi univ (fun _ => Ioi s) := by
    ext t
    simp [Set.mem_pi]
  rw [he, Measure.restrict_pi_pi]
  have hm : ∀ j, AEMeasurable (fun t : ℝ => t - s)
      ((expMeasure (rate j)).restrict (Ioi s)) :=
    fun _ => (measurable_id.sub_const s).aemeasurable
  rw [Measure.pi_map_pi (μ := fun j => (expMeasure (rate j)).restrict (Ioi s))
    (f := fun _ => fun t : ℝ => t - s) hm]
  simp_rw [exponential_residual_law (hr _) hs]
  have hp : Measure.pi (fun j =>
      ENNReal.ofReal (Real.exp (-(rate j * s))) • expMeasure (rate j)) =
      (∏ j, ENNReal.ofReal (Real.exp (-(rate j * s)))) •
        Measure.pi (fun j => expMeasure (rate j)) := by
    apply Measure.pi_eq
    intro A _hA
    rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
    simp only [Measure.smul_apply, smul_eq_mul]
    exact Finset.prod_mul_distrib.symm
  rw [hp, ← ENNReal.ofReal_prod_of_nonneg (fun j _ => (Real.exp_pos _).le),
    ← Real.exp_sum]
  congr 3
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul]

theorem exponentialPDF_mul_exponential_weight {a b : ℝ}
    (ha : 0 < a) (hab : 0 < a + b) (x : ℝ) :
    exponentialPDF a x * ENNReal.ofReal (Real.exp (-(b * x))) =
      ENNReal.ofReal (a / (a + b)) * exponentialPDF (a + b) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (mul_nonneg ha.le (Real.exp_pos _).le),
      ← ENNReal.ofReal_mul (div_nonneg ha.le hab.le)]
    congr 1
    rw [show -((a + b) * x) = -(a * x) + -(b * x) by ring, Real.exp_add]
    field_simp [hab.ne']
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx),
      exponentialPDF_of_neg (lt_of_not_ge hx), zero_mul, mul_zero]

theorem exponential_weighted_law {a b : ℝ} (ha : 0 < a) (hab : 0 < a + b) :
    (expMeasure a).withDensity (fun s : ℝ => ENNReal.ofReal (Real.exp (-(b * s)))) =
      ENNReal.ofReal (a / (a + b)) • expMeasure (a + b) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (-(b * s)))) := by
    fun_prop
  change (volume.withDensity (exponentialPDF a)).withDensity _ =
    ENNReal.ofReal (a / (a + b)) • volume.withDensity (exponentialPDF (a + b))
  rw [← withDensity_mul volume (measurable_exponentialPDF a) hm]
  have he : exponentialPDF a * (fun s : ℝ => ENNReal.ofReal (Real.exp (-(b * s)))) =
      ENNReal.ofReal (a / (a + b)) • exponentialPDF (a + b) := by
    funext s
    exact exponentialPDF_mul_exponential_weight ha hab s
  rw [he, withDensity_smul _ (measurable_exponentialPDF (a + b))]

theorem expMeasure_ae_nonneg {a : ℝ} (ha : 0 < a) :
    ∀ᵐ s ∂expMeasure a, 0 ≤ s := by
  have : IsProbabilityMeasure (expMeasure a) := isProbabilityMeasure_expMeasure ha
  have ht : ∀ᵐ s ∂expMeasure a, 0 < s := by
    apply (mem_ae_iff_prob_eq_one measurableSet_Ioi).mpr
    simpa using expMeasure_Ioi_of_nonneg ha (show (0 : ℝ) ≤ 0 by rfl)
  exact ht.mono fun _ hs => hs.le

def allAfterFirst {ι : Type*} : Set (ℝ × (ι → ℝ)) :=
  {z | ∀ j, z.1 < z.2 j}

def splitClockResidual {ι : Type*} (z : ℝ × (ι → ℝ)) : ℝ × (ι → ℝ) :=
  (z.1, fun j => z.2 j - z.1)

theorem measurableSet_allAfterFirst {ι : Type*} [Fintype ι] :
    MeasurableSet (allAfterFirst (ι := ι)) := by
  have he : allAfterFirst (ι := ι) = ⋂ j : ι, {z : ℝ × (ι → ℝ) | z.1 < z.2 j} := by
    ext z; simp [allAfterFirst]
  rw [he]
  exact MeasurableSet.iInter fun j => measurableSet_lt measurable_fst
    ((measurable_pi_apply j).comp measurable_snd)

theorem measurable_splitClockResidual {ι : Type*} :
    Measurable (splitClockResidual (ι := ι)) :=
  measurable_fst.prodMk (Measurable.of_eval fun j =>
    ((measurable_pi_apply j).comp measurable_snd).sub measurable_fst)

/-- Joint winning time and nonwinning residual clocks, for a designated
clock separated from the other clocks. The remaining family may be empty. -/
theorem split_exponential_winner_residual_law {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 < a) (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) :
    (((expMeasure a).prod (Measure.pi (fun j => expMeasure (rate j)))).restrict
      allAfterFirst).map splitClockResidual =
      ENNReal.ofReal (a / (a + ∑ j, rate j)) •
        ((expMeasure (a + ∑ j, rate j)).prod
          (Measure.pi (fun j => expMeasure (rate j)))) := by
  have : IsProbabilityMeasure (expMeasure a) := isProbabilityMeasure_expMeasure ha
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  have hsum : 0 ≤ ∑ j, rate j := Finset.sum_nonneg (fun j _ => (hr j).le)
  have htotal : 0 < a + ∑ j, rate j := by linarith
  have : IsProbabilityMeasure (expMeasure (a + ∑ j, rate j)) :=
    isProbabilityMeasure_expMeasure htotal
  have : IsFiniteMeasure (ENNReal.ofReal (a / (a + ∑ j, rate j)) •
      expMeasure (a + ∑ j, rate j)) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.ofReal_lt_top
  have hmweight : Measurable (fun s : ℝ =>
      ENNReal.ofReal (Real.exp (-((∑ j, rate j) * s)))) := by fun_prop
  rw [← Measure.prod_smul_left]
  symm
  apply Measure.prod_eq
  intro A B hA hB
  rw [Measure.map_apply measurable_splitClockResidual (hA.prod hB),
    Measure.restrict_apply ((hA.prod hB).preimage measurable_splitClockResidual),
    Measure.prod_apply (((hA.prod hB).preimage measurable_splitClockResidual).inter
      measurableSet_allAfterFirst)]
  have hfiber : ∀ᵐ s ∂expMeasure a,
      (Measure.pi (fun j => expMeasure (rate j)))
        (Prod.mk s ⁻¹' (splitClockResidual ⁻¹' (A ×ˢ B) ∩ allAfterFirst)) =
      A.indicator (fun s : ℝ => ENNReal.ofReal (Real.exp (-((∑ j, rate j) * s))) *
        (Measure.pi (fun j => expMeasure (rate j))) B) s := by
    filter_upwards [expMeasure_ae_nonneg ha] with s hs
    have hm : Measurable (fun t : ι → ℝ => fun j => t j - s) := by fun_prop
    by_cases hAs : s ∈ A
    · rw [Set.indicator_of_mem hAs]
      have hh := congrArg (fun μ : Measure (ι → ℝ) => μ B)
        (independent_exponential_residual_law rate hr hs)
      rw [Measure.map_apply hm hB, Measure.restrict_apply (hB.preimage hm),
        Measure.smul_apply, smul_eq_mul] at hh
      convert hh using 1
      congr 1
      ext t
      simp [splitClockResidual, allAfterFirst, hAs]
    · rw [Set.indicator_of_notMem hAs]
      have he : Prod.mk s ⁻¹' (splitClockResidual ⁻¹' (A ×ˢ B) ∩
          allAfterFirst) = (∅ : Set (ι → ℝ)) := by
        ext t
        simp [splitClockResidual, allAfterFirst, hAs]
      rw [he, measure_empty]
  calc
    _ = ∫⁻ s, A.indicator (fun s : ℝ =>
        ENNReal.ofReal (Real.exp (-((∑ j, rate j) * s))) *
          (Measure.pi (fun j => expMeasure (rate j))) B) s ∂expMeasure a :=
      lintegral_congr_ae hfiber
    _ = (∫⁻ s in A, ENNReal.ofReal (Real.exp (-((∑ j, rate j) * s))) ∂expMeasure a) *
        (Measure.pi (fun j => expMeasure (rate j))) B := by
      rw [lintegral_indicator hA, lintegral_mul_const _ hmweight]
    _ = ((expMeasure a).withDensity (fun s : ℝ =>
        ENNReal.ofReal (Real.exp (-((∑ j, rate j) * s))))) A *
        (Measure.pi (fun j => expMeasure (rate j))) B := by
      rw [withDensity_apply _ hA]
    _ = _ := by rw [exponential_weighted_law ha htotal]

def winnerResidual {ι : Type*} (i : ι) (t : ι → ℝ) : ℝ × ({j // j ≠ i} → ℝ) :=
  (t i, fun j => t j - t i)

theorem measurable_winnerResidual {ι : Type*} (i : ι) :
    Measurable (winnerResidual i) :=
  (measurable_pi_apply i).prodMk (Measurable.of_eval fun j =>
    (measurable_pi_apply (j : ι)).sub (measurable_pi_apply i))

/-- Exact joint winner, winning time and residual-clock law. This equality
also covers a singleton family, whose remaining clock product is empty. -/
theorem independent_exponential_winner_residual_law {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) (i : ι) :
    ((Measure.pi (fun j => expMeasure (rate j))).restrict (clockWins i)).map
      (winnerResidual i) = ENNReal.ofReal (rate i / ∑ j, rate j) •
        ((expMeasure (∑ j, rate j)).prod
          (Measure.pi (fun j : {j // j ≠ i} => expMeasure (rate j)))) := by
  have hm : Measurable (fun t : ι → ℝ => (t i, fun j : {j // j ≠ i} => t j)) :=
    (measurable_pi_apply i).prodMk
      (Measurable.of_eval fun j => measurable_pi_apply (j : ι))
  have hW : clockWins i = (fun t : ι → ℝ =>
      (t i, fun j : {j // j ≠ i} => t j)) ⁻¹' allAfterFirst := by
    ext t
    change (∀ j, j ≠ i → t i < t j) ↔ ∀ j : {j // j ≠ i}, t i < t j
    constructor
    · intro h j; exact h j j.property
    · intro h j hj; exact h ⟨j, hj⟩
  calc
    _ = (((Measure.pi (fun j => expMeasure (rate j))).restrict (clockWins i)).map
        (fun t : ι → ℝ => (t i, fun j : {j // j ≠ i} => t j))).map
        splitClockResidual := by
      rw [Measure.map_map measurable_splitClockResidual hm]
      rfl
    _ = (((Measure.pi (fun j => expMeasure (rate j))).map
        (fun t : ι → ℝ => (t i, fun j : {j // j ≠ i} => t j))).restrict
        allAfterFirst).map splitClockResidual := by
      rw [Measure.restrict_map hm measurableSet_allAfterFirst, ← hW]
    _ = _ := by
      rw [independent_clock_split_law rate hr i,
        split_exponential_winner_residual_law (hr i)
          (fun j : {j // j ≠ i} => rate j) (fun j => hr j), ← sum_rate_split rate i]

theorem clockWins_earliestClock {ι : Type*} [Fintype ι] [Nonempty ι]
    {i : ι} {t : ι → ℝ} (hi : t ∈ clockWins i) : earliestClock t = t i := by
  apply le_antisymm (Finset.inf'_le _ (Finset.mem_univ i))
  change t i ≤ Finset.univ.inf' Finset.univ_nonempty t
  rw [Finset.le_inf'_iff]
  intro j _
  by_cases hji : j = i
  · rw [hji]
  · exact (hi j hji).le

/-- The winning time in the preceding factorization is the actual minimum
of the entire clock family, and the residuals subtract that minimum. -/
theorem independent_exponential_winner_minimum_residual_law {ι : Type*}
    [Fintype ι] [Nonempty ι] (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) (i : ι) :
    ((Measure.pi (fun j => expMeasure (rate j))).restrict (clockWins i)).map
      (fun t : ι → ℝ => (earliestClock t,
        fun j : {j // j ≠ i} => t j - earliestClock t)) =
      ENNReal.ofReal (rate i / ∑ j, rate j) •
        ((expMeasure (∑ j, rate j)).prod
          (Measure.pi (fun j : {j // j ≠ i} => expMeasure (rate j)))) := by
  rw [← independent_exponential_winner_residual_law rate hr i]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (measurableSet_clockWins i)] with t ht
  simp only [clockWins_earliestClock ht]
  rfl

end Freezing1.SIR
