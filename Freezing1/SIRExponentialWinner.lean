module

public import Freezing1.SIRExponentialRace

/-!
# The individual winner in a finite exponential race

Winner events are strict comparisons of the actual independent clocks.
The selected clock is split from the remaining product, whose minimum has
the verified exponential law. This identifies the individual winner weights
without assuming an abstract race or selection law.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def clockWins {ι : Type*} (i : ι) : Set (ι → ℝ) :=
  {t | ∀ j, j ≠ i → t i < t j}

theorem measurableSet_clockWins {ι : Type*} [Fintype ι] (i : ι) :
    MeasurableSet (clockWins i) := by
  have he : clockWins i = ⋂ j : ι, {t : ι → ℝ | j ≠ i → t i < t j} := by
    ext t
    simp [clockWins]
  rw [he]
  apply MeasurableSet.iInter
  intro j
  by_cases hj : j = i
  · simp [hj]
  · simpa [hj] using measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

theorem clockWins_disjoint {ι : Type*} {i j : ι} (hij : i ≠ j) :
    Disjoint (clockWins i) (clockWins j) := by
  apply Set.disjoint_left.mpr
  intro t hi hj
  exact (hi j hij.symm).not_gt (hj i hij)

theorem independent_clock_split_law {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ i, 0 < rate i) (i : ι) :
    (Measure.pi (fun j => expMeasure (rate j))).map
      (fun t : ι → ℝ => (t i, fun j : {j // j ≠ i} => t j)) =
      (expMeasure (rate i)).prod
        (Measure.pi (fun j : {j // j ≠ i} => expMeasure (rate j))) := by
  let : Fintype {j // j = i} := Subtype.fintype (fun j : ι => j = i)
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun j => j = i)
  have hs := (measurePreserving_piEquivPiSubtypeProd
    (fun j => expMeasure (rate j)) (fun j => j = i)).map_eq
  have he := (measurePreserving_eval
    (fun j : {j // j = i} => expMeasure (rate j)) ⟨i, rfl⟩).map_eq
  calc
    _ = ((Measure.pi (fun j => expMeasure (rate j))).map e).map
        (Prod.map (fun t : {j // j = i} → ℝ => t ⟨i, rfl⟩) id) := by
      rw [Measure.map_map
        ((measurable_pi_apply ⟨i, rfl⟩).prodMap measurable_id) e.measurable]
      rfl
    _ = _ := by
      rw [hs]
      have hmap := Measure.map_prod_map
        (Measure.pi (fun j : {j // j = i} => expMeasure (rate j)))
        (Measure.pi (fun j : {j // j ≠ i} => expMeasure (rate j)))
        (show Measurable (fun t : {j // j = i} → ℝ => t ⟨i, rfl⟩) from
          measurable_pi_apply (⟨i, rfl⟩ : {j // j = i}))
        (show Measurable (id : ({j // j ≠ i} → ℝ) → _) from measurable_id)
      rw [← hmap, he, Measure.map_id]

theorem independent_clock_and_rest_minimum {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ i, 0 < rate i) (i : ι)
    [Nonempty {j // j ≠ i}] :
    (Measure.pi (fun j => expMeasure (rate j))).map
      (fun t : ι → ℝ => (t i, earliestClock (fun j : {j // j ≠ i} => t j))) =
      (expMeasure (rate i)).prod (expMeasure (∑ j : {j // j ≠ i}, rate j)) := by
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  have hs := independent_clock_split_law rate hr i
  have hm : Measurable (fun t : ι → ℝ => (t i, fun j : {j // j ≠ i} => t j)) :=
    (measurable_pi_apply i).prodMk
      (Measurable.of_eval fun j => measurable_pi_apply (j : ι))
  calc
    _ = ((Measure.pi (fun j => expMeasure (rate j))).map
        (fun t : ι → ℝ => (t i, fun j : {j // j ≠ i} => t j))).map
        (Prod.map id earliestClock) := by
      rw [Measure.map_map (measurable_id.prodMap measurable_earliestClock) hm]
      rfl
    _ = _ := by
      rw [hs, ← Measure.map_prod_map _ _ measurable_id measurable_earliestClock,
        Measure.map_id, earliestClock_law (fun j : {j // j ≠ i} => rate j)
          (fun j => hr j)]

theorem sum_rate_split {ι : Type*} [Fintype ι] (rate : ι → ℝ) (i : ι) :
    (∑ j, rate j) = rate i + ∑ j : {j // j ≠ i}, rate j := by
  let : Fintype {j // j = i} := Subtype.fintype (fun j : ι => j = i)
  have : Subsingleton {j // j = i} :=
    ⟨fun a b => Subtype.ext (a.property.trans b.property.symm)⟩
  have hs := Fintype.sum_subtype_add_sum_subtype (fun j => j = i) rate
  rw [Fintype.sum_subsingleton _ ⟨i, rfl⟩] at hs
  exact hs.symm

/-- Exact winner probabilities for an arbitrary finite family of actual
independent exponential clocks, including a singleton family. -/
theorem independent_exponential_clock_wins {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) (i : ι) :
    (Measure.pi (fun j => expMeasure (rate j))) (clockWins i) =
      ENNReal.ofReal (rate i / ∑ j, rate j) := by
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  by_cases hn : Nonempty {j // j ≠ i}
  · let := hn
    have hsum : 0 < ∑ j : {j // j ≠ i}, rate j :=
      Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
    have hm : Measurable (fun t : ι → ℝ =>
        (t i, earliestClock (fun j : {j // j ≠ i} => t j))) :=
      (measurable_pi_apply i).prodMk
        (measurable_earliestClock.comp (Measurable.of_eval
          (fun j : {j // j ≠ i} => measurable_pi_apply (j : ι))))
    have hW : clockWins i = (fun t : ι → ℝ =>
        (t i, earliestClock (fun j : {j // j ≠ i} => t j))) ⁻¹'
        {z : ℝ × ℝ | z.1 < z.2} := by
      ext t
      simp only [clockWins, Set.mem_ofPred_eq, Set.mem_preimage,
        earliestClock, Finset.lt_inf'_iff, Finset.mem_univ, forall_const]
      constructor
      · intro ht j; exact ht j j.property
      · intro ht j hj; exact ht ⟨j, hj⟩
    rw [hW, ← Measure.map_apply hm (measurableSet_lt measurable_fst measurable_snd),
      independent_clock_and_rest_minimum rate hr i,
      exponential_race_left (hr i) hsum, sum_rate_split rate i]
  · have hi : ∀ j, j = i := by
      intro j
      by_contra hj
      exact hn ⟨⟨j, hj⟩⟩
    have : Subsingleton ι := ⟨fun a b => (hi a).trans (hi b).symm⟩
    have hW : clockWins i = Set.univ := by
      apply Set.eq_univ_of_forall
      intro t j hj
      exact (hj (hi j)).elim
    rw [hW, measure_univ, Fintype.sum_subsingleton rate i,
      div_self (hr i).ne', ENNReal.ofReal_one]

theorem independent_exponential_has_winner {ι : Type*} [Fintype ι] [Nonempty ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) :
    ∀ᵐ t ∂Measure.pi (fun j => expMeasure (rate j)), ∃ i, t ∈ clockWins i := by
  have : ∀ j, IsProbabilityMeasure (expMeasure (rate j)) :=
    fun j => isProbabilityMeasure_expMeasure (hr j)
  have hs : 0 < ∑ j, rate j := Finset.sum_pos (fun j _ => hr j) Finset.univ_nonempty
  have he : {t : ι → ℝ | ∃ i, t ∈ clockWins i} = ⋃ i, clockWins i := by
    ext t
    simp
  apply (mem_ae_iff_prob_eq_one
    (show MeasurableSet {t : ι → ℝ | ∃ i, t ∈ clockWins i} from
      he.symm ▸ MeasurableSet.iUnion measurableSet_clockWins)).mpr
  rw [he, measure_iUnion (fun i j hij => clockWins_disjoint hij) measurableSet_clockWins,
    tsum_fintype]
  simp_rw [independent_exponential_clock_wins rate hr]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => div_nonneg (hr j).le hs.le),
    ← Finset.sum_div, div_self hs.ne', ENNReal.ofReal_one]

theorem independent_two_clock_law {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) (i j : ι) (hji : j ≠ i) :
    (Measure.pi (fun k => expMeasure (rate k))).map (fun t : ι → ℝ => (t i, t j)) =
      (expMeasure (rate i)).prod (expMeasure (rate j)) := by
  have : ∀ k, IsProbabilityMeasure (expMeasure (rate k)) :=
    fun k => isProbabilityMeasure_expMeasure (hr k)
  have hs := independent_clock_split_law rate hr i
  have he := (measurePreserving_eval
    (fun k : {k // k ≠ i} => expMeasure (rate k)) ⟨j, hji⟩).map_eq
  have hm : Measurable (fun t : ι → ℝ => (t i, fun k : {k // k ≠ i} => t k)) :=
    (measurable_pi_apply i).prodMk
      (Measurable.of_eval fun k => measurable_pi_apply (k : ι))
  calc
    _ = ((Measure.pi (fun k => expMeasure (rate k))).map
        (fun t : ι → ℝ => (t i, fun k : {k // k ≠ i} => t k))).map
        (Prod.map id (fun t : {k // k ≠ i} → ℝ => t ⟨j, hji⟩)) := by
      rw [Measure.map_map
        (measurable_id.prodMap (measurable_pi_apply ⟨j, hji⟩)) hm]
      rfl
    _ = _ := by
      rw [hs]
      have hmap := Measure.map_prod_map (expMeasure (rate i))
        (Measure.pi (fun k : {k // k ≠ i} => expMeasure (rate k)))
        (show Measurable (id : ℝ → ℝ) from measurable_id)
        (show Measurable (fun t : {k // k ≠ i} → ℝ => t ⟨j, hji⟩) from
          measurable_pi_apply (⟨j, hji⟩ : {k // k ≠ i}))
      rw [← hmap, Measure.map_id, he]

theorem independent_exponential_pair_tie_null {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) (i j : ι) (hji : j ≠ i) :
    (Measure.pi (fun k => expMeasure (rate k))) {t | t i = t j} = 0 := by
  have : IsProbabilityMeasure (expMeasure (rate j)) := isProbabilityMeasure_expMeasure (hr j)
  have : NullSingletonClass (expMeasure (rate j)) := by
    change NullSingletonClass (volume.withDensity (gammaPDF 1 (rate j)))
    infer_instance
  have hprod : ((expMeasure (rate i)).prod (expMeasure (rate j)))
      {z : ℝ × ℝ | z.1 = z.2} = 0 := by
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    have hsingle : ∀ x : ℝ, {y : ℝ | x = y} = {x} := by
      intro x; ext y; simp [eq_comm]
    simp only [Set.preimage_ofPred_eq, hsingle, measure_singleton, lintegral_zero]
  have hm : Measurable (fun t : ι → ℝ => (t i, t j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  have he := independent_two_clock_law rate hr i j hji
  have hh := congrArg (fun μ : Measure (ℝ × ℝ) => μ {z | z.1 = z.2}) he
  rw [Measure.map_apply hm (measurableSet_eq_fun measurable_fst measurable_snd), hprod] at hh
  exact hh

theorem independent_exponential_no_ties {ι : Type*} [Fintype ι]
    (rate : ι → ℝ) (hr : ∀ j, 0 < rate j) :
    ∀ᵐ t ∂Measure.pi (fun j => expMeasure (rate j)), Function.Injective t := by
  apply (ae_all_iff).mpr
  intro i
  apply (ae_all_iff).mpr
  intro j
  by_cases hji : j = i
  · exact Filter.Eventually.of_forall fun _ _ => hji.symm
  · have hnull := independent_exponential_pair_tie_null rate hr i j hji
    have hn : ∀ᵐ t ∂Measure.pi (fun k => expMeasure (rate k)), t i ≠ t j :=
      by rw [ae_iff]; simpa only [not_not] using hnull
    exact hn.mono fun _ ht he => (ht he).elim

abbrev IndividualClockIndex (i u : ℕ) := (Fin i × Fin u) ⊕ Fin i

def individualClockRate (r : ℝ) (i u : ℕ) : IndividualClockIndex i u → ℝ :=
  Sum.elim (fun _ => r) (fun _ => 1)

def combineClockTimes {i u : ℕ}
    (z : ((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) : IndividualClockIndex i u → ℝ :=
  Sum.elim z.1 z.2

theorem measurable_combineClockTimes (i u : ℕ) :
    Measurable (combineClockTimes (i := i) (u := u)) := by
  apply Measurable.of_eval
  intro w
  cases w with
  | inl w => exact (measurable_pi_apply w).comp measurable_fst
  | inr w => exact (measurable_pi_apply w).comp measurable_snd

def individualClockWins {i u : ℕ} (w : IndividualClockIndex i u) :
    Set (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  combineClockTimes ⁻¹' clockWins w

theorem measurableSet_individualClockWins {i u : ℕ} (w : IndividualClockIndex i u) :
    MeasurableSet (individualClockWins w) :=
  (measurableSet_clockWins w).preimage (measurable_combineClockTimes i u)

theorem individualClockWins_disjoint {i u : ℕ} {w v : IndividualClockIndex i u}
    (hwv : w ≠ v) : Disjoint (individualClockWins w) (individualClockWins v) :=
  (clockWins_disjoint hwv).preimage combineClockTimes

theorem individualClockRate_pos {r : ℝ} (hr : 0 < r) (i u : ℕ)
    (w : IndividualClockIndex i u) : 0 < individualClockRate r i u w := by
  cases w <;> simp [individualClockRate, hr]

theorem individualClockRate_sum (r : ℝ) (i u : ℕ) :
    (∑ w : IndividualClockIndex i u, individualClockRate r i u w) =
      (i : ℝ) * (1 + r * u) := by
  simp only [IndividualClockIndex, Fintype.sum_sum_type, individualClockRate,
    Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  ring

theorem individualClock_combined_law {r : ℝ} (hr : 0 < r) (i u : ℕ) :
    (individualClockLaw r i u).map combineClockTimes =
      Measure.pi (fun w => expMeasure (individualClockRate r i u w)) := by
  have : ∀ w : IndividualClockIndex i u,
      IsProbabilityMeasure (expMeasure (individualClockRate r i u w)) :=
    fun w => isProbabilityMeasure_expMeasure (individualClockRate_pos hr i u w)
  exact (measurePreserving_sumPiEquivProdPi_symm
    (fun w : IndividualClockIndex i u => expMeasure (individualClockRate r i u w))).map_eq

theorem individualClock_wins_probability {r : ℝ} (hr : 0 < r) (i u : ℕ)
    (w : IndividualClockIndex i u) :
    individualClockLaw r i u (individualClockWins w) =
      ENNReal.ofReal (individualClockRate r i u w / ((i : ℝ) * (1 + r * u))) := by
  rw [individualClockWins, ← Measure.map_apply (measurable_combineClockTimes i u)
    (measurableSet_clockWins w), individualClock_combined_law hr i u,
    independent_exponential_clock_wins _ (individualClockRate_pos hr i u),
    individualClockRate_sum]

theorem individualClock_has_winner {r : ℝ} (hr : 0 < r) (i u : ℕ) [NeZero i] :
    ∀ᵐ z ∂individualClockLaw r i u, ∃ w, z ∈ individualClockWins w := by
  have hh := independent_exponential_has_winner (individualClockRate r i u)
    (individualClockRate_pos hr i u)
  rw [← individualClock_combined_law hr i u] at hh
  exact ae_of_ae_map (measurable_combineClockTimes i u).aemeasurable hh

theorem individualClock_no_ties {r : ℝ} (hr : 0 < r) (i u : ℕ) :
    ∀ᵐ z ∂individualClockLaw r i u, Function.Injective (combineClockTimes z) := by
  have hh := independent_exponential_no_ties (individualClockRate r i u)
    (individualClockRate_pos hr i u)
  rw [← individualClock_combined_law hr i u] at hh
  exact ae_of_ae_map (measurable_combineClockTimes i u).aemeasurable hh

theorem individualClock_winners_among_probability {κ : Type*} [Fintype κ]
    {r : ℝ} (hr : 0 < r) (i u : ℕ) [NeZero i]
    (pick : κ → IndividualClockIndex i u) (hpick : Function.Injective pick) :
    individualClockLaw r i u (⋃ k, individualClockWins (pick k)) =
      ENNReal.ofReal ((∑ k, individualClockRate r i u (pick k)) /
        ((i : ℝ) * (1 + r * u))) := by
  have hi : (0 : ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne i)
  have hd : 0 < (i : ℝ) * (1 + r * u) := by positivity
  rw [measure_iUnion (fun k l hkl => individualClockWins_disjoint
    (fun he => hkl (hpick he))) (fun k => measurableSet_individualClockWins (pick k)),
    tsum_fintype]
  simp_rw [individualClock_wins_probability hr i u]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ =>
    div_nonneg (individualClockRate_pos hr i u (pick k)).le hd.le), ← Finset.sum_div]

def individualClockInfectionBy {i u : ℕ} (j : Fin i) :
    Set (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  ⋃ v : Fin u, individualClockWins (Sum.inl (j, v))

def individualClockRecoveryBy {i u : ℕ} (j : Fin i) :
    Set (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  individualClockWins (Sum.inr j)

/-- The contact winner specifies both an infectious individual and a
susceptible recipient. -/
theorem individualClock_contact_winner_probability {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] (j : Fin i) (v : Fin u) :
    individualClockLaw r i u (individualClockWins (Sum.inl (j, v))) =
      ENNReal.ofReal ((1 / (i : ℝ)) * (r / (1 + r * u))) := by
  rw [individualClock_wins_probability hr i u]
  congr 1
  simp only [individualClockRate, Sum.elim_inl, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The responsible infectious individual has weight 1/I independently of
the infection event type. The empty susceptible set is permitted. -/
theorem individualClock_infection_by_probability {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] (j : Fin i) :
    individualClockLaw r i u (individualClockInfectionBy j) =
      ENNReal.ofReal ((1 / (i : ℝ)) * (r * u / (1 + r * u))) := by
  rw [individualClockInfectionBy, individualClock_winners_among_probability hr i u
    (fun v : Fin u => Sum.inl (j, v)) (by
      intro v w he; exact congrArg Prod.snd (Sum.inl.inj he))]
  congr 1
  simp only [individualClockRate, Sum.elim_inl, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- The responsible infectious individual has the same uniform factor for
the recovery event type. -/
theorem individualClock_recovery_by_probability {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] (j : Fin i) :
    individualClockLaw r i u (individualClockRecoveryBy j) =
      ENNReal.ofReal ((1 / (i : ℝ)) * (1 / (1 + r * u))) := by
  rw [individualClockRecoveryBy, individualClock_wins_probability hr i u]
  congr 1
  simp only [individualClockRate, Sum.elim_inr, div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- Conditional on an infection by a fixed infectious individual, the
susceptible recipient is uniform. This is expressed as an exact joint weight. -/
theorem individualClock_recipient_uniform {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] [NeZero u] (j : Fin i) (v : Fin u) :
    individualClockLaw r i u (individualClockWins (Sum.inl (j, v))) =
      ENNReal.ofReal (1 / (u : ℝ)) *
        individualClockLaw r i u (individualClockInfectionBy j) := by
  rw [individualClock_contact_winner_probability hr i u,
    individualClock_infection_by_probability hr i u,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hu : (u : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne u
  field_simp [hu]

def individualClockInfection (i u : ℕ) :
    Set (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  ⋃ w : Fin i × Fin u, individualClockWins (Sum.inl w)

def individualClockRecovery (i u : ℕ) :
    Set (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  ⋃ j : Fin i, individualClockWins (Sum.inr j)

def individualClockSelected {i u : ℕ} (j : Fin i) :
    Set (((Fin i × Fin u) → ℝ) × (Fin i → ℝ)) :=
  individualClockInfectionBy j ∪ individualClockRecoveryBy j

theorem individualClock_infection_probability {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] :
    individualClockLaw r i u (individualClockInfection i u) =
      ENNReal.ofReal (r * u / (1 + r * u)) := by
  rw [individualClockInfection, individualClock_winners_among_probability hr i u
    (Sum.inl : (Fin i × Fin u) → IndividualClockIndex i u) Sum.inl_injective]
  congr 1
  simp only [individualClockRate, Sum.elim_inl, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  have hi : (i : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne i
  have hd : (1 + r * u : ℝ) ≠ 0 := by positivity
  field_simp [hi, hd]

theorem individualClock_recovery_probability {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] :
    individualClockLaw r i u (individualClockRecovery i u) =
      ENNReal.ofReal (1 / (1 + r * u)) := by
  rw [individualClockRecovery, individualClock_winners_among_probability hr i u
    (Sum.inr : Fin i → IndividualClockIndex i u) Sum.inr_injective]
  congr 1
  simp only [individualClockRate, Sum.elim_inr, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hi : (i : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne i
  have hd : (1 + r * u : ℝ) ≠ 0 := by positivity
  field_simp [hi, hd]

theorem individualClock_selected_uniform {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] (j : Fin i) :
    individualClockLaw r i u (individualClockSelected j) =
      ENNReal.ofReal (1 / (i : ℝ)) := by
  have hdis : Disjoint (individualClockInfectionBy (u := u) j)
      (individualClockRecoveryBy (u := u) j) := by
    apply Set.disjoint_iUnion_left.mpr
    intro v
    exact individualClockWins_disjoint (by simp)
  rw [individualClockSelected, measure_union hdis
    (measurableSet_individualClockWins (Sum.inr j)),
    individualClock_infection_by_probability hr i u,
    individualClock_recovery_by_probability hr i u,
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  have hd : (1 + r * u : ℝ) ≠ 0 := by positivity
  field_simp [hd]
  ring

/-- Exact factorization of the selected infectious individual and event
type, derived from the individual exponential clocks. -/
theorem individualClock_selected_kind_factorization {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] (j : Fin i) :
    (individualClockLaw r i u (individualClockInfectionBy j) =
      individualClockLaw r i u (individualClockSelected j) *
        individualClockLaw r i u (individualClockInfection i u)) ∧
    (individualClockLaw r i u (individualClockRecoveryBy j) =
      individualClockLaw r i u (individualClockSelected j) *
        individualClockLaw r i u (individualClockRecovery i u)) := by
  rw [individualClock_infection_by_probability hr i u,
    individualClock_recovery_by_probability hr i u,
    individualClock_selected_uniform hr i u,
    individualClock_infection_probability hr i u,
    individualClock_recovery_probability hr i u]
  constructor <;> exact ENNReal.ofReal_mul (by positivity)

theorem individualClockSelected_inter_infection {i u : ℕ} (j : Fin i) :
    individualClockSelected j ∩ individualClockInfection i u =
      individualClockInfectionBy j := by
  ext z
  simp only [individualClockSelected, individualClockInfection,
    individualClockInfectionBy, individualClockRecoveryBy,
    Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨(⟨v, hv⟩ | hr), ⟨w, hw⟩⟩
    · exact ⟨v, hv⟩
    · exact (Set.disjoint_left.mp (individualClockWins_disjoint (by simp)) hw hr).elim
  · rintro ⟨v, hv⟩
    exact ⟨Or.inl ⟨v, hv⟩, ⟨(j, v), hv⟩⟩

theorem individualClockSelected_inter_recovery {i u : ℕ} (j : Fin i) :
    individualClockSelected j ∩ individualClockRecovery i u =
      individualClockRecoveryBy j := by
  ext z
  simp only [individualClockSelected, individualClockRecovery,
    individualClockInfectionBy, individualClockRecoveryBy,
    Set.mem_inter_iff, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro ⟨(⟨v, hv⟩ | hr), ⟨k, hk⟩⟩
    · exact (Set.disjoint_left.mp (individualClockWins_disjoint (by simp)) hv hk).elim
    · exact hr
  · intro hr
    exact ⟨Or.inr hr, ⟨j, hr⟩⟩

theorem individualClock_selected_kind_independent {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] (j : Fin i) :
    (individualClockLaw r i u (individualClockSelected j ∩ individualClockInfection i u) =
      individualClockLaw r i u (individualClockSelected j) *
        individualClockLaw r i u (individualClockInfection i u)) ∧
    (individualClockLaw r i u (individualClockSelected j ∩ individualClockRecovery i u) =
      individualClockLaw r i u (individualClockSelected j) *
        individualClockLaw r i u (individualClockRecovery i u)) := by
  rw [individualClockSelected_inter_infection, individualClockSelected_inter_recovery]
  exact individualClock_selected_kind_factorization hr i u j

/-- With contacts disabled, sample only the positive-rate recovery clocks.
This is the finite-clock model for zero contact rate; it does not introduce
a nonempty family of exponential clocks of rate zero. -/
noncomputable def disabledContactClockLaw (i : ℕ) : Measure (Fin i → ℝ) :=
  Measure.pi (fun _ : Fin i => expMeasure 1)

theorem disabledContactClock_selected_uniform (i : ℕ) (j : Fin i) :
    disabledContactClockLaw i (clockWins j) = ENNReal.ofReal (1 / (i : ℝ)) := by
  rw [disabledContactClockLaw, independent_exponential_clock_wins
    (fun _ : Fin i => (1 : ℝ)) (fun _ => by norm_num)]
  simp

theorem disabledContactClock_has_winner (i : ℕ) [NeZero i] :
    ∀ᵐ t ∂disabledContactClockLaw i, ∃ j, t ∈ clockWins j :=
  independent_exponential_has_winner (fun _ : Fin i => (1 : ℝ)) (fun _ => by norm_num)

theorem disabledContactClock_no_ties (i : ℕ) :
    ∀ᵐ t ∂disabledContactClockLaw i, Function.Injective t :=
  independent_exponential_no_ties (fun _ : Fin i => (1 : ℝ)) (fun _ => by norm_num)

theorem individualClock_contact_winner_minima_lt (i u : ℕ) [NeZero i] [NeZero u]
    {z : ((Fin i × Fin u) → ℝ) × (Fin i → ℝ)} {w : Fin i × Fin u}
    (hw : z ∈ individualClockWins (Sum.inl w)) :
    earliestClock z.1 < earliestClock z.2 := by
  have hc : earliestClock z.1 ≤ z.1 w :=
    Finset.inf'_le _ (Finset.mem_univ w)
  have hr : z.1 w < earliestClock z.2 := by
    change z.1 w < Finset.univ.inf' Finset.univ_nonempty z.2
    simp only [Finset.lt_inf'_iff, Finset.mem_univ, forall_const]
    intro k
    exact hw (Sum.inr k) (by simp)
  exact hc.trans_lt hr

theorem individualClock_recovery_winner_minima_lt (i u : ℕ) [NeZero i] [NeZero u]
    {z : ((Fin i × Fin u) → ℝ) × (Fin i → ℝ)} {j : Fin i}
    (hj : z ∈ individualClockWins (Sum.inr j)) :
    earliestClock z.2 < earliestClock z.1 := by
  have hr : earliestClock z.2 ≤ z.2 j :=
    Finset.inf'_le _ (Finset.mem_univ j)
  have hc : z.2 j < earliestClock z.1 := by
    change z.2 j < Finset.univ.inf' Finset.univ_nonempty z.1
    simp only [Finset.lt_inf'_iff, Finset.mem_univ, forall_const]
    intro w
    exact hj (Sum.inl w) (by simp)
  exact hr.trans_lt hc

/-- The event kinds defined by the unique individual clock winner agree
almost surely with comparison of the two aggregate minima. -/
theorem individualClock_kind_minima_ae {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] [NeZero u] :
    ∀ᵐ z ∂individualClockLaw r i u,
      ((z ∈ individualClockInfection i u) ↔ earliestClock z.1 < earliestClock z.2) ∧
      ((z ∈ individualClockRecovery i u) ↔ earliestClock z.2 < earliestClock z.1) := by
  filter_upwards [individualClock_has_winner hr i u] with z hz
  constructor
  · constructor
    · intro h
      obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
      exact individualClock_contact_winner_minima_lt i u hw
    · intro h
      obtain ⟨w, hw⟩ := hz
      cases w with
      | inl w => exact Set.mem_iUnion.mpr ⟨w, hw⟩
      | inr j => exact (h.not_gt (individualClock_recovery_winner_minima_lt i u hw)).elim
  · constructor
    · intro h
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
      exact individualClock_recovery_winner_minima_lt i u hj
    · intro h
      obtain ⟨w, hw⟩ := hz
      cases w with
      | inl w => exact (h.not_gt (individualClock_contact_winner_minima_lt i u hw)).elim
      | inr j => exact Set.mem_iUnion.mpr ⟨j, hw⟩

/-- Joint probabilities for the responsible infectious individual and the
actual aggregate-minimum event type in the finite SIR race. -/
theorem individualClock_selected_minima_joint_probability {r : ℝ} (hr : 0 < r)
    (i u : ℕ) [NeZero i] [NeZero u] (j : Fin i) :
    (individualClockLaw r i u {z | z ∈ individualClockSelected j ∧
        earliestClock z.1 < earliestClock z.2} =
      ENNReal.ofReal ((1 / (i : ℝ)) * (r * u / (1 + r * u)))) ∧
    (individualClockLaw r i u {z | z ∈ individualClockSelected j ∧
        earliestClock z.2 < earliestClock z.1} =
      ENNReal.ofReal ((1 / (i : ℝ)) * (1 / (1 + r * u)))) := by
  constructor
  · calc
      _ = individualClockLaw r i u
          (individualClockSelected j ∩ individualClockInfection i u) := by
        apply measure_congr
        filter_upwards [individualClock_kind_minima_ae hr i u] with z hz
        exact propext (and_congr_right fun _ => hz.1.symm)
      _ = _ := by
        rw [individualClockSelected_inter_infection]
        exact individualClock_infection_by_probability hr i u j
  · calc
      _ = individualClockLaw r i u
          (individualClockSelected j ∩ individualClockRecovery i u) := by
        apply measure_congr
        filter_upwards [individualClock_kind_minima_ae hr i u] with z hz
        exact propext (and_congr_right fun _ => hz.2.symm)
      _ = _ := by
        rw [individualClockSelected_inter_recovery]
        exact individualClock_recovery_by_probability hr i u j

end Freezing1.SIR
