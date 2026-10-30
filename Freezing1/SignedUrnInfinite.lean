module

public import Freezing1.SignedUrnMaximal
public import Mathlib.MeasureTheory.Measure.Continuity

/-!
# Infinite-time concentration from the actual finite path laws

The process assumption here specifies its complete finite-dimensional laws as
the iterated urn kernel. This is a Markov-law assumption, stronger than the
paper's displayed conditioning on the current occupancy alone. No maximal
estimate or martingale bound is included in that assumption.
-/

@[expose] public section

namespace Freezing1.SignedUrn

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- Record k transitions, beginning at time a. -/
def record {Ω : Type*} (U : ℕ → Ω → ℤ) : ℕ → ℕ → Ω → Trajectory
  | a, 0, ω => ⟨[U a ω]⟩
  | a, k + 1, ω => prepend (U a ω) (record U (a + 1) k ω)

theorem deviates_record_iff {Ω : Type*} (Z : ℕ → ℤ) (U : ℕ → Ω → ℤ)
    (x t : ℝ) (a k : ℕ) (ω : Ω) :
    deviates Z x t a (record U a k ω).values ↔
      ∃ i, i ≤ k ∧ t * x < |(U (a + i) ω : ℝ) / Z (a + i) - x| := by
  induction k generalizing a with
  | zero => simp [record, deviates]
  | succ k ih =>
    simp only [record, prepend, deviates, ih]
    constructor
    · rintro (h | ⟨i, hi, hd⟩)
      · exact ⟨0, by omega, by simpa using h⟩
      · refine ⟨i + 1, by omega, ?_⟩
        simpa only [Nat.add_assoc, Nat.add_comm 1] using hd
    · rintro ⟨i, hi, hd⟩
      cases i with
      | zero => exact Or.inl (by simpa using hd)
      | succ i =>
        refine Or.inr ⟨i, by omega, ?_⟩
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1] using hd

/-- A process has the urn's full finite path laws; in particular the choice at
each step is conditional on the whole predecessor trajectory. -/
def HasPathLaws {Ω : Type*} [MeasurableSpace Ω] (U : ℕ → Ω → ℤ)
    (Z : ℕ → ℤ) (u : ℤ) (μ : Measure Ω) : Prop :=
  ∀ k, HasLaw (record U 0 k) (pathLaw Z 0 k u) μ

/-- Infinite-time maximal estimate for the Markov urn law. The deterministic
budgets are uniform in the finite horizon and do not assume probability bounds. -/
theorem infinite_maximal_of_pathLaws {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℤ) (Z : ℕ → ℤ) {u : ℤ}
    (hlaw : HasPathLaws U Z u μ) (hZ : ∀ i, 0 < Z i)
    (hz : ∀ i, Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hu : 0 ≤ u) (huZ : u ≤ Z 0) {D M t : ℝ} (hD : 0 < D) (hDM : D ≤ M)
    (hbudget : ∀ k, squareBudget Z 0 k ≤ D)
    (hinc : ∀ i, 0 < i → (Z i : ℝ)⁻¹ ≤ M) (ht : 0 ≤ t) :
    μ.real {ω | ∃ i : ℕ, t * ((u : ℝ) / Z 0) <
      |(U i ω : ℝ) / Z i - (u : ℝ) / Z 0|} ≤
      2 * Real.exp (-(t ^ 2 * ((u : ℝ) / Z 0)) / (4 * (D + t * M))) := by
  let E : ℕ → Set Ω := fun k => {ω | ∃ i, i ≤ k ∧ t * ((u : ℝ) / Z 0) <
    |(U i ω : ℝ) / Z i - (u : ℝ) / Z 0|}
  let B := 2 * Real.exp (-(t ^ 2 * ((u : ℝ) / Z 0)) / (4 * (D + t * M)))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he : ∀ k, μ.real (E k) ≤ B := by
    intro k
    have hl := (hlaw k).measureReal_eq
      (p := fun H => deviates Z ((u : ℝ) / Z 0) t 0 H.values) (by trivial)
    simp only [deviates_record_iff, Nat.zero_add] at hl
    change μ.real (E k) = _ at hl
    rw [hl]
    exact pathLaw_maximal_optimized Z (fun i _ => hZ i) (fun i _ => hz i)
      hu huZ hD hDM (hbudget k) (fun i hi => hinc i (Finset.mem_Ioc.mp hi).1) ht
  have he' : ∀ k, μ (E k) ≤ ENNReal.ofReal B := by
    intro k
    apply (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hB, measureReal_def] using he k
  have hmono : Monotone E := by
    intro j k hjk ω hω
    obtain ⟨i, hij, hi⟩ := hω
    exact ⟨i, hij.trans hjk, hi⟩
  have hset : {ω | ∃ i : ℕ, t * ((u : ℝ) / Z 0) <
      |(U i ω : ℝ) / Z i - (u : ℝ) / Z 0|} = ⋃ k, E k := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨i, i, le_rfl, hi⟩
    · rintro ⟨k, i, _, hi⟩; exact ⟨i, hi⟩
  have hb : μ (⋃ k, E k) ≤ ENNReal.ofReal B := by
    rw [hmono.measure_iUnion]
    exact iSup_le he'
  have hb' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal hB] at hb'
  simpa only [measureReal_def, hset] using hb'

noncomputable def infiniteSquareBudget (Z : ℕ → ℤ) : ℝ :=
  ∑' i : ℕ, ((Z (i + 1) : ℝ)⁻¹) ^ 2

noncomputable def maximumReciprocal (Z : ℕ → ℤ) : ℝ :=
  sSup (Set.range fun i : ℕ => (Z (i + 1) : ℝ)⁻¹)

theorem squareBudget_zero_eq_sum (Z : ℕ → ℤ) (k : ℕ) :
    squareBudget Z 0 k = ∑ i ∈ Finset.range k, ((Z (i + 1) : ℝ)⁻¹) ^ 2 := by
  unfold squareBudget
  simp only [Nat.zero_add]
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
  · intro i hi j hj hij
    omega
  · intro j hj
    obtain ⟨hj0, hjk⟩ := Finset.mem_Ioc.mp hj
    exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

theorem reciprocal_range_bddAbove (Z : ℕ → ℤ) (hZ : ∀ i, 0 < Z i) :
    BddAbove (Set.range fun i : ℕ => (Z (i + 1) : ℝ)⁻¹) := by
  refine ⟨1, ?_⟩
  rintro r ⟨i, rfl⟩
  have hz : (1 : ℝ) ≤ Z (i + 1) := by exact_mod_cast hZ (i + 1)
  exact inv_le_one_of_one_le₀ hz

theorem reciprocal_le_maximum (Z : ℕ → ℤ) (hZ : ∀ i, 0 < Z i) {i : ℕ} (hi : 0 < i) :
    (Z i : ℝ)⁻¹ ≤ maximumReciprocal Z := by
  apply le_csSup (reciprocal_range_bddAbove Z hZ)
  exact ⟨i - 1, by dsimp only; rw [Nat.sub_add_cancel hi]⟩

/-- For positive integer populations, the reciprocal supremum is attained,
so it is the maximum used in the paper's statement. -/
theorem maximumReciprocal_attained (Z : ℕ → ℤ) (hZ : ∀ i, 0 < Z i) :
    ∃ i : ℕ, 1 ≤ i ∧ maximumReciprocal Z = (Z i : ℝ)⁻¹ := by
  let j := Function.argmin (fun i : ℕ => (Z (i + 1)).toNat)
  have hmin : ∀ i : ℕ, Z (j + 1) ≤ Z (i + 1) := by
    intro i
    have hm := le_of_not_gt (Function.not_lt_argmin (fun i : ℕ => (Z (i + 1)).toNat) i)
    change (Z (j + 1)).toNat ≤ (Z (i + 1)).toNat at hm
    have hi := hZ (i + 1)
    have hj := hZ (j + 1)
    omega
  refine ⟨j + 1, by omega, le_antisymm ?_ (reciprocal_le_maximum Z hZ (by omega))⟩
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨i, rfl⟩
  simpa only [one_div] using one_div_le_one_div_of_le
    (by exact_mod_cast hZ (j + 1) : (0 : ℝ) < Z (j + 1))
    (by exact_mod_cast hmin i : (Z (j + 1) : ℝ) ≤ Z (i + 1))

/-- The displayed infinite-time tail scale, for the explicitly specified
Markov urn. The source only conditions on U_n; that weaker wording is not
silently substituted for `HasPathLaws`. -/
theorem infinite_maximal_summable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (U : ℕ → Ω → ℤ) (Z : ℕ → ℤ)
    (hlaw : HasPathLaws U Z 1 μ) (hZ : ∀ i, 0 < Z i)
    (hz : ∀ i, Z (i + 1) - Z i = 1 ∨ Z (i + 1) - Z i = -1)
    (hsum : Summable (fun i : ℕ => ((Z i : ℝ)⁻¹) ^ 2)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ i : ℕ, 1 ≤ i ∧ t / (Z 0 : ℝ) <
      |(U i ω : ℝ) / Z i - (Z 0 : ℝ)⁻¹|} ≤
      2 * Real.exp (-((t ^ 2 / 4) * (Z 0 : ℝ)⁻¹) /
        (infiniteSquareBudget Z + t * max (infiniteSquareBudget Z) (maximumReciprocal Z))) := by
  have htail : Summable (fun i : ℕ => ((Z (i + 1) : ℝ)⁻¹) ^ 2) :=
    hsum.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hD : 0 < infiniteSquareBudget Z := by
    apply htail.tsum_pos (fun _ => sq_nonneg _) 0
    have hz1 : (0 : ℝ) < Z 1 := by exact_mod_cast hZ 1
    exact sq_pos_of_pos (inv_pos.mpr hz1)
  have hb : ∀ k, squareBudget Z 0 k ≤ infiniteSquareBudget Z := by
    intro k
    rw [squareBudget_zero_eq_sum]
    exact htail.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have hm : ∀ i, 0 < i → (Z i : ℝ)⁻¹ ≤
      max (infiniteSquareBudget Z) (maximumReciprocal Z) :=
    fun i hi => (reciprocal_le_maximum Z hZ hi).trans (le_max_right _ _)
  have hh := infinite_maximal_of_pathLaws U Z hlaw hZ hz (by norm_num) (by have := hZ 0; omega)
    hD (le_max_left _ _) hb hm ht
  calc
    _ ≤ μ.real {ω | ∃ i : ℕ, t * ((1 : ℤ) : ℝ) / Z 0 <
        |(U i ω : ℝ) / Z i - ((1 : ℤ) : ℝ) / Z 0|} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      rintro ω ⟨i, _, hi⟩
      exact ⟨i, by simpa only [Int.cast_one, mul_one, one_div] using hi⟩
    _ ≤ _ := by
      have hexp : -((t ^ 2 / 4) * (Z 0 : ℝ)⁻¹) /
          (infiniteSquareBudget Z + t * max (infiniteSquareBudget Z) (maximumReciprocal Z)) =
          -(t ^ 2 * (1 / (Z 0 : ℝ))) /
            (4 * (infiniteSquareBudget Z + t * max (infiniteSquareBudget Z) (maximumReciprocal Z))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      rw [hexp]
      simpa only [Int.cast_one, mul_one, one_div, div_eq_mul_inv, one_mul] using hh

end Freezing1.SignedUrn
