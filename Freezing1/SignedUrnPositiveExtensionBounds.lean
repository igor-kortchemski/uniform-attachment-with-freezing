module

public import Freezing1.SignedUrnPositiveExtension

/-! The source delta/epsilon bounds for the all-positive infinite extension. -/

@[expose] public section

namespace Freezing1.SignedUrn

open Filter MeasureTheory
open scoped Classical ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def sourceEpsilon (x : SignSequence) (a b : ℕ) (hab : a < b) : ℝ :=
  (Finset.Ioc a b).sup' (Finset.nonempty_Ioc.mpr hab) (fun i => (activeCount x i : ℝ)⁻¹)

theorem positiveExtension_maximum_eq_sourceEpsilon (x : SignSequence) {a b : ℕ}
    (hab : a < b) (hb : PositiveThrough x b) :
    maximumReciprocal (positiveExtensionPopulation x a b) = sourceEpsilon x a b hab := by
  have hpos := positiveExtensionPopulation_positive x (a := a) hb
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    change (positiveExtensionPopulation x a b (i + 1) : ℝ)⁻¹ ≤ sourceEpsilon x a b hab
    by_cases hi : i + 1 ≤ b - a
    · rw [positiveExtensionPopulation_retained x hab.le hi]
      exact Finset.le_sup' (fun j => (activeCount x j : ℝ)⁻¹) (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
    · have hj : b - a + (i + 1 - (b - a)) = i + 1 := by omega
      rw [← hj, positiveExtensionPopulation_tail x hab.le]
      have hz : (0 : ℝ) < activeCount x b := by exact_mod_cast hb b le_rfl
      have hle : (activeCount x b : ℝ) ≤ (activeCount x b + ((i + 1 - (b - a) : ℕ) : ℤ) : ℤ) := by
        exact_mod_cast (show activeCount x b ≤ activeCount x b + ((i + 1 - (b - a) : ℕ) : ℤ) from
          le_add_of_nonneg_right (Int.natCast_nonneg _))
      have hrec : ((activeCount x b + ((i + 1 - (b - a) : ℕ) : ℤ) : ℤ) : ℝ)⁻¹ ≤
          (activeCount x b : ℝ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le hz hle
      exact hrec.trans
        (Finset.le_sup' (fun j => (activeCount x j : ℝ)⁻¹) (Finset.mem_Ioc.mpr ⟨hab, le_rfl⟩))
  · apply Finset.sup'_le
    intro i hi
    have hia : 0 < i - a := by have := (Finset.mem_Ioc.mp hi).1; omega
    have hil : i - a ≤ b - a := by have := (Finset.mem_Ioc.mp hi).2; omega
    have he : positiveExtensionPopulation x a b (i - a) = activeCount x i := by
      rw [positiveExtensionPopulation_retained x hab.le hil, Nat.add_sub_of_le (by have := (Finset.mem_Ioc.mp hi).1; omega)]
    rw [← he]
    exact reciprocal_le_maximum _ hpos hia

theorem initial_reciprocal_le_of_linear {x : SignSequence} {a : ℕ}
    (ha : 0 < a) {d : ℝ} (hd : 0 < d) (hwalk : d * a ≤ (activeCount x a : ℝ)) :
    (activeCount x a : ℝ)⁻¹ ≤ d⁻¹ / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have h := one_div_le_one_div_of_le (mul_pos hd haR) hwalk
  simpa only [one_div, mul_inv, div_eq_mul_inv, one_mul] using h

theorem positiveExtension_maximum_le_of_linear (x : SignSequence) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) {d : ℝ} (hd : 0 < d)
    (hwalk : ∀ i ∈ Finset.Icc a b, d * i ≤ (activeCount x i : ℝ)) :
    maximumReciprocal (positiveExtensionPopulation x a b) ≤ d⁻¹ / a := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  have hbound : d * a ≤ (positiveExtensionPopulation x a b (i + 1) : ℝ) := by
    by_cases hi : i + 1 ≤ b - a
    · rw [positiveExtensionPopulation_retained x hab hi]
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_add_right a (i + 1)) hd.le).trans
        (hwalk _ (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))
    · have hj : b - a + (i + 1 - (b - a)) = i + 1 := by omega
      rw [← hj, positiveExtensionPopulation_tail x hab]
      have hb := hwalk b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩)
      have had : d * a ≤ d * b := mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hd.le
      push_cast
      exact had.trans (hb.trans (le_add_of_nonneg_right (Nat.cast_nonneg _)))
  have hi := one_div_le_one_div_of_le (mul_pos hd haR) hbound
  simpa only [one_div, mul_inv, div_eq_mul_inv, one_mul] using hi

theorem positiveExtension_square_budget_le_of_linear (x : SignSequence) {a b : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hb : PositiveThrough x b) {d : ℝ} (hd : 0 < d)
    (hwalk : ∀ i ∈ Finset.Icc a b, d * i ≤ (activeCount x i : ℝ)) :
    infiniteSquareBudget (positiveExtensionPopulation x a b) ≤ ((d ^ 2)⁻¹ + d⁻¹) / a := by
  rw [positiveExtension_square_budget_eq x hab hb]
  have hfinite : squareBudget (activeCount x) a (b - a) ≤ (d ^ 2)⁻¹ / a := by
    apply squareBudget_le_of_linear_lower _ ha hd
    intro i hi
    exact hwalk i (by simp only [Finset.mem_Ioc, Finset.mem_Icc] at hi ⊢; omega)
  have hS : 0 < (activeCount x b : ℝ) := by exact_mod_cast hb b le_rfl
  have htail := reciprocal_tail_square_le hS
  have hrecip : (activeCount x b : ℝ)⁻¹ ≤ d⁻¹ / a := by
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hlow : d * a ≤ (activeCount x b : ℝ) :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hab) hd.le).trans
        (hwalk b (Finset.mem_Icc.mpr ⟨hab, le_rfl⟩))
    simpa only [one_div, mul_inv, div_eq_mul_inv, one_mul] using
      one_div_le_one_div_of_le (mul_pos hd haR) hlow
  exact (add_le_add hfinite (htail.trans hrecip)).trans_eq (by ring)

/-- One common positive constant controls the source initial reciprocal,
epsilon and complete infinite delta, uniformly above the original cutoff. -/
theorem uniform_positiveExtension_budgets (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hA : Tendsto A atTop atTop) (hnear : NearOriginLinear x A c)
    (hbulk : BulkLowerBound x) (hpositive : ∀ n, PositiveThrough (x n) n) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ a b : ℕ,
      A n ≤ (a : ℝ) → a ≤ b → b ≤ n →
      (activeCount (x n) a : ℝ)⁻¹ ≤ K / a ∧
      maximumReciprocal (positiveExtensionPopulation (x n) a b) ≤ K / a ∧
      infiniteSquareBudget (positiveExtensionPopulation (x n) a b) ≤ K / a := by
  obtain ⟨d, hd, hwalk⟩ := eventually_linear_lower_above_cutoff x A hc hA hnear hbulk
  refine ⟨(d ^ 2)⁻¹ + d⁻¹ + 1, by positivity, ?_⟩
  filter_upwards [hwalk, hA.eventually_gt_atTop 0] with n hn hAn a b hAa hab hbn
  have haR : (0 : ℝ) < a := hAn.trans_le hAa
  have ha : 0 < a := by exact_mod_cast haR
  have hblock : ∀ i ∈ Finset.Icc a b, d * i ≤ (activeCount (x n) i : ℝ) := by
    intro i hi
    exact hn i (hAa.trans (by exact_mod_cast (Finset.mem_Icc.mp hi).1))
      ((Finset.mem_Icc.mp hi).2.trans hbn)
  have hcap1 : d⁻¹ / a ≤ ((d ^ 2)⁻¹ + d⁻¹ + 1) / a := by
    apply div_le_div_of_nonneg_right _ haR.le
    have hh : 0 ≤ (d ^ 2)⁻¹ := by positivity
    linarith
  refine ⟨(initial_reciprocal_le_of_linear ha hd (hblock a (by simp [hab]))).trans hcap1,
    (positiveExtension_maximum_le_of_linear (x n) ha hab hd hblock).trans hcap1, ?_⟩
  have hp : PositiveThrough (x n) b := fun i hi => hpositive n i (hi.trans hbn)
  exact (positiveExtension_square_budget_le_of_linear (x n) ha hab hp hd hblock).trans
    (div_le_div_of_nonneg_right (by linarith) haR.le)

theorem positiveExtension_geometricBlock_lt (C : ℕ) (hC : 2 ≤ C) (k : ℕ) :
    C ^ k < C ^ (k + 1) := by
  have hp : 0 < C ^ k := pow_pos (by omega) k
  rw [pow_succ]
  nlinarith

/-- Literal source geometric window and limsup/liminf hypotheses. Delta is
the complete infinite square sum, exactly decomposed in the core theorem;
epsilon is the paper's finite maximum, not an extra assumed bound. -/
theorem linear_positiveExtension_source_budgets
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x)
    (C : ℕ) (hC : 2 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (activeCount (x n) (C ^ k) : ℝ) ≤ ((C ^ k : ℕ) : ℝ) + 1 ∧
      (activeCount (x n) (C ^ k) : ℝ)⁻¹ ≤ K / ((C ^ k : ℕ) : ℝ) ∧
      sourceEpsilon (x n) (C ^ k) (C ^ (k + 1)) (positiveExtension_geometricBlock_lt C hC k) ≤
        K / ((C ^ k : ℕ) : ℝ) ∧
      infiniteSquareBudget (positiveExtensionPopulation (x n) (C ^ k) (C ^ (k + 1))) ≤
        K / ((C ^ k : ℕ) : ℝ) := by
  have hp : ∀ n, PositiveThrough (x n) n := fun n => (lt_extinctionTime_iff (x n) n).mp (hτ n)
  have hn := (nearOriginLimsup_iff x A hA hc.le hc1 hp).mp hnear
  have hb := (bulkLiminf_iff x hp).mp hbulk
  obtain ⟨K, hK, hbound⟩ := uniform_positiveExtension_budgets x A hc hAinf hn hb hp
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound] with n hn k hAk hupper
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hend : C ^ (k + 1) ≤ n := by
    have he := (le_div_iff₀ hC0).mp hupper
    rw [pow_succ]
    exact_mod_cast he
  have hlt := positiveExtension_geometricBlock_lt C hC k
  have hblocks := hn (C ^ k) (C ^ (k + 1)) hAk hlt.le hend
  have hSa : (activeCount (x n) (C ^ k) : ℝ) ≤ ((C ^ k : ℕ) : ℝ) + 1 := by
    have hI : activeCount (x n) (C ^ k) ≤ ((C ^ k : ℕ) : ℤ) + 1 :=
      (activeCount_le_plusCount_add_one (x n) (C ^ k)).trans
        (Int.add_le_add_right (by exact_mod_cast plusCount_le (x n) (C ^ k)) 1)
    exact_mod_cast hI
  refine ⟨hSa, hblocks.1, ?_, hblocks.2.2⟩
  rw [← positiveExtension_maximum_eq_sourceEpsilon (x n) hlt
    (fun i hi => hp n i (hi.trans hend))]
  exact hblocks.2.1

end Freezing1.SignedUrn
