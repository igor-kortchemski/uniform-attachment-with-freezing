module

public import Freezing1.HeightScale
public import Freezing1.IntervalCounts
public import Mathlib.Algebra.BigOperators.Module

/-!
# Weighted interval estimates for the linear regime

The interval `(a,b]` agrees with Lemma `lem:estimee uniforme sur h_n+`.
The finite estimates use Abel summation of the centered active-count walk.
This replaces the manuscript's geometric-block decomposition; that decomposition
is not verified by these lemmas.
-/

@[expose] public section

namespace Freezing1

open scoped BigOperators

/-- Sum of reciprocal integer indices on `(a,b]`. -/
noncomputable def harmonicInterval (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico a b, 1 / ((i : ℝ) + 1)

/-- Attachment indicators weighted by reciprocal integer indices on `(a,b]`. -/
noncomputable def weightedPlusInterval (x : SignSequence) (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico a b, if x (i + 1) then 1 / ((i : ℝ) + 1) else 0

/-- The actual reciprocal-population height sum on `(a,b]`. -/
noncomputable def heightInterval (x : SignSequence) (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico a b, if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0

theorem heightScale_add_heightInterval (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    heightScale x a + heightInterval x a b = heightScale x b := by
  exact Finset.sum_range_add_sum_Ico _ hab

theorem harmonicInterval_nonneg (a b : ℕ) : 0 ≤ harmonicInterval a b := by
  apply Finset.sum_nonneg
  intro i _
  positivity

/-- Abel's identity for centered increments, with both endpoints explicit. -/
theorem sum_weighted_increments_eq (E : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ Finset.Ico a b, (E (i + 1) - E i) / ((i : ℝ) + 1)) =
      E b / b - E a / a +
        ∑ i ∈ Finset.Ico a b, E i * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1)) := by
  have hp : ∀ i : ℕ, (E (i + 1) - E i) / ((i : ℝ) + 1) =
      (E (i + 1) / (i + 1 : ℕ) - E i / i) +
        E i * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1)) := by
    intro i
    push_cast
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_Ico_sub (fun i ↦ E i / (i : ℝ)) hab]

/-- A linear pointwise error controls all weighted increments uniformly. -/
theorem abs_sum_weighted_increments_le {E : ℕ → ℝ} {a b : ℕ} {η : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (_hη : 0 ≤ η)
    (hE : ∀ i ∈ Finset.Icc a b, |E i| ≤ η * i) :
    |∑ i ∈ Finset.Ico a b, (E (i + 1) - E i) / ((i : ℝ) + 1)| ≤
      η * (2 + harmonicInterval a b) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hea : |E a / a| ≤ η := by
    rw [abs_div, abs_of_pos ha0]
    exact (div_le_iff₀ ha0).mpr (hE a (Finset.left_mem_Icc.mpr hab))
  have heb : |E b / b| ≤ η := by
    rw [abs_div, abs_of_pos hb0]
    exact (div_le_iff₀ hb0).mpr (hE b (Finset.right_mem_Icc.mpr hab))
  have hsum : |∑ i ∈ Finset.Ico a b,
      E i * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1))| ≤ η * harmonicInterval a b := by
    calc
      _ ≤ ∑ i ∈ Finset.Ico a b,
          |E i * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico a b, η * (1 / ((i : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hai, hib⟩ := Finset.mem_Ico.mp hi
        have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
        have hip0 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
        have hd : 0 ≤ 1 / (i : ℝ) - 1 / ((i : ℝ) + 1) :=
          sub_nonneg.mpr (one_div_le_one_div_of_le hi0 (by linarith))
        rw [abs_mul, abs_of_nonneg hd]
        calc
          _ ≤ (η * i) * (1 / (i : ℝ) - 1 / ((i : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (hE i (Finset.mem_Icc.mpr ⟨hai, hib.le⟩)) hd
          _ = η * (1 / ((i : ℝ) + 1)) := by field_simp; ring
      _ = η * harmonicInterval a b := by rw [← Finset.mul_sum]; rfl
  rw [sum_weighted_increments_eq _ hab]
  have hend : |E b / b - E a / a| ≤ η + η := (abs_sub _ _).trans (add_le_add heb hea)
  exact (abs_add_le _ _).trans ((add_le_add hend hsum).trans_eq (by ring))

/-- The attachment indicator is half of one plus the signed walk increment. -/
theorem weightedPlusInterval_centered_identity (x : SignSequence) (a b : ℕ) (c : ℝ) :
    2 * weightedPlusInterval x a b = (c + 1) * harmonicInterval a b +
      ∑ i ∈ Finset.Ico a b,
        (((activeCount x (i + 1) : ℝ) - c * (i + 1)) -
          ((activeCount x i : ℝ) - c * i)) / ((i : ℝ) + 1) := by
  unfold weightedPlusInterval harmonicInterval
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hstep : (activeCount x (i + 1) : ℝ) =
      activeCount x i + if x (i + 1) then 1 else -1 := by
    exact_mod_cast activeCount_succ x i
  rw [hstep]
  cases x (i + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> ring

/-- Uniform ratio errors give a sharp weighted attachment-count estimate. -/
theorem weightedPlusInterval_error_le {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hη : 0 ≤ η)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    |weightedPlusInterval x a b - (c + 1) / 2 * harmonicInterval a b| ≤
      η / 2 * (2 + harmonicInterval a b) := by
  let E : ℕ → ℝ := fun i ↦ (activeCount x i : ℝ) - c * i
  have hE : ∀ i ∈ Finset.Icc a b, |E i| ≤ η * i := by
    intro i hi
    have hi0 : (0 : ℝ) < i := by
      have := (Finset.mem_Icc.mp hi).1
      exact_mod_cast (show 0 < i by omega)
    have heq : (activeCount x i : ℝ) / i - c = E i / i := by
      dsimp [E]
      field_simp
    have h := herr i hi
    rw [heq, abs_div, abs_of_pos hi0] at h
    exact (div_le_iff₀ hi0).mp h
  have hb := abs_sum_weighted_increments_le ha hab hη hE
  have hid : 2 * weightedPlusInterval x a b = (c + 1) * harmonicInterval a b +
      ∑ i ∈ Finset.Ico a b, (E (i + 1) - E i) / ((i : ℝ) + 1) := by
    simpa only [E, Nat.cast_add, Nat.cast_one] using weightedPlusInterval_centered_identity x a b c
  have heq : weightedPlusInterval x a b - (c + 1) / 2 * harmonicInterval a b =
      (∑ i ∈ Finset.Ico a b, (E (i + 1) - E i) / ((i : ℝ) + 1)) / 2 := by linarith
  rw [heq, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Reciprocal populations are close to reciprocal linear populations, uniformly
when the slope error is at most half the positive limiting slope. -/
theorem reciprocal_activeCount_error_le {x : SignSequence} {i : ℕ} {c η : ℝ}
    (hi : 1 ≤ i) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η ≤ c / 2)
    (herr : |(activeCount x i : ℝ) / i - c| ≤ η) :
    |1 / (activeCount x i : ℝ) - (1 / c) * (1 / (i : ℝ))| ≤
      (2 * η / c ^ 2) * (1 / (i : ℝ)) := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  have hlow : c / 2 * i ≤ (activeCount x i : ℝ) := by
    have hl := (abs_le.mp herr).1
    have hratio : c / 2 ≤ (activeCount x i : ℝ) / i := by linarith
    exact (le_div_iff₀ hi0).mp hratio
  have hs0 : (0 : ℝ) < activeCount x i := (mul_pos (half_pos hc) hi0).trans_le hlow
  have hnum : |c * i - (activeCount x i : ℝ)| ≤ η * i := by
    have heq : c * i - (activeCount x i : ℝ) =
        -((activeCount x i : ℝ) / i - c) * i := by field_simp; ring
    rw [heq, abs_mul, abs_neg, abs_of_pos hi0]
    exact mul_le_mul_of_nonneg_right herr hi0.le
  have heq : 1 / (activeCount x i : ℝ) - (1 / c) * (1 / (i : ℝ)) =
      (c * i - (activeCount x i : ℝ)) / ((activeCount x i : ℝ) * c * i) := by
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (activeCount x i : ℝ) * c * i)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (activeCount x i : ℝ) * c * i)).mpr
  refine hnum.trans ?_
  calc
    η * i = (2 * η / c) * (c / 2 * i) := by field_simp
    _ ≤ (2 * η / c) * (activeCount x i : ℝ) :=
      mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = (2 * η / c ^ 2 * (1 / (i : ℝ))) * ((activeCount x i : ℝ) * c * i) := by
      field_simp

/-- Replace the random-population denominators by their linear approximation. -/
theorem heightInterval_sub_weightedPlus_le {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (_ha : 1 ≤ a) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η ≤ c / 2)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    |heightInterval x a b - (1 / c) * weightedPlusInterval x a b| ≤
      (2 * η / c ^ 2) * harmonicInterval a b := by
  unfold heightInterval weightedPlusInterval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ Finset.Ico a b,
        |(if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0) -
          (1 / c) * (if x (i + 1) then 1 / ((i : ℝ) + 1) else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.Ico a b, (2 * η / c ^ 2) * (1 / ((i : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hib := Finset.mem_Ico.mp hi
      have hip : i + 1 ∈ Finset.Icc a b := Finset.mem_Icc.mpr (by omega)
      by_cases hx : x (i + 1) = true
      · simp only [hx, ↓reduceIte]
        simpa only [Nat.cast_add, Nat.cast_one] using
          reciprocal_activeCount_error_le (by omega : 1 ≤ i + 1) hc hη hηc (herr (i + 1) hip)
      · simp only [Bool.not_eq_true] at hx
        simp only [hx, Bool.false_eq_true, ↓reduceIte, mul_zero, sub_self, abs_zero]
        positivity
    _ = (2 * η / c ^ 2) * harmonicInterval a b := by rw [← Finset.mul_sum]; rfl

/-- The finite quantitative heart of the uniform logarithmic interval estimate. -/
theorem heightInterval_harmonic_error_le {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η ≤ c / 2)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    |heightInterval x a b - (c + 1) / (2 * c) * harmonicInterval a b| ≤
      η * ((2 / c ^ 2 + 1 / (2 * c)) * harmonicInterval a b + 1 / c) := by
  have hrec := heightInterval_sub_weightedPlus_le ha hc hη hηc herr
  have hweight := weightedPlusInterval_error_le ha hab hη herr
  have heq : heightInterval x a b - (c + 1) / (2 * c) * harmonicInterval a b =
      (heightInterval x a b - (1 / c) * weightedPlusInterval x a b) +
        (1 / c) * (weightedPlusInterval x a b - (c + 1) / 2 * harmonicInterval a b) := by
    ring
  rw [heq]
  calc
    _ ≤ |heightInterval x a b - (1 / c) * weightedPlusInterval x a b| +
        |(1 / c) * (weightedPlusInterval x a b - (c + 1) / 2 * harmonicInterval a b)| :=
      abs_add_le _ _
    _ ≤ (2 * η / c ^ 2) * harmonicInterval a b +
        (1 / c) * (η / 2 * (2 + harmonicInterval a b)) := by
      apply add_le_add hrec
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hc)]
      exact mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring

theorem log_increment_bounds {u : ℝ} (hu : 0 < u) :
    1 / (u + 1) ≤ Real.log (u + 1) - Real.log u ∧
      Real.log (u + 1) - Real.log u ≤ 1 / u := by
  have hp : 0 < u + 1 := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hu)
  have hupp := Real.log_le_sub_one_of_pos (div_pos hp hu)
  rw [Real.log_div hp.ne' hu.ne'] at hl hupp
  constructor
  · convert hl using 1
    field_simp
    ring
  · convert hupp using 1
    field_simp
    ring

/-- The harmonic sum on `(a,b]` differs from `log(b/a)` by at most `1/a`.
This uniform endpoint error replaces geometric-block rounding estimates. -/
theorem harmonicInterval_log_error {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Real.log ((b : ℝ) / a) - harmonicInterval a b ∧
      Real.log ((b : ℝ) / a) - harmonicInterval a b ≤ 1 / (a : ℝ) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hlog : (∑ i ∈ Finset.Ico a b, (Real.log ((i : ℝ) + 1) - Real.log i)) =
      Real.log (b : ℝ) - Real.log a := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      Finset.sum_Ico_sub (fun i : ℕ ↦ Real.log (i : ℝ)) hab
  have hlower : harmonicInterval a b ≤ Real.log (b : ℝ) - Real.log a := by
    rw [← hlog]
    apply Finset.sum_le_sum
    intro i hi
    have := (Finset.mem_Ico.mp hi).1
    exact (log_increment_bounds (by exact_mod_cast (show 0 < i by omega))).1
  have hupper : Real.log (b : ℝ) - Real.log a ≤ ∑ i ∈ Finset.Ico a b, 1 / (i : ℝ) := by
    rw [← hlog]
    apply Finset.sum_le_sum
    intro i hi
    have := (Finset.mem_Ico.mp hi).1
    exact (log_increment_bounds (by exact_mod_cast (show 0 < i by omega))).2
  have hinv := Finset.sum_Ico_sub (fun i : ℕ ↦ 1 / (i : ℝ)) hab
  simp only [Finset.sum_sub_distrib, Nat.cast_add, Nat.cast_one] at hinv
  change harmonicInterval a b - (∑ i ∈ Finset.Ico a b, 1 / (i : ℝ)) =
    1 / (b : ℝ) - 1 / (a : ℝ) at hinv
  rw [Real.log_div hb0.ne' ha0.ne']
  have hbnonneg : 0 ≤ 1 / (b : ℝ) := by positivity
  constructor <;> linarith

/-- A logarithmic interval of ratio at least `exp L` has a uniform relative
error. This estimate has exactly the `(a,b]` endpoint convention in Lemma 8. -/
theorem heightInterval_log_error_le {x : SignSequence} {a b : ℕ} {c η L : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η ≤ c / 2)
    (hL : 0 < L) (hLlog : L ≤ Real.log ((b : ℝ) / a))
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    |heightInterval x a b / Real.log ((b : ℝ) / a) - (c + 1) / (2 * c)| ≤
      η * (2 / c ^ 2 + 1 / (2 * c) + 1 / (c * L)) +
        ((c + 1) / (2 * c)) / ((a : ℝ) * L) := by
  let K : ℝ := (c + 1) / (2 * c)
  let D : ℝ := 2 / c ^ 2 + 1 / (2 * c)
  let l : ℝ := Real.log ((b : ℝ) / a)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hl : 0 < l := hL.trans_le hLlog
  have herr' := heightInterval_harmonic_error_le ha hab hc hη hηc herr
  have hh := harmonicInterval_log_error ha hab
  have hnum : |heightInterval x a b - K * l| ≤ η * (D * l + 1 / c) + K / a := by
    calc
      _ = |(heightInterval x a b - K * harmonicInterval a b) +
          K * (harmonicInterval a b - l)| := by congr 1; ring
      _ ≤ |heightInterval x a b - K * harmonicInterval a b| +
          |K * (harmonicInterval a b - l)| := abs_add_le _ _
      _ ≤ η * (D * harmonicInterval a b + 1 / c) + K * (1 / (a : ℝ)) := by
        apply add_le_add herr'
        rw [abs_mul, abs_of_nonneg hK, abs_of_nonpos (by dsimp [l]; linarith [hh.1])]
        exact mul_le_mul_of_nonneg_left (by dsimp [l]; linarith [hh.2]) hK
      _ ≤ η * (D * l + 1 / c) + K / a := by
        have hhl : harmonicInterval a b ≤ l := by dsimp [l]; linarith [hh.1]
        have hmul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hhl hD) hη
        convert add_le_add_right hmul (η / c + K / a) using 1 <;> ring
  have hrem : 0 ≤ η / (c * L) + K / ((a : ℝ) * L) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hLlog hrem
  have heq : (η / (c * L) + K / ((a : ℝ) * L)) * L = η / c + K / a := by
    field_simp
  have hbound : η * (D * l + 1 / c) + K / a ≤
      (η * (D + 1 / (c * L)) + K / ((a : ℝ) * L)) * l := by
    rw [heq] at hmul
    convert add_le_add_left hmul (η * D * l) using 1 <;> ring
  change |heightInterval x a b / l - K| ≤
    η * (D + 1 / (c * L)) + K / ((a : ℝ) * L)
  rw [show heightInterval x a b / l - K = (heightInterval x a b - K * l) / l by
    field_simp]
  rw [abs_div, abs_of_pos hl]
  exact (div_le_iff₀ hl).mpr (hnum.trans hbound)

end Freezing1
