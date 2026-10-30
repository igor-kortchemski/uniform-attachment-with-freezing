module

public import Freezing1.IncreasingBinaryGrowth
public import Freezing1.TangentDerivativePolynomial

/-!
# Counting increasing binary trees by actual active-leaf growth

The finite sum below ranges over genuine increasing trees with prescribed
consecutive labels. The largest-label deletion bijection proves its
differential recurrence; no counting recurrence is assumed.
-/

@[expose] public section

namespace Freezing1.BinaryBijection

open Polynomial
open scoped Classical BigOperators

noncomputable def growthPolynomial (m : ℕ) : Polynomial ℚ :=
  ∑ t : IncreasingStage m, X ^ t.val.activeCount

def initialIncreasingStage : IncreasingStage 0 :=
  ⟨.leaf none, by simp [FullBinary.Increasing], by simp [FullBinary.labels]⟩

theorem increasingStage_zero_unique (t : IncreasingStage 0) : t = initialIncreasingStage := by
  apply Subtype.ext
  apply (FullBinary.labels_eq_zero_iff t.val).mp
  simpa using t.property.2

theorem growthPolynomial_zero : growthPolynomial 0 = X := by
  have hu : (Finset.univ : Finset (IncreasingStage 0)) = {initialIncreasingStage} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact increasingStage_zero_unique t
  unfold growthPolynomial
  rw [hu, Finset.sum_singleton]
  change (X : Polynomial ℚ) ^ 1 = X
  exact pow_one _

theorem polynomial_growth_monomial (k : ℕ) :
    (k : Polynomial ℚ) * (X ^ (k + 1) + X ^ (k - 1)) =
      (1 + X ^ 2) * (X ^ k : Polynomial ℚ).derivative := by
  cases k with
  | zero => simp
  | succ k =>
    rw [derivative_X_pow, C_eq_natCast]
    simp only [Nat.add_sub_cancel]
    rw [show k + 1 + 1 = k + 2 by omega, pow_add]
    ring

theorem sum_growStage_monomial (m : ℕ) (t : IncreasingStage m) :
    (∑ p : t.val.ActiveLeaf × Bool,
      (X : Polynomial ℚ) ^ (growStage m ⟨t, p⟩).val.activeCount) =
      (1 + X ^ 2) * (X ^ t.val.activeCount : Polynomial ℚ).derivative := by
  have hg : (∑ p : t.val.ActiveLeaf × Bool,
      (X : Polynomial ℚ) ^ (growStage m ⟨t, p⟩).val.activeCount) =
      ∑ p : t.val.ActiveLeaf × Bool,
        (X : Polynomial ℚ) ^ (if p.2 then t.val.activeCount + 1 else t.val.activeCount - 1) := by
    apply Finset.sum_congr rfl
    intro p _
    exact congrArg (fun k : ℕ => (X : Polynomial ℚ) ^ k) (growStage_activeCount m ⟨t, p⟩)
  rw [hg, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [Finset.sum_const, Finset.card_univ, FullBinary.activeLeaf_card, nsmul_eq_mul]
  exact polynomial_growth_monomial t.val.activeCount

theorem growthPolynomial_succ (m : ℕ) :
    growthPolynomial (m + 1) = (1 + X ^ 2) * (growthPolynomial m).derivative := by
  calc
    growthPolynomial (m + 1) =
        ∑ p : GrowthInput m, (X : Polynomial ℚ) ^ (growStage m p).val.activeCount :=
      (Equiv.sum_comp (growthEquiv m) (fun t => (X : Polynomial ℚ) ^ t.val.activeCount)).symm
    _ = ∑ t : IncreasingStage m, ∑ p : t.val.ActiveLeaf × Bool,
        (X : Polynomial ℚ) ^ (growStage m ⟨t, p⟩).val.activeCount := by
      exact Fintype.sum_sigma _
    _ = ∑ t : IncreasingStage m,
        (1 + X ^ 2) * (X ^ t.val.activeCount : Polynomial ℚ).derivative := by
      exact Finset.sum_congr rfl (fun t _ => sum_growStage_monomial m t)
    _ = (1 + X ^ 2) * (growthPolynomial m).derivative := by
      simp only [growthPolynomial, derivative_sum, Finset.mul_sum]

theorem growthPolynomial_eq_tangentDerivativePolynomial (m : ℕ) :
    growthPolynomial m = tangentDerivativePolynomial m := by
  induction m with
  | zero => exact growthPolynomial_zero
  | succ m ih => rw [growthPolynomial_succ, tangentDerivativePolynomial_succ, ih]

def stageFrozenEquiv (m : ℕ) :
    {t : IncreasingStage m // t.val.activeCount = 0} ≃
      FullyFrozenClass (Finset.Icc 1 m) where
  toFun t := ⟨t.val.val, t.val.property.1, t.property, t.val.property.2⟩
  invFun t := ⟨⟨t.val, t.property.1, t.property.2.2⟩, t.property.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem growthPolynomial_constant (m : ℕ) :
    (growthPolynomial m).coeff 0 = (frozenBinaryCount (Finset.Icc 1 m) : ℚ) := by
  classical
  unfold growthPolynomial
  simp only [finsetSum_coeff, coeff_X_pow]
  simp_rw [eq_comm (a := 0)]
  rw [Finset.sum_boole, ← Fintype.card_subtype]
  congr 1
  rw [Fintype.card_congr (stageFrozenEquiv m), frozenBinaryCount, Nat.card_eq_fintype_card]

theorem frozenBinaryCount_eq_tangentDerivative (m : ℕ) :
    (frozenBinaryCount (Finset.Icc 1 m) : ℝ) = iteratedDeriv m Real.tan 0 := by
  rw [← tangentDerivativePolynomial_constant, ← growthPolynomial_eq_tangentDerivativePolynomial,
    growthPolynomial_constant]
  norm_cast

theorem tangent_iteratedDeriv_zero_nonneg (m : ℕ) : 0 ≤ iteratedDeriv m Real.tan 0 := by
  rw [← frozenBinaryCount_eq_tangentDerivative]
  positivity

theorem source_fullyFrozen_card_tangent (n : ℕ) (hn : 0 < n) :
    (Nat.card (UnorderedIncreasingClass 0 n (Finset.Icc 1 (2 * n - 1))) : ℝ) =
      iteratedDeriv (2 * n - 1) Real.tan 0 := by
  rw [source_fullyFrozen_card n hn]
  exact frozenBinaryCount_eq_tangentDerivative _

end Freezing1.BinaryBijection
