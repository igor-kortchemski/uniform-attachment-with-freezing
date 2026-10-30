module

public import Freezing1.GeometricChainCutoffs
public import Freezing1.ForwardGoodChains

/-!
# The source good-set indices are exactly the ceiling interval

The source tests all positive integers ell below k for which A is no larger
than C^ell. Once the ceiling index is positive, this is precisely the finite
interval used by the actual good-chain observable.
-/

@[expose] public section

namespace Freezing1

open scoped Classical

theorem chainLowerIndex_le_iff (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ) (n ell : ℕ)
    (hA : 0 < A n) :
    chainLowerIndex C A n ≤ ell ↔ A n ≤ ((C ^ ell : ℕ) : ℝ) := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hc : 0 < Real.log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  rw [chainLowerIndex, Nat.ceil_le, div_le_iff₀ hc]
  constructor
  · intro h
    have hh := Real.exp_le_exp.mpr h
    simpa only [Real.exp_log hA, Real.exp_nat_mul, Real.exp_log hC0, Nat.cast_pow] using hh
  · intro h
    apply Real.exp_le_exp.mp
    simpa only [Real.exp_log hA, Real.exp_nat_mul, Real.exp_log hC0, Nat.cast_pow] using h

theorem mem_chainInterval_iff_source (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (n k ell : ℕ) (hA : 0 < A n) (hk₀ : 1 ≤ chainLowerIndex C A n) :
    ell ∈ Finset.Ico (chainLowerIndex C A n) k ↔
      1 ≤ ell ∧ ell < k ∧ A n ≤ ((C ^ ell : ℕ) : ℝ) := by
  rw [Finset.mem_Ico]
  constructor
  · rintro ⟨hlo, hhi⟩
    exact ⟨hk₀.trans hlo, hhi, (chainLowerIndex_le_iff C hC A n ell hA).mp hlo⟩
  · rintro ⟨_, hhi, hpow⟩
    exact ⟨(chainLowerIndex_le_iff C hC A n ell hA).mpr hpow, hhi⟩

theorem chainInterval_eq_source_filter (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (n k : ℕ) (hA : 0 < A n) (hk₀ : 1 ≤ chainLowerIndex C A n) :
    Finset.Ico (chainLowerIndex C A n) k =
      (Finset.Ico 1 k).filter fun ell => A n ≤ ((C ^ ell : ℕ) : ℝ) := by
  ext ell
  rw [mem_chainInterval_iff_source C hC A n k ell hA hk₀]
  simp only [Finset.mem_filter, Finset.mem_Ico, and_assoc]

namespace Forward

/-- Literal source predicate for the good set, with the source lower cutoff
and positive-index condition retained explicitly. -/
theorem goodSet_eq_source_filter (s : State) (C : ℕ) (hC : 1 < C) (A : ℕ → ℝ)
    (n k : ℕ) (t : ℝ) (hA : 0 < A n) (hk₀ : 1 ≤ chainLowerIndex C A n) :
    goodSet s C (chainLowerIndex C A n) k t = s.active.filter fun v =>
      ∀ ell : ℕ, 1 ≤ ell → ell < k → A n ≤ ((C ^ ell : ℕ) : ℝ) →
        t < (blockHeight s (C ^ ell) (C ^ (ell + 1)) v : ℝ) := by
  ext v
  simp only [goodSet, Finset.mem_filter]
  apply and_congr_right
  intro _
  constructor
  · intro h ell hlo hhi hpow
    exact h ell ((mem_chainInterval_iff_source C hC A n k ell hA hk₀).mpr ⟨hlo, hhi, hpow⟩)
  · intro h ell he
    obtain ⟨hlo, hhi, hpow⟩ := (mem_chainInterval_iff_source C hC A n k ell hA hk₀).mp he
    exact h ell hlo hhi hpow

end Forward
end Freezing1
