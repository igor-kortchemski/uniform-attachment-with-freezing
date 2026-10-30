module

public import Freezing1.ForwardGoodChainJoint
public import Freezing1.GeometricChainErrors
public import Freezing1.SummableFailureChain

/-!
# Survival of good chains from the actual block estimates

Every event is read from one terminal forward tree, using its canonical
prefixes. The initial population and the two block estimates remain explicit
inputs here; the linear-regime main result supplies all of them.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory Filter
open scoped ENNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

theorem goodChain_survival
    (x : ℕ → SignSequence) (C : ℕ) (hC : 1 < C) (k₀ K : ℕ → ℕ)
    (hk₀ : Tendsto k₀ atTop atTop) (hindices : ∀ᶠ n in atTop, k₀ n ≤ K n)
    (ρ : ℝ) (hρ : 0 < ρ) (t L : ℝ) (hL : 0 ≤ L)
    (hτ : ∀ n : ℕ, (n : ℕ∞) ≤ extinctionTime (x n))
    (hwindow : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n), C ^ (k + 1) ≤ n)
    (hbase : ∀ᶠ n in atTop, ∀ᵐ s ∂treeLaw (x n) n,
      ρ * (2 : ℝ) ^ k₀ n ≤ ((goodSet (truncateAt s (C ^ k₀ n)) C (k₀ n) (k₀ n) t).card : ℝ))
    (hN : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n),
      (treeLaw (x n) n).real {s |
        (blockTallCount s (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)} ≤
          L / (C ^ k : ℕ))
    (hM : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n),
      (treeLaw (x n) (C ^ (k + 1))).real {s |
        (k : ℝ) ^ 3 < (componentMaximum s (C ^ k) : ℝ)} ≤ 1 / (k : ℝ) ^ 2) :
    Tendsto (fun n => (treeLaw (x n) n).real
      {s | goodSet (truncateAt s (C ^ K n)) C (k₀ n) (K n) t = ∅}) atTop (𝓝 0) := by
  let G : ℕ → ℕ → State → Prop := fun n k s =>
    ρ * (2 : ℝ) ^ k ≤ ((goodSet (truncateAt s (C ^ k)) C (k₀ n) k t).card : ℝ)
  have hC2 : 2 ≤ C := by omega
  have hbase0 : Tendsto (fun n => (treeLaw (x n) n).real {s | ¬G n (k₀ n) s})
      atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hbase] with n hn
    exact (congrArg ENNReal.toReal (ae_iff.mp hn)).symm
  have hstep : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (k₀ n) (K n),
      (treeLaw (x n) n).real {s | G n k s ∧ ¬G n (k + 1) s} ≤
        geometricChainError C L 1 ρ k := by
    filter_upwards [hwindow, hN, hM, hk₀.eventually_ge_atTop 2] with n hn hNn hMn hn2
    intro k hk
    have hk0 := (Finset.mem_Ico.mp hk).1
    have hk2 : 2 ≤ k := hn2.trans hk0
    have hpow : 3 ≤ C ^ k := by
      calc
        3 ≤ 2 ^ 2 := by norm_num
        _ ≤ C ^ 2 := pow_le_pow_left' hC2 2
        _ ≤ C ^ k := pow_le_pow_right₀ hC.le hk2
    have hevent : {s | G n k s ∧ ¬G n (k + 1) s} =
        {s | ρ * (2 : ℝ) ^ k ≤ ((goodSet (truncateAt s (C ^ k)) C (k₀ n) k t).card : ℝ) ∧
          ((goodSet (truncateAt s (C ^ (k + 1))) C (k₀ n) (k + 1) t).card : ℝ) <
            2 * (ρ * (2 : ℝ) ^ k)} := by
      ext s
      simp only [G, not_le]
      rw [show ρ * (2 : ℝ) ^ (k + 1) = 2 * (ρ * (2 : ℝ) ^ k) by ring]
    rw [hevent]
    have hh := treeLaw_goodChain_step_le (b := ρ * (2 : ℝ) ^ k) (M := (k : ℝ) ^ 3)
      (x n) (hτ n) hC.le hk0 (hn k hk)
      (by exact_mod_cast hpow) t (mul_pos hρ (by positivity)) (pow_nonneg (Nat.cast_nonneg k) 3)
    exact hh.trans (by
      change _ ≤ L / (C : ℝ) ^ k + 1 / (k : ℝ) ^ 2 +
        3 * (k : ℝ) ^ 3 / (ρ * (2 : ℝ) ^ k)
      simpa only [Nat.cast_pow] using add_le_add (add_le_add (hNn k hk) (hMn k hk))
        (le_rfl (a := 3 * (k : ℝ) ^ 3 / (ρ * (2 : ℝ) ^ k))))
  have hlim := tendsto_failure_chain_zero (fun n => treeLaw (x n) n) G k₀ K hk₀ hindices
    (geometricChainError C L 1 ρ)
    (geometricChainError_nonneg C hL (by norm_num) hρ)
    (summable_geometricChainError C hC2 L 1 ρ) hbase0 hstep
  apply squeeze_zero (fun _ => measureReal_nonneg) ?_ hlim
  intro n
  apply measureReal_mono _ (measure_ne_top _ _)
  intro s hs
  change ¬ρ * (2 : ℝ) ^ K n ≤ ((goodSet (truncateAt s (C ^ K n)) C (k₀ n) (K n) t).card : ℝ)
  rw [hs, Finset.card_empty, Nat.cast_zero]
  exact not_le.mpr (mul_pos hρ (by positivity))

end Freezing1.Forward
