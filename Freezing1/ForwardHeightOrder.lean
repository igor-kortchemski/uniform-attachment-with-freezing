module

public import Freezing1.ForwardHeight

/-!
# Stochastic monotonicity of the actual active-height law

For every antitone test function, expectation decreases along Algorithm 1 before
extinction. This follows from its proved uniform-active recursion, including
freezing steps; no coupling or Bernoulli representation is assumed.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory

/-- Shifting an active height upwards decreases every antitone test function. -/
theorem uniformActiveHeightLaw_shift_integral_le (x : SignSequence) (n : ℕ)
    {f : ℕ → ℝ} (hf : Antitone f) :
    (∫ k, f (k + 1) ∂uniformActiveHeightLaw x n) ≤
      ∫ k, f k ∂uniformActiveHeightLaw x n := by
  apply integral_mono (uniformActiveHeightLaw_integrable x n _)
    (uniformActiveHeightLaw_integrable x n _)
  intro k
  exact hf (Nat.le_succ k)

/-- One actual step preserves or decreases expectations of antitone functions. -/
theorem uniformActiveHeightLaw_integral_succ_le (x : SignSequence) (n : ℕ)
    (hτ : ((n + 1 : ℕ) : ℕ∞) < extinctionTime x)
    {f : ℕ → ℝ} (hf : Antitone f) :
    (∫ k, f k ∂uniformActiveHeightLaw x (n + 1)) ≤
      ∫ k, f k ∂uniformActiveHeightLaw x n := by
  rw [uniformActiveHeightLaw_integral_succ x n hτ]
  cases hx : x (n + 1)
  · exact le_rfl
  · simp only [↓reduceIte]
    have hs : (0 : ℝ) < activeCount x (n + 1) := by
      exact_mod_cast ((lt_extinctionTime_iff x (n + 1)).mp hτ) (n + 1) le_rfl
    have hmul := mul_le_mul_of_nonneg_left
      (uniformActiveHeightLaw_shift_integral_le x n hf) (one_div_nonneg.mpr hs.le)
    nlinarith

/-- The active-height law increases stochastically up to extinction. -/
theorem uniformActiveHeightLaw_integral_antitone (x : SignSequence)
    {f : ℕ → ℝ} (hf : Antitone f) {l i : ℕ} (hli : l ≤ i)
    (hiτ : (i : ℕ∞) < extinctionTime x) :
    (∫ k, f k ∂uniformActiveHeightLaw x i) ≤
      ∫ k, f k ∂uniformActiveHeightLaw x l := by
  induction i generalizing l with
  | zero =>
    have hl : l = 0 := by omega
    subst l
    exact le_rfl
  | succ i ih =>
    by_cases hli' : l ≤ i
    · have hiτ' : (i : ℕ∞) < extinctionTime x :=
        lt_trans (by exact_mod_cast Nat.lt_succ_self i) hiτ
      exact (uniformActiveHeightLaw_integral_succ_le x i hiτ hf).trans (ih hli' hiτ')
    · have hl : l = i + 1 := by omega
      subst l
      exact le_rfl

/-- A child born later has no larger antitone expectation than an earlier
uniform active vertex. This also covers an attachment's extra unit of height. -/
theorem uniformActiveHeightLaw_shift_integral_le_earlier (x : SignSequence)
    {f : ℕ → ℝ} (hf : Antitone f) {l i : ℕ} (hli : l ≤ i)
    (hiτ : (i : ℕ∞) < extinctionTime x) :
    (∫ k, f (k + 1) ∂uniformActiveHeightLaw x i) ≤
      ∫ k, f k ∂uniformActiveHeightLaw x l :=
  (uniformActiveHeightLaw_shift_integral_le x i hf).trans
    (uniformActiveHeightLaw_integral_antitone x hf hli hiτ)

/-- A negative exponential moment of a later child is bounded by the earlier
active-height scale, with the extra child edge kept explicitly. -/
theorem uniformActiveHeightLaw_shift_mgf_le_earlier (x : SignSequence)
    {l i : ℕ} (hli : l ≤ i) (hiτ : (i : ℕ∞) < extinctionTime x)
    {θ : ℝ} (hθ : θ ≤ 0) :
    (∫ k : ℕ, Real.exp (θ * ((k + 1 : ℕ) : ℝ)) ∂uniformActiveHeightLaw x i) ≤
      Real.exp (heightScale x l * (Real.exp θ - 1)) := by
  have hf : Antitone (fun k : ℕ => Real.exp (θ * (k : ℝ))) := by
    intro a b hab
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (by exact_mod_cast hab) hθ)
  have hlτ : (l : ℕ∞) < extinctionTime x :=
    lt_of_le_of_lt (by exact_mod_cast hli) hiτ
  exact (uniformActiveHeightLaw_shift_integral_le_earlier x hf hli hiτ).trans
    (uniformActiveHeightLaw_mgf_le x l hlτ θ)

end Freezing1.Forward
