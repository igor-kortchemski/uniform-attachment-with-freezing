module

public import Freezing1.RateFunction

/-!
# Checks of numerical claims in the source

Proposition `prop:bounds` has an incorrect upper bound when `n = 1` and the first
step is an attachment. That tree deterministically has height one, whereas
`h₁⁺ = 1/2`. At `t = 1/4` the event in the proposition has probability one.
The lemma below checks that its displayed proposed upper bound is strictly
less than one. It checks the numerical obstruction; no tree law is encoded here.
-/

public section

namespace Freezing1

/-- The purported upper bound in `prop:bounds` at `n = 1`, `h = 1/2`, `t = 1/4`
is strictly less than the actual probability one. -/
theorem height_upper_bound_rhs_at_one_lt_one :
    Real.exp (-(1 / 2 : ℝ) * bennettRate ((1 / 4 : ℝ) / (1 / 2 : ℝ)) +
      Real.log 1) < 1 := by
  rw [Real.exp_lt_one_iff]
  have h := bennettRate_pos (show (0 : ℝ) < (1 / 4 : ℝ) / (1 / 2 : ℝ) by norm_num)
  simp only [Real.log_one, add_zero]
  linarith

end Freezing1
