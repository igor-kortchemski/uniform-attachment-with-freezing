module

public import Freezing1.SIRFluidProfile
public import Freezing1.SIRProbability
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Deterministic estimates for the corrected SIR fluid argument

The rate perturbation remains explicit: the exact scaled rate is a=n*rate,
not the limiting lambda. The discrete estimate controls a past sum of errors
and does not assume the source's insufficient future-maximum criterion.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter Set
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false

theorem discrete_geometric_identity (b : ℝ) (n : ℕ) :
    1 + b * ∑ i ∈ Finset.range n, (1 + b) ^ i = (1 + b) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith

theorem discrete_gronwall {e : ℕ → ℝ} {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    {N : ℕ} (h : ∀ n ≤ N, e n ≤ A + b * ∑ i ∈ Finset.range n, e i) :
    ∀ n ≤ N, e n ≤ A * (1 + b) ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    calc
      e n ≤ A + b * ∑ i ∈ Finset.range n, e i := h n hn
      _ ≤ A + b * ∑ i ∈ Finset.range n, A * (1 + b) ^ i := by
        have hsum : (∑ i ∈ Finset.range n, e i) ≤ ∑ i ∈ Finset.range n, A * (1 + b) ^ i := by
          apply Finset.sum_le_sum
          intro i hi
          exact ih i (Finset.mem_range.mp hi) ((Finset.mem_range.mp hi).le.trans hn)
        have := mul_le_mul_of_nonneg_left hsum hb
        linarith
      _ = A * (1 + b) ^ n := by
        rw [← Finset.mul_sum]
        nlinarith [discrete_geometric_identity b n]

theorem discrete_gronwall_exp {e : ℕ → ℝ} {A b : ℝ} (hA : 0 ≤ A) (hb : 0 ≤ b)
    {N : ℕ} (h : ∀ n ≤ N, e n ≤ A + b * ∑ i ∈ Finset.range n, e i) :
    ∀ n ≤ N, e n ≤ A * Real.exp (b * n) := by
  intro n hn
  apply (discrete_gronwall hA hb h n hn).trans
  apply mul_le_mul_of_nonneg_left _ hA
  have hstep : 1 + b ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  calc
    (1 + b) ^ n ≤ (Real.exp b) ^ n := pow_le_pow_left₀ (by linarith) hstep _
    _ = Real.exp (b * n) := by rw [mul_comm, Real.exp_nat_mul]

theorem infectionFraction_scaled_error {a lam u v : ℝ}
    (ha : 0 ≤ a) (hlam : 0 ≤ lam) (hu : u ∈ Icc (0 : ℝ) 1) (hv : 0 ≤ v) :
    |infectionFraction (a * u) - infectionFraction (lam * v)| ≤
      |a - lam| + lam * |u - v| := by
  apply (infectionFraction_abs_sub_le (mul_nonneg ha hu.1) (mul_nonneg hlam hv)).trans
  have he : a * u - lam * v = (a - lam) * u + lam * (u - v) := by ring
  rw [he]
  calc
    |(a - lam) * u + lam * (u - v)| ≤ |(a - lam) * u| + |lam * (u - v)| := abs_add_le _ _
    _ = |a - lam| * u + lam * |u - v| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu.1, abs_of_nonneg hlam]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hu.2 (abs_nonneg (a - lam))
      linarith

theorem fluidProfile_hasDerivAt_deriv {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    HasDerivAt (deriv (fluidProfile lam))
      (lam ^ 2 * fluidProfile lam t / (1 + lam * fluidProfile lam t) ^ 3) t := by
  have hg := fluidProfile_hasDerivAt hlam t
  have hn : 1 + lam * fluidProfile lam t ≠ 0 := ne_of_gt (by
    have := fluidProfile_pos hlam t
    positivity)
  have hd := (hg.const_mul (-lam)).div ((hasDerivAt_const t (1 : ℝ)).add (hg.const_mul lam)) hn
  simp only [Pi.add_apply] at hd
  convert hd using 1
  · funext r
    rw [(fluidProfile_hasDerivAt hlam r).deriv]
    rfl
  · field_simp [hn]
    ring

theorem fluidProfile_deriv2_nonneg_le {lam t : ℝ} (hlam : 0 < lam) (ht : 0 ≤ t) :
    0 ≤ deriv (deriv (fluidProfile lam)) t ∧
      deriv (deriv (fluidProfile lam)) t ≤ lam ^ 2 := by
  rw [(fluidProfile_hasDerivAt_deriv hlam t).deriv]
  have hg0 := (fluidProfile_pos hlam t).le
  have hg1 := fluidProfile_le_one hlam ht
  have hd : 1 ≤ (1 + lam * fluidProfile lam t) ^ 3 :=
    one_le_pow₀ (by nlinarith : 1 ≤ 1 + lam * fluidProfile lam t)
  constructor
  · positivity
  · calc
      lam ^ 2 * fluidProfile lam t / (1 + lam * fluidProfile lam t) ^ 3 ≤
          lam ^ 2 * fluidProfile lam t := div_le_self (by positivity) hd
      _ ≤ lam ^ 2 := by nlinarith [sq_nonneg lam]

theorem fluidProfile_deriv_abs_sub_le {lam s t : ℝ} (hlam : 0 < lam)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |deriv (fluidProfile lam) t - deriv (fluidProfile lam) s| ≤ lam ^ 2 * |t - s| := by
  have hh := (convex_Ici (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := deriv (fluidProfile lam))
    (fun x _ => (fluidProfile_hasDerivAt_deriv hlam x).differentiableAt)
    (fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (fluidProfile_deriv2_nonneg_le hlam hx).1]
      exact (fluidProfile_deriv2_nonneg_le hlam hx).2) hs ht
  simpa only [Real.norm_eq_abs] using hh

theorem fluidProfile_euler_step_error {lam a h : ℝ} (hlam : 0 < lam)
    (ha : 0 ≤ a) (hh : 0 ≤ h) :
    |fluidProfile lam (a + h) - fluidProfile lam a +
      h * infectionFraction (lam * fluidProfile lam a)| ≤ lam ^ 2 * h ^ 2 := by
  by_cases hh0 : h = 0
  · simp [hh0]
  · have hhp : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
    obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope (fluidProfile lam)
      (deriv (fluidProfile lam)) (by linarith : a < a + h)
      (fluidProfile_continuous hlam).continuousOn
      (fun x _ => (fluidProfile_hasDerivAt hlam x).differentiableAt.hasDerivAt)
    have heq : fluidProfile lam (a + h) - fluidProfile lam a =
        h * deriv (fluidProfile lam) c := by
      rw [add_sub_cancel_left] at he
      have := (eq_div_iff hh0).mp he
      linarith
    have hda : deriv (fluidProfile lam) a = -infectionFraction (lam * fluidProfile lam a) := by
      rw [(fluidProfile_hasDerivAt hlam a).deriv, infectionFraction]
      ring
    have hcb : |c - a| ≤ h := by rw [abs_of_nonneg (by linarith [hc.1])]; linarith [hc.2]
    have hb := (fluidProfile_deriv_abs_sub_le hlam ha (by linarith [hc.1])).trans
      (mul_le_mul_of_nonneg_left hcb (sq_nonneg lam))
    have hre : fluidProfile lam (a + h) - fluidProfile lam a +
        h * infectionFraction (lam * fluidProfile lam a) =
        h * (deriv (fluidProfile lam) c - deriv (fluidProfile lam) a) := by
      rw [heq, hda]
      ring
    rw [hre, abs_mul, abs_of_nonneg hh]
    nlinarith [mul_le_mul_of_nonneg_left hb hh]

noncomputable def fluidEulerRemainder (lam h : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, (fluidProfile lam (((i : ℝ) + 1) * h) -
    fluidProfile lam ((i : ℝ) * h) + h * infectionFraction (lam * fluidProfile lam ((i : ℝ) * h)))

theorem fluidProfile_euler_decomposition {lam : ℝ} (hlam : 0 < lam) (h : ℝ) (k : ℕ) :
    fluidProfile lam ((k : ℝ) * h) = 1 -
      h * ∑ i ∈ Finset.range k, infectionFraction (lam * fluidProfile lam ((i : ℝ) * h)) +
      fluidEulerRemainder lam h k := by
  induction k with
  | zero => simp [fluidEulerRemainder, fluidProfile_zero hlam]
  | succ k ih =>
    simp only [fluidEulerRemainder, Finset.sum_range_succ] at ih ⊢
    push_cast
    nlinarith

theorem fluidEulerRemainder_abs_le {lam h : ℝ} (hlam : 0 < lam) (hh : 0 ≤ h) (k : ℕ) :
    |fluidEulerRemainder lam h k| ≤ (k : ℝ) * lam ^ 2 * h ^ 2 := by
  unfold fluidEulerRemainder
  calc
    _ ≤ ∑ i ∈ Finset.range k, |fluidProfile lam (((i : ℝ) + 1) * h) -
        fluidProfile lam ((i : ℝ) * h) + h * infectionFraction (lam * fluidProfile lam ((i : ℝ) * h))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, lam ^ 2 * h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have he : ((i : ℝ) + 1) * h = (i : ℝ) * h + h := by ring
      rw [he]
      exact fluidProfile_euler_step_error hlam (mul_nonneg (Nat.cast_nonneg _) hh) hh
    _ = _ := by simp; ring

/-- A deterministic semimartingale/Euler comparison. The noise is the
accumulated error in the normalized path, not a bound on each increment.
The exact rate `a` remains separate from the limiting `lam`. -/
theorem susceptible_fluid_error_bound
    {lam a h B : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hh : 0 ≤ h) (hB : 0 ≤ B)
    (u M : ℕ → ℝ) (N : ℕ)
    (hu : ∀ k ≤ N, u k ∈ Icc (0 : ℝ) 1)
    (hM : ∀ k ≤ N, |M k| ≤ B)
    (hdecomp : ∀ k ≤ N, u k = u 0 + M k -
      h * ∑ i ∈ Finset.range k, infectionFraction (a * u i)) :
    ∀ k ≤ N, |u k - fluidProfile lam ((k : ℝ) * h)| ≤
      (|u 0 - 1| + B + (N : ℝ) * h * |a - lam| + (N : ℝ) * lam ^ 2 * h ^ 2) *
        Real.exp (lam * h * N) := by
  let e : ℕ → ℝ := fun k => |u k - fluidProfile lam ((k : ℝ) * h)|
  let A : ℝ := |u 0 - 1| + B + (N : ℝ) * h * |a - lam| +
    (N : ℝ) * lam ^ 2 * h ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hb : 0 ≤ lam * h := mul_nonneg hlam.le hh
  have hrec : ∀ k ≤ N, e k ≤ A + (lam * h) * ∑ i ∈ Finset.range k, e i := by
    intro k hk
    let d : ℕ → ℝ := fun i => infectionFraction (a * u i) -
      infectionFraction (lam * fluidProfile lam ((i : ℝ) * h))
    have hd : ∀ i ∈ Finset.range k, |d i| ≤ |a - lam| + lam * e i := by
      intro i hi
      exact infectionFraction_scaled_error ha hlam.le
        (hu i ((Finset.mem_range.mp hi).le.trans hk)) (fluidProfile_pos hlam _).le
    have hsum : |∑ i ∈ Finset.range k, d i| ≤
        (k : ℝ) * |a - lam| + lam * ∑ i ∈ Finset.range k, e i := by
      calc
        _ ≤ ∑ i ∈ Finset.range k, |d i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ Finset.range k, (|a - lam| + lam * e i) := Finset.sum_le_sum hd
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    have heq : u k - fluidProfile lam ((k : ℝ) * h) =
        (u 0 - 1) + M k + -(h * ∑ i ∈ Finset.range k, d i) +
          -(fluidEulerRemainder lam h k) := by
      rw [hdecomp k hk, fluidProfile_euler_decomposition hlam]
      dsimp [d]
      rw [Finset.sum_sub_distrib]
      ring
    have habs : e k ≤ |u 0 - 1| + |M k| +
        h * |∑ i ∈ Finset.range k, d i| + |fluidEulerRemainder lam h k| := by
      dsimp [e]
      rw [heq]
      have h1 := abs_add_le (u 0 - 1) (M k)
      have h2 := abs_add_le ((u 0 - 1) + M k) (-(h * ∑ i ∈ Finset.range k, d i))
      have h3 := abs_add_le ((u 0 - 1) + M k + -(h * ∑ i ∈ Finset.range k, d i))
        (-(fluidEulerRemainder lam h k))
      simp only [abs_neg, abs_mul, abs_of_nonneg hh] at h2 h3
      linarith
    have hsum' := mul_le_mul_of_nonneg_left hsum hh
    have hR := fluidEulerRemainder_abs_le hlam hh k
    have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
    have hmax : h * (k : ℝ) * |a - lam| + (k : ℝ) * lam ^ 2 * h ^ 2 ≤
        h * (N : ℝ) * |a - lam| + (N : ℝ) * lam ^ 2 * h ^ 2 := by gcongr
    have hm := hM k hk
    dsimp [A]
    nlinarith
  intro k hk
  have he := discrete_gronwall_exp hA hb hrec k hk
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have htime : lam * h * (k : ℝ) ≤ lam * h * N := mul_le_mul_of_nonneg_left hkR hb
  exact he.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htime) hA)

theorem susceptible_fluid_error_bound_on_time_interval
    {lam a h B T : ℝ} (hlam : 0 < lam) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hB : 0 ≤ B) (hT : 0 ≤ T) (u M : ℕ → ℝ) (N : ℕ)
    (horizon : (N : ℝ) * h ≤ T)
    (hu : ∀ k ≤ N, u k ∈ Icc (0 : ℝ) 1)
    (hM : ∀ k ≤ N, |M k| ≤ B)
    (hdecomp : ∀ k ≤ N, u k = u 0 + M k -
      h * ∑ i ∈ Finset.range k, infectionFraction (a * u i)) :
    ∀ k ≤ N, |u k - fluidProfile lam ((k : ℝ) * h)| ≤
      (|u 0 - 1| + B + T * |a - lam| + T * lam ^ 2 * h) * Real.exp (lam * T) := by
  intro k hk
  have he := susceptible_fluid_error_bound hlam ha hh hB u M N hu hM hdecomp k hk
  have hA : |u 0 - 1| + B + (N : ℝ) * h * |a - lam| + (N : ℝ) * lam ^ 2 * h ^ 2 ≤
      |u 0 - 1| + B + T * |a - lam| + T * lam ^ 2 * h := by
    have h1 := mul_le_mul_of_nonneg_right horizon (abs_nonneg (a - lam))
    have h2 := mul_le_mul_of_nonneg_right horizon (mul_nonneg (sq_nonneg lam) hh)
    nlinarith
  have htime : lam * h * (N : ℝ) ≤ lam * T := by
    have := mul_le_mul_of_nonneg_left horizon hlam.le
    nlinarith
  apply he.trans
  apply mul_le_mul hA (Real.exp_le_exp.mpr htime) (Real.exp_pos _).le
  positivity

end Freezing1.SIR
