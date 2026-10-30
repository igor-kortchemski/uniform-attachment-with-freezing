module

public import Freezing1.HeightScale
public import Freezing1.Extinction
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Early and late contributions to the height scale

All finite sums here use the paper's actual positive step indices. These
estimates justify the early cutoff and bounded late contribution in the proof
of Theorem `thm:lineaire` (I), independently of the central logarithmic block.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology BigOperators

/-- Attachment reciprocals on an arbitrary finite set of actual step indices. -/
noncomputable def heightScaleOn (x : SignSequence) (s : Finset ℕ) : ℝ :=
  ∑ i ∈ s, if x i then 1 / (activeCount x i : ℝ) else 0

theorem heightScaleOn_Ioc_eq (x : SignSequence) (a b : ℕ) :
    heightScaleOn x (Finset.Ioc a b) =
      ∑ i ∈ Finset.Ico a b, if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0 := by
  unfold heightScaleOn
  symm
  simpa only [Finset.Ico_add_one_add_one_eq_Ioc] using
    Finset.sum_Ico_add' (fun i => if x i then (1 : ℝ) / activeCount x i else 0) a b 1

theorem heightScale_add_heightScaleOn_Ioc {x : SignSequence} {a b : ℕ} (hab : a ≤ b) :
    heightScale x a + heightScaleOn x (Finset.Ioc a b) = heightScale x b := by
  rw [heightScaleOn_Ioc_eq]
  exact Finset.sum_range_add_sum_Ico _ hab

theorem heightScaleOn_Ioc_zero (x : SignSequence) (n : ℕ) :
    heightScaleOn x (Finset.Ioc 0 n) = heightScale x n := by
  unfold heightScaleOn heightScale
  symm
  simpa only [Nat.Ico_zero_eq_range, Finset.Ico_add_one_add_one_eq_Ioc] using
    Finset.sum_Ico_add' (fun i => if x i then (1 : ℝ) / activeCount x i else 0) 0 n 1

/-- At an attachment step before extinction there are at least two active vertices. -/
theorem two_le_activeCount_of_attachment {x : SignSequence} {i n : ℕ}
    (h : PositiveThrough x n) (hi : 1 ≤ i) (hin : i ≤ n) (hx : x i = true) :
    (2 : ℤ) ≤ activeCount x i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hk := h k (by omega)
  rw [activeCount_succ, hx]
  simp only [↓reduceIte]
  omega

/-- A deterministic uniform lower denominator bounds any finite reciprocal sum. -/
theorem heightScaleOn_bounds {x : SignSequence} {s : Finset ℕ} {d : ℝ}
    (hd : 0 < d) (hs : ∀ i ∈ s, x i = true → d ≤ (activeCount x i : ℝ)) :
    0 ≤ heightScaleOn x s ∧ heightScaleOn x s ≤ s.card / d := by
  have hterm : ∀ i ∈ s, 0 ≤ (if x i then 1 / (activeCount x i : ℝ) else 0) ∧
      (if x i then 1 / (activeCount x i : ℝ) else 0) ≤ 1 / d := by
    intro i hi
    cases hx : x i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨le_rfl, by positivity⟩
    · simp only [↓reduceIte]
      have hiS := hs i hi hx
      exact ⟨one_div_nonneg.mpr (hd.le.trans hiS), one_div_le_one_div_of_le hd hiS⟩
  constructor
  · exact Finset.sum_nonneg (fun i hi => (hterm i hi).1)
  · calc
      heightScaleOn x s ≤ ∑ _i ∈ s, (1 : ℝ) / d :=
        Finset.sum_le_sum (fun i hi => (hterm i hi).2)
      _ = s.card / d := by simp [div_eq_mul_inv]

theorem heightScaleOn_le_card_half {x : SignSequence} {n : ℕ} {s : Finset ℕ}
    (h : PositiveThrough x n) (hs : s ⊆ Finset.Ioc 0 n) :
    0 ≤ heightScaleOn x s ∧ heightScaleOn x s ≤ s.card / 2 := by
  apply heightScaleOn_bounds (by norm_num)
  intro i hi hxi
  have hii := Finset.mem_Ioc.mp (hs hi)
  exact_mod_cast two_le_activeCount_of_attachment h (by omega) hii.2 hxi

/-- The early contribution is at most half its number of steps. -/
theorem heightScale_le_half {x : SignSequence} {n : ℕ} (h : PositiveThrough x n) :
    0 ≤ heightScale x n ∧ heightScale x n ≤ (n : ℝ) / 2 := by
  have hb := heightScaleOn_le_card_half h (Finset.Subset.refl (Finset.Ioc 0 n))
  simpa only [heightScaleOn_Ioc_zero, Nat.card_Ioc, Nat.sub_zero] using hb

/-- A late block with active count at least `δ*n` contributes at most `1/δ`. -/
theorem heightScaleOn_le_inv_delta {x : SignSequence} {n : ℕ} {s : Finset ℕ} {δ : ℝ}
    (hn : 1 ≤ n) (hδ : 0 < δ) (hs : s ⊆ Finset.Ioc 0 n)
    (hS : ∀ i ∈ s, x i = true → δ * n ≤ (activeCount x i : ℝ)) :
    0 ≤ heightScaleOn x s ∧ heightScaleOn x s ≤ 1 / δ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hb := heightScaleOn_bounds (mul_pos hδ hnR) hS
  have hc : s.card ≤ n := by
    simpa only [Nat.card_Ioc, Nat.sub_zero] using Finset.card_le_card hs
  refine ⟨hb.1, hb.2.trans ?_⟩
  calc
    (s.card : ℝ) / (δ * n) ≤ n / (δ * n) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
    _ = 1 / δ := by field_simp

/-- Rounding a nonnegative sublogarithmic cutoff upwards preserves sublogarithmic growth. -/
theorem tendsto_ceil_div_log_zero {A : ℕ → ℝ}
    (hA : ∀ᶠ n in atTop, 0 ≤ A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (Nat.ceil (A n) : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => 1 / Real.log (n : ℝ)) atTop (𝓝 0) := by
    have hh := tendsto_inv_atTop_zero.comp hlog
    change Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) at hh
    simpa only [one_div] using hh
  have hup := hsmall.add hinv
  simp only [add_zero] at hup
  apply squeeze_zero' ?_ ?_ hup
  · filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    positivity
  · filter_upwards [hA, hlog.eventually_gt_atTop 0] with n hn hln
    rw [← add_div]
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hn).le hln.le

/-- A ceiling cutoff also retains divergence to infinity. -/
theorem tendsto_nat_ceil_atTop_of_tendsto {A : ℕ → ℝ} (hA : Tendsto A atTop atTop) :
    Tendsto (fun n => (Nat.ceil (A n) : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun n => Nat.le_ceil (A n)) hA

/-- A sublogarithmic natural cutoff eventually lies before time `n`. -/
theorem eventually_natCutoff_le_of_sublog {a : ℕ → ℕ}
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, a n ≤ n := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually_gt_atTop 0, hsmall.eventually (gt_mem_nhds zero_lt_one)]
    with n hln hn
  have ha : (a n : ℝ) < Real.log (n : ℝ) := by
    have := (div_lt_iff₀ hln).mp hn
    simpa only [one_mul] using this
  exact_mod_cast ha.le.trans (Real.log_le_self (Nat.cast_nonneg n))

/-- Sublogarithmic natural cutoffs are also sublinear. -/
theorem tendsto_natCutoff_div_nat_zero_of_sublog {a : ℕ → ℕ}
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ hsmall
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hn (Real.log_le_self (Nat.cast_nonneg n))

theorem eventually_natCutoff_le_mul_nat_of_sublog {a : ℕ → ℕ}
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (a n : ℝ) ≤ ε * n := by
  have hr := tendsto_natCutoff_div_nat_zero_of_sublog hsmall
  filter_upwards [eventually_ge_atTop 1, hr.eventually (gt_mem_nhds hε)] with n hn hsmalln
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ((div_lt_iff₀ hnR).mp hsmalln).le

/-- The early contribution below a sublogarithmic natural cutoff is negligible. -/
theorem tendsto_early_heightScale_div_log_zero (x : ℕ → SignSequence) (a : ℕ → ℕ)
    (hsurv : ∀ n, PositiveThrough (x n) n)
    (ha : ∀ᶠ n in atTop, a n ≤ n)
    (hsmall : Tendsto (fun n : ℕ => (a n : ℝ) / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => heightScale (x n) (a n) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' ?_ ?_ hsmall
  · filter_upwards [ha, hlog.eventually_gt_atTop 0] with n hn hln
    exact div_nonneg (heightScale_le_half ((hsurv n).mono hn)).1 hln.le
  · filter_upwards [ha, hlog.eventually_gt_atTop 0] with n hn hln
    apply div_le_div_of_nonneg_right _ hln.le
    have hh := (heightScale_le_half ((hsurv n).mono hn)).2
    have ha0 : (0 : ℝ) ≤ a n := Nat.cast_nonneg _
    linarith

/-- The actual ceiling enlargement of the paper's real cutoff has negligible early contribution. -/
theorem tendsto_early_ceil_heightScale_div_log_zero (x : ℕ → SignSequence) {A : ℕ → ℝ}
    (hsurv : ∀ n, PositiveThrough (x n) n)
    (hA : ∀ᶠ n in atTop, 0 ≤ A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => heightScale (x n) (Nat.ceil (A n)) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hc := tendsto_ceil_div_log_zero hA hsmall
  exact tendsto_early_heightScale_div_log_zero x (fun n => Nat.ceil (A n)) hsurv
    (eventually_natCutoff_le_of_sublog hc) hc

/-- Any fixed-denominator late block contributes negligibly after division by `log n`. -/
theorem tendsto_late_heightScale_div_log_zero (x : ℕ → SignSequence) (s : ℕ → Finset ℕ)
    {δ : ℝ} (hδ : 0 < δ)
    (hs : ∀ᶠ n in atTop, s n ⊆ Finset.Ioc 0 n)
    (hS : ∀ᶠ n in atTop, ∀ i ∈ s n, x n i = true → δ * n ≤ (activeCount (x n) i : ℝ)) :
    Tendsto (fun n : ℕ => heightScaleOn (x n) (s n) / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (1 / δ) / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hb : ∀ᶠ n : ℕ in atTop, 0 ≤ heightScaleOn (x n) (s n) ∧ heightScaleOn (x n) (s n) ≤ 1 / δ := by
    filter_upwards [eventually_ge_atTop 1, hs, hS] with n hn hsn hSn
    exact heightScaleOn_le_inv_delta hn hδ hsn hSn
  apply squeeze_zero' ?_ ?_ hi
  · filter_upwards [hb, hlog.eventually_gt_atTop 0] with n hn hln
    exact div_nonneg hn.1 hln.le
  · filter_upwards [hb, hlog.eventually_gt_atTop 0] with n hn hln
    exact div_le_div_of_nonneg_right hn.2 hln.le

end Freezing1
