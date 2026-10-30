module

public import Freezing1.LinearRegimeIntervals
public import Freezing1.LinearRegimeAssumptions
public import Freezing1.HeightScaleBounds

/-!
# Uniform logarithmic blocks in the linear regime

This proves Lemma `lem:estimee uniforme sur h_n+` with its original nested
limit and its original interval `(a,b]`. The proof uses the quantitative Abel
estimate from `LinearRegimeIntervals`, rather than geometric subdivisions.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology NNReal

/-- The quantified form of the uniform logarithmic interval conclusion. -/
def UniformLogIntervals (x : ℕ → SignSequence) (A : ℕ → ℝ) (c C : ℝ) : Prop :=
  ∀ δ > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
    ∀ a b : ℕ, A n ≤ (a : ℝ) → a < b → (b : ℝ) ≤ ε * n →
      (a : ℝ) * C < b →
      |heightInterval (x n) a b / Real.log ((b : ℝ) / a) - (c + 1) / (2 * c)| ≤ δ

/-- The near-origin hypothesis alone gives the uniform logarithmic-block estimate. -/
theorem uniformLogIntervals_of_nearOriginLinear {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (hnear : NearOriginLinear x A c)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hC : 1 < C) :
    UniformLogIntervals x A c C := by
  intro δ hδ
  let L : ℝ := Real.log C
  let K : ℝ := (c + 1) / (2 * c)
  let B : ℝ := 2 / c ^ 2 + 1 / (2 * c) + 1 / (c * L)
  let η : ℝ := min (c / 2) (δ / (2 * B))
  have hL : 0 < L := Real.log_pos hC
  have hK : 0 < K := by dsimp [K]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hη : 0 < η := lt_min (half_pos hc) (div_pos hδ (by positivity))
  obtain ⟨ε, hε0, hε1, hnε⟩ := hnear η hη
  refine ⟨ε, hε0, hε1, ?_⟩
  filter_upwards [hnε, hA.eventually_ge_atTop (max 1 (2 * K / (δ * L)))] with n hn hAn
  intro a b hAa hab hbε haC
  have ha1 : (1 : ℝ) ≤ a := (le_max_left _ _).trans (hAn.trans hAa)
  have ha : 1 ≤ a := by exact_mod_cast ha1
  have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha1
  have hLc : L ≤ Real.log ((b : ℝ) / a) := by
    apply Real.log_le_log (lt_trans zero_lt_one hC)
    exact ((lt_div_iff₀ ha0).mpr (by simpa only [mul_comm] using haC)).le
  have herror : ∀ i ∈ Finset.Icc a b, |(activeCount (x n) i : ℝ) / i - c| ≤ η := by
    intro i hi
    obtain ⟨hai, hib⟩ := Finset.mem_Icc.mp hi
    exact hn i (hAa.trans (by exact_mod_cast hai)) ((by exact_mod_cast hib : (i : ℝ) ≤ b).trans hbε)
  have hfinite := heightInterval_log_error_le ha hab.le hc hη.le (min_le_left _ _) hL hLc herror
  have hfirst : η * B ≤ δ / 2 := by
    have hsmall : η ≤ δ / (2 * B) := min_le_right _ _
    have hmul := (le_div_iff₀ (show 0 < 2 * B by positivity)).mp hsmall
    nlinarith
  have hsecond : K / ((a : ℝ) * L) ≤ δ / 2 := by
    have hcut : 2 * K / (δ * L) ≤ (a : ℝ) :=
      (le_max_right _ _).trans (hAn.trans hAa)
    have hmul := (div_le_iff₀ (mul_pos hδ hL)).mp hcut
    apply (div_le_iff₀ (mul_pos ha0 hL)).mpr
    nlinarith
  exact hfinite.trans (by change η * B + K / ((a : ℝ) * L) ≤ δ; linarith)

/-- The pairs occurring in the maximum in the source, including every cutoff. -/
noncomputable def logIntervalPairs (A : ℕ → ℝ) (C ε : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter fun p =>
    A n ≤ (p.1 : ℝ) ∧ p.1 < p.2 ∧ (p.2 : ℝ) ≤ ε * n ∧ (p.1 : ℝ) * C < p.2

/-- The finite nonnegative maximum is zero if its index set is empty. -/
noncomputable def logIntervalMaximum (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c C ε : ℝ) (n : ℕ) : ℝ :=
  (((logIntervalPairs A C ε n).sup (fun p =>
    (⟨|heightInterval (x n) p.1 p.2 / Real.log ((p.2 : ℝ) / p.1) - (c + 1) / (2 * c)|,
      abs_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ)

/-- The literal double-limit conclusion of Lemma 8, for one fixed `C > 1`. -/
def LogIntervalLimsup (x : ℕ → SignSequence) (A : ℕ → ℝ) (c C : ℝ) : Prop :=
  Tendsto (fun ε : ℝ => limsup (logIntervalMaximum x A c C ε) atTop)
    (𝓝[>] 0) (𝓝 0)

theorem mem_logIntervalPairs {A : ℕ → ℝ} {C ε : ℝ} {n a b : ℕ}
    (hε : ε ≤ 1) : (a, b) ∈ logIntervalPairs A C ε n ↔
      A n ≤ (a : ℝ) ∧ a < b ∧ (b : ℝ) ≤ ε * n ∧ (a : ℝ) * C < b := by
  classical
  simp only [logIntervalPairs, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    have hbn : (b : ℝ) ≤ n := h.2.2.1.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    have hbn' : b ≤ n := by exact_mod_cast hbn
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩, h⟩

theorem logIntervalMaximum_nonneg (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c C ε : ℝ) (n : ℕ) : 0 ≤ logIntervalMaximum x A c C ε n := NNReal.coe_nonneg _

theorem logIntervalMaximum_eq_sup' (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c C ε : ℝ) (n : ℕ) (hne : (logIntervalPairs A C ε n).Nonempty) :
    logIntervalMaximum x A c C ε n = (logIntervalPairs A C ε n).sup' hne
      (fun p => |heightInterval (x n) p.1 p.2 / Real.log ((p.2 : ℝ) / p.1) -
        (c + 1) / (2 * c)|) := by
  classical
  let s := logIntervalPairs A C ε n
  let f : ℕ × ℕ → ℝ := fun p =>
    |heightInterval (x n) p.1 p.2 / Real.log ((p.2 : ℝ) / p.1) - (c + 1) / (2 * c)|
  have h0 : 0 ≤ s.sup' hne f :=
    (abs_nonneg _).trans (Finset.le_sup' f hne.choose_spec)
  apply le_antisymm
  · change s.sup (fun p => (⟨f p, abs_nonneg _⟩ : ℝ≥0)) ≤ (⟨s.sup' hne f, h0⟩ : ℝ≥0)
    apply Finset.sup_le
    intro p hp
    exact Finset.le_sup' f hp
  · apply Finset.sup'_le
    intro p hp
    exact Finset.le_sup (f := fun p => (⟨f p, abs_nonneg _⟩ : ℝ≥0)) hp

theorem logIntervalMaximum_le_iff {x : ℕ → SignSequence} {A : ℕ → ℝ}
    {c C ε δ : ℝ} {n : ℕ} (hε : ε ≤ 1) (hδ : 0 ≤ δ) :
    logIntervalMaximum x A c C ε n ≤ δ ↔
      ∀ a b : ℕ, A n ≤ (a : ℝ) → a < b → (b : ℝ) ≤ ε * n →
        (a : ℝ) * C < b →
        |heightInterval (x n) a b / Real.log ((b : ℝ) / a) - (c + 1) / (2 * c)| ≤ δ := by
  classical
  change (logIntervalPairs A C ε n).sup (fun p =>
    (⟨|heightInterval (x n) p.1 p.2 / Real.log ((p.2 : ℝ) / p.1) - (c + 1) / (2 * c)|,
      abs_nonneg _⟩ : ℝ≥0)) ≤ (⟨δ, hδ⟩ : ℝ≥0) ↔ _
  rw [Finset.sup_le_iff]
  change (∀ p ∈ logIntervalPairs A C ε n,
    |heightInterval (x n) p.1 p.2 / Real.log ((p.2 : ℝ) / p.1) - (c + 1) / (2 * c)| ≤ δ) ↔ _
  simp only [Prod.forall, mem_logIntervalPairs hε]
  aesop

theorem logIntervalMaximum_mono (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c C : ℝ) {δ ε : ℝ} (hδε : δ ≤ ε) (n : ℕ) :
    logIntervalMaximum x A c C δ n ≤ logIntervalMaximum x A c C ε n := by
  classical
  unfold logIntervalMaximum
  apply NNReal.coe_le_coe.mpr
  apply Finset.sup_mono
  intro p hp
  simp only [logIntervalPairs, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1, hp.2.2.1,
    hp.2.2.2.1.trans (mul_le_mul_of_nonneg_right hδε (Nat.cast_nonneg n)), hp.2.2.2.2⟩

/-- The quantified uniform estimate entails the literal nested limit. The
eventual boundedness needed for real-valued `limsup` follows from the estimate. -/
theorem logIntervalLimsup_of_uniformLogIntervals {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (h : UniformLogIntervals x A c C) :
    LogIntervalLimsup x A c C := by
  have hq : ∀ δ > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ᶠ n in atTop, logIntervalMaximum x A c C ε n ≤ δ := by
    intro δ hδ
    obtain ⟨ε, hε0, hε1, he⟩ := h δ hδ
    refine ⟨ε, hε0, hε1, ?_⟩
    exact he.mono fun n hn => (logIntervalMaximum_le_iff hε1.le hδ.le).mpr hn
  have hb : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsBoundedUnder (· ≤ ·) atTop (logIntervalMaximum x A c C ε) := by
    obtain ⟨ε, hε0, _, he⟩ := hq 1 zero_lt_one
    filter_upwards [Ioo_mem_nhdsGT hε0] with δ hδ
    exact isBoundedUnder_of_eventually_le (he.mono fun n hn =>
      (logIntervalMaximum_mono x A c C hδ.2.le n).trans hn)
  exact (tendsto_limsup_nhdsGT_zero_iff _ (logIntervalMaximum_nonneg x A c C)
    (fun _ hδε n => logIntervalMaximum_mono x A c C hδε n) hb).mpr hq

/-- Lemma 8, in its original nested maximum/limsup/limit form. -/
theorem logIntervalLimsup_of_nearOriginLinear {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (hnear : NearOriginLinear x A c)
    (hA : Tendsto A atTop atTop) (hc : 0 < c) (hC : 1 < C) :
    LogIntervalLimsup x A c C :=
  logIntervalLimsup_of_uniformLogIntervals
    (uniformLogIntervals_of_nearOriginLinear hnear hA hc hC)

/-- The logarithmic-block conclusion under the literal first source hypothesis. -/
theorem logIntervalLimsup_of_nearOriginLimsup {x : ℕ → SignSequence}
    {A : ℕ → ℝ} {c C : ℝ} (hnear : NearOriginLimsup x A c)
    (hApos : ∀ n, 0 < A n) (hA : Tendsto A atTop atTop)
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 1 < C)
    (hsurv : ∀ n, PositiveThrough (x n) n) : LogIntervalLimsup x A c C :=
  logIntervalLimsup_of_nearOriginLinear
    ((nearOriginLimsup_iff x A hApos hc.le hc1 hsurv).mp hnear) hA hc hC

/-- Under the source cutoff assumptions the maximum in Lemma 8 is eventually
over a nonempty set, for every fixed positive outer cutoff. -/
theorem eventually_logIntervalPairs_nonempty {A : ℕ → ℝ} {C ε : ℝ}
    (hApos : ∀ n, 0 < A n)
    (hsmall : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    (hC : 1 < C) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n in atTop, (logIntervalPairs A C ε n).Nonempty := by
  let a : ℕ → ℕ := fun n => Nat.ceil (A n)
  have ha : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 0) :=
    tendsto_natCutoff_div_nat_zero_of_sublog
      (tendsto_ceil_div_log_zero (Eventually.of_forall fun n => (hApos n).le) hsmall)
  have hr : Tendsto (fun n : ℕ => ((C + 1) * (a n : ℝ) + 1) / n) atTop (𝓝 0) := by
    simpa only [add_div, mul_div_assoc, mul_zero, add_zero] using
      (tendsto_const_nhds.mul ha).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  filter_upwards [hr.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
  let b : ℕ := Nat.ceil ((C + 1) * (a n : ℝ))
  have haA : A n ≤ (a n : ℝ) := Nat.le_ceil _
  have ha0 : (0 : ℝ) < a n := (hApos n).trans_le haA
  have hb : (C + 1) * (a n : ℝ) ≤ b := Nat.le_ceil _
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hbε : (b : ℝ) ≤ ε * n := by
    have hround : (b : ℝ) < (C + 1) * (a n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    exact hround.le.trans ((div_lt_iff₀ hnp).mp hn).le
  refine ⟨(a n, b), (mem_logIntervalPairs hε1).mpr ⟨haA, ?_, hbε, ?_⟩⟩
  · have : (a n : ℝ) < b := by nlinarith
    exact_mod_cast this
  · nlinarith

end Freezing1
