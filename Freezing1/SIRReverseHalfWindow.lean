module

public import Freezing1.SIRStrongCounts
public import Freezing1.SIRLateAttachmentBudget
public import Freezing1.SIRCountsExtinctionIndex
public import Freezing1.SIRReversedHeightIdentity

/-! The half-window reduction in the corrected late SIR charge.
The early remainder is bounded on a genuine triangle-fluid good event;
no reversal or iid domination is assumed. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory Set
open scoped Topology BigOperators Classical NNReal

noncomputable def intervalBirthCharge (H : ℕ → Counts) (a b : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ico a b, birthCharge (H i) (H (i + 1))

def reverseHalfWindowCut (n τ : ℕ) : ℕ := τ - min (n / 2) (τ - n)

theorem reverseHalfWindowCut_bounds {n τ : ℕ} (hnτ : n ≤ τ) (hτ : τ ≤ 2 * n + 1) :
    n ≤ reverseHalfWindowCut n τ ∧ reverseHalfWindowCut n τ ≤ τ ∧
      reverseHalfWindowCut n τ ≤ n + n / 2 + 2 := by
  unfold reverseHalfWindowCut
  omega

theorem intervalBirthCharge_split (H : ℕ → Counts) {n τ : ℕ} (hnτ : n ≤ τ) :
    intervalBirthCharge H n τ =
      intervalBirthCharge H n (reverseHalfWindowCut n τ) +
        intervalBirthCharge H (reverseHalfWindowCut n τ) τ := by
  have hc : n ≤ reverseHalfWindowCut n τ := by unfold reverseHalfWindowCut; omega
  exact (Finset.sum_Ico_consecutive _ hc (Nat.sub_le _ _)).symm

theorem intervalBirthCharge_nonneg (H : ℕ → Counts) (a b : ℕ) :
    0 ≤ intervalBirthCharge H a b :=
  Finset.sum_nonneg (fun _ _ => birthCharge_nonneg _ _)

theorem reverseHalfWindow_early_charge_le (H : ℕ → Counts) {n τ : ℕ}
    (hn : 8 ≤ n) (hnτ : n ≤ τ) (hτ : τ ≤ 2 * n + 1)
    (hgood : ∀ k ≤ 2 * n,
      |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| < (n : ℝ) / 8) :
    intervalBirthCharge H n (reverseHalfWindowCut n τ) ≤ 16 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hcutn, hcutτ, hcut⟩ := reverseHalfWindowCut_bounds hnτ hτ
  have hterm (k : ℕ) (hk : k ∈ Finset.Ico n (reverseHalfWindowCut n τ)) :
      birthCharge (H k) (H (k + 1)) ≤ 8 / (n : ℝ) := by
    obtain ⟨hnk, hkc⟩ := Finset.mem_Ico.mp hk
    have hk2n : k ≤ 2 * n := by omega
    have hprofile : n ≤ 4 * min k (2 * n - k) := by omega
    have hprofileR : (n : ℝ) ≤ 4 * (min k (2 * n - k) : ℕ) := by exact_mod_cast hprofile
    have hlow : (n : ℝ) / 8 ≤ (H k).infectious := by
      have he := (abs_lt.mp (hgood k hk2n)).1
      linarith
    have hi0 : 0 < ((H k).infectious : ℝ) := (div_pos hn0 (by norm_num)).trans_le hlow
    unfold birthCharge
    split_ifs
    · have hh := one_div_le_one_div_of_le (div_pos hn0 (by norm_num : (0 : ℝ) < 8)) hlow
      convert hh using 1; field_simp
    · positivity
  calc
    _ ≤ ∑ _k ∈ Finset.Ico n (reverseHalfWindowCut n τ), 8 / (n : ℝ) :=
      Finset.sum_le_sum hterm
    _ = ((reverseHalfWindowCut n τ - n : ℕ) : ℝ) * (8 / (n : ℝ)) := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    _ ≤ 16 := by
      have hlen : reverseHalfWindowCut n τ - n ≤ 2 * n := by omega
      have hlenR : ((reverseHalfWindowCut n τ - n : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
        exact_mod_cast hlen
      calc
        _ ≤ (2 * (n : ℝ)) * (8 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right hlenR (by positivity)
        _ = _ := by field_simp; norm_num

theorem reverseHalfWindow_early_charge_le_all (H : ℕ → Counts) {n τ : ℕ}
    (hn : 8 ≤ n) (hτ : τ ≤ 2 * n + 1)
    (hgood : ∀ k ≤ 2 * n,
      |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| < (n : ℝ) / 8) :
    intervalBirthCharge H n (reverseHalfWindowCut n τ) ≤ 16 := by
  by_cases hnτ : n ≤ τ
  · exact reverseHalfWindow_early_charge_le H hn hnτ hτ hgood
  · have hc : reverseHalfWindowCut n τ ≤ n := by unfold reverseHalfWindowCut; omega
    simp only [intervalBirthCharge, Finset.Ico_eq_empty_of_le hc, Finset.sum_empty]
    norm_num

/-- The early remainder vanishes uniformly over every possible epidemic
endpoint. The actual endpoint is at most `2*n+1`; no reverse-time
probability or iid coupling enters this fluid-limit reduction. -/
theorem countsFullLaw_reverseHalfWindow_early_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real {H |
      ∃ τ : ℕ, τ ≤ 2 * n + 1 ∧
        ε ≤ intervalBirthCharge H n (reverseHalfWindowCut n τ) / Real.log (n : ℝ)})
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => ε * Real.log (n : ℝ)) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hε
  have hbound : ∀ᶠ n in atTop,
      (countsFullLaw (rate n) n).real {H | ∃ τ : ℕ, τ ≤ 2 * n + 1 ∧
        ε ≤ intervalBirthCharge H n (reverseHalfWindowCut n τ) / Real.log (n : ℝ)} ≤
      (countsFullLaw (rate n) n).real {H | ∃ k ≤ 2 * n,
        ((1 : ℝ) / 8) * n ≤ |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} := by
    filter_upwards [eventually_ge_atTop 8, hlog.eventually_gt_atTop 16] with n hn hlarge
    apply measureReal_mono _ (measure_ne_top _ _)
    rintro H ⟨τ, hτ, hbad⟩
    by_contra hnot
    have hg : ∀ k ≤ 2 * n,
        |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| < (n : ℝ) / 8 := by
      intro k hk
      have hh : |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| < ((1 : ℝ) / 8) * n :=
        lt_of_not_ge (fun he => hnot ⟨k, hk, he⟩)
      linarith
    have hc := reverseHalfWindow_early_charge_le_all H hn hτ hg
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hprod := (le_div_iff₀ (Real.log_pos hnR)).mp hbad
    linarith
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (countsFullLaw_triangle_tendsto_zero rate hstrong (by norm_num : (0 : ℝ) < 1 / 8))

theorem intervalBirthCharge_split_all (H : ℕ → Counts) (n τ : ℕ) :
    intervalBirthCharge H n τ = intervalBirthCharge H n (reverseHalfWindowCut n τ) +
      intervalBirthCharge H (reverseHalfWindowCut n τ) τ := by
  by_cases hnτ : n ≤ τ
  · exact intervalBirthCharge_split H hnτ
  · have hc : reverseHalfWindowCut n τ = τ := by unfold reverseHalfWindowCut; omega
    simp only [hc, intervalBirthCharge, Finset.Ico_self, Finset.sum_empty, add_zero]

theorem intervalBirthCharge_reverse (H : ℕ → Counts) (n τ : ℕ) :
    intervalBirthCharge H n τ =
      ∑ j ∈ Finset.Icc 1 (τ - n),
        if (H (τ - j + 1)).susceptible < (H (τ - j)).susceptible then
          1 / ((H (τ - j)).infectious : ℝ) else 0 := by
  let x : SignSequence := fun i => decide ((H i).susceptible < (H (i - 1)).susceptible)
  have hh := reverse_preStep_attachment_sum x (fun i => ((H i).infectious : ℝ)) n τ
  simpa only [x, intervalBirthCharge, birthCharge, Nat.add_sub_cancel,
    decide_eq_true_eq] using hh

theorem intervalBirthCharge_lastHalf_reverse (H : ℕ → Counts) (n τ : ℕ) :
    intervalBirthCharge H (reverseHalfWindowCut n τ) τ =
      ∑ j ∈ Finset.Icc 1 (min (n / 2) (τ - n)),
        if (H (τ - j + 1)).susceptible < (H (τ - j)).susceptible then
          1 / ((H (τ - j)).infectious : ℝ) else 0 := by
  rw [intervalBirthCharge_reverse]
  have hm : min (n / 2) (τ - n) ≤ τ := (min_le_right _ _).trans (Nat.sub_le _ _)
  rw [reverseHalfWindowCut, Nat.sub_sub_self hm]

theorem countsFullLaw_actualHalfWindow_early_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (countsFullLaw (rate n) n).real {H |
      ε ≤ intervalBirthCharge H n (reverseHalfWindowCut n (boundedExtinctionIndex n H)) /
        Real.log (n : ℝ)}) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _
    (countsFullLaw_reverseHalfWindow_early_tendsto_zero rate hstrong hε)
  intro n
  apply measureReal_mono _ (measure_ne_top _ _)
  intro H hH
  exact ⟨boundedExtinctionIndex n H, boundedExtinctionIndex_le n H, hH⟩

/-- The exact source sufficiency reduction after correcting its charge
index: vanishing of the last half-window implies vanishing of the entire
post-population charge. The early remainder is proved negligible from
the actual fluid limit, rather than assumed. -/
theorem countsFullLaw_late_charge_reduced_to_lastHalf (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (hlast : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      (countsFullLaw (rate n) n).real {H |
        ε ≤ intervalBirthCharge H (reverseHalfWindowCut n (boundedExtinctionIndex n H))
          (boundedExtinctionIndex n H) / Real.log (n : ℝ)}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      (countsFullLaw (rate n) n).real {H |
        ε ≤ intervalBirthCharge H n (boundedExtinctionIndex n H) / Real.log (n : ℝ)})
      atTop (𝓝 0) := by
  intro ε hε
  have hsum := (countsFullLaw_actualHalfWindow_early_tendsto_zero rate hstrong (half_pos hε)).add
    (hlast (ε / 2) (half_pos hε))
  simp only [add_zero] at hsum
  apply squeeze_zero (fun _ => ENNReal.toReal_nonneg) _ hsum
  intro n
  calc
    _ ≤ (countsFullLaw (rate n) n).real
        ({H | ε / 2 ≤ intervalBirthCharge H n
          (reverseHalfWindowCut n (boundedExtinctionIndex n H)) / Real.log (n : ℝ)} ∪
         {H | ε / 2 ≤ intervalBirthCharge H
          (reverseHalfWindowCut n (boundedExtinctionIndex n H))
          (boundedExtinctionIndex n H) / Real.log (n : ℝ)}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro H hH
      change ε ≤ intervalBirthCharge H n (boundedExtinctionIndex n H) / Real.log (n : ℝ) at hH
      rw [intervalBirthCharge_split_all H n (boundedExtinctionIndex n H), add_div] at hH
      by_cases he : ε / 2 ≤ intervalBirthCharge H n
          (reverseHalfWindowCut n (boundedExtinctionIndex n H)) / Real.log (n : ℝ)
      · exact Or.inl he
      · exact Or.inr (by change ε / 2 ≤ _; linarith)
    _ ≤ _ := measureReal_union_le _ _

end Freezing1.SIR
