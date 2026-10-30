module

public import Freezing1.Extinction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Topology.Order.LeftRightNhds

/-!
# The two uniform hypotheses in the linear regime

The finite maximum is a nonnegative supremum, with value zero on an empty
index set. Its indices agree with the paper's interval for `0 < ε < 1`.
The bulk minimum always includes the endpoint `n`; for `ε ≤ 1` this is
exactly the paper's finite interval. The equivalences below preserve the
order of the limits and allow the bulk lower constant to depend on `ε`.
-/

@[expose] public section

namespace Freezing1

open Filter
open scoped Topology NNReal

set_option backward.isDefEq.respectTransparency false

def NearOriginLinear (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ η > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop,
    ∀ i : ℕ, A n ≤ (i : ℝ) → (i : ℝ) ≤ ε * n →
      |(activeCount (x n) i : ℝ) / i - c| ≤ η

def BulkLowerBound (x : ℕ → SignSequence) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, ∀ᶠ (n : ℕ) in atTop,
    ∀ i : ℕ, ε * n ≤ (i : ℝ) → i ≤ n →
      δ ≤ (activeCount (x n) i : ℝ) / n

noncomputable def nearOriginIndices (A : ℕ → ℝ) (ε : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter fun i => A n ≤ (i : ℝ) ∧ (i : ℝ) ≤ ε * n

noncomputable def nearOriginMaximum (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c ε : ℝ) (n : ℕ) : ℝ :=
  (((nearOriginIndices A ε n).sup
    (fun i => (⟨|(activeCount (x n) i : ℝ) / i - c|, abs_nonneg _⟩ : ℝ≥0)) : ℝ≥0) : ℝ)

def NearOriginLimsup (x : ℕ → SignSequence) (A : ℕ → ℝ) (c : ℝ) : Prop :=
  Tendsto (fun ε : ℝ => limsup (nearOriginMaximum x A c ε) atTop)
    (𝓝[>] 0) (𝓝 0)

noncomputable def bulkIndices (ε : ℝ) (n : ℕ) : Finset ℕ :=
  insert n ((Finset.range (n + 1)).filter fun i => ε * n ≤ (i : ℝ))

noncomputable def bulkMinimum (x : ℕ → SignSequence) (ε : ℝ) (n : ℕ) : ℝ :=
  (bulkIndices ε n).inf' (Finset.insert_nonempty _ _)
    (fun i => (activeCount (x n) i : ℝ) / n)

def BulkLiminf (x : ℕ → SignSequence) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → 0 < liminf (bulkMinimum x ε) atTop

/-- A bounded nonnegative family of maxima has the paper's nested limit
exactly when it admits arbitrarily small eventual uniform bounds. Boundedness
is required only for sufficiently small positive outer parameters. -/
theorem tendsto_limsup_nhdsGT_zero_iff (F : ℝ → ℕ → ℝ)
    (h_nonneg : ∀ ε n, 0 ≤ F ε n)
    (h_mono : ∀ {δ ε : ℝ}, 0 < δ → δ ≤ ε → ∀ n, F δ n ≤ F ε n)
    (h_bdd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsBoundedUnder (· ≤ ·) atTop (F ε)) :
    Tendsto (fun ε => limsup (F ε) atTop) (𝓝[>] 0) (𝓝 0) ↔
      ∀ η > 0, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ᶠ n in atTop, F ε n ≤ η := by
  constructor
  · intro h η hη
    have he := ((h.eventually (gt_mem_nhds hη)).and h_bdd).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨ε, ⟨hlim, hb⟩, hε0, hε1⟩ := he.exists
    refine ⟨ε, hε0, hε1, ?_⟩
    exact (eventually_lt_of_limsup_lt hlim hb).mono fun _ hn => hn.le
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨ε, hε0, _, hbound⟩ := h (η / 2) (half_pos hη)
    filter_upwards [Ioo_mem_nhdsGT hε0] with δ hδ
    have hboundδ : ∀ᶠ n in atTop, F δ n ≤ η / 2 :=
      hbound.mono fun n hn => (h_mono hδ.1 hδ.2.le n).trans hn
    have hlim : limsup (F δ) atTop ≤ η / 2 :=
      limsup_le_of_le (isCoboundedUnder_le_of_le atTop (h_nonneg δ)) hboundδ
    have h0 : 0 ≤ limsup (F δ) atTop := by
      apply le_limsup_of_le (isBoundedUnder_of_eventually_le hboundδ)
      intro b hb
      obtain ⟨n, hn⟩ := hb.exists
      exact (h_nonneg δ n).trans hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    linarith

theorem mem_nearOriginIndices {A : ℕ → ℝ} {ε : ℝ} {n i : ℕ}
    (hε : ε ≤ 1) :
    i ∈ nearOriginIndices A ε n ↔ A n ≤ (i : ℝ) ∧ (i : ℝ) ≤ ε * n := by
  classical
  simp only [nearOriginIndices, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    have : (i : ℝ) ≤ n := h.2.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact Nat.lt_succ_of_le (by exact_mod_cast this)

theorem nearOriginMaximum_nonneg (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c ε : ℝ) (n : ℕ) : 0 ≤ nearOriginMaximum x A c ε n := NNReal.coe_nonneg _

/-- On a nonempty interval the default-zero maximum is the ordinary finite
maximum of the real absolute errors. -/
theorem nearOriginMaximum_eq_sup' (x : ℕ → SignSequence) (A : ℕ → ℝ)
    (c ε : ℝ) (n : ℕ) (hne : (nearOriginIndices A ε n).Nonempty) :
    nearOriginMaximum x A c ε n = (nearOriginIndices A ε n).sup' hne
      (fun i => |(activeCount (x n) i : ℝ) / i - c|) := by
  classical
  let s := nearOriginIndices A ε n
  let f : ℕ → ℝ := fun i => |(activeCount (x n) i : ℝ) / i - c|
  have h0 : 0 ≤ s.sup' hne f :=
    (abs_nonneg _).trans (Finset.le_sup' f hne.choose_spec)
  apply le_antisymm
  · change s.sup (fun i => (⟨f i, abs_nonneg _⟩ : ℝ≥0)) ≤ (⟨s.sup' hne f, h0⟩ : ℝ≥0)
    apply Finset.sup_le
    intro i hi
    exact Finset.le_sup' f hi
  · apply Finset.sup'_le
    intro i hi
    exact Finset.le_sup (f := fun i => (⟨f i, abs_nonneg _⟩ : ℝ≥0)) hi

theorem nearOriginMaximum_le_iff {x : ℕ → SignSequence} {A : ℕ → ℝ}
    {c ε η : ℝ} {n : ℕ} (hε : ε ≤ 1) (hη : 0 ≤ η) :
    nearOriginMaximum x A c ε n ≤ η ↔
      ∀ i : ℕ, A n ≤ (i : ℝ) → (i : ℝ) ≤ ε * n →
        |(activeCount (x n) i : ℝ) / i - c| ≤ η := by
  classical
  change (nearOriginIndices A ε n).sup
    (fun i => (⟨|(activeCount (x n) i : ℝ) / i - c|, abs_nonneg _⟩ : ℝ≥0)) ≤
      (⟨η, hη⟩ : ℝ≥0) ↔ _
  rw [Finset.sup_le_iff]
  change (∀ i ∈ nearOriginIndices A ε n,
    |(activeCount (x n) i : ℝ) / i - c| ≤ η) ↔ _
  simp only [mem_nearOriginIndices hε]
  aesop

theorem activeCount_ratio_bounds {x : SignSequence} {n i : ℕ}
    (hs : PositiveThrough x n) (hi : 1 ≤ i) (hin : i ≤ n) :
    0 ≤ (activeCount x i : ℝ) / i ∧ (activeCount x i : ℝ) / i ≤ 2 := by
  have hip : (0 : ℝ) < i := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hi)
  have hlow : (0 : ℝ) ≤ activeCount x i := by exact_mod_cast (hs i hin).le
  have hu : activeCount x i ≤ (i : ℤ) + 1 :=
    (activeCount_le_plusCount_add_one x i).trans (by exact_mod_cast Nat.add_le_add_right (plusCount_le x i) 1)
  have hur : (activeCount x i : ℝ) ≤ (i : ℝ) + 1 := by exact_mod_cast hu
  constructor
  · exact div_nonneg hlow hip.le
  · apply (div_le_iff₀ hip).mpr
    have : (1 : ℝ) ≤ i := by exact_mod_cast hi
    linarith

theorem nearOriginMaximum_le_two (x : ℕ → SignSequence) (A : ℕ → ℝ) {c ε : ℝ}
    (hA : ∀ n, 0 < A n) (hc : 0 ≤ c) (hc1 : c ≤ 1) (hε : ε ≤ 1)
    (hs : ∀ n, PositiveThrough (x n) n) (n : ℕ) :
    nearOriginMaximum x A c ε n ≤ 2 := by
  apply (nearOriginMaximum_le_iff hε (by norm_num)).mpr
  intro i hAi hiε
  have hip : 0 < i := by exact_mod_cast lt_of_lt_of_le (hA n) hAi
  have hin : i ≤ n := by
    have : (i : ℝ) ≤ n := hiε.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact_mod_cast this
  obtain ⟨hl, hu⟩ := activeCount_ratio_bounds (hs n) hip hin
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem nearOriginLimsup_iff (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hA : ∀ n, 0 < A n) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hs : ∀ n, PositiveThrough (x n) n) :
    NearOriginLimsup x A c ↔ NearOriginLinear x A c := by
  have hb (ε : ℝ) (hε : ε ≤ 1) :
      IsBoundedUnder (· ≤ ·) atTop (nearOriginMaximum x A c ε) :=
    isBoundedUnder_of ⟨2, nearOriginMaximum_le_two x A hA hc hc1 hε hs⟩
  have hcb (ε : ℝ) : IsCoboundedUnder (· ≤ ·) atTop (nearOriginMaximum x A c ε) :=
    isCoboundedUnder_le_of_le atTop (nearOriginMaximum_nonneg x A c ε)
  have hnonneg (ε : ℝ) (hε : ε ≤ 1) :
      0 ≤ limsup (nearOriginMaximum x A c ε) atTop := by
    apply le_limsup_of_le (hb ε hε)
    intro b hbound
    obtain ⟨n, hn⟩ := hbound.exists
    exact (nearOriginMaximum_nonneg x A c ε n).trans hn
  constructor
  · intro h η hη
    have he := (h.eventually (gt_mem_nhds hη)).and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨ε, hlim, hε0, hε1⟩ := he.exists
    refine ⟨ε, hε0, hε1, ?_⟩
    filter_upwards [eventually_lt_of_limsup_lt hlim (hb ε hε1.le)] with n hn
    exact (nearOriginMaximum_le_iff hε1.le hη.le).mp hn.le
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨ε, hε0, hε1, hbound⟩ := h (η / 2) (half_pos hη)
    filter_upwards [Ioo_mem_nhdsGT hε0] with δ hδ
    have hδ1 : δ ≤ 1 := hδ.2.le.trans hε1.le
    have hlim : limsup (nearOriginMaximum x A c δ) atTop ≤ η / 2 := by
      apply limsup_le_of_le (hcb δ)
      filter_upwards [hbound] with n hn
      apply (nearOriginMaximum_le_iff hδ1 (half_pos hη).le).mpr
      intro i hAi hiδ
      exact hn i hAi (hiδ.trans (mul_le_mul_of_nonneg_right hδ.2.le (Nat.cast_nonneg n)))
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hnonneg δ hδ1)]
    linarith

theorem mem_bulkIndices {ε : ℝ} {n i : ℕ} (hε : ε ≤ 1) :
    i ∈ bulkIndices ε n ↔ ε * n ≤ (i : ℝ) ∧ i ≤ n := by
  classical
  simp only [bulkIndices, Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro (rfl | ⟨hi, hεi⟩)
    · exact ⟨by nlinarith [Nat.cast_nonneg (α := ℝ) i], le_rfl⟩
    · exact ⟨hεi, Nat.le_of_lt_succ hi⟩
  · rintro ⟨hεi, hi⟩
    exact Or.inr ⟨Nat.lt_succ_of_le hi, hεi⟩

theorem le_bulkMinimum_iff {x : ℕ → SignSequence} {ε δ : ℝ} {n : ℕ}
    (hε : ε ≤ 1) :
    δ ≤ bulkMinimum x ε n ↔ ∀ i : ℕ, ε * n ≤ (i : ℝ) → i ≤ n →
      δ ≤ (activeCount (x n) i : ℝ) / n := by
  classical
  simp only [bulkMinimum, Finset.le_inf'_iff, mem_bulkIndices hε]
  aesop

theorem bulkMinimum_nonneg (x : ℕ → SignSequence) {ε : ℝ} (hε : ε ≤ 1)
    (hs : ∀ n, PositiveThrough (x n) n) (n : ℕ) : 0 ≤ bulkMinimum x ε n := by
  apply (le_bulkMinimum_iff hε).mpr
  intro i _ hin
  exact div_nonneg (by exact_mod_cast (hs n i hin).le) (Nat.cast_nonneg n)

theorem bulkMinimum_le_two (x : ℕ → SignSequence) (ε : ℝ) (n : ℕ) :
    bulkMinimum x ε n ≤ 2 := by
  have hi : bulkMinimum x ε n ≤ (activeCount (x n) n : ℝ) / n :=
    Finset.inf'_le _ (Finset.mem_insert_self _ _)
  apply hi.trans
  cases n with
  | zero => simp
  | succ n =>
    have hu : activeCount (x (n + 1)) (n + 1) ≤ ((n + 1 : ℕ) : ℤ) + 1 :=
      (activeCount_le_plusCount_add_one _ _).trans
        (by exact_mod_cast Nat.add_le_add_right (plusCount_le (x (n + 1)) (n + 1)) 1)
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    have hur : (activeCount (x (n + 1)) (n + 1) : ℝ) ≤ (n + 1 : ℕ) + 1 := by exact_mod_cast hu
    push_cast at hur ⊢
    linarith [Nat.cast_nonneg (α := ℝ) n]

theorem bulkLiminf_iff (x : ℕ → SignSequence)
    (hs : ∀ n, PositiveThrough (x n) n) : BulkLiminf x ↔ BulkLowerBound x := by
  constructor
  · intro h ε hε0 hε1
    have hp := h ε hε0 hε1
    refine ⟨liminf (bulkMinimum x ε) atTop / 2, half_pos hp, ?_⟩
    have hbelow : IsBoundedUnder (· ≥ ·) atTop (bulkMinimum x ε) :=
      isBoundedUnder_of ⟨0, bulkMinimum_nonneg x hε1.le hs⟩
    filter_upwards [eventually_lt_of_lt_liminf (u := bulkMinimum x ε) (show liminf (bulkMinimum x ε) atTop / 2 <
      liminf (bulkMinimum x ε) atTop by linarith) hbelow] with n hn
    exact (le_bulkMinimum_iff hε1.le).mp hn.le
  · intro h ε hε0 hε1
    obtain ⟨δ, hδ, he⟩ := h ε hε0 hε1
    apply hδ.trans_le
    apply le_liminf_of_le (isCoboundedUnder_ge_of_le atTop (bulkMinimum_le_two x ε))
    filter_upwards [he] with n hn
    exact (le_bulkMinimum_iff hε1.le).mpr hn

/-- The paper's sublogarithmic cutoff is in particular sublinear. -/
theorem cutoff_div_nat_tendsto_zero (A : ℕ → ℝ)
    (hA : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => A n / n) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / n) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    funext n
    simp
  have hm := hA.mul hlog
  simp only [mul_zero] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hlognz : Real.log (n : ℝ) ≠ 0 := (Real.log_pos hn1).ne'
  field_simp

/-- The maximum in the source is eventually over a nonempty interval, so its
empty-set convention has no effect on either asymptotic hypothesis. -/
theorem eventually_nearOriginIndices_nonempty (A : ℕ → ℝ)
    (hApos : ∀ n, 0 < A n)
    (hA : Tendsto (fun n : ℕ => A n / Real.log (n : ℝ)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∀ᶠ n in atTop, (nearOriginIndices A ε n).Nonempty := by
  have hratio : Tendsto (fun n : ℕ => (A n + 1) / n) atTop (𝓝 0) := by
    simpa only [add_div, add_zero] using
      (cutoff_div_nat_tendsto_zero A hA).add (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  filter_upwards [hratio.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
  refine ⟨Nat.ceil (A n), (mem_nearOriginIndices hε1).mpr ⟨Nat.le_ceil _, ?_⟩⟩
  have hnp : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hAn : A n + 1 < ε * n := (div_lt_iff₀ hnp).mp hn
  exact (Nat.ceil_lt_add_one (hApos n).le).le.trans hAn.le

end Freezing1
