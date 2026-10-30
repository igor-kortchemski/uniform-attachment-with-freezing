module

public import Freezing1.GeometricHeightBlocks

/-!
# Finite geometric height-block bounds with integer rounding

These estimates use actual attachment counts and reciprocal populations.
The complete-block constants are the printed `U` and `L`. The last
partial block retains the additional integer endpoint error `1 / A`.
-/

@[expose] public section

namespace Freezing1.GeometricHeight

open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def upperBlock (c β η A : ℝ) : ℝ :=
  (((c + 1) / 2) * (β - 1 + 1 / A) + β * η) / (c - η)

noncomputable def lowerBlock (c β η A : ℝ) : ℝ :=
  (((c + 1) / 2) * (1 - 1 / β - 2 / (β * A)) - η) / (c + η)

theorem intervalPlusCount_bounds_le {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hη : 0 ≤ η)
    (haerr : |(activeCount x a : ℝ) / a - c| ≤ η)
    (hberr : |(activeCount x b : ℝ) / b - c| ≤ η) :
    (c + 1) / 2 * ((b : ℝ) - a) - b * η ≤ intervalPlusCount x a b ∧
    (intervalPlusCount x a b : ℝ) ≤ (c + 1) / 2 * ((b : ℝ) - a) + b * η := by
  rcases hab.eq_or_lt with h | h
  · subst b
    simp [intervalPlusCount, mul_nonneg (Nat.cast_nonneg a) hη]
  · exact intervalPlusCount_bounds ha h hη haerr hberr

theorem indicator_sum (x : SignSequence) (a b : ℕ) :
    (∑ i ∈ Finset.Ioc a b, if x i then (1 : ℝ) else 0) = intervalPlusCount x a b := by
  simp [intervalPlusCount, Finset.sum_boole]

theorem heightInterval_upper_of_lower {x : SignSequence} {a b : ℕ} {d : ℝ}
    (hd : 0 < d) (hS : ∀ i ∈ Finset.Ioc a b, d ≤ (activeCount x i : ℝ)) :
    heightInterval x a b ≤ (intervalPlusCount x a b : ℝ) / d := by
  rw [heightInterval_eq_intervalSum]
  calc
    _ ≤ ∑ i ∈ Finset.Ioc a b, (1 / d) * (if x i then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      cases x i
      · simp
      · simp only [↓reduceIte, mul_one]
        exact one_div_le_one_div_of_le hd (hS i hi)
    _ = _ := by rw [← Finset.mul_sum, indicator_sum]; ring

theorem heightInterval_lower_of_upper {x : SignSequence} {a b : ℕ} {D : ℝ}
    (_hD : 0 < D)
    (hS : ∀ i ∈ Finset.Ioc a b, 0 < (activeCount x i : ℝ) ∧ (activeCount x i : ℝ) ≤ D) :
    (intervalPlusCount x a b : ℝ) / D ≤ heightInterval x a b := by
  rw [heightInterval_eq_intervalSum]
  calc
    _ = ∑ i ∈ Finset.Ioc a b, (1 / D) * (if x i then (1 : ℝ) else 0) := by
      rw [← Finset.mul_sum, indicator_sum]; ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      cases x i
      · simp
      · simp only [↓reduceIte, mul_one]
        exact one_div_le_one_div_of_le (hS i hi).1 (hS i hi).2

theorem population_ratio_bounds {x : SignSequence} {i : ℕ} {c η : ℝ}
    (hi : 1 ≤ i) (_hη : 0 ≤ η) (hηc : η < c)
    (herr : |(activeCount x i : ℝ) / i - c| ≤ η) :
    0 < (activeCount x i : ℝ) ∧
    (c - η) * i ≤ (activeCount x i : ℝ) ∧
    (activeCount x i : ℝ) ≤ (c + η) * i := by
  have hi0 : (0 : ℝ) < i := by exact_mod_cast (show 0 < i by omega)
  obtain ⟨hl, hu⟩ := abs_le.mp herr
  have hlow := (le_div_iff₀ hi0).mp (show c - η ≤ (activeCount x i : ℝ) / i by linarith)
  have hupp := (div_le_iff₀ hi0).mp (show (activeCount x i : ℝ) / i ≤ c + η by linarith)
  exact ⟨(mul_pos (sub_pos.mpr hηc) hi0).trans_le hlow, hlow, hupp⟩

theorem real_cut_count_bounds {x : SignSequence} {t u c η : ℝ}
    (ht : 1 ≤ t) (htu : t ≤ u) (hc : 0 < c) (hη : 0 ≤ η)
    (herr : ∀ i ∈ Finset.Icc (Nat.floor t) (Nat.floor u),
      |(activeCount x i : ℝ) / i - c| ≤ η) :
    (c + 1) / 2 * (u - t - 2) - u * η ≤
        intervalPlusCount x (Nat.floor t) (Nat.floor u) ∧
    (intervalPlusCount x (Nat.floor t) (Nat.floor u) : ℝ) ≤
      (c + 1) / 2 * (u - t + 1) + u * η := by
  have ht0 : 0 ≤ t := by linarith
  have hu0 := ht0.trans htu
  have hf := Nat.floor_mono htu
  have ha : 1 ≤ Nat.floor t := (Nat.le_floor_iff ht0).mpr (by simpa using ht)
  obtain ⟨hl, hh⟩ := intervalPlusCount_bounds_le ha hf hη
    (herr _ (Finset.left_mem_Icc.mpr hf)) (herr _ (Finset.right_mem_Icc.mpr hf))
  have htf := Nat.floor_le ht0
  have huf := Nat.floor_le hu0
  have htf' := Nat.lt_floor_add_one t
  have huf' := Nat.lt_floor_add_one u
  have hηfloor : (Nat.floor u : ℝ) * η ≤ u * η := mul_le_mul_of_nonneg_right huf hη
  constructor <;> nlinarith

theorem real_cut_height_bounds {x : SignSequence} {t u c η : ℝ}
    (ht : 1 ≤ t) (htu : t ≤ u) (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc (Nat.floor t) (Nat.floor u),
      |(activeCount x i : ℝ) / i - c| ≤ η) :
    (intervalPlusCount x (Nat.floor t) (Nat.floor u) : ℝ) / (u * (c + η)) ≤
        heightInterval x (Nat.floor t) (Nat.floor u) ∧
    heightInterval x (Nat.floor t) (Nat.floor u) ≤
      (intervalPlusCount x (Nat.floor t) (Nat.floor u) : ℝ) / (t * (c - η)) := by
  have ht0 : 0 < t := by linarith
  have hu0 := ht0.trans_le htu
  have hcη : 0 < c + η := by linarith
  have hh (i : ℕ) (hi : i ∈ Finset.Ioc (Nat.floor t) (Nat.floor u)) :
      0 < (activeCount x i : ℝ) ∧
      t * (c - η) ≤ (activeCount x i : ℝ) ∧
      (activeCount x i : ℝ) ≤ u * (c + η) := by
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ioc.mp hi
    have hti : t < (i : ℝ) := (Nat.floor_lt ht0.le).mp hi1
    have hiu : (i : ℝ) ≤ u := (by exact_mod_cast hi2 : (i : ℝ) ≤ Nat.floor u).trans
      (Nat.floor_le hu0.le)
    have hip := population_ratio_bounds (by exact_mod_cast (by linarith : (1 : ℝ) ≤ i))
      hη hηc (herr i (Finset.mem_Icc.mpr ⟨hi1.le, hi2⟩))
    exact ⟨hip.1, by nlinarith [hip.2.1], by nlinarith [hip.2.2]⟩
  exact ⟨heightInterval_lower_of_upper (mul_pos hu0 hcη) (fun i hi => ⟨(hh i hi).1, (hh i hi).2.2⟩),
    heightInterval_upper_of_lower (mul_pos ht0 (sub_pos.mpr hηc)) (fun i hi => (hh i hi).2.1)⟩

theorem complete_block_bounds {x : SignSequence} {β t A c η : ℝ}
    (hβ : 1 < β) (hA : 1 ≤ A) (hAt : A ≤ t) (hc : 0 < c)
    (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc (Nat.floor t) (Nat.floor (β * t)),
      |(activeCount x i : ℝ) / i - c| ≤ η) :
    lowerBlock c β η A ≤ heightInterval x (Nat.floor t) (Nat.floor (β * t)) ∧
    heightInterval x (Nat.floor t) (Nat.floor (β * t)) ≤ upperBlock c β η A := by
  have ht1 := hA.trans hAt
  have ht0 : 0 < t := by linarith
  have hA0 : 0 < A := by linarith
  have hβ0 : 0 < β := by linarith
  have htu : t ≤ β * t := by nlinarith
  obtain ⟨hcl, hcu⟩ := real_cut_count_bounds ht1 htu hc hη herr
  obtain ⟨hhl, hhu⟩ := real_cut_height_bounds ht1 htu hη hηc herr
  have hta : 1 ≤ t / A := (le_div_iff₀ hA0).mpr (by simpa using hAt)
  have hde : 0 < β * t * (c + η) := by positivity
  have hdu : 0 < t * (c - η) := mul_pos ht0 (sub_pos.mpr hηc)
  have hL : lowerBlock c β η A * (β * t * (c + η)) =
      (c + 1) / 2 * ((β - 1) * t - 2 * (t / A)) - β * t * η := by
    dsimp only [lowerBlock]
    field_simp
  have hU : upperBlock c β η A * (t * (c - η)) =
      (c + 1) / 2 * ((β - 1) * t + t / A) + β * t * η := by
    dsimp only [upperBlock]
    field_simp
  constructor
  · apply le_trans _ hhl
    apply (le_div_iff₀ hde).mpr
    rw [hL]
    nlinarith
  · apply hhu.trans
    apply (div_le_iff₀ hdu).mpr
    rw [hU]
    nlinarith

theorem interval_count_le_length (x : SignSequence) {a b : ℕ} (hab : a ≤ b) :
    (intervalPlusCount x a b : ℝ) ≤ (b : ℝ) - a := by
  have h : intervalPlusCount x a b ≤ b - a := by
    simpa only [intervalPlusCount, Nat.card_Ioc] using
      Finset.card_filter_le (s := Finset.Ioc a b) (p := fun i => x i = true)
  exact_mod_cast (show (intervalPlusCount x a b : ℝ) ≤ ((b - a : ℕ) : ℝ) by exact_mod_cast h)

theorem initial_partial_bound {x : SignSequence} {a q : ℕ} {β c η : ℝ}
    (ha : 1 ≤ a) (haq : a ≤ q) (hq : (q : ℝ) ≤ β * a)
    (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc a q, |(activeCount x i : ℝ) / i - c| ≤ η) :
    heightInterval x a q ≤ (β - 1) / (c - η) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hd := sub_pos.mpr hηc
  have hS : ∀ i ∈ Finset.Ioc a q, (a : ℝ) * (c - η) ≤ (activeCount x i : ℝ) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ioc.mp hi
    have hp := population_ratio_bounds (by omega : 1 ≤ i) hη hηc
      (herr i (Finset.mem_Icc.mpr ⟨hi1.le, hi2⟩))
    have hai : (a : ℝ) ≤ i := by exact_mod_cast hi1.le
    nlinarith [hp.2.1]
  apply (heightInterval_upper_of_lower (mul_pos ha0 hd) hS).trans
  apply (div_le_iff₀ (mul_pos ha0 hd)).mpr
  have heq : (β - 1) / (c - η) * ((a : ℝ) * (c - η)) = (β - 1) * a := by
    field_simp
  rw [heq]
  have := interval_count_le_length x haq
  nlinarith

theorem final_partial_bound {x : SignSequence} {b : ℕ} {β t A c η : ℝ}
    (hA : 1 ≤ A) (hAt : A ≤ t) (htb : t ≤ (b : ℝ)) (hb : (b : ℝ) ≤ β * t)
    (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc (Nat.floor t) b,
      |(activeCount x i : ℝ) / i - c| ≤ η) :
    heightInterval x (Nat.floor t) b ≤ (β - 1 + 1 / A) / (c - η) := by
  have ht1 := hA.trans hAt
  have ht0 : 0 < t := by linarith
  have hA0 : 0 < A := by linarith
  have hd := sub_pos.mpr hηc
  have hf : Nat.floor t ≤ b := Nat.floor_le_of_le htb
  have hS : ∀ i ∈ Finset.Ioc (Nat.floor t) b,
      t * (c - η) ≤ (activeCount x i : ℝ) := by
    intro i hi
    obtain ⟨hi1, hi2⟩ := Finset.mem_Ioc.mp hi
    have hti := (Nat.floor_lt ht0.le).mp hi1
    have hiNat : 1 ≤ i := by exact_mod_cast (show (1 : ℝ) ≤ i by linarith)
    have hp := population_ratio_bounds hiNat hη hηc
      (herr i (Finset.mem_Icc.mpr ⟨hi1.le, hi2⟩))
    nlinarith [hp.2.1]
  apply (heightInterval_upper_of_lower (mul_pos ht0 hd) hS).trans
  apply (div_le_iff₀ (mul_pos ht0 hd)).mpr
  have heq : (β - 1 + 1 / A) / (c - η) * (t * (c - η)) =
      (β - 1) * t + t / A := by
    field_simp
  rw [heq]
  have hcount := interval_count_le_length x hf
  have hround := Nat.lt_floor_add_one t
  have hta : 1 ≤ t / A := (le_div_iff₀ hA0).mpr (by simpa using hAt)
  nlinarith

theorem heightInterval_nonneg_of_ratio {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (ha : 1 ≤ a) (hη : 0 ≤ η) (hηc : η < c)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    0 ≤ heightInterval x a b := by
  rw [heightInterval_eq_intervalSum]
  apply Finset.sum_nonneg
  intro i hi
  obtain ⟨hi1, hi2⟩ := Finset.mem_Ioc.mp hi
  have hp := population_ratio_bounds (by omega : 1 ≤ i) hη hηc
    (herr i (Finset.mem_Icc.mpr ⟨hi1.le, hi2⟩))
  split_ifs
  · exact (one_div_pos.mpr hp.1).le
  · exact le_rfl

theorem upperBlock_nonneg {β A c η : ℝ} (hβ : 1 < β) (hA : 0 < A)
    (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c) : 0 ≤ upperBlock c β η A := by
  dsimp only [upperBlock]
  have hb := sub_pos.mpr hβ
  have hnum : 0 ≤ (c + 1) / 2 * (β - 1 + 1 / A) + β * η :=
    add_nonneg (mul_nonneg (by positivity)
      (add_nonneg hb.le (one_div_pos.mpr hA).le)) (mul_nonneg (by linarith) hη)
  exact div_nonneg hnum (sub_pos.mpr hηc).le

theorem heightInterval_geometric_unnormalized {x : SignSequence} {a b : ℕ}
    {β C A c η : ℝ} (hβ : 1 < β) (hβC : β < C) (hA : 1 ≤ A) (hAa : A ≤ a)
    (haC : (a : ℝ) * C < b) (hc : 0 < c) (hη : 0 ≤ η) (hηc : η < c)
    (hL : 0 ≤ lowerBlock c β η A)
    (herr : ∀ i ∈ Finset.Icc a b, |(activeCount x i : ℝ) / i - c| ≤ η) :
    (Real.log ((b : ℝ) / a) / Real.log β - 2) * lowerBlock c β η A ≤
        heightInterval x a b ∧
    heightInterval x a b ≤ (Real.log ((b : ℝ) / a) / Real.log β) * upperBlock c β η A +
      (2 * (β - 1) + 1 / A) / (c - η) := by
  have ha : 1 ≤ a := by exact_mod_cast (hA.trans hAa)
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  obtain ⟨hal, hlm, hmb⟩ := cut_endpoints hβ hβC ha haC
  let l := firstIndex β a
  let m := lastIndex β b
  have hlm' : l ≤ m := first_le_last hβ hβC ha haC
  have hβ0 : 0 < β := by linarith
  have hb : 1 ≤ b := by
    have : (0 : ℝ) < b := (mul_pos ha0 (by linarith : 0 < C)).trans haC
    exact Nat.succ_le_of_lt (by exact_mod_cast this)
  have hpart : heightInterval x a b = heightInterval x a (cut β l) +
      (∑ k ∈ Finset.Ico l m, heightInterval x (cut β k) (cut β (k + 1))) +
      heightInterval x (cut β m) b := by
    simpa only [← heightInterval_eq_intervalSum] using intervalSum_partition
      (fun i => if x i then 1 / (activeCount x i : ℝ) else 0) hβ hβC ha haC
  have hfirst := initial_partial_bound ha hal
    ((Nat.floor_le (pow_pos hβ0 _).le).trans (first_pow_bounds hβ ha).2.le)
    hη hηc (fun i hi => herr i (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (hlm.trans hmb)⟩))
  have hAtm : A ≤ β ^ m := hAa.trans ((first_pow_bounds hβ ha).1.trans
    (pow_le_pow_right₀ hβ.le hlm'))
  have hlast := final_partial_bound (β := β) hA hAtm (last_pow_bounds hβ hb).1
    (by simpa only [pow_succ, m, mul_comm] using (last_pow_bounds hβ hb).2.le) hη hηc
    (fun i hi => herr i (Finset.mem_Icc.mpr
      ⟨hal.trans (hlm.trans (Finset.mem_Icc.mp hi).1), (Finset.mem_Icc.mp hi).2⟩))
  change heightInterval x (cut β m) b ≤ (β - 1 + 1 / A) / (c - η) at hlast
  have hblock (k : ℕ) (hk : k ∈ Finset.Ico l m) :
      lowerBlock c β η A ≤ heightInterval x (cut β k) (cut β (k + 1)) ∧
      heightInterval x (cut β k) (cut β (k + 1)) ≤ upperBlock c β η A := by
    obtain ⟨hlk, hkm⟩ := Finset.mem_Ico.mp hk
    have hat : A ≤ β ^ k := hAa.trans ((first_pow_bounds hβ ha).1.trans
      (pow_le_pow_right₀ hβ.le hlk))
    have hp : Nat.floor (β * β ^ k) = cut β (k + 1) := by
      simp only [cut, pow_succ, mul_comm]
    have hek : ∀ i ∈ Finset.Icc (Nat.floor (β ^ k)) (Nat.floor (β * β ^ k)),
        |(activeCount x i : ℝ) / i - c| ≤ η := by
      intro i hi
      rw [hp] at hi
      exact herr i (Finset.mem_Icc.mpr
        ⟨hal.trans ((cut_mono hβ.le hlk).trans (Finset.mem_Icc.mp hi).1),
          (Finset.mem_Icc.mp hi).2.trans ((cut_mono hβ.le (by omega)).trans hmb)⟩)
    simpa only [cut, pow_succ, mul_comm] using complete_block_bounds hβ hA hat hc hη hηc hek
  have hslo := Finset.sum_le_sum (fun k hk => (hblock k hk).1)
  have hshi := Finset.sum_le_sum (fun k hk => (hblock k hk).2)
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hslo hshi
  obtain ⟨hcountU, hcountL⟩ := index_count_bounds hβ hβC ha haC
  have hlowcount := mul_le_mul_of_nonneg_right hcountL hL
  have huppcount := mul_le_mul_of_nonneg_right hcountU
    (upperBlock_nonneg hβ (by linarith : 0 < A) hc hη hηc)
  have hfirst0 := heightInterval_nonneg_of_ratio ha hη hηc
    (fun i hi => herr i (Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hi).1, (Finset.mem_Icc.mp hi).2.trans (hlm.trans hmb)⟩))
  have hm1 : 1 ≤ cut β m := ha.trans (hal.trans hlm)
  have hlast0 := heightInterval_nonneg_of_ratio hm1 hη hηc
    (fun i hi => herr i (Finset.mem_Icc.mpr
      ⟨hal.trans (hlm.trans (Finset.mem_Icc.mp hi).1), (Finset.mem_Icc.mp hi).2⟩))
  dsimp only [l, m] at hpart hlast hslo hshi hlast0
  constructor
  · rw [hpart]
    linarith
  · rw [hpart]
    have hp : (β - 1) / (c - η) + (β - 1 + 1 / A) / (c - η) =
        (2 * (β - 1) + 1 / A) / (c - η) := by ring
    linarith

end Freezing1.GeometricHeight
