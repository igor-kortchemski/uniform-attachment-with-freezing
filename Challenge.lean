module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Finset.Sum
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Bernoulli concentration and supporting results: statement reference

This comparison interface covers Proposition `prop:bennett` (both tails), the
deterministic height-scale lower bound, uniform birth-label law, count
identities, and analytic characterization of the linear-regime height factor
from `attachement-uniforme-1-final.tex`. It also includes the explicitly labelled
numerical check of an erroneous bound in the source. It does not claim the
Introduction's probability limit theorems or full-paper coverage.

The statements and their mathematical definitions have been independently
reviewed against the source. The complete proofs below are reproduced from the
development to respect the project's prohibition of proof holes. They are not
an independent proof implementation. This file imports only Mathlib and is
never imported by the Solution or the proof library.

The exact selected exports are listed in `comparator.json`. Unlisted helper
results support these exports; passing comparison does not certify claims
outside this explicitly limited scope. The deterministic label law does not
supply the unconstructed random forest, and the numerical source check does
not itself encode a tree-law counterexample.
-/

@[expose] public section

/-! ## Path -/

namespace Freezing1

/-- An attachment/freezing schedule; index zero is unused. -/
abbrev SignSequence := ℕ → Bool

/-- Number of attachment steps among steps `1, …, n`. -/
def plusCount (x : SignSequence) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 else 0

/-- Number of freezing steps among steps `1, …, n`. -/
def minusCount (x : SignSequence) (n : ℕ) : ℕ := n - plusCount x n

/-- The integer walk `S_n = 1 + ∑_{i=1}^n x_i` from the Introduction. -/
def activeCount (x : SignSequence) (n : ℕ) : ℤ :=
  1 + ∑ i ∈ Finset.range n, if x (i + 1) then 1 else -1

/-- Positivity of the walk up to and including time `n`, i.e. `τ > n`. -/
def PositiveThrough (x : SignSequence) (n : ℕ) : Prop :=
  ∀ k ≤ n, 0 < activeCount x k

@[simp] theorem plusCount_zero (x : SignSequence) : plusCount x 0 = 0 := by
  simp [plusCount]

@[simp] theorem plusCount_succ (x : SignSequence) (n : ℕ) :
    plusCount x (n + 1) = plusCount x n + if x (n + 1) then 1 else 0 := by
  simp only [plusCount, Finset.sum_range_succ]

@[simp] theorem activeCount_zero (x : SignSequence) : activeCount x 0 = 1 := by
  simp [activeCount]

theorem activeCount_succ (x : SignSequence) (n : ℕ) :
    activeCount x (n + 1) = activeCount x n + if x (n + 1) then 1 else -1 := by
  simp [activeCount, Finset.sum_range_succ, add_assoc]

theorem plusCount_le (x : SignSequence) (n : ℕ) : plusCount x n ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [plusCount_succ]
    split <;> omega

/-- The counting identity used throughout the paper. -/
theorem activeCount_eq (x : SignSequence) (n : ℕ) :
    activeCount x n = 1 + 2 * (plusCount x n : ℤ) - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [activeCount_succ, plusCount_succ, ih]
    cases x (n + 1) <;> simp <;> omega

theorem plusCount_add_minusCount (x : SignSequence) (n : ℕ) :
    plusCount x n + minusCount x n = n := by
  simp [minusCount, Nat.add_sub_of_le (plusCount_le x n)]

theorem activeCount_eq_counts (x : SignSequence) (n : ℕ) :
    activeCount x n = 1 + (plusCount x n : ℤ) - minusCount x n := by
  rw [activeCount_eq, minusCount, Nat.cast_sub (plusCount_le x n)]
  ring

theorem activeCount_le_plusCount_add_one (x : SignSequence) (n : ℕ) :
    activeCount x n ≤ (plusCount x n : ℤ) + 1 := by
  rw [activeCount_eq_counts]
  omega

theorem PositiveThrough.mono {x : SignSequence} {m n : ℕ}
    (h : PositiveThrough x n) (hmn : m ≤ n) : PositiveThrough x m :=
  fun k hk => h k (hk.trans hmn)

/-- Before extinction, attachment steps comprise at least half of all steps. -/
theorem le_two_mul_plusCount {x : SignSequence} {n : ℕ}
    (h : PositiveThrough x n) : n ≤ 2 * plusCount x n := by
  have hn := h n le_rfl
  rw [activeCount_eq] at hn
  omega

end Freezing1

/-! ## Extinction -/

namespace Freezing1

/-- First zero of `S`, or infinity if there is none (equation `eq:defintro`). -/
noncomputable def extinctionTime (x : SignSequence) : ℕ∞ :=
  open Classical in
  if h : ∃ k, activeCount x k = 0 then (Nat.find h : ℕ∞) else ⊤

/-- A nearest-neighbour walk starting at one stays positive until its first zero. -/
theorem positiveThrough_iff_no_zero (x : SignSequence) (n : ℕ) :
    PositiveThrough x n ↔ ∀ k ≤ n, activeCount x k ≠ 0 := by
  constructor
  · intro h k hk
    exact (h k hk).ne'
  · intro h
    induction n with
    | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
    | succ n ih =>
      have hn : PositiveThrough x n := ih (fun k hk => h k (by omega))
      intro k hk
      by_cases hkn : k ≤ n
      · exact hn k hkn
      · have hks : k = n + 1 := by omega
        subst k
        have hprev := hn n le_rfl
        have hnext := h (n + 1) le_rfl
        rw [activeCount_succ] at hnext ⊢
        cases hx : x (n + 1)
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hnext ⊢
          omega
        · simp only [↓reduceIte]
          omega

theorem extinctionTime_le_iff (x : SignSequence) (n : ℕ) :
    extinctionTime x ≤ n ↔ ∃ k ≤ n, activeCount x k = 0 := by
  classical
  unfold extinctionTime
  split_ifs with h
  · simp only [ENat.natCast_le_natCast]
    constructor
    · intro hn
      exact ⟨Nat.find h, hn, Nat.find_spec h⟩
    · rintro ⟨k, hkn, hk⟩
      exact (Nat.find_min' h hk).trans hkn
  · simp only [top_le_iff, ENat.natCast_ne_top, false_iff]
    rintro ⟨k, hk, hz⟩
    exact h ⟨k, hz⟩

/-- Exact bridge between the paper's `τ > n` and `PositiveThrough`. -/
theorem lt_extinctionTime_iff (x : SignSequence) (n : ℕ) :
    (n : ℕ∞) < extinctionTime x ↔ PositiveThrough x n := by
  rw [← not_le, extinctionTime_le_iff, positiveThrough_iff_no_zero]
  push Not
  rfl

theorem extinctionTime_eq_top_iff (x : SignSequence) :
    extinctionTime x = ⊤ ↔ ∀ n, 0 < activeCount x n := by
  constructor
  · intro h n
    have hn : (n : ℕ∞) < extinctionTime x := by simp [h]
    exact ((lt_extinctionTime_iff x n).mp hn) n le_rfl
  · intro h
    unfold extinctionTime
    split_ifs with hz
    · obtain ⟨n, hn⟩ := hz
      exact False.elim ((h n).ne' hn)
    · rfl

/-- The walk is nonnegative through the extinction endpoint. -/
theorem activeCount_nonneg_of_le_extinctionTime {x : SignSequence} {n : ℕ}
    (hn : (n : ℕ∞) ≤ extinctionTime x) : 0 ≤ activeCount x n := by
  cases n with
  | zero => simp
  | succ n =>
    have hlt : (n : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hn
    have hpos := ((lt_extinctionTime_iff x n).mp hlt) n le_rfl
    rw [activeCount_succ]
    cases x (n + 1) <;> simp_all <;> omega

end Freezing1

/-! ## HeightScale -/

namespace Freezing1

/-- The deterministic height scale `h_n^+` from the Introduction. -/
noncomputable def heightScale (x : SignSequence) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, if x (i + 1) then 1 / (activeCount x (i + 1) : ℝ) else 0

/-- The shifted harmonic sum `1/2 + 1/3 + … + 1/(n+1)`. -/
noncomputable def shiftedHarmonic (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2)

@[simp] theorem heightScale_zero (x : SignSequence) : heightScale x 0 = 0 := by
  simp [heightScale]

theorem heightScale_succ (x : SignSequence) (n : ℕ) :
    heightScale x (n + 1) = heightScale x n +
      if x (n + 1) then 1 / (activeCount x (n + 1) : ℝ) else 0 := by
  simp [heightScale, Finset.sum_range_succ]

@[simp] theorem shiftedHarmonic_zero : shiftedHarmonic 0 = 0 := by
  simp [shiftedHarmonic]

theorem shiftedHarmonic_succ (n : ℕ) :
    shiftedHarmonic (n + 1) = shiftedHarmonic n + 1 / ((n : ℝ) + 2) := by
  simp [shiftedHarmonic, Finset.sum_range_succ]

/-- The harmonic lower bound in the proof of the paper's lower-bound lemma. -/
theorem shiftedHarmonic_le_heightScale {x : SignSequence} {n : ℕ}
    (h : PositiveThrough x n) : shiftedHarmonic (plusCount x n) ≤ heightScale x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (h.mono (Nat.le_succ n))
    rw [plusCount_succ, heightScale_succ]
    cases hx : x (n + 1)
    · simpa [hx] using ih'
    · simp only [↓reduceIte, shiftedHarmonic_succ]
      apply add_le_add ih'
      have hpos : 0 < (activeCount x (n + 1) : ℝ) := by
        exact_mod_cast h (n + 1) le_rfl
      have hbound : (activeCount x (n + 1) : ℝ) ≤ (plusCount x n : ℝ) + 2 := by
        have hi := activeCount_le_plusCount_add_one x (n + 1)
        simp [hx] at hi
        exact_mod_cast hi
      exact one_div_le_one_div_of_le hpos hbound

/-- An elementary logarithmic lower bound for the shifted harmonic sum. -/
theorem log_le_shiftedHarmonic (n : ℕ) :
    Real.log (((n : ℝ) + 2) / 2) ≤ shiftedHarmonic n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : 0 < (n : ℝ) + 2 := by positivity
    have hn' : 0 < (n : ℝ) + 3 := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn' hn)
    have hr : ((n : ℝ) + 3) / ((n : ℝ) + 2) - 1 = 1 / ((n : ℝ) + 2) := by
      field_simp
      ring
    rw [hr, Real.log_div hn'.ne' hn.ne'] at hlog
    rw [shiftedHarmonic_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Real.log_div (by positivity) (by norm_num)] at ih ⊢
    have heq : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
    rw [heq]
    linarith

/-- A stronger intermediate form of the lower bound, in terms of attachments. -/
theorem log_plusCount_le_heightScale {x : SignSequence} {n : ℕ}
    (h : PositiveThrough x n) :
    Real.log (((plusCount x n : ℝ) + 2) / 2) ≤ heightScale x n :=
  (log_le_shiftedHarmonic _).trans (shiftedHarmonic_le_heightScale h)

/-- The normalization used in the height theorems is strictly positive. -/
theorem heightScale_pos {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (h : PositiveThrough x n) : 0 < heightScale x n := by
  have hc : 1 ≤ plusCount x n := by
    have := le_two_mul_plusCount h
    omega
  have hc' : (1 : ℝ) ≤ plusCount x n := by exact_mod_cast hc
  have hlog : 0 < Real.log (((plusCount x n : ℝ) + 2) / 2) := by
    apply Real.log_pos
    linarith
  exact hlog.trans_le (log_plusCount_le_heightScale h)

/-- Paper lemma `lemme minoration h_n^+`: `h_n^+ ≥ log(n/4)` before extinction. -/
theorem log_quarter_le_heightScale {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (h : PositiveThrough x n) :
    Real.log ((n : ℝ) / 4) ≤ heightScale x n := by
  have hn' : 0 < (n : ℝ) / 4 := by positivity
  have hcount : (n : ℝ) ≤ 2 * (plusCount x n : ℝ) := by
    exact_mod_cast le_two_mul_plusCount h
  apply (Real.log_le_log hn' ?_).trans (log_plusCount_le_heightScale h)
  linarith

/-- The height scale diverges for every admissible triangular array of schedules.
This is the deterministic input to the proof of Theorem `thm:height` (I). -/
theorem tendsto_heightScale_atTop (x : ℕ → SignSequence)
    (h : ∀ n, PositiveThrough (x n) n) :
    Filter.Tendsto (fun n => heightScale (x n) n) Filter.atTop Filter.atTop := by
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) / 4))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp
      (Filter.Tendsto.atTop_div_const (by norm_num) tendsto_natCast_atTop_atTop)
  apply Filter.tendsto_atTop_mono' Filter.atTop ?_ hlog
  exact (Filter.eventually_ge_atTop 1).mono fun n hn =>
    log_quarter_le_heightScale hn (h n)

end Freezing1

/-! ## RateFunction -/

namespace Freezing1

open Set

/-- The function defining the height factor, strictly increasing on `[1, ∞)`. -/
noncomputable def heightRate (x : ℝ) : ℝ := x * Real.log x - x

/-- Bennett's rate function, used only at nonnegative arguments in this development. -/
noncomputable def bennettRate (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

theorem heightRate_eq (x : ℝ) : heightRate x = x * (Real.log x - 1) := by
  unfold heightRate
  ring

theorem continuous_heightRate : Continuous heightRate :=
  Real.continuous_mul_log.sub continuous_id

theorem hasDerivAt_heightRate {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt heightRate (Real.log x) x := by
  convert (Real.hasDerivAt_mul_log hx).fun_sub (hasDerivAt_id' x) using 1
  · rfl
  · ring

theorem strictMonoOn_heightRate : StrictMonoOn heightRate (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_heightRate.continuousOn ?_
  intro x hx
  have hx1 : 1 < x := by simpa using hx
  rw [(hasDerivAt_heightRate (by linarith)).deriv]
  exact Real.log_pos hx1

@[simp] theorem heightRate_one : heightRate 1 = -1 := by simp [heightRate]

@[simp] theorem heightRate_exp_one : heightRate (Real.exp 1) = 0 := by
  simp [heightRate]

/-- Existence and uniqueness of the number specified in Theorem `thm:lineaire` (III).
The quantifier ranges over all real numbers strictly larger than one. -/
theorem linearHeightFactor_existsUnique {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    ∃! x : ℝ, 1 < x ∧ x * (Real.log x - 1) = (c - 1) / (c + 1) := by
  have hc : 0 < c + 1 := by linarith
  have htarget : (c - 1) / (c + 1) ∈ Icc (heightRate 1) (heightRate (Real.exp 1)) := by
    simp only [heightRate_one, heightRate_exp_one, mem_Icc]
    constructor
    · rw [le_div_iff₀ hc]
      linarith
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hc.le
  have he : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
  obtain ⟨x, hx, hxeq⟩ := intermediate_value_Icc he
    continuous_heightRate.continuousOn htarget
  have hx1 : 1 < x := by
    refine lt_of_le_of_ne hx.1 ?_
    intro h
    have ht : -1 < (c - 1) / (c + 1) := by
      rw [lt_div_iff₀ hc]
      linarith
    have : heightRate x = -1 := by rw [← h, heightRate_one]
    linarith
  refine ⟨x, ⟨hx1, by simpa [heightRate_eq] using hxeq⟩, ?_⟩
  intro y hy
  apply strictMonoOn_heightRate.injOn hy.1.le hx1.le
  rw [heightRate_eq, heightRate_eq, hy.2]
  simpa only [heightRate_eq] using hxeq.symm

/-- The admissible linear growth constants of Theorem `thm:lineaire`. -/
abbrev LinearRegimeParameter := Ioc (0 : ℝ) 1

/-- The height factor `f(c)`. Its domain records exactly `0 < c ≤ 1`.
The choice is justified by `linearHeightFactor_existsUnique`, and uniqueness
ensures that all later statements are independent of that choice. -/
noncomputable def linearHeightFactor (c : LinearRegimeParameter) : ℝ :=
  Classical.choose (linearHeightFactor_existsUnique c.property.1 c.property.2).exists

theorem linearHeightFactor_spec (c : LinearRegimeParameter) :
    1 < linearHeightFactor c ∧
      linearHeightFactor c * (Real.log (linearHeightFactor c) - 1) =
        ((c : ℝ) - 1) / ((c : ℝ) + 1) :=
  Classical.choose_spec (linearHeightFactor_existsUnique c.property.1 c.property.2).exists

theorem one_lt_linearHeightFactor (c : LinearRegimeParameter) : 1 < linearHeightFactor c :=
  (linearHeightFactor_spec c).1

theorem linearHeightFactor_unique (c : LinearRegimeParameter) {x : ℝ}
    (hx : 1 < x) (heq : x * (Real.log x - 1) = ((c : ℝ) - 1) / ((c : ℝ) + 1)) :
    x = linearHeightFactor c :=
  (linearHeightFactor_existsUnique c.property.1 c.property.2).unique
    ⟨hx, heq⟩ (linearHeightFactor_spec c)

theorem linearHeightFactor_le_exp_one (c : LinearRegimeParameter) :
    linearHeightFactor c ≤ Real.exp 1 := by
  by_contra h
  have hlt : Real.exp 1 < linearHeightFactor c := lt_of_not_ge h
  have he : (1 : ℝ) ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
  have hr := strictMonoOn_heightRate he (one_lt_linearHeightFactor c).le hlt
  rw [heightRate_exp_one, heightRate_eq, (linearHeightFactor_spec c).2] at hr
  have hnonpos : ((c : ℝ) - 1) / ((c : ℝ) + 1) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith [c.property.2])
      (by linarith [c.property.1])
  exact (not_lt_of_ge hnonpos) hr

/-- Increasing the limiting active fraction increases the height factor `f(c)`. -/
theorem strictMono_linearHeightFactor : StrictMono linearHeightFactor := by
  intro a b hab
  have ha : 0 < (a : ℝ) + 1 := by linarith [a.property.1]
  have hb : 0 < (b : ℝ) + 1 := by linarith [b.property.1]
  have hab' : (a : ℝ) < (b : ℝ) := hab
  have ht : ((a : ℝ) - 1) / ((a : ℝ) + 1) <
      ((b : ℝ) - 1) / ((b : ℝ) + 1) := by
    apply (div_lt_div_iff₀ ha hb).2
    nlinarith
  by_contra h
  have hle : linearHeightFactor b ≤ linearHeightFactor a := le_of_not_gt h
  have hr := strictMonoOn_heightRate.monotoneOn
    (one_lt_linearHeightFactor b).le (one_lt_linearHeightFactor a).le hle
  rw [heightRate_eq, heightRate_eq, (linearHeightFactor_spec b).2,
    (linearHeightFactor_spec a).2] at hr
  exact (not_lt_of_ge hr) ht

@[simp] theorem linearHeightFactor_one :
    linearHeightFactor ⟨1, by constructor <;> norm_num⟩ = Real.exp 1 := by
  symm
  apply linearHeightFactor_unique
  · exact Real.one_lt_exp_iff.mpr zero_lt_one
  · simp

theorem bennettRate_eq_heightRate (u : ℝ) :
    bennettRate u = heightRate (1 + u) + 1 := by
  unfold bennettRate heightRate
  ring

@[simp] theorem bennettRate_zero : bennettRate 0 = 0 := by simp [bennettRate]

theorem strictMonoOn_bennettRate : StrictMonoOn bennettRate (Ici 0) := by
  intro x hx y hy hxy
  rw [bennettRate_eq_heightRate, bennettRate_eq_heightRate]
  have h := strictMonoOn_heightRate
    (show 1 + x ∈ Ici (1 : ℝ) by simp only [mem_Ici] at *; linarith)
    (show 1 + y ∈ Ici (1 : ℝ) by simp only [mem_Ici] at *; linarith)
    (show 1 + x < 1 + y by linarith)
  linarith

theorem bennettRate_pos {u : ℝ} (hu : 0 < u) : 0 < bennettRate u := by
  simpa using strictMonoOn_bennettRate (show (0 : ℝ) ∈ Ici 0 by simp) hu.le hu

theorem bennettRate_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ bennettRate u := by
  simpa using strictMonoOn_bennettRate.monotoneOn
    (show (0 : ℝ) ∈ Ici 0 by simp) hu hu

/-- The normalization used in the upper bound of the linear-regime height theorem. -/
theorem bennettRate_linearHeightFactor (c : LinearRegimeParameter) :
    bennettRate (linearHeightFactor c - 1) = 2 * (c : ℝ) / ((c : ℝ) + 1) := by
  rw [bennettRate_eq_heightRate]
  have hs : 1 + (linearHeightFactor c - 1) = linearHeightFactor c := by ring
  rw [hs, heightRate_eq, (linearHeightFactor_spec c).2]
  have hc : (c : ℝ) + 1 ≠ 0 := by linarith [c.property.1]
  field_simp [hc]
  ring

/-- The strict rate inequality used when adding a positive margin to `f(c)`. -/
theorem bennettRate_linearHeightFactor_add {ε : ℝ} (c : LinearRegimeParameter)
    (hε : 0 < ε) :
    2 * (c : ℝ) / ((c : ℝ) + 1) < bennettRate (linearHeightFactor c - 1 + ε) := by
  rw [← bennettRate_linearHeightFactor c]
  have hf := one_lt_linearHeightFactor c
  apply strictMonoOn_bennettRate
  · simp only [mem_Ici]
    linarith
  · simp only [mem_Ici]
    linarith
  · linarith

@[simp] theorem bennettRate_exp_one_sub_one : bennettRate (Real.exp 1 - 1) = 1 := by
  rw [bennettRate_eq_heightRate]
  have hs : 1 + (Real.exp 1 - 1) = Real.exp 1 := by ring
  rw [hs, heightRate_exp_one]
  norm_num

theorem one_lt_bennettRate_exp_one_sub_one_add {ε : ℝ} (hε : 0 < ε) :
    1 < bennettRate (Real.exp 1 - 1 + ε) := by
  have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have h := strictMonoOn_bennettRate (show Real.exp 1 - 1 ∈ Ici 0 by
    simp only [mem_Ici]; linarith)
    (show Real.exp 1 - 1 + ε ∈ Ici 0 by simp only [mem_Ici]; linarith)
    (show Real.exp 1 - 1 < Real.exp 1 - 1 + ε by linarith)
  simpa using h

/-- A rate estimate used to control all real moments in the height argument. -/
theorem self_le_bennettRate {u : ℝ} (hu : Real.exp 2 - 1 ≤ u) : u ≤ bennettRate u := by
  have hpos : 0 < 1 + u := by linarith [Real.exp_pos 2]
  have hlog : 2 ≤ Real.log (1 + u) :=
    (Real.le_log_iff_exp_le hpos).mpr (by linarith)
  unfold bennettRate
  nlinarith

end Freezing1

/-! ## BirthTime -/

open MeasureTheory
open scoped ENNReal

namespace Freezing1

instance instMeasurableSingletonVertexLabel : MeasurableSingletonClass (ℕ ⊕ ℕ) where
  measurableSet_singleton v := by
    cases v with
    | inl i => simpa only [Set.image_singleton] using
        (measurableSet_singleton i).inl_image (β := ℕ)
    | inr i => simpa only [Set.image_singleton] using
        (measurableSet_singleton i).inr_image (α := ℕ)

/-- Zero-based indices of freezing steps among the first `n` steps. -/
def frozenIndices (x : SignSequence) (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun i => x (i + 1) = false

/-- The deterministic label set in equation `eq:labels`, with disjoint tags. -/
def vertexLabels (x : SignSequence) (n : ℕ) : Finset (ℕ ⊕ ℕ) :=
  (Finset.range (activeCount x n).toNat).disjSum (frozenIndices x n)

/-- Birth time in Algorithm 2: active labels are born at `n`, frozen label
`i+1` is born at `i`. Values outside `vertexLabels` are not used. -/
def birthTime (n : ℕ) : ℕ ⊕ ℕ → ℕ
  | .inl _ => n
  | .inr i => i

/-- A uniformly chosen vertex of the deterministic label set. -/
noncomputable def uniformVertex (x : SignSequence) (n : ℕ) : Measure (ℕ ⊕ ℕ) :=
  Measure.uniformOfFinset (vertexLabels x n)

theorem card_frozenIndices (x : SignSequence) (n : ℕ) :
    (frozenIndices x n).card = minusCount x n := by
  have h : (frozenIndices x n).card + plusCount x n = n := by
    rw [frozenIndices, Finset.card_eq_sum_ones, Finset.sum_filter, plusCount,
      ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i ∈ Finset.range n, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        cases x (i + 1) <;> simp
      _ = n := by simp
  unfold minusCount
  omega

/-- Active and frozen labels together give exactly `1 + p_n` vertices. -/
theorem card_vertexLabels {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) :
    (vertexLabels x n).card = plusCount x n + 1 := by
  simp only [vertexLabels, Finset.card_disjSum, Finset.card_range, card_frozenIndices]
  have h := activeCount_eq_counts x n
  have hnat := Int.toNat_of_nonneg hn
  omega

theorem vertexLabels_nonempty {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) : (vertexLabels x n).Nonempty := by
  rw [← Finset.card_pos, card_vertexLabels hn]
  omega

/-- The displayed vertex-count identity in Section 2.1. -/
theorem card_vertexLabels_real {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) :
    ((vertexLabels x n).card : ℝ) = ((activeCount x n : ℝ) + n + 1) / 2 := by
  rw [card_vertexLabels hn]
  have h : (activeCount x n : ℝ) = 1 + 2 * (plusCount x n : ℝ) - n := by
    exact_mod_cast activeCount_eq x n
  push_cast
  linarith

theorem uniformVertex_isProbabilityMeasure {x : SignSequence} {n : ℕ}
    (hn : 0 ≤ activeCount x n) : IsProbabilityMeasure (uniformVertex x n) := by
  constructor
  rw [uniformVertex, Measure.uniformOfFinset_apply]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.div_self (by exact_mod_cast (vertexLabels_nonempty hn).card_pos.ne')
    (by simp)

theorem birthTime_filter {x : SignSequence} {m n : ℕ} (hmn : m ≤ n) :
    (vertexLabels x n).filter (fun v => birthTime n v < m) =
      (∅ : Finset ℕ).disjSum (frozenIndices x m) := by
  apply Finset.ext
  intro v
  cases v with
  | inl j =>
    constructor
    · intro hv
      have hv' := (Finset.mem_filter.mp hv).2
      exact False.elim ((not_lt_of_ge hmn) hv')
    · intro hv
      simp at hv
  | inr i =>
    constructor
    · intro hv
      obtain ⟨hv, him⟩ := Finset.mem_filter.mp hv
      have hf : i ∈ frozenIndices x n := Finset.inr_mem_disjSum.mp hv
      obtain ⟨hin, hx⟩ := Finset.mem_filter.mp hf
      apply Finset.inr_mem_disjSum.mpr
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr him, hx⟩
    · intro hv
      have hf : i ∈ frozenIndices x m := Finset.inr_mem_disjSum.mp hv
      obtain ⟨him, hx⟩ := Finset.mem_filter.mp hf
      have him' := Finset.mem_range.mp him
      apply Finset.mem_filter.mpr
      refine ⟨Finset.inr_mem_disjSum.mpr ?_, him'⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (him'.trans_le hmn), hx⟩

/-- Lemma `lem:bunif`, first expressed as a ratio of exact finite counts. -/
theorem uniform_birthTime_lt_counts {x : SignSequence} {m n : ℕ}
    (hn : 0 ≤ activeCount x n) (hmn : m ≤ n) :
    ((uniformVertex x n) {v | birthTime n v < m}).toReal =
      (minusCount x m : ℝ) / (plusCount x n + 1 : ℝ) := by
  rw [uniformVertex, Measure.uniformOfFinset_apply]
  simp only [Set.mem_ofPred_eq]
  rw [birthTime_filter hmn, Finset.card_disjSum, Finset.card_empty, zero_add,
    card_frozenIndices, card_vertexLabels hn]
  simp [ENNReal.toReal_add]

/-- The exact probability formula of Lemma `lem:bunif`. The only endpoint
condition needed for the deterministic-label law is `S_n ≥ 0`; before or at
extinction this follows from the walk. -/
theorem uniform_birthTime_lt {x : SignSequence} {m n : ℕ}
    (hn : 0 ≤ activeCount x n) (hmn : m ≤ n) :
    ((uniformVertex x n) {v | birthTime n v < m}).toReal =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  rw [uniform_birthTime_lt_counts hn hmn]
  have hm : (activeCount x m : ℝ) = 1 + (plusCount x m : ℝ) - minusCount x m := by
    exact_mod_cast activeCount_eq_counts x m
  have hn' : (activeCount x n : ℝ) = 1 + 2 * (plusCount x n : ℝ) - n := by
    exact_mod_cast activeCount_eq x n
  have hc : (plusCount x m : ℝ) + minusCount x m = m := by
    exact_mod_cast plusCount_add_minusCount x m
  have hnum : (m : ℝ) + 1 - activeCount x m = 2 * minusCount x m := by linarith
  have hden : (n : ℝ) + 1 + activeCount x n = 2 * (plusCount x n + 1) := by linarith
  rw [hnum, hden, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

end Freezing1

/-! ## IntervalCounts -/

namespace Freezing1

/-- Number of attachment steps with paper index in `(a, b]`. -/
def intervalPlusCount (x : SignSequence) (a b : ℕ) : ℕ :=
  ((Finset.Ioc a b).filter fun i => x i = true).card

theorem intervalPlusCount_eq_sum (x : SignSequence) (a b : ℕ) :
    intervalPlusCount x a b =
      ∑ i ∈ Finset.Ico a b, if x (i + 1) then 1 else 0 := by
  rw [Finset.sum_Ico_add' (fun i => if x i then (1 : ℕ) else 0) a b 1,
    Finset.Ico_add_one_add_one_eq_Ioc]
  simp [intervalPlusCount]

theorem plusCount_add_intervalPlusCount {x : SignSequence} {a b : ℕ}
    (hab : a ≤ b) : plusCount x a + intervalPlusCount x a b = plusCount x b := by
  simpa only [plusCount, intervalPlusCount_eq_sum] using
    Finset.sum_range_add_sum_Ico (fun i => if x (i + 1) then (1 : ℕ) else 0) hab

theorem intervalPlusCount_eq_sub {x : SignSequence} {a b : ℕ} (hab : a ≤ b) :
    intervalPlusCount x a b = plusCount x b - plusCount x a := by
  have := plusCount_add_intervalPlusCount (x := x) hab
  omega

/-- The exact counting identity in equation `EqProp9`. -/
theorem intervalPlusCount_eq_activeCount {x : SignSequence} {a b : ℕ}
    (hab : a ≤ b) :
    (intervalPlusCount x a b : ℝ) =
      ((activeCount x b : ℝ) - activeCount x a + b - a) / 2 := by
  have hc : (plusCount x a : ℝ) + intervalPlusCount x a b = plusCount x b := by
    exact_mod_cast plusCount_add_intervalPlusCount (x := x) hab
  have ha : (activeCount x a : ℝ) = 1 + 2 * (plusCount x a : ℝ) - a := by
    exact_mod_cast activeCount_eq x a
  have hb : (activeCount x b : ℝ) = 1 + 2 * (plusCount x b : ℝ) - b := by
    exact_mod_cast activeCount_eq x b
  linarith

/-- Equation `EqProp9`: endpoint ratio estimates control attachment counts.
The source uses the same `η` as a uniform maximum over a larger index set;
only the two resulting endpoint estimates are needed here. -/
theorem intervalPlusCount_bounds {x : SignSequence} {a b : ℕ} {c η : ℝ}
    (ha : 1 ≤ a) (hab : a < b) (hη : 0 ≤ η)
    (haerr : |(activeCount x a : ℝ) / a - c| ≤ η)
    (hberr : |(activeCount x b : ℝ) / b - c| ≤ η) :
    (c + 1) / 2 * ((b : ℝ) - a) - b * η ≤ intervalPlusCount x a b ∧
      (intervalPlusCount x a b : ℝ) ≤
        (c + 1) / 2 * ((b : ℝ) - a) + b * η := by
  have ha' : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by omega)
  have hb' : 0 < (b : ℝ) := by exact_mod_cast (show 0 < b by omega)
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
  obtain ⟨hal, hau⟩ := abs_le.mp haerr
  obtain ⟨hbl, hbu⟩ := abs_le.mp hberr
  have hal' : (c - η) * a ≤ (activeCount x a : ℝ) :=
    (le_div_iff₀ ha').mp (by linarith)
  have hau' : (activeCount x a : ℝ) ≤ (c + η) * a :=
    (div_le_iff₀ ha').mp (by linarith)
  have hbl' : (c - η) * b ≤ (activeCount x b : ℝ) :=
    (le_div_iff₀ hb').mp (by linarith)
  have hbu' : (activeCount x b : ℝ) ≤ (c + η) * b :=
    (div_le_iff₀ hb').mp (by linarith)
  have heta : (a : ℝ) * η ≤ b * η := mul_le_mul_of_nonneg_right hab' hη
  rw [intervalPlusCount_eq_activeCount hab.le]
  constructor <;> nlinarith

end Freezing1

/-! ## BernoulliConcentration -/

namespace Freezing1

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The exact moment generating function of a Bernoulli variable. -/
theorem mgf_bernoulli {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (θ : ℝ) :
    mgf Y μ θ = (p : ℝ) * Real.exp θ + (1 - (p : ℝ)) := by
  calc
    mgf Y μ θ = ∫ x : ℝ, Real.exp (θ * x) ∂bernoulliMeasure 1 0 p := by
      exact hY.integral_comp (f := fun x : ℝ ↦ Real.exp (θ * x)) (by fun_prop)
    _ = (p : ℝ) * Real.exp θ + (1 - (p : ℝ)) := by
      rw [integral_bernoulliMeasure]
      simp

theorem integrable_exp_mul_bernoulli {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (θ : ℝ) :
    Integrable (fun ω ↦ Real.exp (θ * Y ω)) μ :=
  hY.integrable_fun_comp
    (integrable_bernoulliMeasure 1 0 p (fun x : ℝ ↦ Real.exp (θ * x)))

/-- Exponential upper bound obtained from `1 + z ≤ exp z`. -/
theorem mgf_bernoulli_le {Y : Ω → ℝ} {p : unitInterval}
    (hY : HasLaw Y (bernoulliMeasure (1 : ℝ) 0 p) μ) (θ : ℝ) :
    mgf Y μ θ ≤ Real.exp ((p : ℝ) * (Real.exp θ - 1)) := by
  rw [mgf_bernoulli hY]
  have h := Real.add_one_le_exp ((p : ℝ) * (Real.exp θ - 1))
  linarith

/-- The MGF bound for a finite sum, with its mean derived from the Bernoulli parameters. -/
theorem mgf_sum_bernoulli_le {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (θ : ℝ) :
    mgf (∑ i ∈ s, Y i) μ θ ≤
      Real.exp ((∑ i ∈ s, (p i : ℝ)) * (Real.exp θ - 1)) := by
  rw [h_indep.mgf_sum hY]
  calc
    ∏ i ∈ s, mgf (Y i) μ θ ≤ ∏ i ∈ s, Real.exp ((p i : ℝ) * (Real.exp θ - 1)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mgf_nonneg
      · intro i hi
        exact mgf_bernoulli_le (hLaw i) θ
    _ = Real.exp (∑ i ∈ s, (p i : ℝ) * (Real.exp θ - 1)) := (Real.exp_sum s _).symm
    _ = Real.exp ((∑ i ∈ s, (p i : ℝ)) * (Real.exp θ - 1)) := by
      rw [Finset.sum_mul]

/-- The negative-parameter centered rate is bounded by the positive-parameter rate. -/
theorem exp_neg_sub_one_add_le {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.exp (-θ) - 1 + θ ≤ Real.exp θ - 1 - θ := by
  have h := Real.self_le_sinh_iff.mpr hθ
  rw [Real.sinh_eq] at h
  linarith

/-- Chernoff's optimizing parameter gives the Bennett rate exactly. -/
theorem bennett_exponent_identity {m t : ℝ} (hm : 0 < m) (ht : 0 < t) :
    -Real.log (1 + t / m) * (m + t) + m * (Real.exp (Real.log (1 + t / m)) - 1) =
      -m * bennettRate (t / m) := by
  have hpos : 0 < 1 + t / m := by positivity
  rw [Real.exp_log hpos]
  unfold bennettRate
  field_simp [hm.ne']
  ring

/-- Bennett's upper-tail bound. Measurability is the usual random-variable typing condition. -/
theorem bernoulli_sum_upper_tail [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ s, (p i : ℝ)) + t < ∑ i ∈ s, Y i ω} ≤
      Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by
    have hd : 0 < t / m := div_pos ht hm
    linarith)
  have h_int : Integrable (fun ω ↦ Real.exp (θ * (∑ i ∈ s, Y i) ω)) μ :=
    h_indep.integrable_exp_mul_sum hY (fun i _ ↦ integrable_exp_mul_bernoulli (hLaw i) θ)
  calc
    μ.real {ω | m + t < ∑ i ∈ s, Y i ω} ≤ μ.real {ω | m + t ≤ (∑ i ∈ s, Y i) ω} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      change m + t < ∑ i ∈ s, Y i ω at hω
      change m + t ≤ (∑ i ∈ s, Y i) ω
      simpa only [Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-θ * (m + t)) * mgf (∑ i ∈ s, Y i) μ θ :=
      measure_ge_le_exp_mul_mgf (m + t) hθ h_int
    _ ≤ Real.exp (-θ * (m + t)) * Real.exp (m * (Real.exp θ - 1)) := by
      apply mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le hY h_indep hLaw s θ)
      exact (Real.exp_pos _).le
    _ = Real.exp (-m * bennettRate (t / m)) := by
      rw [← Real.exp_add]
      congr 1
      exact bennett_exponent_identity hm ht

/-- Bennett's lower-tail bound with the same rate as the upper tail. -/
theorem bernoulli_sum_lower_tail [IsProbabilityMeasure μ]
    {Y : ι → Ω → ℝ} {p : ι → unitInterval}
    (hY : ∀ i, Measurable (Y i)) (h_indep : iIndepFun Y μ)
    (hLaw : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 (p i)) μ)
    (s : Finset ι) (hm : 0 < ∑ i ∈ s, (p i : ℝ)) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (∑ i ∈ s, Y i ω) < (∑ i ∈ s, (p i : ℝ)) - t} ≤
      Real.exp (-(∑ i ∈ s, (p i : ℝ)) * bennettRate (t / (∑ i ∈ s, (p i : ℝ)))) := by
  let m : ℝ := ∑ i ∈ s, (p i : ℝ)
  let θ : ℝ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by
    have hd : 0 < t / m := div_pos ht hm
    linarith)
  have h_int : Integrable (fun ω ↦ Real.exp ((-θ) * (∑ i ∈ s, Y i) ω)) μ :=
    h_indep.integrable_exp_mul_sum hY (fun i _ ↦ integrable_exp_mul_bernoulli (hLaw i) (-θ))
  calc
    μ.real {ω | (∑ i ∈ s, Y i ω) < m - t} ≤ μ.real {ω | (∑ i ∈ s, Y i) ω ≤ m - t} := by
      refine measureReal_mono ?_ (measure_ne_top μ _)
      intro ω hω
      change (∑ i ∈ s, Y i ω) < m - t at hω
      change (∑ i ∈ s, Y i) ω ≤ m - t
      simpa only [Finset.sum_apply] using hω.le
    _ ≤ Real.exp (-(-θ) * (m - t)) * mgf (∑ i ∈ s, Y i) μ (-θ) :=
      measure_le_le_exp_mul_mgf (m - t) (neg_nonpos.mpr hθ) h_int
    _ ≤ Real.exp (-(-θ) * (m - t)) * Real.exp (m * (Real.exp (-θ) - 1)) := by
      apply mul_le_mul_of_nonneg_left (mgf_sum_bernoulli_le hY h_indep hLaw s (-θ))
      exact (Real.exp_pos _).le
    _ = Real.exp (-(-θ) * (m - t) + m * (Real.exp (-θ) - 1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-θ * (m + t) + m * (Real.exp θ - 1)) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (exp_neg_sub_one_add_le hθ) hm.le
      nlinarith
    _ = Real.exp (-m * bennettRate (t / m)) := by
      congr 1
      exact bennett_exponent_identity hm ht

end Freezing1

/-! ## SourceChecks -/

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

/-! ## PaperResults -/

namespace Freezing1

/-- Lemma `lemme minoration h_n^+`, with the paper's exact stopping condition. -/
theorem heightScale_lower_bound {x : SignSequence} {n : ℕ}
    (hn : 1 ≤ n) (hτ : (n : ℕ∞) < extinctionTime x) :
    Real.log ((n : ℝ) / 4) ≤ heightScale x n := by
  exact log_quarter_le_heightScale hn ((lt_extinctionTime_iff x n).mp hτ)

/-- Lemma `lem:bunif` on its deterministic vertex-label space, including
the endpoint `n = τ`. The labels use the exact paper birth-time shift. -/
theorem uniform_birthTime_lt_of_le_extinctionTime {x : SignSequence} {m n : ℕ}
    (_hm : 1 ≤ m) (hmn : m ≤ n) (hτ : (n : ℕ∞) ≤ extinctionTime x) :
    ((uniformVertex x n) {v | birthTime n v < m}).toReal =
      ((m : ℝ) + 1 - activeCount x m) / ((n : ℝ) + 1 + activeCount x n) := by
  exact uniform_birthTime_lt (activeCount_nonneg_of_le_extinctionTime hτ) hmn

end Freezing1
