module

import Challenge.LocalLimits

open Freezing1 Filter

theorem activeCount_succ' (x : SignSequence) (n : ℕ) :
    activeCount x (n + 1) = activeCount x n + (if x (n + 1) then 1 else -1) := by
  unfold activeCount
  rw [Finset.sum_range_succ]; ring

-- (1) all-plus schedule: tau = top, (III) false
theorem plus_tau : extinctionTime (fun _ => true) = ⊤ := by
  unfold extinctionTime
  rw [dif_neg]
  rintro ⟨k, hk⟩
  have : ∀ m, activeCount (fun _ => true) m = 1 + m := by
    intro m; induction m with
    | zero => simp [activeCount]
    | succ m ih => rw [activeCount_succ', ih]; simp; ring
  have := this k
  omega

-- (2) alternating schedule: odd steps attach, even steps freeze
def alt : SignSequence := fun i => decide (i % 2 = 1)

theorem alt_even (k : ℕ) : activeCount alt (2 * k) = 1 := by
  induction k with
  | zero => simp [activeCount]
  | succ k ih =>
    have h : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [h, activeCount_succ', activeCount_succ']
    have e1 : alt (2 * k + 1) = true := by simp [alt]
    have e2 : alt (2 * k + 1 + 1) = false := by simp [alt]; omega
    rw [e1, e2, ih]; simp

theorem alt_odd (k : ℕ) : activeCount alt (2 * k + 1) = 2 := by
  have e1 : alt (2 * k + 1) = true := by simp [alt]
  rw [activeCount_succ', e1, alt_even]; simp

theorem alt_pos (k : ℕ) : 1 ≤ activeCount alt k := by
  rcases Nat.even_or_odd' k with ⟨m, rfl | rfl⟩
  · rw [alt_even]
  · rw [alt_odd]; norm_num

theorem alt_tau : extinctionTime alt = ⊤ := by
  unfold extinctionTime
  rw [dif_neg]
  rintro ⟨k, hk⟩
  have := alt_pos k
  omega

theorem alt_sum_ge (n : ℕ) : ((n / 2 : ℕ) : ℝ) ≤ freezingReciprocalSum alt n := by
  induction n with
  | zero => simp [freezingReciprocalSum]
  | succ n ih =>
    have hstep : freezingReciprocalSum alt (n + 1) =
        freezingReciprocalSum alt n + (if alt (n + 1) then 0 else 1 / (activeCount alt (n + 1) : ℝ)) := by
      unfold freezingReciprocalSum
      rw [Finset.sum_Icc_succ_top (by omega)]
    rw [hstep]
    rcases Nat.even_or_odd' n with ⟨m, rfl | rfl⟩
    · have : alt (2 * m + 1) = true := by simp [alt]
      rw [this]
      have h2 : (2 * m + 1) / 2 = 2 * m / 2 := by omega
      rw [h2]; simpa using ih
    · have : alt (2 * m + 1 + 1) = false := by simp [alt]; omega
      rw [this]
      have h3 : 2 * m + 1 + 1 = 2 * (m + 1) := by ring
      rw [h3, alt_even]
      have h4 : (2 * m + 1) / 2 = m := by omega
      rw [h4] at ih
      have h5 : 2 * (m + 1) / 2 = m + 1 := by omega
      rw [h5]
      push_cast
      simp
      linarith

theorem alt_div : Tendsto (freezingReciprocalSum alt) atTop atTop := by
  refine tendsto_atTop_mono alt_sum_ge ?_
  refine tendsto_natCast_atTop_atTop.comp ?_
  exact Nat.tendsto_div_const_atTop (by norm_num)

/-- Instantiating the Challenge hypotheses: all-plus gives (III) false, alt gives (III) true;
rows `x n = alt` satisfy `hxy`. -/
example : (∀ i, 1 ≤ i → ∀ᶠ n in atTop, (fun _ : ℕ => alt) n i = alt i) ∧
    extinctionTime alt = ⊤ ∧ Tendsto (freezingReciprocalSum alt) atTop atTop :=
  ⟨fun _ _ => Eventually.of_forall (fun _ => rfl), alt_tau, alt_div⟩

/-- rows agreeing with `alt` up to index n/2 and then freezing forever -/
def row (n : ℕ) : SignSequence := fun i => if i ≤ n / 2 then alt i else false

theorem row_hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, row n i = alt i := by
  intro i _
  filter_upwards [eventually_ge_atTop (2 * i)] with n hn
  simp only [row]
  rw [if_pos (by omega)]

theorem row_agree (n m : ℕ) (hm : m ≤ n / 2) : activeCount (row n) m = activeCount alt m := by
  induction m with
  | zero => simp [activeCount]
  | succ m ih =>
    rw [activeCount_succ', activeCount_succ', ih (by omega)]
    have : row n (m + 1) = alt (m + 1) := by simp only [row]; rw [if_pos (by omega)]
    rw [this]

theorem row_dec (n k : ℕ) :
    activeCount (row n) (n / 2 + k) = activeCount alt (n / 2) - k := by
  induction k with
  | zero => simp [row_agree n (n / 2) le_rfl]
  | succ k ih =>
    rw [← add_assoc, activeCount_succ', ih]
    have : row n (n / 2 + k + 1) = false := by simp only [row]; rw [if_neg (by omega)]
    rw [this]; simp; ring

theorem row_extinct (n : ℕ) : ∃ k, k ≤ n / 2 + 2 ∧ activeCount (row n) k = 0 := by
  have h1 := alt_pos (n / 2)
  have h2 : activeCount alt (n / 2) ≤ 2 := by
    rcases Nat.even_or_odd' (n / 2) with ⟨m, hm | hm⟩
    · rw [hm, alt_even]; norm_num
    · rw [hm, alt_odd]
  refine ⟨n / 2 + (activeCount alt (n / 2)).toNat, by omega, ?_⟩
  rw [row_dec]
  omega

theorem row_tau_ne_top (n : ℕ) : extinctionTime (row n) ≠ ⊤ := by
  obtain ⟨k, -, hk⟩ := row_extinct n
  unfold extinctionTime
  rw [dif_pos ⟨k, hk⟩]
  exact ENat.coe_ne_top _

#check @local_convergence_equivalences
#print axioms plus_tau
#print axioms alt_div
