module

public import Freezing1.ForwardHeight
public import Freezing1.ForwardCutUpdates

/-!
# Conditional averaging of heights added after a cut

Old vertices start at cut height zero. Future attachment and freezing obey
the same empirical averaging identities as ordinary heights. These exact
forward identities support a tail bound for the extra terminal height.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped BigOperators ENNReal Classical

def cutHeightView (s : State) (a : ℕ) : State := {s with height := cutHeight s a}

def cutActiveSum (s : State) (a : ℕ) (f : ℕ → ℝ) : ℝ :=
  activeSum (cutHeightView s a) f

noncomputable def cutActiveMean (s : State) (a : ℕ) (f : ℕ → ℝ) : ℝ :=
  cutActiveSum s a f / s.active.card

theorem cutHeightAux_le (s : State) (a m v : ℕ) : cutHeightAux s a m v ≤ m := by
  induction m generalizing v with
  | zero => simp [cutHeightAux]
  | succ m ih =>
    simp only [cutHeightAux]
    split_ifs
    · omega
    · exact Nat.add_le_add_right (ih (s.parent v)) 1

theorem cutHeight_le_height (s : State) (a v : ℕ) : cutHeight s a v ≤ s.height v :=
  cutHeightAux_le s a _ v

theorem cutActiveSum_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    {a p : ℕ} (ha : a ≤ n) (hp : p ∈ s.active) (f : ℕ → ℝ) :
    cutActiveSum (attach s (n + 1) p) a f =
      cutActiveSum s a f + f (cutHeight s a p + 1) := by
  have hfresh : n + 1 ∉ s.active := by
    intro h
    have hh := hs.vertices_le _ (hs.active_subset h)
    omega
  unfold cutActiveSum activeSum
  change (∑ v ∈ insert (n + 1) s.active, f (cutHeight (attach s (n + 1) p) a v)) =
    (∑ v ∈ s.active, f (cutHeight s a v)) + f (cutHeight s a p + 1)
  rw [Finset.sum_insert hfresh, cutHeight_attach_new hs ha hp, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  exact congrArg f (cutHeight_attach_old hs a p (hs.active_subset hv))

theorem cutActiveSum_freeze {s : State} {p : ℕ} (hp : p ∈ s.active)
    (t a : ℕ) (f : ℕ → ℝ) :
    cutActiveSum (freeze s t p) a f = cutActiveSum s a f - f (cutHeight s a p) := by
  have hh := Finset.sum_erase_add s.active (fun v => f (cutHeight s a v)) hp
  change (∑ v ∈ s.active.erase p, f (cutHeight (freeze s t p) a v)) =
    (∑ v ∈ s.active, f (cutHeight s a v)) - f (cutHeight s a p)
  simp_rw [cutHeight_freeze]
  linarith

theorem average_cutActiveMean_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    (hne : s.active.Nonempty) {a : ℕ} (ha : a ≤ n) (f : ℕ → ℝ) :
    (∑ p ∈ s.active, cutActiveMean (attach s (n + 1) p) a f) / s.active.card =
      ((s.active.card : ℝ) / (s.active.card + 1)) * cutActiveMean s a f +
        (1 / (s.active.card + 1)) * cutActiveMean s a (fun k => f (k + 1)) := by
  have hfresh : n + 1 ∉ s.active := by
    intro h
    have hh := hs.vertices_le _ (hs.active_subset h)
    omega
  have hcard : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hcard1 : (s.active.card : ℝ) + 1 ≠ 0 := by positivity
  have he (p : ℕ) (hp : p ∈ s.active) :
      cutActiveMean (attach s (n + 1) p) a f =
        (cutActiveSum s a f + f (cutHeight s a p + 1)) / (s.active.card + 1) := by
    rw [cutActiveMean, cutActiveSum_attach hs ha hp]
    simp [attach, hfresh]
  rw [Finset.sum_congr rfl he, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul]
  unfold cutActiveMean cutActiveSum activeSum
  simp only [cutHeightView]
  field_simp

theorem average_cutActiveMean_freeze {s : State} (hs : 1 < s.active.card)
    (t a : ℕ) (f : ℕ → ℝ) :
    (∑ p ∈ s.active, cutActiveMean (freeze s t p) a f) / s.active.card = cutActiveMean s a f := by
  have hcard : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast (by omega : s.active.card ≠ 0)
  have hcard1 : (s.active.card : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < s.active.card := by exact_mod_cast hs
    linarith
  have he (p : ℕ) (hp : p ∈ s.active) :
      cutActiveMean (freeze s t p) a f =
        (cutActiveSum s a f - f (cutHeight s a p)) / ((s.active.card : ℝ) - 1) := by
    rw [cutActiveMean, cutActiveSum_freeze hp]
    simp only [freeze, Finset.card_erase_of_mem hp,
      Nat.cast_sub (show 1 ≤ s.active.card by omega), Nat.cast_one]
  rw [Finset.sum_congr rfl he, ← Finset.sum_div, Finset.sum_sub_distrib,
    Finset.sum_const, nsmul_eq_mul]
  unfold cutActiveMean cutActiveSum activeSum
  simp only [cutHeightView]
  field_simp

theorem transitionLaw_cutActiveMean_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    (hne : s.active.Nonempty) {a : ℕ} (ha : a ≤ n) (f : ℕ → ℝ) :
    (∫ s', cutActiveMean s' a f ∂transitionLaw s (n + 1) true) =
      ((s.active.card : ℝ) / (s.active.card + 1)) * cutActiveMean s a f +
        (1 / (s.active.card + 1)) * cutActiveMean s a (fun k => f (k + 1)) := by
  rw [transitionLaw_integral s _ _ hne]
  convert average_cutActiveMean_attach hs hne ha f using 1
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  simp [step, hp]

theorem transitionLaw_cutActiveMean_freeze {s : State} (hs : 1 < s.active.card)
    (t a : ℕ) (f : ℕ → ℝ) :
    (∫ s', cutActiveMean s' a f ∂transitionLaw s t false) = cutActiveMean s a f := by
  rw [transitionLaw_integral s _ _ (Finset.card_pos.mp (by omega))]
  convert average_cutActiveMean_freeze hs t a f using 1
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  simp [step, hp]

theorem treeLaw_integrable_cutActiveMean (x : SignSequence) (n a : ℕ) (f : ℕ → ℝ) :
    Integrable (fun s => cutActiveMean s a f) (treeLaw x n) := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  apply (integrable_const C).mono' measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  rw [Real.norm_eq_abs]
  change |activeMean (cutHeightView s a) f| ≤ C
  apply activeMean_bound hC
  intro v hv
  have hv' : v ∈ s.active := hv
  have hh : cutHeight s a v ≤ n := (cutHeight_le_height s a v).trans
    ((hs.height_le_id v (hs.active_subset hv')).trans (hs.vertices_le v (hs.active_subset hv')))
  exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (show cutHeight s a v < n + 1 by omega))

end Freezing1.Forward
