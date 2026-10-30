module

public import Freezing1.IidScheduleDrift
public import Mathlib.Data.Finset.Interval

/-! The actual last-negative position of the iid auxiliary signs. All
probabilities are derived from their genuine coordinate independence. -/

@[expose] public section

namespace Freezing1.SIR.OneSusceptible

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Classical

def lastNegative : ℕ → SignSequence → ℕ
  | 0, _ => 0
  | m + 1, x => if x (m + 1) then lastNegative m x else m + 1

theorem lastNegative_le (m : ℕ) (x : SignSequence) : lastNegative m x ≤ m := by
  induction m with
  | zero => rfl
  | succ m ih => cases hx : x (m + 1) <;> simp [lastNegative, hx, Nat.le_succ_of_le ih]

theorem lastNegative_mem (m : ℕ) (x : SignSequence) (hp : 0 < lastNegative m x) :
    1 ≤ lastNegative m x ∧ lastNegative m x ≤ m ∧ x (lastNegative m x) = false := by
  refine ⟨hp, lastNegative_le m x, ?_⟩
  induction m with
  | zero => simp [lastNegative] at hp
  | succ m ih =>
    cases hx : x (m + 1)
    · simp only [lastNegative, hx, Bool.false_eq_true, ite_false]
    · simp only [lastNegative, hx, ite_true] at hp ⊢
      exact ih hp

theorem negative_le_lastNegative (m : ℕ) (x : SignSequence) (j : ℕ)
    (hj : 1 ≤ j) (hjm : j ≤ m) (hxj : x j = false) : j ≤ lastNegative m x := by
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases he : j = m + 1
    · subst j
      simp [lastNegative, hxj]
    · have hjm' : j ≤ m := by omega
      cases hx : x (m + 1)
      · simpa only [lastNegative, hx, Bool.false_eq_true, ite_false] using hjm
      · simpa only [lastNegative, hx, ite_true] using ih hjm'

theorem lastNegative_eq_iff (m : ℕ) (x : SignSequence) (j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    lastNegative m x = j ↔ x j = false ∧ ∀ k, j < k → k ≤ m → x k = true := by
  constructor
  · intro he
    have hmem := lastNegative_mem m x (by omega)
    refine ⟨by simpa only [he] using hmem.2.2, ?_⟩
    intro k hjk hkm
    cases hx : x k
    · have hh := negative_le_lastNegative m x k (by omega) hkm hx
      omega
    · rfl
  · rintro ⟨hxj, hlater⟩
    have hlo := negative_le_lastNegative m x j hj hjm hxj
    apply le_antisymm _ hlo
    by_contra hn
    have hp : 0 < lastNegative m x := by omega
    have hmem := lastNegative_mem m x hp
    have htrue := hlater (lastNegative m x) (by omega) hmem.2.1
    rw [hmem.2.2] at htrue
    contradiction

theorem lastNegative_lt_iff (m : ℕ) (x : SignSequence) (a : ℕ) (ha : 0 < a) :
    lastNegative m x < a ↔ ∀ k, a ≤ k → k ≤ m → x k = true := by
  constructor
  · intro hlo k hak hkm
    cases hx : x k
    · have hh := negative_le_lastNegative m x k (by omega) hkm hx
      omega
    · rfl
  · intro h
    by_contra hn
    have hp : 0 < lastNegative m x := by omega
    have hmem := lastNegative_mem m x hp
    have htrue := h (lastNegative m x) (by omega) hmem.2.1
    rw [hmem.2.2] at htrue
    contradiction

theorem measurable_lastNegative (m : ℕ) : Measurable (lastNegative m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    exact (measurable_of_countable (fun q : Bool × ℕ => if q.1 then q.2 else m + 1)).comp
      ((measurable_pi_apply (m + 1)).prodMk ih)

def lastNegativeGate (m : ℕ) : Set SignSequence := {x | 3 ≤ lastNegative m x}

theorem measurableSet_lastNegativeGate (m : ℕ) : MeasurableSet (lastNegativeGate m) :=
  measurableSet_le measurable_const (measurable_lastNegative m)

theorem iid_aux_coordinate_probability (p : unitInterval) (j : ℕ) (b : Bool) :
    (ForwardAnnealed.iidSignLaw (unitInterval.symm p)) {x | x j = b} =
      if b then (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞)
      else (unitInterval.toNNReal p : ℝ≥0∞) := by
  have hm := (ForwardAnnealed.iidSignLaw_coordinate (unitInterval.symm p) j).map_eq
  change (ForwardAnnealed.iidSignLaw (unitInterval.symm p))
    ((fun x : SignSequence => x j) ⁻¹' {b}) = _
  rw [← Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton b), hm]
  cases b <;> simp [ForwardAnnealed.signLaw, bernoulliMeasure_def]

theorem iid_aux_all_true_probability (p : unitInterval) (S : Finset ℕ) :
    (ForwardAnnealed.iidSignLaw (unitInterval.symm p)) {x | ∀ k ∈ S, x k = true} =
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ S.card := by
  have he : {x : SignSequence | ∀ k ∈ S, x k = true} = ⋂ k ∈ S, {x | x k = true} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
  have hi := (ForwardAnnealed.iidSignLaw_independent (unitInterval.symm p)).meas_biInter
    (S := S) (s := fun k => {x : SignSequence | x k = true})
    (fun k _ => (measurableSet_singleton true).preimage (comap_measurable (fun x : SignSequence => x k)))
  rw [he, hi]
  simp only [iid_aux_coordinate_probability, ite_true, Finset.prod_const]

theorem iid_lastNegative_probability (p : unitInterval) (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m) :
    (ForwardAnnealed.iidSignLaw (unitInterval.symm p)) {x | lastNegative m x = j} =
      (unitInterval.toNNReal p : ℝ≥0∞) *
        (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (m - j) := by
  let P : ℝ≥0∞ := unitInterval.toNNReal p
  let Q : ℝ≥0∞ := unitInterval.toNNReal (unitInterval.symm p)
  have he : {x : SignSequence | lastNegative m x = j} =
      ⋂ k ∈ Finset.Icc j m, {x | x k = if k = j then false else true} := by
    ext x
    rw [Set.mem_ofPred_eq, lastNegative_eq_iff m x j hj hjm]
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxj, hlater⟩ k hk
      obtain ⟨hjk, hkm⟩ := Finset.mem_Icc.mp hk
      by_cases hkj : k = j
      · simpa only [hkj, ite_true] using hxj
      · simpa only [ite_eq_right hkj] using hlater k (by omega) hkm
    · intro h
      refine ⟨by simpa using h j (Finset.mem_Icc.mpr ⟨le_rfl, hjm⟩), ?_⟩
      intro k hjk hkm
      have hh := h k (Finset.mem_Icc.mpr ⟨hjk.le, hkm⟩)
      simpa only [ite_eq_right (by omega : k ≠ j)] using hh
  have hi := (ForwardAnnealed.iidSignLaw_independent (unitInterval.symm p)).meas_biInter
    (S := Finset.Icc j m) (s := fun k => {x : SignSequence | x k = if k = j then false else true})
    (fun k _ => (measurableSet_singleton _).preimage (comap_measurable (fun x : SignSequence => x k)))
  rw [he, hi]
  calc
    _ = ∏ k ∈ Finset.Icc j m, if k = j then P else Q := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hkj : k = j <;> simp [hkj, iid_aux_coordinate_probability, P, Q]
    _ = P * Q ^ (m - j) := by
      rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
        (Finset.mem_Icc.mpr ⟨le_rfl, hjm⟩), ite_eq_left (rfl : j = j)]
      have hs : Finset.Icc j m \ {j} = Finset.Ioc j m := by
        ext k
        simp only [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_singleton, Finset.mem_Ioc]
        omega
      rw [hs]
      congr 1
      calc
        _ = ∏ _k ∈ Finset.Ioc j m, Q := by
          apply Finset.prod_congr rfl
          intro k hk
          exact ite_eq_right (by have := (Finset.mem_Ioc.mp hk).1; omega)
        _ = _ := by simp

theorem iid_lastNegativeGate_compl_probability (p : unitInterval) (m : ℕ) :
    (ForwardAnnealed.iidSignLaw (unitInterval.symm p)) (lastNegativeGate m)ᶜ =
      (unitInterval.toNNReal (unitInterval.symm p) : ℝ≥0∞) ^ (m - 2) := by
  have he : (lastNegativeGate m)ᶜ = {x : SignSequence | ∀ k ∈ Finset.Icc 3 m, x k = true} := by
    ext x
    simp only [lastNegativeGate, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
      lastNegative_lt_iff m x 3 (by omega), Finset.mem_Icc]
    tauto
  rw [he, iid_aux_all_true_probability]
  congr 1
  simp only [Nat.card_Icc]
  omega

end Freezing1.SIR.OneSusceptible
