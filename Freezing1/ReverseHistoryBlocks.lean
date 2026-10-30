module

public import Freezing1.ReverseHistoryBernoulli

/-!
# Block increments independent of the entire earlier reverse history

A fixed vertex's block height is independent of the complete history at the
block's earlier phase. In particular, root membership at that phase can be
weighted against a block-height event without an independence assumption.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

/-- The last coordinate may encode the entire remaining history. No
independence of that coordinate from its own past is required. -/
theorem iIndepFun_iterates_with_terminal {α : Type*} [MeasurableSpace α]
    (b : ℕ) (D : Fin b → History → α) (μ : Measure History) [IsProbabilityMeasure μ]
    (hind : ∀ i : Fin b, i.val + 1 < b →
      IndepFun (fun H => D i ((previous^[i.val]) H)) (previous^[i.val + 1]) μ) :
    iIndepFun (fun i : Fin b => fun H => D i ((previous^[i.val]) H)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hsets
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert i s hlt ih =>
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    have hnot : i ∉ s := by intro hi; exact lt_irrefl i (hlt i hi)
    obtain ⟨j, hj⟩ := hne
    have hib : i.val + 1 < b := by have hh := hlt j hj; have := j.isLt; omega
    let E : Set History := ⋂ j ∈ s,
      (fun H => D j ((previous^[j.val - (i.val + 1)]) H)) ⁻¹' sets j
    have hE : MeasurableSet E := by trivial
    have heq : (previous^[i.val + 1]) ⁻¹' E =
        ⋂ j ∈ s, (fun H => D j ((previous^[j.val]) H)) ⁻¹' sets j := by
      ext H
      simp only [E, Set.mem_preimage, Set.mem_iInter]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro hj
      have hij : i.val + 1 ≤ j.val := hlt j hj
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]
    rw [Finset.prod_insert hnot]
    simp only [Finset.mem_insert, Set.iInter_iInter_eq_or_left]
    rw [← heq, (hind i hib).measure_inter_preimage_eq_mul _ _
      (hsets i (Finset.mem_insert_self _ _)) hE, heq]
    congr 1
    exact ih (fun j hj => hsets j (Finset.mem_insert_of_mem hj))

theorem sum_fin_filter_interval_eq_sum_Ico (f : ℕ → ℕ) (N a b : ℕ) (hb : b ≤ N) :
    (∑ i ∈ (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b), f i.val) =
      ∑ i ∈ Finset.Ico a b, f i := by
  rw [Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun i => if a ≤ i ∧ i < b then f i else 0) N,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  omega

/-- The whole block sum, not merely each individual increment, is independent
of the complete history at phase `b`. -/
theorem blockSum_indep_past (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    {a b : ℕ} (hb : b ≤ birthTime n v) :
    IndepFun (fun H => ∑ i ∈ Finset.Ico a b, phaseIncrement v i H)
      (previous^[b]) (fullLaw x n) := by
  let D : Fin (b + 1) → History → ℕ × History := fun i H =>
    if i.val < b then (heightIncrement v H, initial x n) else (0, H)
  let X : Fin (b + 1) → History → ℕ × History := fun i H => D i ((previous^[i.val]) H)
  have hind : iIndepFun X (fullLaw x n) := by
    apply iIndepFun_iterates_with_terminal
    intro i hi
    have hil : i.val < b := by omega
    have hh := (phaseIncrement_indep_past x n hn hv i.val (hil.trans_le hb)).comp
      (measurable_of_countable (fun z : ℕ => (z, initial x n))) measurable_id
    simpa only [D, hil, ite_true, Function.comp_def, phaseIncrement, id_eq] using hh
  let s : Finset (Fin (b + 1)) := Finset.univ.filter fun i => a ≤ i.val ∧ i.val < b
  let t : Finset (Fin (b + 1)) := {Fin.last b}
  have hdis : Disjoint s t := by
    simp [s, t, Finset.disjoint_singleton_right]
  have htuples := hind.indepFun_finset s t hdis (fun _ => measurable_from_top)
  let φ : (s → ℕ × History) → ℕ := fun z => ∑ i : s, (z i).1
  let ψ : (t → ℕ × History) → History := fun z => (z ⟨Fin.last b, by simp [t]⟩).2
  have hh := htuples.comp (show Measurable φ by fun_prop) (show Measurable ψ by fun_prop)
  have hleft (H : History) : φ (fun i : s => X i H) =
      ∑ i ∈ Finset.Ico a b, phaseIncrement v i H := by
    change (∑ i : s, (X i H).1) = _
    rw [Finset.sum_coe_sort s (fun i => (X i H).1)]
    calc
      _ = ∑ i ∈ s, phaseIncrement v i.val H := by
        apply Finset.sum_congr rfl
        intro i hi
        have hil := (Finset.mem_filter.mp hi).2.2
        simp only [X, D, hil, ite_true, phaseIncrement]
      _ = _ := sum_fin_filter_interval_eq_sum_Ico (fun i => phaseIncrement v i H)
        (b + 1) a b (Nat.le_succ b)
  have hright (H : History) : ψ (fun i : t => X i H) = (previous^[b]) H := by
    simp only [ψ, X, D, Fin.val_last, lt_self_iff_false, ite_false]
  apply hh.congr
  · exact Filter.Eventually.of_forall hleft
  · exact Filter.Eventually.of_forall hright

/-- The actual block height is independent of its full earlier history. -/
theorem depth_difference_indep_past (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ birthTime n v) :
    IndepFun (fun H => (stage H a).depth v - (stage H b).depth v)
      (previous^[b]) (fullLaw x n) := by
  apply (blockSum_indep_past x n hn hv (a := a) hb).congr
  · filter_upwards [fullLaw_depth_difference_eq_sum_phaseIncrements x n hn hv hab hb] with H hH
    exact hH.symm
  · exact Filter.Eventually.of_forall fun _ => rfl

/-- Exact factorization against any earlier-history event. The Bernoulli
probability is derived from the actual block law. -/
theorem depth_difference_event_and_past (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ birthTime n v) (A : Set ℕ) (B : Set History) :
    (fullLaw x n) {H | (stage H a).depth v - (stage H b).depth v ∈ A ∧
      (previous^[b]) H ∈ B} =
      (bernoulliPartialSumLaw
        (fun i : Fin b => Reverse.attachmentParameter x n hn
          ⟨i.val, i.isLt.trans_le (hb.trans (Reverse.birthTime_le_of_mem hv))⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val)) A *
      (fullLaw x n) {H | (previous^[b]) H ∈ B} := by
  have hind := depth_difference_indep_past x n hn hv hab hb
  have hh := hind.measure_inter_preimage_eq_mul A B (by measurability) (by trivial)
  have hLaw := fullLaw_depth_difference_hasLaw x n hn hv hab hb
  change (fullLaw x n) {H | (stage H a).depth v - (stage H b).depth v ∈ A ∧
      (previous^[b]) H ∈ B} =
    (fullLaw x n) {H | (stage H a).depth v - (stage H b).depth v ∈ A} *
      (fullLaw x n) {H | (previous^[b]) H ∈ B} at hh
  rw [hLaw.measure_eq (p := fun k => k ∈ A) (by measurability)] at hh
  exact hh

/-- Root membership at phase `b` is allowed to be random. Its conjunction
with a block-height event factors by the proved whole-history independence. -/
theorem depth_difference_event_and_root (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ birthTime n v) (A : Set ℕ) :
    (fullLaw x n).real {H | v ∈ (stage H b).roots ∧
      (stage H a).depth v - (stage H b).depth v ∈ A} =
      (fullLaw x n).real {H | v ∈ (stage H b).roots} *
      (bernoulliPartialSumLaw
        (fun i : Fin b => Reverse.attachmentParameter x n hn
          ⟨i.val, i.isLt.trans_le (hb.trans (Reverse.birthTime_le_of_mem hv))⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val)).real A := by
  have hh := depth_difference_event_and_past x n hn hv hab hb A
    {G | v ∈ G.current.roots}
  have hr := congrArg ENNReal.toReal hh
  simp only [ENNReal.toReal_mul, Set.mem_ofPred_eq, current_previous_iterate_eq_stage] at hr
  simpa only [Measure.real, and_comm, mul_comm] using hr

end Freezing1.ReverseHistory
