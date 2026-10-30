module

public import Freezing1.ReverseHistoryHeight
public import Freezing1.ReverseSeparationLaw
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Independent height increments in the actual reverse history

For one fixed vertex, the increments from its birth to the terminal tree
are mutually independent on the coherent history probability space. This
is an assertion about that vertex's actual increments; it does not assert
independence between increments belonging to different vertices.
-/

@[expose] public section

namespace Freezing1.ReverseHistory

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

/-- Deleting the latest `j` transitions preserves the complete earlier history law. -/
theorem map_lawAfter_previous_iterate (x : SignSequence) (n k j : ℕ)
    (hk : k ≤ n) (hj : j ≤ k) :
    (lawAfter x n k).map (previous^[j]) = lawAfter x n (k - j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjk : j < k := by omega
    have hkj : k - j = (k - (j + 1)) + 1 := by omega
    rw [Function.iterate_succ', ← Measure.map_map measurable_from_top measurable_from_top,
      ih (by omega), hkj]
    exact map_lawAfter_previous x n (k - (j + 1)) (by omega)

theorem map_fullLaw_previous_iterate (x : SignSequence) (n j : ℕ) (hj : j ≤ n) :
    (fullLaw x n).map (previous^[j]) = lawAfter x n (n - j) :=
  map_lawAfter_previous_iterate x n n j le_rfl hj

theorem stage_previous (H : History) (i : ℕ) :
    stage (previous H) i = stage H (i + 1) := by
  cases H with
  | mk F past =>
    cases past with
    | nil => cases i <;> rfl
    | cons G past => rfl

theorem current_previous_iterate_eq_stage (H : History) (i : ℕ) :
    ((previous^[i]) H).current = stage H i := by
  induction i generalizing H with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply, ih, stage_previous]

/-- Paper step `i+1`, read from the completed common history. -/
def phaseIncrement (v : ℕ ⊕ ℕ) (i : ℕ) (H : History) : ℕ :=
  heightIncrement v ((previous^[i]) H)

theorem phaseIncrement_eq_stage (v : ℕ ⊕ ℕ) (i : ℕ) (H : History) :
    phaseIncrement v i H = (stage H i).depth v - (stage H (i + 1)).depth v := by
  simp only [phaseIncrement, heightIncrement, ← Function.iterate_succ_apply',
    current_previous_iterate_eq_stage]

/-- The actual increment at paper step `i+1` has the attachment-masked Bernoulli law. -/
theorem phaseIncrement_hasLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    (i : ℕ) (hi : i < birthTime n v) :
    HasLaw (phaseIncrement v i)
      (bernoulliMeasure (1 : ℕ) 0
        (Reverse.attachmentParameter x n hn ⟨i, hi.trans_le (Reverse.birthTime_le_of_mem hv)⟩))
      (fullLaw x n) := by
  have hin : i < n := hi.trans_le (Reverse.birthTime_le_of_mem hv)
  have hlocal := lawAfter_heightIncrement_hasLaw x n (n - (i + 1)) hn (by omega) hv (by omega)
  have htime : n - (i + 1) + 1 = n - i := by omega
  simp only [htime, Nat.sub_sub_self hin.le] at hlocal
  have hp : HasLaw (previous^[i]) (lawAfter x n (n - i)) (fullLaw x n) :=
    ⟨measurable_from_top.aemeasurable, map_fullLaw_previous_iterate x n i hin.le⟩
  exact hlocal.fun_comp hp

/-- The increment at a phase is independent of the entire history at the
preceding phase, on the same completed history space. -/
theorem phaseIncrement_indep_past (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    (i : ℕ) (hi : i < birthTime n v) :
    IndepFun (phaseIncrement v i) (previous^[i + 1]) (fullLaw x n) := by
  have hin : i < n := hi.trans_le (Reverse.birthTime_le_of_mem hv)
  have hlocal := lawAfter_heightIncrement_indep_previous x n (n - (i + 1)) hn
    (by omega) hv (by omega)
  have htime : n - (i + 1) + 1 = n - i := by omega
  rw [htime] at hlocal
  apply indepFun_of_identDistrib_pair hlocal
  refine ⟨measurable_from_top.aemeasurable, measurable_from_top.aemeasurable, ?_⟩
  rw [show (fun H => (phaseIncrement v i H, (previous^[i + 1]) H)) =
      (fun H => (heightIncrement v H, previous H)) ∘ (previous^[i]) by
    funext H
    simp only [Function.comp_def, phaseIncrement, Function.iterate_succ_apply'],
    ← Measure.map_map measurable_from_top measurable_from_top,
    map_fullLaw_previous_iterate x n i hin.le]

/-- A finite family read from successive suffixes is independent if each
entry is independent of its entire preceding suffix. -/
theorem iIndepFun_iterates_of_indep_past (D : History → ℕ) (b : ℕ)
    (μ : Measure History) [IsProbabilityMeasure μ]
    (hind : ∀ i < b, IndepFun (fun H => D ((previous^[i]) H)) (previous^[i + 1]) μ) :
    iIndepFun (fun i : Fin b => fun H => D ((previous^[i.val]) H)) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hsets
  induction s using Finset.induction_on_min with
  | empty => simp
  | insert i s hlt ih =>
    have hnot : i ∉ s := by intro hi; exact lt_irrefl i (hlt i hi)
    let E : Set History := ⋂ j ∈ s,
      (fun H => D ((previous^[j.val - (i.val + 1)]) H)) ⁻¹' sets j
    have hE : MeasurableSet E := by trivial
    have heq : (previous^[i.val + 1]) ⁻¹' E =
        ⋂ j ∈ s, (fun H => D ((previous^[j.val]) H)) ⁻¹' sets j := by
      ext H
      simp only [E, Set.mem_preimage, Set.mem_iInter]
      apply forall_congr'
      intro j
      apply forall_congr'
      intro hj
      have hij : i.val + 1 ≤ j.val := by have hh := hlt j hj; exact hh
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij]
    rw [Finset.prod_insert hnot]
    simp only [Finset.mem_insert, Set.iInter_iInter_eq_or_left]
    rw [← heq, (hind i.val i.isLt).measure_inter_preimage_eq_mul _ _
        (hsets i (Finset.mem_insert_self _ _)) hE, heq]
    congr 1
    exact ih (fun j hj => hsets j (Finset.mem_insert_of_mem hj))

/-- The source's independent Bernoulli increments, now on the actual common
history space, for each fixed vertex separately. -/
theorem phaseIncrements_independent (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    iIndepFun (fun i : Fin (birthTime n v) => phaseIncrement v i.val) (fullLaw x n) := by
  exact iIndepFun_iterates_of_indep_past (heightIncrement v) (birthTime n v) (fullLaw x n)
    (fun i hi => phaseIncrement_indep_past x n hn hv i hi)

/-- The entire actual increment vector has the product of the prescribed
Bernoulli laws. This joint assertion concerns one fixed vertex. -/
theorem phaseIncrements_hasLaw_product (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    HasLaw (fun H => fun i : Fin (birthTime n v) => phaseIncrement v i.val H)
      (Measure.pi (fun i : Fin (birthTime n v) => bernoulliMeasure (1 : ℕ) 0
        (Reverse.attachmentParameter x n hn
          ⟨i.val, i.isLt.trans_le (Reverse.birthTime_le_of_mem hv)⟩))) (fullLaw x n) := by
  exact (phaseIncrements_independent x n hn hv).hasLaw_pi
    (fun i => phaseIncrement_hasLaw x n hn hv i.val i.isLt)

/-- While the vertex is present, a reverse transition cannot decrease its depth. -/
theorem lawAfter_depth_le_current (x : SignSequence) (n k : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : k < n)
    {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) (hbirth : n - k ≤ birthTime n v) :
    ∀ᵐ H ∂lawAfter x n (k + 1), (previous H).current.depth v ≤ H.current.depth v := by
  apply (ae_iff_prob_eq_one measurable_from_top).mpr
  rw [lawAfter, ite_eq_left hk, Measure.bind_apply (by trivial)
    measurable_from_top.aemeasurable]
  calc
    _ = ∫⁻ _H, (1 : ℝ≥0∞) ∂lawAfter x n k := by
      apply lintegral_congr_ae
      filter_upwards [lawAfter_current_valid x n k hn hk.le] with H hH
      have hphase : n - k = n - (k + 1) + 1 := by omega
      have hvH : v ∈ H.current.vertices := by
        rw [hH.vertices_eq]
        exact (Reverse.mem_phaseLabels_iff_birthTime (by omega) hv).mpr hbirth
      rw [hphase] at hH
      apply (ae_iff_prob_eq_one measurable_from_top).mp
      apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
      filter_upwards [Reverse.transitionLaw_present_depth_support hn (by omega) hH hvH] with F hF
      change H.current.depth v ≤ F.depth v
      rcases hF.2 with h | h <;> omega
    _ = 1 := by simp

/-- Every actual present-vertex increment is a genuine natural difference. -/
theorem fullLaw_depth_at_phase_succ_le (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    (i : ℕ) (hi : i < birthTime n v) :
    ∀ᵐ H ∂fullLaw x n,
      ((previous^[i + 1]) H).current.depth v ≤ ((previous^[i]) H).current.depth v := by
  have hin : i < n := hi.trans_le (Reverse.birthTime_le_of_mem hv)
  have hh := lawAfter_depth_le_current x n (n - (i + 1)) hn (by omega) hv (by omega)
  have htime : n - (i + 1) + 1 = n - i := by omega
  rw [htime] at hh
  have hp : ∀ᵐ H ∂fullLaw x n,
      (previous ((previous^[i]) H)).current.depth v ≤ ((previous^[i]) H).current.depth v := by
    apply ae_of_ae_map (f := previous^[i])
      (p := fun H : History => (previous H).current.depth v ≤ H.current.depth v)
      measurable_from_top.aemeasurable
    rw [map_fullLaw_previous_iterate x n i hin.le]
    exact hh
  simpa only [Function.iterate_succ_apply'] using hp

/-- At its birth phase the tracked vertex is a singleton of depth zero. -/
theorem fullLaw_birth_depth_zero (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, ((previous^[birthTime n v]) H).current.depth v = 0 := by
  let b := birthTime n v
  have hb : b ≤ n := Reverse.birthTime_le_of_mem hv
  have hp : HasLaw (previous^[b]) (lawAfter x n (n - b)) (fullLaw x n) :=
    ⟨measurable_from_top.aemeasurable, map_fullLaw_previous_iterate x n b hb⟩
  have hc : HasLaw History.current (Reverse.lawAfter x n (n - b)) (lawAfter x n (n - b)) :=
    ⟨measurable_from_top.aemeasurable, map_lawAfter_current x n (n - b)⟩
  have hd := Reverse.lawAfter_trackedDepth_hasLaw x n hn hv (n - b) (by omega)
  have he : Reverse.heightIndices n v (n - b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    simp only [Reverse.heightIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.sub_sub_self hb] at hi
    exact (not_lt_of_ge hi.1) hi.2
  rw [he, bernoulliPartialSumLaw_empty] at hd
  have hz := (hd.fun_comp (hc.fun_comp hp)).ae_eq_of_dirac
  have hvalid : ∀ᵐ H ∂fullLaw x n,
      Reverse.ValidAt x n b ((previous^[b]) H).current := by
    apply ae_of_ae_map (f := previous^[b])
      (p := fun H : History => Reverse.ValidAt x n b H.current)
      measurable_from_top.aemeasurable
    rw [map_fullLaw_previous_iterate x n b hb]
    simpa only [Nat.sub_sub_self hb] using lawAfter_current_valid x n (n - b) hn (by omega)
  filter_upwards [hz, hvalid] with H hzero hH
  have hvH : v ∈ ((previous^[b]) H).current.vertices := by
    rw [hH.vertices_eq]
    exact (Reverse.mem_phaseLabels_iff_birthTime hb hv).mpr le_rfl
  simpa only [Reverse.trackedDepth, ite_eq_left hvH] using hzero

/-- The finite natural telescoping identity needs only adjacent monotonicity. -/
theorem sum_range_depth_differences (a : ℕ → ℕ) (b : ℕ)
    (hmono : ∀ i < b, a (i + 1) ≤ a i) :
    (∑ i ∈ Finset.range b, (a i - a (i + 1))) + a b = a 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hh := ih (fun i hi => hmono i (by omega))
    have hb := hmono b (by omega)
    rw [Finset.sum_range_succ]
    omega

/-- The actual terminal height is the sum of its own independent Bernoulli
increments, on the very same history space. -/
theorem fullLaw_depth_eq_sum_phaseIncrements (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n) :
    ∀ᵐ H ∂fullLaw x n, H.current.depth v =
      ∑ i : Fin (birthTime n v), phaseIncrement v i.val H := by
  have hmono : ∀ᵐ H ∂fullLaw x n, ∀ i < birthTime n v,
      ((previous^[i + 1]) H).current.depth v ≤ ((previous^[i]) H).current.depth v := by
    exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun hi =>
      fullLaw_depth_at_phase_succ_le x n hn hv i hi
  filter_upwards [hmono, fullLaw_birth_depth_zero x n hn hv] with H hH hzero
  have hh := sum_range_depth_differences
    (fun i => ((previous^[i]) H).current.depth v) (birthTime n v) hH
  rw [hzero, add_zero] at hh
  rw [Fin.sum_univ_eq_sum_range (fun i => phaseIncrement v i H) (birthTime n v)]
  simpa only [phaseIncrement, heightIncrement, Function.iterate_succ_apply',
    Function.iterate_zero_apply] using hh.symm

/-- The sum on a finite prefix, filtered below by `a`, is precisely `(a,b]`
in paper step numbering. -/
theorem sum_fin_filter_ge_eq_sum_Ico (f : ℕ → ℕ) (a b : ℕ) :
    (∑ i ∈ (Finset.univ.filter fun i : Fin b => a ≤ i.val), f i.val) =
      ∑ i ∈ Finset.Ico a b, f i := by
  rw [Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun i => if a ≤ i then f i else 0) b,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  tauto

/-- An actual block height is the sum of the actual increments in that
block, retaining both endpoint phases. -/
theorem fullLaw_depth_difference_eq_sum_phaseIncrements (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ birthTime n v) :
    ∀ᵐ H ∂fullLaw x n, (stage H a).depth v - (stage H b).depth v =
      ∑ i ∈ Finset.Ico a b, phaseIncrement v i H := by
  have hmono : ∀ᵐ H ∂fullLaw x n, ∀ i < birthTime n v,
      ((previous^[i + 1]) H).current.depth v ≤ ((previous^[i]) H).current.depth v := by
    exact ae_all_iff.mpr fun i => ae_all_iff.mpr fun hi =>
      fullLaw_depth_at_phase_succ_le x n hn hv i hi
  filter_upwards [hmono] with H hH
  have hh := sum_range_depth_differences
    (fun i => ((previous^[a + i]) H).current.depth v) (b - a)
    (fun i hi => by simpa only [Nat.add_assoc] using hH (a + i) (by omega))
  simp only [Nat.add_sub_of_le hab, Nat.add_zero] at hh
  rw [Finset.sum_Ico_eq_sum_range]
  have he : (∑ i ∈ Finset.range (b - a), phaseIncrement v (a + i) H) +
      (stage H b).depth v = (stage H a).depth v := by
    simpa only [phaseIncrement, heightIncrement, ← Function.iterate_succ_apply',
      ← Nat.add_assoc, current_previous_iterate_eq_stage] using hh
  omega

/-- The actual block-height law is a partial sum of independent Bernoulli
coordinates with the original schedule parameters, for every vertex present
at the earlier phase `b`. -/
theorem fullLaw_depth_difference_hasLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {v : ℕ ⊕ ℕ} (hv : v ∈ vertexLabels x n)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ birthTime n v) :
    HasLaw (fun H => (stage H a).depth v - (stage H b).depth v)
      (bernoulliPartialSumLaw
        (fun i : Fin b => Reverse.attachmentParameter x n hn
          ⟨i.val, i.isLt.trans_le (hb.trans (Reverse.birthTime_le_of_mem hv))⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val)) (fullLaw x n) := by
  let p : Fin b → unitInterval := fun i => Reverse.attachmentParameter x n hn
    ⟨i.val, i.isLt.trans_le (hb.trans (Reverse.birthTime_le_of_mem hv))⟩
  let s : Finset (Fin b) := Finset.univ.filter fun i => a ≤ i.val
  have hind : iIndepFun (fun i : Fin b => phaseIncrement v i.val) (fullLaw x n) :=
    iIndepFun_iterates_of_indep_past (heightIncrement v) b (fullLaw x n)
      (fun i hi => phaseIncrement_indep_past x n hn hv i (hi.trans_le hb))
  have hvec : HasLaw (fun H => fun i : Fin b => phaseIncrement v i.val H)
      (bernoulliProductLaw p) (fullLaw x n) :=
    hind.hasLaw_pi (fun i => phaseIncrement_hasLaw x n hn hv i.val (i.isLt.trans_le hb))
  have hsum := (bernoulliPartialSumLaw_hasLaw p s).fun_comp hvec
  apply hsum.congr
  filter_upwards [fullLaw_depth_difference_eq_sum_phaseIncrements x n hn hv hab hb] with H hH
  change (stage H a).depth v - (stage H b).depth v =
    ∑ i ∈ (Finset.univ.filter fun i : Fin b => a ≤ i.val), phaseIncrement v i.val H
  rw [sum_fin_filter_ge_eq_sum_Ico (fun i => phaseIncrement v i H) a b]
  exact hH

end Freezing1.ReverseHistory
