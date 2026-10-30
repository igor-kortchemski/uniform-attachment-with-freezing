module

public import Freezing1.SIRRandomEnvironmentTransferCounts

/-!
# Joint tree-history and adaptive-word laws

The mixture is on the entire tree-state prefix. Earlier count gates and
later tree observations therefore belong to the same genuine history.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal NNReal Classical Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def conditionalTreePrefixWordLaw (n : ℕ) :
    {k : ℕ} → (Fin k → Bool) → Measure (Prefix (E := TreeState) k)
  | 0, _ => Measure.dirac (fun _ => initialTreeState n)
  | k + 1, w => (conditionalTreePrefixWordLaw n (Fin.init w)).bind fun P =>
      (signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (w (Fin.last k))).map
        (prefixAppend P)

instance conditionalTreePrefixWordLaw_probability (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    IsProbabilityMeasure (conditionalTreePrefixWordLaw n w) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    have := ih (Fin.init w)
    apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    exact Eventually.of_forall fun P =>
      Measure.isProbabilityMeasure_map_iff (measurable_prefixAppend_right P).aemeasurable
        |>.mpr inferInstance

theorem conditionalTreePrefixWordLaw_snoc (n : ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    conditionalTreePrefixWordLaw n (Fin.snoc w b) =
      (conditionalTreePrefixWordLaw n w).bind fun P =>
        (signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) b).map (prefixAppend P) := by
  simp only [conditionalTreePrefixWordLaw, Fin.init_snoc, Fin.snoc_last]

theorem conditionalTreePrefixWordLaw_phase (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    ∀ᵐ P ∂conditionalTreePrefixWordLaw n w,
      (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).Valid n ∧
        ∀ i, (P i).counts = countsPrefixWord n w i := by
  induction k with
  | zero =>
    simp only [conditionalTreePrefixWordLaw, ae_dirac_eq]
    exact ⟨initialTreeState_valid n, fun _ => counts_initialTreeState n⟩
  | succ k ih =>
    apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
    rw [conditionalTreePrefixWordLaw, Measure.bind_apply (by measurability)
      (measurable_of_countable _).aemeasurable]
    calc
      _ = ∫⁻ _P, (1 : ℝ≥0∞) ∂conditionalTreePrefixWordLaw n (Fin.init w) := by
        apply lintegral_congr_ae
        filter_upwards [ih (Fin.init w)] with P hP
        apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
        apply (ae_map_iff (measurable_prefixAppend_right P).aemeasurable (by measurability)).mpr
        have hc : (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).counts =
            countsRunWord n (Fin.init w) := by
          rw [hP.2, countsPrefixWord_last]
        have hnext : ∀ᵐ z ∂signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (w (Fin.last k)),
            z.Valid n ∧ z.counts = countsRunWord n w := by
          apply signedTreeLaw_ae
          · intro he
            refine ⟨hP.1, ?_⟩
            change _ = countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))
            rw [← hc, countsStep_of_absorbed (by simp [TreeState.counts, he])]
          · intro u hu
            refine ⟨hP.1.step _ _, ?_⟩
            change _ = countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))
            rw [treeStep_counts hP.1.1 hu, hc]
        filter_upwards [hnext] with z hz
        constructor
        · simpa only [prefixAppend, dite_eq_right (show ¬k + 1 ≤ k by omega)] using hz.1
        · intro i
          by_cases hi : i.val ≤ k
          · simpa only [countsPrefixWord, prefixAppend, dite_eq_left hi] using
              hP.2 ⟨i.val, Finset.mem_Iic.mpr hi⟩
          · simpa only [countsPrefixWord, prefixAppend, dite_eq_right hi] using hz.2
      _ = 1 := by simp

theorem conditionalTreePrefixWordLaw_bind_treeKernel (rate : ℝ≥0) (n : ℕ)
    {k : ℕ} (w : Fin k → Bool) :
    (conditionalTreePrefixWordLaw n w).bind
        (fun P => (treeKernel rate (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map (prefixAppend P)) =
      (bernoulliMeasure true false (infectionProbability rate
        (countsRunWord n w).susceptible)).bind (fun b =>
          (conditionalTreePrefixWordLaw n w).bind fun P =>
            (signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) b).map (prefixAppend P)) := by
  ext A hA
  rw [Measure.bind_apply hA (measurable_of_countable _).aemeasurable,
    Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ P, ∫⁻ b,
        ((signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) b).map (prefixAppend P)) A
        ∂bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible)
        ∂conditionalTreePrefixWordLaw n w := by
      apply lintegral_congr_ae
      filter_upwards [conditionalTreePrefixWordLaw_phase n w] with P hP
      have hc : (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).counts = countsRunWord n w := by
        rw [hP.2, countsPrefixWord_last]
      have hu := congrArg Counts.susceptible hc
      change (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).susceptible =
        (countsRunWord n w).susceptible at hu
      rw [Measure.map_apply (measurable_prefixAppend_right P) hA, treeKernel_apply, hu]
      apply lintegral_congr
      intro b
      exact (Measure.map_apply (measurable_prefixAppend_right P) hA).symm
    _ = ∫⁻ b, ∫⁻ P,
        ((signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) b).map (prefixAppend P)) A
        ∂conditionalTreePrefixWordLaw n w
        ∂bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible) :=
      lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
    _ = _ := by simp only [Measure.bind_apply hA (measurable_of_countable _).aemeasurable]

theorem treeFullLaw_prefix_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (Preorder.frestrictLe k) =
      (signWordLaw rate n k).bind (conditionalTreePrefixWordLaw n) := by
  rw [treeFullLaw, CountableMarkovChain.map_prefix]
  induction k with
  | zero =>
    rw [Kernel.partialTraj_self, Kernel.id_apply]
    simp [signWordLaw, conditionalTreePrefixWordLaw]
  | succ k ih =>
    rw [partialTraj_successor (treeKernel rate) (Nat.zero_le k), ih,
      Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_appended_transition (treeKernel rate) k).aemeasurable]
    conv_rhs => rw [signWordLaw]
    rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
    congr 1
    funext w
    rw [conditionalTreePrefixWordLaw_bind_treeKernel,
      Measure.bind_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    congr 1
    funext b
    exact (conditionalTreePrefixWordLaw_snoc n w b).symm

theorem conditionalTreePrefixWordLaw_map_last (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    (conditionalTreePrefixWordLaw n w).map (fun P => P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) =
      conditionalTreeWordLaw n w := by
  induction k with
  | zero => simp [conditionalTreePrefixWordLaw, conditionalTreeWordLaw]
  | succ k ih =>
    rw [conditionalTreePrefixWordLaw, Measure.map_bind
      (measurable_of_countable _).aemeasurable (measurable_pi_apply _).aemeasurable]
    have he (P : Prefix (E := TreeState) k) :
        ((signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (w (Fin.last k))).map
          (prefixAppend P)).map (fun Q => Q ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩) =
        signedTreeLaw (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩) (w (Fin.last k)) := by
      rw [Measure.map_map (measurable_pi_apply _) (measurable_prefixAppend_right P)]
      have hf : (fun Q : Prefix (E := TreeState) (k + 1) =>
          Q ⟨k + 1, Finset.mem_Iic.mpr le_rfl⟩) ∘ prefixAppend P = id := by
        funext z
        simp [prefixAppend]
      rw [hf, Measure.map_id]
    simp_rw [he]
    rw [conditionalTreeWordLaw, ← ih (Fin.init w),
      Measure.bind_map (measurable_pi_apply _).aemeasurable
        (measurable_of_countable _).aemeasurable]

/-- Joint law of every earlier count and the final plane state. It is
not inferred from separate endpoint or count marginal identities. -/
theorem treeFullLaw_countsPrefix_tree_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H =>
      ((fun i : Finset.Iic k => (H i.val).counts), (H k).tree)) =
      (signWordLaw rate n k).bind (fun w => (planeWordLaw w).map
        (fun s => (countsPrefixWord n w, s))) := by
  have hf : (fun H : ℕ → TreeState =>
      ((fun i : Finset.Iic k => (H i.val).counts), (H k).tree)) =
      (fun P : Prefix (E := TreeState) k =>
        ((fun i => (P i).counts), (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).tree)) ∘
        Preorder.frestrictLe k := rfl
  have hG : Measurable (fun P : Prefix (E := TreeState) k =>
      ((fun i => (P i).counts), (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).tree)) :=
    measurable_of_countable _
  rw [hf, ← Measure.map_map hG (Preorder.measurable_frestrictLe k),
    treeFullLaw_prefix_word_mixture,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [signWordLaw_feasible rate n k] with w hw
  calc
    _ = (conditionalTreePrefixWordLaw n w).map (fun P =>
        (countsPrefixWord n w, (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).tree)) := by
      apply Measure.map_congr
      filter_upwards [conditionalTreePrefixWordLaw_phase n w] with P hP
      exact congrArg (fun c => (c, (P ⟨k, Finset.mem_Iic.mpr le_rfl⟩).tree)) (funext hP.2)
    _ = ((conditionalTreePrefixWordLaw n w).map
        (fun P => P ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).map
          (fun z => (countsPrefixWord n w, z.tree)) := by
      rw [Measure.map_map (measurable_of_countable
        (fun z : TreeState => (countsPrefixWord n w, z.tree)))
          (measurable_pi_apply (⟨k, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic k))]
      rfl
    _ = (planeWordLaw w).map (fun s => (countsPrefixWord n w, s)) := by
      rw [conditionalTreePrefixWordLaw_map_last,
        ← conditionalTreeWordLaw_map_tree_feasible n w hw,
        Measure.map_map (measurable_of_countable
          (fun s : PlaneForward.State => (countsPrefixWord n w, s)))
          (measurable_of_countable TreeState.tree)]
      rfl

end Freezing1.SIR
