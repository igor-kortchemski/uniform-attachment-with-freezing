module

public import Freezing1.SIRTreeLaw
public import Freezing1.SIRSignWords
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Actual infection-tree laws as mixtures over adaptive potential signs

The conditional law of the counts is deterministic given the finite sign
word. Thus its susceptible count supplies the correct next-sign parameter.
Before the population horizon the capacity guard does not change the plane
attachment/freezing kernel. No independence of the SIR signs is assumed.
-/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def conditionalTreeWordLaw (n : ℕ) : {k : ℕ} → (Fin k → Bool) → Measure TreeState
  | 0, _ => Measure.dirac (initialTreeState n)
  | k+1, w => (conditionalTreeWordLaw n (Fin.init w)).bind
      (fun z => signedTreeLaw z (w (Fin.last k)))

instance conditionalTreeWordLaw_probability (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    IsProbabilityMeasure (conditionalTreeWordLaw n w) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    have := ih (Fin.init w)
    exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Eventually.of_forall fun z => signedTreeLaw_probability z _)

theorem conditionalTreeWordLaw_snoc (n : ℕ) {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    conditionalTreeWordLaw n (Fin.snoc w b) =
      (conditionalTreeWordLaw n w).bind (fun z => signedTreeLaw z b) := by
  simp only [conditionalTreeWordLaw, Fin.init_snoc, Fin.snoc_last]

theorem conditionalTreeWordLaw_phase (n : ℕ) {k : ℕ} (w : Fin k → Bool) :
    ∀ᵐ z ∂conditionalTreeWordLaw n w, z.Valid n ∧ z.counts = countsRunWord n w := by
  induction k with
  | zero => simp [conditionalTreeWordLaw, countsRunWord, initialTreeState_valid]
  | succ k ih =>
    apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
    rw [conditionalTreeWordLaw, Measure.bind_apply (by measurability)
      (measurable_of_countable _).aemeasurable]
    calc
      _ = ∫⁻ _z, (1 : ℝ≥0∞) ∂conditionalTreeWordLaw n (Fin.init w) := by
        apply lintegral_congr_ae
        filter_upwards [ih (Fin.init w)] with z hz
        apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
        apply signedTreeLaw_ae
        · intro he
          refine ⟨hz.1, ?_⟩
          change z.counts = countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))
          have hi : z.counts.infectious = 0 := by simp [TreeState.counts, he]
          rw [← hz.2, countsStep_of_absorbed hi]
        · intro u hu
          refine ⟨hz.1.step _ _, ?_⟩
          change (treeStep z (w (Fin.last k)) u).counts =
            countsStep (countsRunWord n (Fin.init w)) (w (Fin.last k))
          rw [treeStep_counts hz.1.1 hu, hz.2]
      _ = 1 := by rw [lintegral_one, measure_univ]

theorem conditionalTreeWordLaw_bind_treeKernel (rate : ℝ≥0) (n : ℕ)
    {k : ℕ} (w : Fin k → Bool) :
    (conditionalTreeWordLaw n w).bind (treeKernel rate) =
      (bernoulliMeasure true false (infectionProbability rate
        (countsRunWord n w).susceptible)).bind (fun b =>
          (conditionalTreeWordLaw n w).bind (fun z => signedTreeLaw z b)) := by
  ext A hA
  rw [Measure.bind_apply hA (treeKernel rate).aemeasurable,
    Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  calc
    _ = ∫⁻ z, ∫⁻ b, signedTreeLaw z b A
        ∂bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible)
          ∂conditionalTreeWordLaw n w := by
      apply lintegral_congr_ae
      filter_upwards [conditionalTreeWordLaw_phase n w] with z hz
      have hu : z.susceptible = (countsRunWord n w).susceptible :=
        congrArg Counts.susceptible hz.2
      rw [treeKernel_apply, hu]
    _ = ∫⁻ b, ∫⁻ z, signedTreeLaw z b A ∂conditionalTreeWordLaw n w
        ∂bernoulliMeasure true false (infectionProbability rate (countsRunWord n w).susceptible) :=
      lintegral_lintegral_swap (measurable_of_countable _).aemeasurable
    _ = _ := by
      simp only [Measure.bind_apply hA (measurable_of_countable _).aemeasurable]

theorem treeFullLaw_eval_word_mixture (rate : ℝ≥0) (n k : ℕ) :
    (treeFullLaw rate n).map (fun H => H k) =
      (signWordLaw rate n k).bind (conditionalTreeWordLaw n) := by
  induction k with
  | zero =>
    rw [treeFullLaw, CountableMarkovChain.map_eval_zero]
    simp [signWordLaw, conditionalTreeWordLaw]
  | succ k ih =>
    rw [treeFullLaw, CountableMarkovChain.map_eval_succ]
    change ((treeFullLaw rate n).map (fun H => H k)).bind (treeKernel rate) = _
    rw [ih, Measure.bind_bind (measurable_of_countable _).aemeasurable
      (treeKernel rate).aemeasurable]
    conv_rhs => rw [signWordLaw]
    rw [Measure.bind_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
    congr 1
    funext w
    rw [conditionalTreeWordLaw_bind_treeKernel,
      Measure.bind_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    congr 1
    funext b
    exact (conditionalTreeWordLaw_snoc n w b).symm

noncomputable def planeWordLaw : {k : ℕ} → (Fin k → Bool) → Measure PlaneForward.State
  | 0, _ => Measure.dirac PlaneForward.initial
  | k+1, w => (planeWordLaw (Fin.init w)).bind
      (fun s => PlaneForward.signedTransitionLaw s (w (Fin.last k)))

instance planeWordLaw_probability {k : ℕ} (w : Fin k → Bool) :
    IsProbabilityMeasure (planeWordLaw w) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac _); infer_instance
  | succ k ih =>
    have := ih (Fin.init w)
    exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Eventually.of_forall fun s => PlaneForward.signedTransitionLaw_probability s _)

theorem planeWordLaw_snoc {k : ℕ} (w : Fin k → Bool) (b : Bool) :
    planeWordLaw (Fin.snoc w b) =
      (planeWordLaw w).bind (fun s => PlaneForward.signedTransitionLaw s b) := by
  simp only [planeWordLaw, Fin.init_snoc, Fin.snoc_last]

theorem treeStep_tree_of_susceptible_pos {z : TreeState} (hu : 0 < z.susceptible)
    (b : Bool) (u : PlaneTree.Address) :
    (treeStep z b u).tree = PlaneForward.step z.tree b u := by
  unfold treeStep PlaneForward.step
  split_ifs <;> simp_all [infectTreeState, recoverTreeState]

theorem signedTreeLaw_tree_of_susceptible_pos {z : TreeState} (hu : 0 < z.susceptible)
    (b : Bool) : (signedTreeLaw z b).map TreeState.tree =
      PlaneForward.signedTransitionLaw z.tree b := by
  unfold signedTreeLaw PlaneForward.signedTransitionLaw
  split_ifs with ha
  · rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext u
    exact treeStep_tree_of_susceptible_pos hu b u
  · simp

theorem conditionalTreeWordLaw_map_tree (n : ℕ) {k : ℕ} (w : Fin k → Bool) (hk : k ≤ n) :
    (conditionalTreeWordLaw n w).map TreeState.tree = planeWordLaw w := by
  induction k with
  | zero => simp [conditionalTreeWordLaw, planeWordLaw, initialTreeState]
  | succ k ih =>
    rw [conditionalTreeWordLaw, Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
    change (conditionalTreeWordLaw n (Fin.init w)).bind
      (fun z => (signedTreeLaw z (w (Fin.last k))).map TreeState.tree) =
        (planeWordLaw (Fin.init w)).bind
          (fun s => PlaneForward.signedTransitionLaw s (w (Fin.last k)))
    rw [← ih (Fin.init w) (by omega), Measure.bind_map
      (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [conditionalTreeWordLaw_phase n (Fin.init w)] with z hz
    apply signedTreeLaw_tree_of_susceptible_pos
    have hu := (countsRunWord_susceptible_bounds n (Fin.init w)).1
    have hzU : z.susceptible = (countsRunWord n (Fin.init w)).susceptible :=
      congrArg Counts.susceptible hz.2
    omega

/-- The requested fixed early-horizon law, averaged over the true adaptive
SIR signs rather than an assumed iid sequence. -/
theorem treeFullLaw_plane_word_mixture (rate : ℝ≥0) (n k : ℕ) (hk : k ≤ n) :
    (treeFullLaw rate n).map (fun H => (H k).tree) =
      (signWordLaw rate n k).bind planeWordLaw := by
  change (treeFullLaw rate n).map (TreeState.tree ∘ (fun H => H k)) = _
  rw [← Measure.map_map (measurable_of_countable (TreeState.tree)) (measurable_pi_apply k),
    treeFullLaw_eval_word_mixture,
    Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  congr 1
  funext w
  exact conditionalTreeWordLaw_map_tree n w hk

private theorem bind_snoc_singleton {k : ℕ} (μ : Measure (Fin k → Bool))
    (β : (Fin k → Bool) → Measure Bool) (w : Fin (k+1) → Bool) :
    (μ.bind (fun v => (β v).map (Fin.snoc v))) {w} =
      μ {Fin.init w} * β (Fin.init w) {w (Fin.last k)} := by
  rw [Measure.bind_apply (measurableSet_singleton w) (measurable_of_countable _).aemeasurable]
  have he (v : Fin k → Bool) : (Fin.snoc v) ⁻¹' {w} =
      if v = Fin.init w then {w (Fin.last k)} else ∅ := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff, snoc_eq_iff]
    by_cases hv : v = Fin.init w <;> simp [hv]
  calc
    _ = ∫⁻ v, ({Fin.init w} : Set (Fin k → Bool)).indicator
        (fun _ => β (Fin.init w) {w (Fin.last k)}) v ∂μ := by
      apply lintegral_congr
      intro v
      rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton w), he v]
      by_cases hv : v = Fin.init w <;> simp [hv]
    _ = β (Fin.init w) {w (Fin.last k)} * μ {Fin.init w} :=
      lintegral_indicator_const (measurableSet_singleton _) _
    _ = _ := mul_comm _ _

theorem finiteSignLaw_snoc_bind (p : unitInterval) (k : ℕ) :
    ForwardAnnealed.finiteSignLaw p (k+1) =
      (ForwardAnnealed.finiteSignLaw p k).bind (fun w =>
        (bernoulliMeasure true false p).map (Fin.snoc w)) := by
  apply Measure.ext_of_singleton
  intro w
  rw [bind_snoc_singleton]
  simp only [ForwardAnnealed.finiteSignLaw, ForwardAnnealed.signLaw,
    Measure.pi_singleton, Fin.prod_univ_castSucc, Fin.init]

private theorem planeWordLaw_bind_transition (p : unitInterval) {k : ℕ} (w : Fin k → Bool) :
    (planeWordLaw w).bind (PlaneForward.transition p) =
      (bernoulliMeasure true false p).bind (fun b =>
        (planeWordLaw w).bind (fun s => PlaneForward.signedTransitionLaw s b)) := by
  ext A hA
  rw [Measure.bind_apply hA (PlaneForward.transition p).aemeasurable,
    Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  simp_rw [PlaneForward.transition_apply,
    Measure.bind_apply hA (measurable_of_countable _).aemeasurable]
  exact lintegral_lintegral_swap (measurable_of_countable _).aemeasurable

theorem planeWordLaw_iid_mixture (p : unitInterval) (k : ℕ) :
    (ForwardAnnealed.finiteSignLaw p k).bind planeWordLaw =
      (PlaneForward.fullLaw p PlaneForward.initial).map (fun H => H k) := by
  symm
  induction k with
  | zero =>
    rw [PlaneForward.fullLaw, CountableMarkovChain.map_eval_zero]
    simp [ForwardAnnealed.finiteSignLaw, planeWordLaw]
  | succ k ih =>
    rw [PlaneForward.fullLaw, CountableMarkovChain.map_eval_succ]
    change ((PlaneForward.fullLaw p PlaneForward.initial).map (fun H => H k)).bind
      (PlaneForward.transition p) = _
    rw [ih, Measure.bind_bind (measurable_of_countable _).aemeasurable
      (PlaneForward.transition p).aemeasurable, finiteSignLaw_snoc_bind,
      Measure.bind_bind (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    congr 1
    funext w
    rw [planeWordLaw_bind_transition,
      Measure.bind_map (measurable_of_countable _).aemeasurable
        (measurable_of_countable _).aemeasurable]
    congr 1
    funext b
    exact (planeWordLaw_snoc w b).symm

private theorem finite_mixture_real_apply {ι : Type*} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] [Fintype ι] (μ : Measure ι) [IsProbabilityMeasure μ]
    (K : ι → Measure PlaneForward.State) [∀ i, IsProbabilityMeasure (K i)]
    (A : Set PlaneForward.State) :
    (μ.bind K).real A = ∑ i, μ.real {i} * (K i).real A := by
  simp only [measureReal_def]
  rw [Measure.bind_apply (Set.to_countable A).measurableSet
    (measurable_of_countable _).aemeasurable, lintegral_fintype,
    ENNReal.toReal_sum (by intros; finiteness)]
  simp only [ENNReal.toReal_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem planeWordLaw_mixture_abs_sub_le {k : ℕ}
    (μ ν : Measure (Fin k → Bool)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set PlaneForward.State) :
    |(μ.bind planeWordLaw).real A - (ν.bind planeWordLaw).real A| ≤
      ∑ w : Fin k → Bool, |μ.real {w} - ν.real {w}| := by
  rw [finite_mixture_real_apply, finite_mixture_real_apply, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w : Fin k → Bool, |μ.real {w} * (planeWordLaw w).real A -
        ν.real {w} * (planeWordLaw w).real A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro w _
      rw [← sub_mul, abs_mul, abs_of_nonneg measureReal_nonneg]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (measureReal_le_one : (planeWordLaw w).real A ≤ 1) (abs_nonneg (μ.real {w} - ν.real {w}))

noncomputable def signWordError (rate : ℝ≥0) (n : ℕ) (p : unitInterval) (k : ℕ) : ℝ :=
  ∑ w : Fin k → Bool, |(signWordLaw rate n k).real {w} -
    (ForwardAnnealed.finiteSignLaw p k).real {w}|

theorem signWordError_tendsto_zero (rate : ℕ → ℝ≥0) (l : ℝ≥0)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (l : ℝ))) (k : ℕ) :
    Tendsto (fun n => signWordError (rate n) n (infectionProbability l 1) k)
      atTop (𝓝 0) := by
  have hh := tendsto_finsetSum Finset.univ (fun w (_ : w ∈ (Finset.univ : Finset (Fin k → Bool))) =>
    ((signWordLaw_singleton_tendsto rate l hl k w).sub
      (tendsto_const_nhds (x := (ForwardAnnealed.finiteSignLaw (infectionProbability l 1) k).real {w}))).abs)
  simpa only [signWordError, sub_self, abs_zero, Finset.sum_const_zero] using hh

theorem signWordError_tendsto_zero_strong (rate : ℕ → ℝ≥0)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop) (k : ℕ) :
    Tendsto (fun n => signWordError (rate n) n 1 k) atTop (𝓝 0) := by
  have hh := tendsto_finsetSum Finset.univ (fun w (_ : w ∈ (Finset.univ : Finset (Fin k → Bool))) =>
    ((signWordLaw_singleton_tendsto_one rate hl k w).sub
      (tendsto_const_nhds (x := (ForwardAnnealed.finiteSignLaw 1 k).real {w}))).abs)
  simpa only [signWordError, sub_self, abs_zero, Finset.sum_const_zero] using hh

theorem treeFullLaw_plane_event_error_le (rate : ℝ≥0) (n k : ℕ) (hk : k ≤ n)
    (p : unitInterval) (A : Set PlaneForward.State) :
    |((treeFullLaw rate n).map (fun H => (H k).tree)).real A -
      ((PlaneForward.fullLaw p PlaneForward.initial).map (fun H => H k)).real A| ≤
        signWordError rate n p k := by
  rw [treeFullLaw_plane_word_mixture rate n k hk, ← planeWordLaw_iid_mixture]
  exact planeWordLaw_mixture_abs_sub_le _ _ A

/-- At every fixed early horizon, one error bound works simultaneously
for every state event. The SIR signs themselves remain adaptive. -/
theorem treeFullLaw_plane_events_tendsto (rate : ℕ → ℝ≥0) (l : ℝ≥0)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (l : ℝ)))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ A : Set PlaneForward.State,
      |((treeFullLaw (rate n) n).map (fun H => (H k).tree)).real A -
        ((PlaneForward.fullLaw (infectionProbability l 1) PlaneForward.initial).map
          (fun H => H k)).real A| < ε := by
  have he := (tendsto_order.mp (signWordError_tendsto_zero rate l hl k)).2 ε hε
  filter_upwards [he, eventually_ge_atTop k] with n hn hnk
  intro A
  exact (treeFullLaw_plane_event_error_le (rate n) n k hnk _ A).trans_lt hn

theorem treeFullLaw_plane_events_tendsto_strong (rate : ℕ → ℝ≥0)
    (hl : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ A : Set PlaneForward.State,
      |((treeFullLaw (rate n) n).map (fun H => (H k).tree)).real A -
        ((PlaneForward.fullLaw 1 PlaneForward.initial).map (fun H => H k)).real A| < ε := by
  have he := (tendsto_order.mp (signWordError_tendsto_zero_strong rate hl k)).2 ε hε
  filter_upwards [he, eventually_ge_atTop k] with n hn hnk
  intro A
  exact (treeFullLaw_plane_event_error_le (rate n) n k hnk _ A).trans_lt hn

end Freezing1.SIR
