module

public import Freezing1.SIRTreeState
public import Freezing1.SIRCountLaw
public import Freezing1.ForwardPlaneKernel
public import Freezing1.PlaneGraftHistory

/-!
# Genuine finite-population infection-tree kernels

At each event a uniform infectious vertex is chosen, and the fresh infection
sign has probability depending on the susceptible count. The full chain is
held after extinction. Its count projection is proved to be the embedded
SIR count chain, not imposed as an assumption.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

noncomputable def signedTreeLaw (z : TreeState) (sign : Bool) : Measure TreeState :=
  if z.tree.active.Nonempty then
    (Measure.uniformOfFinset z.tree.active).map (treeStep z sign)
  else Measure.dirac z

instance signedTreeLaw_probability (z : TreeState) (sign : Bool) :
    IsProbabilityMeasure (signedTreeLaw z sign) := by
  unfold signedTreeLaw
  split_ifs with h
  · have := PlaneForward.uniform_active_probability z.tree h
    exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
      |>.mpr inferInstance
  · infer_instance

theorem signedTreeLaw_absorbed {z : TreeState} (hz : z.tree.active = ∅) (sign : Bool) :
    signedTreeLaw z sign = Measure.dirac z := by simp [signedTreeLaw, hz]

theorem signedTreeLaw_apply (z : TreeState) (sign : Bool) (hz : z.tree.active.Nonempty)
    (A : Set TreeState) :
    signedTreeLaw z sign A =
      ((z.tree.active.filter (fun u => treeStep z sign u ∈ A)).card : ℝ≥0∞) /
        z.tree.active.card := by
  rw [signedTreeLaw, ite_eq_left hz,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable A).measurableSet,
    Measure.uniformOfFinset_apply]
  rfl

theorem signedTreeLaw_ae (z : TreeState) (sign : Bool) (P : TreeState → Prop)
    (hhold : z.tree.active = ∅ → P z)
    (hstep : ∀ u ∈ z.tree.active, P (treeStep z sign u)) :
    ∀ᵐ w ∂signedTreeLaw z sign, P w := by
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  by_cases hz : z.tree.active.Nonempty
  · rw [signedTreeLaw_apply z sign hz]
    have he : z.tree.active.filter (fun u => treeStep z sign u ∈ {w | P w}) =
        z.tree.active := Finset.filter_eq_self.mpr hstep
    rw [he]
    exact ENNReal.div_self (by exact_mod_cast hz.card_pos.ne') (by simp)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hz
    rw [signedTreeLaw_absorbed he]
    simp [hhold he]

noncomputable def treeKernel (rate : ℝ≥0) : Kernel TreeState TreeState where
  toFun z := (bernoulliMeasure true false (infectionProbability rate z.susceptible)).bind
    (signedTreeLaw z)
  measurable' := measurable_of_countable _

instance treeKernel_markov (rate : ℝ≥0) : IsMarkovKernel (treeKernel rate) := by
  constructor
  intro z
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Filter.Eventually.of_forall fun sign => signedTreeLaw_probability z sign)

theorem treeKernel_apply (rate : ℝ≥0) (z : TreeState) (A : Set TreeState) :
    treeKernel rate z A = ∫⁻ sign, signedTreeLaw z sign A
      ∂bernoulliMeasure true false (infectionProbability rate z.susceptible) :=
  Measure.bind_apply (Set.to_countable A).measurableSet (measurable_of_countable _).aemeasurable

theorem treeKernel_valid (rate : ℝ≥0) {n : ℕ} {z : TreeState} (hz : z.Valid n) :
    ∀ᵐ w ∂treeKernel rate z, w.Valid n := by
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  rw [treeKernel_apply]
  calc
    _ = ∫⁻ _sign, (1 : ℝ≥0∞)
        ∂bernoulliMeasure true false (infectionProbability rate z.susceptible) := by
      apply lintegral_congr_ae
      apply Filter.Eventually.of_forall
      intro sign
      apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
      exact signedTreeLaw_ae z sign (TreeState.Valid n) (fun _ => hz)
        (fun u _ => hz.step sign u)
    _ = 1 := by rw [lintegral_one, measure_univ]

theorem signedTreeLaw_counts {z : TreeState} (hz : PlaneForward.Valid z.tree)
    (sign : Bool) :
    (signedTreeLaw z sign).map TreeState.counts = Measure.dirac (countsStep z.counts sign) := by
  classical
  ext A hA
  rw [Measure.map_apply (measurable_of_countable _) hA]
  by_cases ha : z.tree.active.Nonempty
  · rw [signedTreeLaw_apply z sign ha]
    have hfilter : z.tree.active.filter
        (fun u => treeStep z sign u ∈ TreeState.counts ⁻¹' A) =
        if countsStep z.counts sign ∈ A then z.tree.active else ∅ := by
      ext u
      by_cases hu : u ∈ z.tree.active
      · simp only [Finset.mem_filter, hu, true_and, Set.mem_preimage,
          treeStep_counts hz hu sign]
        split_ifs <;> simp_all
      · simp only [Finset.mem_filter, hu, false_and]
        split_ifs <;> simp_all
    rw [hfilter, Measure.dirac_apply' _ hA]
    by_cases hm : countsStep z.counts sign ∈ A
    · simp only [hm, ite_true, Set.indicator_of_mem, Pi.one_apply]
      exact ENNReal.div_self (by exact_mod_cast ha.card_pos.ne') (by simp)
    · simp [hm]
  · have he : z.tree.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    rw [signedTreeLaw_absorbed he]
    have hc : z.counts.infectious = 0 := by simp [TreeState.counts, he]
    rw [countsStep_of_absorbed hc, Measure.dirac_apply' _ (hA.preimage (measurable_of_countable _)),
      Measure.dirac_apply' _ hA]
    rfl

theorem treeKernel_counts (rate : ℝ≥0) {z : TreeState} (hz : PlaneForward.Valid z.tree) :
    (treeKernel rate z).map TreeState.counts = countsKernel rate z.counts := by
  change ((bernoulliMeasure true false (infectionProbability rate z.susceptible)).bind
    (signedTreeLaw z)).map TreeState.counts = _
  rw [Measure.map_bind (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aemeasurable]
  simp_rw [signedTreeLaw_counts hz]
  change (bernoulliMeasure true false (infectionProbability rate z.susceptible)).bind
    (Measure.dirac ∘ countsStep z.counts) =
    (bernoulliMeasure true false (infectionProbability rate z.susceptible)).map
      (countsStep z.counts)
  exact Measure.bind_dirac_eq_map _ (measurable_of_countable _)

noncomputable def treeFullLaw (rate : ℝ≥0) (n : ℕ) : Measure (ℕ → TreeState) :=
  CountableMarkovChain.fullLaw (treeKernel rate) (initialTreeState n)

instance treeFullLaw_probability (rate : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (treeFullLaw rate n) := by unfold treeFullLaw; infer_instance

theorem treeFullLaw_valid (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n, ∀ k, (H k).Valid n := by
  apply ae_all_iff.mpr
  intro k
  apply (ae_map_iff (measurable_pi_apply k).aemeasurable (by trivial)).mp
  induction k with
  | zero =>
    rw [treeFullLaw, CountableMarkovChain.map_eval_zero]
    simp [initialTreeState_valid]
  | succ k ih =>
    rw [treeFullLaw, CountableMarkovChain.map_eval_succ]
    apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
    rw [Measure.bind_apply (by trivial) (treeKernel rate).aemeasurable]
    calc
      _ = ∫⁻ _z, (1 : ℝ≥0∞)
          ∂(CountableMarkovChain.fullLaw (treeKernel rate) (initialTreeState n)).map
            (fun H => H k) := by
        apply lintegral_congr_ae
        filter_upwards [ih] with z hz
        exact (ae_iff_prob_eq_one (measurable_of_countable _)).mp (treeKernel_valid rate hz)
      _ = 1 := by rw [lintegral_one, measure_univ]

theorem map_treeFullLaw_counts (rate : ℝ≥0) (n : ℕ) :
    (treeFullLaw rate n).map (fun H k => (H k).counts) = countsFullLaw rate n := by
  change (CountableMarkovChain.fullLaw (treeKernel rate) (initialTreeState n)).map
    (fun H k => TreeState.counts (H k)) = _
  rw [show countsFullLaw rate n = CountableMarkovChain.fullLaw (countsKernel rate)
    (TreeState.counts (initialTreeState n)) by rw [counts_initialTreeState]; rfl]
  apply CountableMarkovChain.map_fullLaw_of_ae_intertwining
  intro k
  filter_upwards [treeFullLaw_valid rate n] with H hH
  exact treeKernel_counts rate (hH k).1

end Freezing1.SIR
