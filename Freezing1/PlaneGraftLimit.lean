module

public import Freezing1.PlaneGraftHistory
public import Freezing1.PlaneGraftShape
public import Freezing1.PlaneChainLimit
public import Freezing1.PlaneInterleavingFairness
public import Freezing1.InterleavedChainsIndependent
public import Freezing1.InterleavedLimitTransfer
public import Freezing1.ProbabilityLawConvergence

/-!
# The actual graft-chain limit is the graft of independent copies

L06 is applied to the genuine interleaved chain with its proved global
fairness. Exact-clock convergence transfers to global time even when a
coordinate is selected only finitely often. The full graft-history identity
then yields weak convergence of the actual chain started after one birth.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Classical

noncomputable def extractedLimitPair (H : ℕ → InterleavedChain.State State) :
    PlaneTree.Tree × PlaneTree.Tree :=
  (chainLimit (InterleavedChain.extracted H true),
    chainLimit (InterleavedChain.extracted H false))

private theorem extracted_pair_law (p : unitInterval) (hp : (p : ℝ) < 1) :
    (InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
      (fun H => (InterleavedChain.extracted H true, InterleavedChain.extracted H false)) =
      (fullLaw p initial).prod (fullLaw p initial) :=
  InterleavedChain.extracted_pair_map_eq_prod (transition p) selectionParameter
    (interleaving_fair p hp) initial initial true

theorem aemeasurable_extractedLimitPair (p : unitInterval) (hp : (p : ℝ) < 1) :
    AEMeasurable extractedLimitPair
      (InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)) := by
  have hprod : AEMeasurable (Prod.map chainLimit chainLimit)
      ((fullLaw p initial).prod (fullLaw p initial)) := by
    have hl := aemeasurable_chainLimit p hp
    fun_prop
  have hmap : AEMeasurable (Prod.map chainLimit chainLimit)
      ((InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
        (fun H => (InterleavedChain.extracted H true, InterleavedChain.extracted H false))) := by
    rw [extracted_pair_law p hp]
    exact hprod
  exact hmap.comp_aemeasurable
    ((InterleavedChain.measurable_extracted true).prodMk
      (InterleavedChain.measurable_extracted false)).aemeasurable

theorem map_extractedLimitPair (p : unitInterval) (hp : (p : ℝ) < 1) :
    (InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
      extractedLimitPair =
        (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree).prod
          (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree) := by
  have hprod : AEMeasurable (Prod.map chainLimit chainLimit)
      ((fullLaw p initial).prod (fullLaw p initial)) := by
    have hl := aemeasurable_chainLimit p hp
    fun_prop
  have hmap : AEMeasurable (Prod.map chainLimit chainLimit)
      ((InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
        (fun H => (InterleavedChain.extracted H true, InterleavedChain.extracted H false))) := by
    rw [extracted_pair_law p hp]
    exact hprod
  change (InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
    (Prod.map chainLimit chainLimit ∘
      (fun H => (InterleavedChain.extracted H true, InterleavedChain.extracted H false))) = _
  rw [← AEMeasurable.map_map_of_aemeasurable hmap
    ((InterleavedChain.measurable_extracted true).prodMk
      (InterleavedChain.measurable_extracted false)).aemeasurable,
    extracted_pair_law p hp, ← Measure.map_prod_map_of_aemeasurable
      (fullLaw p initial) (fullLaw p initial) (aemeasurable_chainLimit p hp)
        (aemeasurable_chainLimit p hp), map_fullLaw_chainLimit p hp]

theorem interleaved_fullLaw_tendsto_graft (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true),
      Tendsto (fun n => shape (graft (H n).1 (H n).2.1)) atTop
        (𝓝 (PlaneTree.graft (extractedLimitPair H).1 (extractedLimitPair H).2)) := by
  have hleft : ∀ᵐ q ∂(fullLaw p initial).prod (fullLaw p initial),
      Tendsto (fun n => shape (q.1 n)) atTop (𝓝 (chainLimit q.1)) := by
    apply ae_of_ae_map (μ := (fullLaw p initial).prod (fullLaw p initial))
      (f := Prod.fst)
      (p := fun H : ℕ → State => Tendsto (fun n => shape (H n)) atTop (𝓝 (chainLimit H)))
      measurable_fst.aemeasurable
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    exact fullLaw_tendsto_chainLimit p hp
  have hright : ∀ᵐ q ∂(fullLaw p initial).prod (fullLaw p initial),
      Tendsto (fun n => shape (q.2 n)) atTop (𝓝 (chainLimit q.2)) := by
    apply ae_of_ae_map (μ := (fullLaw p initial).prod (fullLaw p initial))
      (f := Prod.snd)
      (p := fun H : ℕ → State => Tendsto (fun n => shape (H n)) atTop (𝓝 (chainLimit H)))
      measurable_snd.aemeasurable
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
    exact fullLaw_tendsto_chainLimit p hp
  have hpair := hleft.and hright
  rw [← extracted_pair_law p hp] at hpair
  have hsource := ae_of_ae_map
    ((InterleavedChain.measurable_extracted true).prodMk
      (InterleavedChain.measurable_extracted false)).aemeasurable hpair
  filter_upwards [hsource, interleaved_fullLaw_valid p,
    InterleavedChain.fullLaw_movesOnlySelected (transition p) selectionParameter
      (initial, initial, true)] with H hc hv hm
  have hl := InterleavedChain.tendsto_coordinate_of_extracted H hm true shape hc.1
  have hr := InterleavedChain.tendsto_coordinate_of_extracted H hm false shape hc.2
  simp only [InterleavedChain.coordinate, ite_true, Bool.false_eq_true, ite_false] at hl hr
  have hg := (PlaneTree.continuous_graft.tendsto _).comp (hl.prodMk_nhds hr)
  apply hg.congr'
  exact Filter.Eventually.of_forall fun n => (shape_graft (hv n).1 (hv n).2).symm

noncomputable def graftProbabilityLaw (p : unitInterval) (n : ℕ) :
    ProbabilityMeasure PlaneTree.Tree :=
  ProbabilityMeasure.map
    (⟨fullLaw p (graft initial initial), inferInstance⟩ : ProbabilityMeasure (ℕ → State))
    (fun H => shape (H n))

noncomputable def graftLimitLaw (p : unitInterval) : ProbabilityMeasure PlaneTree.Tree :=
  ProbabilityMeasure.map
    (⟨(ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree).prod
      (ForwardAnnealed.planeLimitLaw p : Measure PlaneTree.Tree), inferInstance⟩ :
      ProbabilityMeasure (PlaneTree.Tree × PlaneTree.Tree))
    (fun q => PlaneTree.graft q.1 q.2)

theorem tendsto_graftProbabilityLaw (p : unitInterval) (hp : (p : ℝ) < 1) :
    Tendsto (graftProbabilityLaw p) atTop (𝓝 (graftLimitLaw p)) := by
  let μ : ProbabilityMeasure (ℕ → InterleavedChain.State State) :=
    ⟨InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true),
      inferInstance⟩
  let F : ℕ → (ℕ → InterleavedChain.State State) → PlaneTree.Tree :=
    fun n H => shape (graft (H n).1 (H n).2.1)
  let f : (ℕ → InterleavedChain.State State) → PlaneTree.Tree :=
    fun H => PlaneTree.graft (extractedLimitPair H).1 (extractedLimitPair H).2
  have hmF : ∀ n, Measurable (F n) := fun n =>
    (measurable_of_countable (fun s : InterleavedChain.State State => shape (graft s.1 s.2.1))).comp
      (measurable_pi_apply n)
  have hmf : AEMeasurable f (μ : Measure _) :=
    PlaneTree.continuous_graft.measurable.comp_aemeasurable (aemeasurable_extractedLimitPair p hp)
  have hw := tendsto_probability_map_of_ae_tendsto μ F f hmF hmf
    (interleaved_fullLaw_tendsto_graft p hp)
  have hleft : ∀ n, μ.map (F n) = graftProbabilityLaw p n := by
    intro n
    apply ProbabilityMeasure.toMeasure_injective
    change (μ : Measure _).map (F n) =
      (fullLaw p (graft initial initial)).map (fun H => shape (H n))
    rw [← map_interleaved_fullLaw_graft p]
    have hmGraft : Measurable (fun H : ℕ → InterleavedChain.State State =>
        fun n => graft (H n).1 (H n).2.1) :=
      Measurable.of_eval fun n => (measurable_of_countable
        (fun s : InterleavedChain.State State => graft s.1 s.2.1)).comp (measurable_pi_apply n)
    exact (Measure.map_map (measurable_shape_eval n) hmGraft).symm
  have hright : μ.map f = graftLimitLaw p := by
    apply ProbabilityMeasure.toMeasure_injective
    change (InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
      ((fun q => PlaneTree.graft q.1 q.2) ∘ extractedLimitPair) = _
    rw [← AEMeasurable.map_map_of_aemeasurable
      PlaneTree.continuous_graft.measurable.aemeasurable (aemeasurable_extractedLimitPair p hp)]
    change ((InterleavedChain.fullLaw (transition p) selectionParameter (initial, initial, true)).map
      extractedLimitPair).map (fun q => PlaneTree.graft q.1 q.2) = _
    rw [map_extractedLimitPair p hp]
    rfl
  simpa only [hleft, hright] using hw

end Freezing1.PlaneForward
