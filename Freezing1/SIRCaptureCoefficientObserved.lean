module

public import Freezing1.SIRCaptureCoefficientLaw
public import Freezing1.CanonicalReverseBirthClock
public import Freezing1.UniformPairDistance
public import Freezing1.ForwardSupportCharacterization

/-! Same-epsilon capture for the actual terminal uniform vertex and its genuine reverse clock. -/

@[expose] public section

namespace Freezing1.SIR

open Filter MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal Topology

set_option backward.isDefEq.respectTransparency false

noncomputable def wordObservedBirthKernel (n : ℕ) (w : Fin (2 * n + 1) → Bool) : Measure ℕ :=
  (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).bind fun s =>
    (Measure.uniformOfFinset s.vertices).map (Forward.reverseBirthClock (captureWordExtinction n w) s)

instance wordObservedBirthKernel_probability (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    IsProbabilityMeasure (wordObservedBirthKernel n w) := by
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) (2 * n + 1)] with s hs
  have := Forward.uniform_vertices_probability s ⟨0, hs.root_mem⟩
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance

theorem wordObservedBirthKernel_eq_reverse (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) : wordObservedBirthKernel n w = wordReverseBirthKernel n w := by
  have hs := captureWordExtinction_spec n w hw
  have h := CanonicalTree.forward_terminal_reverseBirthLaw hs.2.1 (2 * n + 1 - captureWordExtinction n w)
  rw [wordReverseBirthKernel, ite_eq_left hw]
  unfold wordObservedBirthKernel
  exact (by simpa only [Nat.add_sub_of_le hs.1] using h)

/-- Actual conditional uniform sampling from the complete original forward
tree, with the native freezing clock; adaptive word weights are retained. -/
noncomputable def actualTerminalReverseBirthLaw (r : ℝ≥0) (n : ℕ) : Measure ℕ :=
  (signWordLaw r n (2 * n + 1)).bind (wordObservedBirthKernel n)

instance actualTerminalReverseBirthLaw_probability (r : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (actualTerminalReverseBirthLaw r n) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem actualTerminalReverseBirthLaw_eq (r : ℝ≥0) (n : ℕ) :
    actualTerminalReverseBirthLaw r n = terminalReverseBirthLaw r n := by
  apply Measure.bind_congr_right
  exact (signWordLaw_feasible r n (2 * n + 1)).mono fun w hw => wordObservedBirthKernel_eq_reverse n w hw

theorem actualTerminalReverseBirthLaw_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualTerminalReverseBirthLaw (rate n) n).real
        {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
  simpa only [actualTerminalReverseBirthLaw_eq] using
    terminalReverseBirthLaw_same_epsilon rate lam hlam hscaled heps hepsT

theorem reverseBirthClock_ge_vertex {x : SignSequence} {N : ℕ} {s : Forward.State}
    (hs : Forward.HistoryShape x N s) (hv : Forward.ValidAt N s)
    {v : ℕ} (hmem : v ∈ s.vertices) : v ≤ Forward.reverseBirthClock N s v := by
  unfold Forward.reverseBirthClock
  cases hf : s.frozenAt v with
  | none => simpa only [Option.getD_none, Nat.add_sub_cancel] using hv.vertices_le v hmem
  | some j =>
    have h := hs.frozen_after_birth v hmem j hf
    simp only [Option.getD_some]
    omega

theorem word_terminal_clock_ge_vertex (n : ℕ) (w : Fin (2 * n + 1) → Bool)
    (hw : SignWordFeasible n w) :
    ∀ᵐ s ∂Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1),
      ∀ v ∈ s.vertices, v ≤ Forward.reverseBirthClock (captureWordExtinction n w) s v := by
  have hs := captureWordExtinction_spec n w hw
  have he : Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1) =
      Forward.treeLaw (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w) := by
    simpa only [Nat.add_sub_of_le hs.1] using
      Forward.treeLaw_constant_after_extinction hs.2.1 (2 * n + 1 - captureWordExtinction n w)
  rw [he]
  filter_upwards [Forward.treeLaw_historyShape (ForwardAnnealed.wordSchedule w)
    (captureWordExtinction n w) hs.2.1.symm.le,
    Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) (captureWordExtinction n w)] with s hshape hvalid
  exact fun v hv => reverseBirthClock_ge_vertex hshape hvalid hv

noncomputable def wordObservedVertexBirthKernel (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    Measure (ℕ × ℕ) :=
  (Forward.treeLaw (ForwardAnnealed.wordSchedule w) (2 * n + 1)).bind fun s =>
    (Measure.uniformOfFinset s.vertices).map
      (fun v => (v, Forward.reverseBirthClock (captureWordExtinction n w) s v))

instance wordObservedVertexBirthKernel_probability (n : ℕ) (w : Fin (2 * n + 1) → Bool) :
    IsProbabilityMeasure (wordObservedVertexBirthKernel n w) := by
  apply isProbabilityMeasure_bind measurable_from_top.aemeasurable
  filter_upwards [Forward.treeLaw_valid (ForwardAnnealed.wordSchedule w) (2 * n + 1)] with s hs
  have := Forward.uniform_vertices_probability s ⟨0, hs.root_mem⟩
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable |>.mpr inferInstance

noncomputable def actualTerminalVertexBirthLaw (r : ℝ≥0) (n : ℕ) : Measure (ℕ × ℕ) :=
  (signWordLaw r n (2 * n + 1)).bind (wordObservedVertexBirthKernel n)

instance actualTerminalVertexBirthLaw_probability (r : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (actualTerminalVertexBirthLaw r n) :=
  isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall fun _ => inferInstance)

theorem actualTerminalVertexBirthLaw_map_snd (r : ℝ≥0) (n : ℕ) :
    (actualTerminalVertexBirthLaw r n).map Prod.snd = actualTerminalReverseBirthLaw r n := by
  rw [actualTerminalVertexBirthLaw, actualTerminalReverseBirthLaw,
    Measure.map_bind (measurable_of_countable _).aemeasurable measurable_snd.aemeasurable]
  congr 1
  funext w
  rw [wordObservedVertexBirthKernel, wordObservedBirthKernel,
    Measure.map_bind measurable_from_top.aemeasurable measurable_snd.aemeasurable]
  congr 1
  funext s
  rw [Measure.map_map measurable_snd (measurable_of_countable _)]
  rfl

theorem actualTerminalVertexBirthLaw_order (r : ℝ≥0) (n : ℕ) :
    ∀ᵐ z ∂actualTerminalVertexBirthLaw r n, z.1 ≤ z.2 := by
  apply ae_bind_of_ae (measurable_of_countable _).aemeasurable ((Set.to_countable _).measurableSet)
  filter_upwards [signWordLaw_feasible r n (2 * n + 1)] with w hw
  apply ae_bind_of_ae measurable_from_top.aemeasurable ((Set.to_countable _).measurableSet)
  filter_upwards [word_terminal_clock_ge_vertex n w hw] with s hs
  apply (ae_map_iff (measurable_of_countable _).aemeasurable ((Set.to_countable _).measurableSet)).mpr
  have hmem : ∀ᵐ v ∂Measure.uniformOfFinset s.vertices, v ∈ s.vertices := by
    rw [ae_iff]
    simp [Measure.uniformOfFinset_apply]
  exact hmem.mono fun v hv => hs v hv

/-- The source reverse-birth estimate implies true chronological-prefix
capture for the very same conditionally uniform vertex. -/
theorem actualTerminalVertexBirthLaw_forward_capture_same_epsilon (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : (1 : ℝ) < lam)
    (hscaled : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    {eps : ℝ} (heps : 0 < eps) (hepsT : eps < fluidExtinctionTime lam) :
    ∀ᶠ n : ℕ in atTop,
      1 - eps ≤ (actualTerminalVertexBirthLaw (rate n) n).real
        {z | (z.1 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
  filter_upwards [actualTerminalReverseBirthLaw_same_epsilon rate lam hlam hscaled heps hepsT]
    with n hn
  have he : (actualTerminalReverseBirthLaw (rate n) n).real
      {j | (j : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} =
      (actualTerminalVertexBirthLaw (rate n) n).real
        {z | (z.2 : ℝ) ≤ (n : ℝ) * (fluidExtinctionTime lam - eps)} := by
    rw [← actualTerminalVertexBirthLaw_map_snd,
      map_measureReal_apply measurable_snd ((Set.to_countable _).measurableSet)]
    rfl
  rw [he] at hn
  apply hn.trans
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [actualTerminalVertexBirthLaw_order (rate n) n] with z hz hcap
  exact (show (z.1 : ℝ) ≤ z.2 by exact_mod_cast hz).trans hcap

end Freezing1.SIR
