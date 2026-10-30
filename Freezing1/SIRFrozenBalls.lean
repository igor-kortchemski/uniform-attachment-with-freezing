module

public import Freezing1.SIRAbsorption
public import Freezing1.PlaneFrozenBalls

/-!
# Terminal infection balls are determined by frozen early prefixes
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical

def TreeState.Update (z w : TreeState) : Prop :=
  w = z ∨ ∃ sign u, u ∈ z.tree.active ∧ w = treeStep z sign u

theorem treeKernel_update (rate : ℝ≥0) (z : TreeState) :
    ∀ᵐ w ∂treeKernel rate z, z.Update w := by
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  rw [treeKernel_apply]
  calc
    _ = ∫⁻ _sign, (1 : ℝ≥0∞)
        ∂bernoulliMeasure true false (infectionProbability rate z.susceptible) := by
      apply lintegral_congr_ae
      apply Filter.Eventually.of_forall
      intro sign
      apply (ae_iff_prob_eq_one (measurable_of_countable _)).mp
      exact signedTreeLaw_ae z sign (TreeState.Update z)
        (fun _ => Or.inl rfl) (fun u hu => Or.inr ⟨sign, u, hu, rfl⟩)
    _ = 1 := by rw [lintegral_one, measure_univ]

theorem treeFullLaw_update (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂treeFullLaw rate n, ∀ k, (H k).Update (H (k + 1)) :=
  CountableMarkovChain.fullLaw_steps (treeKernel rate) (initialTreeState n)
    TreeState.Update (treeKernel_update rate)

theorem treeStep_frozenBall {z : TreeState} (hz : PlaneForward.Valid z.tree)
    {h : ℕ} (hf : PlaneForward.FrozenBall z.tree h) (sign : Bool) (u : PlaneTree.Address) :
    PlaneForward.FrozenBall (treeStep z sign u).tree h := by
  unfold treeStep
  split_ifs with hu hsign hs
  · exact hf
  · exact hf.attach hz hu
  · exact hf.freeze u
  · exact hf

theorem treeStep_ball_shape_of_frozen {z : TreeState} (hz : PlaneForward.Valid z.tree)
    {h : ℕ} (hf : PlaneForward.FrozenBall z.tree h) (sign : Bool) (u : PlaneTree.Address) :
    PlaneTree.ball (PlaneForward.shape (treeStep z sign u).tree) h =
      PlaneTree.ball (PlaneForward.shape z.tree) h := by
  unfold treeStep
  split_ifs with hu hsign hs
  · rfl
  · change PlaneTree.ball (PlaneForward.shape (PlaneForward.attach z.tree u)) h = _
    rw [(hz.attach hu).ball_shape, hz.ball_shape]
    exact PlaneForward.heightVertices_attach_of_frozen hz hf hu (Nat.le_succ h)
  · change PlaneTree.ball (PlaneForward.shape (PlaneForward.freeze z.tree u)) h = _
    rw [(hz.freeze u).ball_shape, hz.ball_shape]
    rfl
  · rfl

theorem TreeState.Update.frozenBall {z w : TreeState} (hu : z.Update w)
    (hz : PlaneForward.Valid z.tree) {h : ℕ} (hf : PlaneForward.FrozenBall z.tree h) :
    PlaneForward.FrozenBall w.tree h ∧
      PlaneTree.ball (PlaneForward.shape w.tree) h =
        PlaneTree.ball (PlaneForward.shape z.tree) h := by
  rcases hu with rfl | ⟨sign, u, _, rfl⟩
  · exact ⟨hf, rfl⟩
  · exact ⟨treeStep_frozenBall hz hf sign u, treeStep_ball_shape_of_frozen hz hf sign u⟩

theorem frozenBall_persists {H : ℕ → TreeState}
    (hv : ∀ k, PlaneForward.Valid (H k).tree)
    (hu : ∀ k, (H k).Update (H (k + 1))) {a h : ℕ}
    (hf : PlaneForward.FrozenBall (H a).tree h) :
    ∀ k ≥ a, PlaneForward.FrozenBall (H k).tree h ∧
      PlaneTree.ball (PlaneForward.shape (H k).tree) h =
        PlaneTree.ball (PlaneForward.shape (H a).tree) h := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨hf, rfl⟩
  | succ k hk ih =>
    have hh := (hu k).frozenBall (hv k) ih.1
    exact ⟨hh.1, hh.2.trans ih.2⟩

private theorem abs_event_difference_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E F B : Set Ω)
    (h : ∀ᵐ ω ∂μ, ω ∉ B → (ω ∈ E ↔ ω ∈ F)) :
    |μ.real E - μ.real F| ≤ μ.real B := by
  have hEF : μ.real E - μ.real F ≤ μ.real B := by
    apply (le_measureReal_sdiff (μ := μ) (s₁ := E) (s₂ := F)).trans
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [h] with ω hω hEF
    by_contra hB
    exact hEF.2 ((hω hB).mp hEF.1)
  have hFE : μ.real F - μ.real E ≤ μ.real B := by
    apply (le_measureReal_sdiff (μ := μ) (s₁ := F) (s₂ := E)).trans
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [h] with ω hω hFE
    by_contra hB
    exact hFE.2 ((hω hB).mpr hFE.1)
  exact abs_le.mpr ⟨by linarith, hEF⟩

theorem terminal_ball_event_difference_le (rate : ℝ≥0) (n k h : ℕ)
    (hk : k ≤ 2 * n + 1) (A : Set (Finset PlaneTree.Address)) :
    |(treeFullLaw rate n).real {H |
        PlaneTree.ball (PlaneForward.shape (H (2 * n + 1)).tree) h ∈ A} -
      (treeFullLaw rate n).real {H |
        PlaneTree.ball (PlaneForward.shape (H k).tree) h ∈ A}| ≤
      (treeFullLaw rate n).real {H | ¬PlaneForward.FrozenBall (H k).tree h} := by
  apply abs_event_difference_le
  filter_upwards [treeFullLaw_valid rate n, treeFullLaw_update rate n] with H hv hu hf
  have hf' : PlaneForward.FrozenBall (H k).tree h := by simpa using hf
  rw [(frozenBall_persists (fun k => (hv k).1) hu hf' (2 * n + 1) hk).2]

end Freezing1.SIR
