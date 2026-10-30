module

public import Freezing1.BernoulliPairCouplingKernel
public import Freezing1.BernoulliReciprocalParameters

/-! Source A60's auxiliary coin coupled to an actual history transition. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def auxiliaryParameter (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (i : ℕ) : unitInterval :=
  if hi : i < n then enlargedAttachmentParameter x n hn ⟨i, hi⟩ else 0

theorem auxiliaryParameter_of_lt (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {i : ℕ} (hi : i < n) :
    auxiliaryParameter x n hn i = enlargedAttachmentParameter x n hn ⟨i, hi⟩ := by
  simp only [auxiliaryParameter, dite_eq_left hi]

theorem step_parameters_relation (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {i : ℕ} (hi : i < n) :
    (1 - (Reverse.stepParameter x n hn i : ℝ)) * (auxiliaryParameter x n hn i : ℝ) =
      (Reverse.stepParameter x n hn i : ℝ) := by
  rw [Reverse.stepParameter_of_lt x n hn hi, auxiliaryParameter_of_lt x n hn hi,
    Reverse.attachmentParameter_coe, enlargedAttachmentParameter_coe]
  cases hx : x (i + 1)
  · simp
  · simp only [↓reduceIte]
    have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
      le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
    have htwo : (2 : ℝ) ≤ activeCount x (i + 1) :=
      by exact_mod_cast two_le_activeCount_succ_of_attachment hiτ hx
    let S : ℝ := activeCount x (i + 1)
    change (1 - 1 / S) * (1 / (S - 1)) = 1 / S
    have hS0 : S ≠ 0 := by dsimp only [S]; linarith only [htwo]
    have hS1 : S - 1 ≠ 0 := by dsimp only [S]; linarith only [htwo]
    field_simp [hS0, hS1]

theorem historyIncrement_hasLaw {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u : ℕ ⊕ ℕ} (hu : u ∈ H.current.vertices) :
    HasLaw (ReverseHistory.heightIncrement u)
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.stepParameter x n hn i))
      (ReverseHistory.transitionLaw x i H) := by
  refine ⟨measurable_from_top.aemeasurable, ?_⟩
  have h := congrArg (fun μ : Measure (Base × ℕ) => μ.map Prod.snd)
    (ReverseHistory.transitionLaw_previous_increment hn hi hH hu)
  rw [Measure.map_map measurable_snd measurable_from_top,
    Measure.map_map measurable_snd (measurable_of_countable _)] at h
  simpa only [Function.comp_def, Reverse.stepParameter_of_lt x n hn hi] using h.trans Measure.map_id

theorem history_exclusive_increments {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices)
    (huv : H.current.root u ≠ H.current.root v) :
    ∀ᵐ H' ∂ReverseHistory.transitionLaw x i H,
      ReverseHistory.heightIncrement u H' = 0 ∨ ReverseHistory.heightIncrement v H' = 0 := by
  rw [ReverseHistory.transitionLaw]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [Reverse.transitionLaw_exclusive_depth_increments hn hi hH hu hv huv] with F hF
  rcases hF with hF | hF
  · left
    change F.depth u - H.current.depth u = 0
    rw [hF, Nat.sub_self]
  · right
    change F.depth v - H.current.depth v = 0
    rw [hF, Nat.sub_self]

theorem history_same_increments {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices)
    (huv : H.current.root u = H.current.root v) :
    ReverseHistory.heightIncrement u =ᵐ[ReverseHistory.transitionLaw x i H]
      ReverseHistory.heightIncrement v := by
  rw [ReverseHistory.transitionLaw]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  cases hx : x (i + 1)
  · have hfu : Sum.inr i ∉ H.current.vertices := hH.vertices_eq.symm ▸ Reverse.fresh_freezing_label x n i
    simp only [Reverse.transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    apply (ae_dirac_iff (by trivial)).mpr
    change (Reverse.insertLabel H.current i).depth u - H.current.depth u =
      (Reverse.insertLabel H.current i).depth v - H.current.depth v
    rw [Reverse.insertLabel, dite_eq_right hfu,
      RootedForest.adjoin_depth_old H.current hfu hu, RootedForest.adjoin_depth_old H.current hfu hv]
    simp only [Nat.sub_self]
  · have htwo : 2 ≤ H.current.roots.card := by
      rw [hH.roots_card]
      have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
        le_trans (by exact_mod_cast Nat.succ_le_of_lt hi) hn
      have hS := two_le_activeCount_succ_of_attachment hiτ hx
      omega
    simp only [Reverse.transitionLaw, hx, ↓reduceIte]
    apply H.current.joinLaw_ae htwo
    intro pair hpair
    change (H.current.joinChoice pair).depth u - H.current.depth u =
      (H.current.joinChoice pair).depth v - H.current.depth v
    rw [RootedForest.joinChoice_depth H.current hpair, RootedForest.joinChoice_depth H.current hpair, huv]
    split_ifs <;> omega

noncomputable def stepLaw (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (u v : ℕ ⊕ ℕ) (i : ℕ) (H : Base) : Measure StepSample :=
  augmentLaw (ReverseHistory.transitionLaw x i H) (H.current.root u = H.current.root v)
    (ReverseHistory.heightIncrement u) (ReverseHistory.heightIncrement v) (auxiliaryParameter x n hn i)

instance stepLaw_probability (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (u v : ℕ ⊕ ℕ) (i : ℕ) (H : Base) : IsProbabilityMeasure (stepLaw x n hn u v i H) := by
  unfold stepLaw
  infer_instance

theorem stepLaw_map_history (x : SignSequence) (n : ℕ) (hn : (n : ℕ∞) ≤ extinctionTime x)
    (u v : ℕ ⊕ ℕ) (i : ℕ) (H : Base) :
    (stepLaw x n hn u v i H).map StepSample.history = ReverseHistory.transitionLaw x i H :=
  augmentLaw_map_history _ _ _ _ _

/-- The two driver coins are independent under the coupled actual
transition, conditional on any genuine complete predecessor history. -/
theorem stepLaw_map_drivers {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (stepLaw x n hn u v i H).map
        (fun s => (ReverseHistory.heightIncrement u s.history, s.auxiliary)) =
      (bernoulliMeasure (1 : ℕ) 0 (Reverse.stepParameter x n hn i)).prod
        (bernoulliMeasure (1 : ℕ) 0 (auxiliaryParameter x n hn i)) := by
  unfold stepLaw
  exact augmentLaw_map_pair (ReverseHistory.transitionLaw x i H)
    (H.current.root u = H.current.root v)
    (ReverseHistory.heightIncrement u) (ReverseHistory.heightIncrement v)
    (Reverse.stepParameter x n hn i) (auxiliaryParameter x n hn i)
    (historyIncrement_hasLaw hn hi hH hu) (historyIncrement_hasLaw hn hi hH hv)
    (fun hsep => history_exclusive_increments hn hi hH hu hv hsep)
    (step_parameters_relation x n hn hi)

/-- Actual source formula1921, expressed by the state before the step.
This includes paths that first merge during this very step. -/
theorem stepLaw_relation {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ s ∂stepLaw x n hn u v i H,
      ReverseHistory.heightIncrement v s.history =
        if H.current.root u = H.current.root v then ReverseHistory.heightIncrement u s.history
        else s.auxiliary * (1 - ReverseHistory.heightIncrement u s.history) := by
  unfold stepLaw
  have h := augmentLaw_relation (ReverseHistory.transitionLaw x i H)
    (H.current.root u = H.current.root v)
    (ReverseHistory.heightIncrement u) (ReverseHistory.heightIncrement v)
    (Reverse.stepParameter x n hn i) (auxiliaryParameter x n hn i)
    (historyIncrement_hasLaw hn hi hH hu)
    (fun hsame => history_same_increments hn hi hH hu hv hsame)
    (fun hsep => history_exclusive_increments hn hi hH hu hv hsep)
  filter_upwards [h] with s hs
  by_cases he : H.current.root u = H.current.root v
  · simpa only [ite_eq_left he] using hs
  · simpa only [ite_eq_right he] using hs

end Freezing1.BernoulliPairCoupling
