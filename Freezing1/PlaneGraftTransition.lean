module

public import Freezing1.PlaneStateGraftRight
public import Freezing1.ForwardPlaneKernel

/-!
# Exact active-choice counts for first-child interleaving
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

theorem graft_filter_left (s t : State) (sign : Bool) (A : Set State) :
    (s.active.image (List.cons 1)).filter (fun a => step (graft s t) sign a ∈ A) =
      (s.active.filter (fun u => graft (step s sign u) t ∈ A)).image (List.cons 1) := by
  rw [Finset.filter_image]
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [graft_step_left]

theorem graft_filter_right {s : State} (hs : [] ∈ s.vertices) (t : State)
    (sign : Bool) (A : Set State) :
    (t.active.image shiftRoot).filter (fun a => step (graft s t) sign a ∈ A) =
      (t.active.filter (fun u => graft s (step t sign u) ∈ A)).image shiftRoot := by
  rw [Finset.filter_image]
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [graft_step_right hs]

theorem graft_active_filter_card {s : State} (hs : [] ∈ s.vertices) (t : State)
    (sign : Bool) (A : Set State) :
    ((graft s t).active.filter (fun a => step (graft s t) sign a ∈ A)).card =
      (s.active.filter (fun u => graft (step s sign u) t ∈ A)).card +
      (t.active.filter (fun u => graft s (step t sign u) ∈ A)).card := by
  change ((s.active.image (List.cons 1) ∪ t.active.image shiftRoot).filter _).card = _
  rw [Finset.filter_union, Finset.card_union_of_disjoint,
    graft_filter_left, graft_filter_right hs,
    Finset.card_image_of_injective _ (fun _ _ he => (List.cons.inj he).2),
    Finset.card_image_of_injective _ shiftRoot_injective]
  exact (graft_images_disjoint s.active t.active).mono (Finset.filter_subset _ _)
    (Finset.filter_subset _ _)

theorem signedTransitionLaw_graft_apply {s : State} (hs : [] ∈ s.vertices) (t : State)
    (sign : Bool) (A : Set State) (hn : s.active.card + t.active.card ≠ 0) :
    signedTransitionLaw (graft s t) sign A =
      (((s.active.filter (fun u => graft (step s sign u) t ∈ A)).card : ℝ≥0∞) +
        ((t.active.filter (fun u => graft s (step t sign u) ∈ A)).card : ℝ≥0∞)) /
          ((s.active.card : ℝ≥0∞) + t.active.card) := by
  have hne : (graft s t).active.Nonempty := by
    apply Finset.card_pos.mp
    rw [graft_active_card]
    omega
  rw [signedTransitionLaw_apply _ sign hne, graft_active_filter_card hs,
    graft_active_card, Nat.cast_add, Nat.cast_add]

theorem signedTransitionLaw_count (s : State) (sign : Bool) (A : Set State) :
    (s.active.card : ℝ≥0∞) * signedTransitionLaw s sign A =
      ((s.active.filter (fun u => step s sign u ∈ A)).card : ℝ≥0∞) := by
  by_cases hn : s.active.Nonempty
  · rw [signedTransitionLaw_apply s sign hn]
    exact ENNReal.mul_div_cancel (by exact_mod_cast hn.card_pos.ne') (by simp)
  · have he : s.active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he]

theorem selectionParameter_coe (s t : State) (hn : s.active.card + t.active.card ≠ 0) :
    (unitInterval.toNNReal (selectionParameter (s, t)) : ℝ≥0∞) =
      (s.active.card : ℝ≥0∞) / ((s.active.card : ℝ≥0∞) + t.active.card) := by
  rw [← Nat.cast_add]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast hn))).mp
  rw [ENNReal.coe_toReal, unitInterval.coe_toNNReal, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, Nat.cast_add]
  exact selectionParameter_eq s t hn

theorem selectionParameter_symm_coe (s t : State) (hn : s.active.card + t.active.card ≠ 0) :
    (unitInterval.toNNReal (unitInterval.symm (selectionParameter (s, t))) : ℝ≥0∞) =
      (t.active.card : ℝ≥0∞) / ((s.active.card : ℝ≥0∞) + t.active.card) := by
  rw [← Nat.cast_add]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness)
    (ENNReal.div_ne_top (by simp) (by exact_mod_cast hn))).mp
  rw [ENNReal.coe_toReal, unitInterval.coe_toNNReal, ENNReal.toReal_div,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, Nat.cast_add]
  change 1 - (selectionParameter (s, t) : ℝ) = _
  rw [selectionParameter_eq s t hn]
  have hpos : (0 : ℝ) < (s.active.card : ℝ) + t.active.card := by
    exact_mod_cast Nat.pos_of_ne_zero hn
  field_simp [ne_of_gt hpos]
  <;> ring

theorem signedTransitionLaw_graft {s : State} (hs : [] ∈ s.vertices) (t : State)
    (sign : Bool) :
    signedTransitionLaw (graft s t) sign =
      unitInterval.toNNReal (selectionParameter (s, t)) •
        (signedTransitionLaw s sign).map (fun z => graft z t) +
      unitInterval.toNNReal (unitInterval.symm (selectionParameter (s, t))) •
        (signedTransitionLaw t sign).map (fun z => graft s z) := by
  by_cases hn : s.active.card + t.active.card = 0
  · have he1 : s.active = ∅ := Finset.card_eq_zero.mp (by omega)
    have he2 : t.active = ∅ := Finset.card_eq_zero.mp (by omega)
    have he : (graft s t).active = ∅ := by simp [graft, he1, he2]
    rw [signedTransitionLaw_eq_dirac_of_empty _ _ he,
      signedTransitionLaw_eq_dirac_of_empty _ _ he1,
      signedTransitionLaw_eq_dirac_of_empty _ _ he2,
      selectionParameter_both_empty s t he1 he2]
    simp
  · ext A hA
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.map_apply (measurable_of_countable _) hA,
      Measure.map_apply (measurable_of_countable _) hA]
    change _ = (unitInterval.toNNReal (selectionParameter (s, t)) : ℝ≥0∞) *
      signedTransitionLaw s sign ((fun z => graft z t) ⁻¹' A) +
      (unitInterval.toNNReal (unitInterval.symm (selectionParameter (s, t))) : ℝ≥0∞) *
      signedTransitionLaw t sign ((fun z => graft s z) ⁻¹' A)
    rw [signedTransitionLaw_graft_apply hs t sign A hn,
      selectionParameter_coe s t hn, selectionParameter_symm_coe s t hn]
    have hl := signedTransitionLaw_count s sign ((fun z => graft z t) ⁻¹' A)
    have hr := signedTransitionLaw_count t sign ((fun z => graft s z) ⁻¹' A)
    simp only [Set.mem_preimage] at hl hr
    rw [← hl, ← hr]
    simp only [div_eq_mul_inv]
    ring

theorem transition_graft (p : unitInterval) {s : State} (hs : [] ∈ s.vertices) (t : State) :
    transition p (graft s t) =
      unitInterval.toNNReal (selectionParameter (s, t)) •
        (transition p s).map (fun z => graft z t) +
      unitInterval.toNNReal (unitInterval.symm (selectionParameter (s, t))) •
        (transition p t).map (fun z => graft s z) := by
  ext A hA
  rw [transition_apply_split, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_of_countable _) hA,
    Measure.map_apply (measurable_of_countable _) hA,
    transition_apply_split, transition_apply_split]
  rw [signedTransitionLaw_graft hs t true, signedTransitionLaw_graft hs t false]
  simp only [Measure.add_apply, Measure.smul_apply,
    Measure.map_apply (measurable_of_countable _) hA, ENNReal.smul_def, smul_eq_mul]
  ring

theorem map_interleaved_transition_graft (p : unitInterval) {s : State}
    (hs : [] ∈ s.vertices) (t : State) (i : Bool) :
    (InterleavedChain.transition (transition p) selectionParameter (s, t, i)).map
      (fun q => graft q.1 q.2.1) = transition p (graft s t) := by
  ext A hA
  rw [Measure.map_apply (measurable_of_countable _) hA,
    InterleavedChain.transition_apply, transition_graft p hs,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (measurable_of_countable _) hA,
    Measure.map_apply (measurable_of_countable _) hA]
  rfl

end Freezing1.PlaneForward
