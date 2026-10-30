module

public import Freezing1.ForwardDegree
public import Freezing1.ForwardVertexLifetime
public import Freezing1.ForwardHeight

/-!
# Joint survival and degree estimates from the actual forward kernels

The bounded test records both continued activity and the exponential of the
negative root degree. Its two exact one-step factors retain the preceding
active population. No conditional independence is assumed.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

noncomputable def survivingRootWeight (θ : ℝ) (s : State) : ℝ :=
  if 0 ∈ s.active then Real.exp (-θ * (rootDegree s : ℝ)) else 0

theorem survivingRootWeight_bounds {θ : ℝ} (hθ : 0 ≤ θ) (s : State) :
    0 ≤ survivingRootWeight θ s ∧ survivingRootWeight θ s ≤ 1 := by
  unfold survivingRootWeight
  split_ifs
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) (Nat.cast_nonneg _))⟩
  · norm_num

theorem integrable_survivingRootWeight {θ : ℝ} (hθ : 0 ≤ θ)
    (μ : Measure State) [IsFiniteMeasure μ] : Integrable (survivingRootWeight θ) μ := by
  apply (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (survivingRootWeight_bounds hθ s).1]
    exact (survivingRootWeight_bounds hθ s).2

theorem survivingRootWeight_step {n : ℕ} {s : State} (hs : ValidAt n s)
    {p : ℕ} (hp : p ∈ s.active) (sign : Bool) (θ : ℝ) :
    survivingRootWeight θ (step s (n + 1) sign p) =
      survivingRootWeight θ s * if p = 0 then (if sign then Real.exp (-θ) else 0) else 1 := by
  have hactive := step_active_old (Nat.zero_le n) hp sign
  rw [survivingRootWeight, rootDegree_step hs hp sign]
  by_cases hroot : 0 ∈ s.active
  · by_cases hp0 : p = 0
    · subst p
      cases sign
      · simp only [Bool.false_eq_true, false_or, ne_eq, not_true_eq_false, and_false] at hactive
        simp [hactive, survivingRootWeight, hroot]
      · simp only [true_or, and_true] at hactive
        simp only [hactive, hroot, ↓reduceIte, true_and, Nat.cast_add, Nat.cast_one,
          survivingRootWeight]
        rw [show -θ * ((rootDegree s : ℝ) + 1) = -θ * (rootDegree s : ℝ) + -θ by ring,
          Real.exp_add]
    · have h0p : (0 : ℕ) ≠ p := Ne.symm hp0
      have hrootnew := hactive.mpr ⟨hroot, Or.inr h0p⟩
      simp [hrootnew, survivingRootWeight, hroot, hp0]
  · have hp0 : p ≠ 0 := by intro he; subst p; exact hroot hp
    simp only [hroot, false_and] at hactive
    simp [hactive, survivingRootWeight, hroot, hp0]

noncomputable def degreeSurvivalFactor (x : SignSequence) (θ : ℝ) (i : ℕ) : ℝ :=
  if x i then 1 + (Real.exp (-θ) - 1) / (activeCount x (i - 1) : ℝ)
  else vertexSurvivalFactor x i

theorem transitionLaw_survivingRootWeight {x : SignSequence} {n : ℕ} {s : State}
    (hs : PhaseData x n s) (hne : s.active.Nonempty) (θ : ℝ) :
    (∫ q, survivingRootWeight θ q ∂transitionLaw s (n + 1) (x (n + 1))) =
      survivingRootWeight θ s * degreeSurvivalFactor x θ (n + 1) := by
  rw [transitionLaw_integral _ _ _ hne]
  rw [Finset.sum_congr rfl (fun p hp => survivingRootWeight_step hs.valid hp _ θ),
    ← Finset.mul_sum]
  have hcount : (s.active.card : ℝ) = (activeCount x n : ℝ) := by exact_mod_cast hs.count
  have hneR : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  by_cases hroot : 0 ∈ s.active
  · let b : ℝ := if x (n + 1) then Real.exp (-θ) else 0
    have hsum : (∑ p ∈ s.active, if p = 0 then b else 1) = s.active.card + (b - 1) := by
      calc
        _ = ∑ p ∈ s.active, (1 + if p = 0 then b - 1 else 0) := by
          apply Finset.sum_congr rfl
          intro p _
          by_cases hp : p = 0 <;> simp [hp]
        _ = _ := by simp [Finset.sum_add_distrib, hroot]
    change survivingRootWeight θ s * (∑ p ∈ s.active, if p = 0 then b else 1) /
      s.active.card = _
    rw [hsum]
    have hZ : (activeCount x n : ℝ) ≠ 0 := hcount ▸ hneR
    rw [hcount]
    dsimp only [b, degreeSurvivalFactor, vertexSurvivalFactor]
    simp only [Nat.add_sub_cancel]
    cases x (n + 1)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      field_simp
      ring
    · simp only [↓reduceIte]
      field_simp
  · simp [survivingRootWeight, hroot]

end Freezing1.Forward
