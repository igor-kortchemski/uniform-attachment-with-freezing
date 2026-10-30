module

public import Freezing1.PolyaBernoulliMGF
public import Mathlib.Probability.Distributions.Bernoulli

/-!
# The finite signed Pólya urn kernel

The population and occupancy are integer valued. On the valid domain the
transition selects a marked ball with probability `u / Z`, then adds or removes
a marked ball according to the prescribed sign. Clipping only makes the kernel
total outside this domain; `parameter_eq` proves that it is absent on all valid
states, and `transitionLaw_valid` proves preservation of those states.
-/

@[expose] public section

namespace Freezing1.SignedUrn

open MeasureTheory ProbabilityTheory

noncomputable def parameter (Z u : ℤ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((u : ℝ) / Z)

noncomputable def transitionLaw (Z z u : ℤ) : Measure ℤ :=
  bernoulliMeasure (u + z) u (parameter Z u)

instance transitionLaw_probability (Z z u : ℤ) :
    IsProbabilityMeasure (transitionLaw Z z u) := by
  unfold transitionLaw
  infer_instance

theorem parameter_eq {Z u : ℤ} (hZ : 0 < Z) (hu : 0 ≤ u) (huZ : u ≤ Z) :
    (parameter Z u : ℝ) = (u : ℝ) / Z := by
  have hZr : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hmem : (u : ℝ) / Z ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by exact_mod_cast hu) hZr.le,
      (div_le_one hZr).mpr (by exact_mod_cast huZ)⟩
  exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hmem)

theorem parameter_zero (Z : ℤ) : parameter Z 0 = 0 := by
  apply Subtype.ext
  simp [parameter]

theorem parameter_self {Z : ℤ} (hZ : 0 < Z) : parameter Z Z = 1 := by
  apply Subtype.ext
  rw [parameter_eq hZ hZ.le le_rfl]
  simp [ne_of_gt hZ]

theorem transitionLaw_valid {Z z u : ℤ} (hZ : 0 < Z)
    (hnext : 0 < Z + z) (hz : z = 1 ∨ z = -1) (hu : 0 ≤ u) (huZ : u ≤ Z) :
    ∀ᵐ v ∂transitionLaw Z z u, 0 ≤ v ∧ v ≤ Z + z := by
  by_cases hu0 : u = 0
  · subst u
    simp [transitionLaw, parameter_zero, hnext.le]
  by_cases hutop : u = Z
  · subst u
    simp [transitionLaw, parameter_self hZ, hnext.le]
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  apply bernoulliMeasure_apply_of_mem_of_mem _ (Set.to_countable _).measurableSet
  · rcases hz with rfl | rfl <;> change 0 ≤ u + _ ∧ u + _ ≤ Z + _ <;> omega
  · rcases hz with rfl | rfl <;> change 0 ≤ u ∧ u ≤ Z + _ <;> omega

theorem integral_transitionLaw (Z z u : ℤ) (f : ℤ → ℝ) :
    ∫ v, f v ∂transitionLaw Z z u =
      (parameter Z u : ℝ) * f (u + z) + (1 - parameter Z u) * f u := by
  simpa only [transitionLaw, smul_eq_mul] using
    integral_bernoulliMeasure (u + z) u (parameter Z u) f

theorem normalized_increment {Z z u : ℤ} (hZ : Z ≠ 0) (hnext : Z + z ≠ 0) :
    ((u + z : ℤ) : ℝ) / (Z + z) =
        (u : ℝ) / Z + (z : ℝ) / (Z + z) * (1 - (u : ℝ) / Z) ∧
      (u : ℝ) / (Z + z) = (u : ℝ) / Z - (z : ℝ) / (Z + z) * ((u : ℝ) / Z) := by
  have hZr : (Z : ℝ) ≠ 0 := by exact_mod_cast hZ
  have hnextr : (Z : ℝ) + z ≠ 0 := by exact_mod_cast hnext
  push_cast
  constructor <;> field_simp <;> ring

theorem normalized_mean {Z z u : ℤ} (hZ : 0 < Z) (hnext : 0 < Z + z)
    (hu : 0 ≤ u) (huZ : u ≤ Z) :
    ∫ v, (v : ℝ) / (Z + z) ∂transitionLaw Z z u = (u : ℝ) / Z := by
  rw [integral_transitionLaw, parameter_eq hZ hu huZ]
  obtain ⟨h1, h0⟩ := normalized_increment (u := u) hZ.ne' hnext.ne'
  rw [h1, h0]
  ring

/-- The actual signed urn transition satisfies the backward MGF estimate.
The future quadratic budget is explicit and must be supplied by the schedule. -/
theorem backward_exponential_step {Z z u : ℤ} (hZ : 0 < Z) (hnext : 0 < Z + z)
    (hu : 0 ≤ u) (huZ : u ≤ Z) {θ B : ℝ} (hB : 0 ≤ B)
    (hbudget : |θ| * B ≤ 1 / 4) (hincrement : |θ * ((z : ℝ) / (Z + z))| ≤ 1 / 4) :
    ∫ v, Real.exp ((θ * (1 + θ * B)) * ((v : ℝ) / (Z + z)))
        ∂transitionLaw Z z u ≤
      Real.exp ((θ * (1 + θ * (B + ((z : ℝ) / (Z + z)) ^ 2))) * ((u : ℝ) / Z)) := by
  rw [integral_transitionLaw, parameter_eq hZ hu huZ]
  obtain ⟨h1, h0⟩ := normalized_increment (u := u) hZ.ne' hnext.ne'
  rw [h1, h0]
  apply polya_backward_exponential_step
  · exact div_nonneg (by exact_mod_cast hu) (by exact_mod_cast hZ.le)
  · apply (div_le_one (by exact_mod_cast hZ : (0 : ℝ) < Z)).mpr
    exact_mod_cast huZ
  · exact hB
  · exact hbudget
  · exact hincrement

end Freezing1.SignedUrn
