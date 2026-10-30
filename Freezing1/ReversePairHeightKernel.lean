module

public import Freezing1.ReverseHistoryHeight
public import Freezing1.ReverseCoalescence

/-!
# Two heights under the actual reverse transition

Before two components coalesce, their height increments cannot both be one.
This gives a product supersolution for nonnegative increasing test functions.
Killing the pair when its roots coincide preserves that upper bound. These
are statements about the actual transition kernel, not a conditional law
obtained by informally conditioning on noncoalescence.

This is the one-step part of an alternative proof of A59--A62. The paper's
specific auxiliary-`ξ` coupling remains a separate statement to be checked.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

/-- Averaging a natural-valued test function over one Bernoulli increment. -/
noncomputable def bernoulliAverage (p : unitInterval) (f : ℕ → ℝ) (d : ℕ) : ℝ :=
  (p : ℝ) * f (d + 1) + (1 - (p : ℝ)) * f d

theorem bernoulliAverage_nonneg (p : unitInterval) {f : ℕ → ℝ}
    (hf : ∀ d, 0 ≤ f d) (d : ℕ) : 0 ≤ bernoulliAverage p f d := by
  exact add_nonneg (mul_nonneg p.2.1 (hf _))
    (mul_nonneg (sub_nonneg.mpr p.2.2) (hf _))

theorem bernoulliAverage_mono (p : unitInterval) {f : ℕ → ℝ}
    (hf : Monotone f) : Monotone (bernoulliAverage p f) := by
  intro a b hab
  exact add_le_add (mul_le_mul_of_nonneg_left (hf (Nat.add_le_add_right hab 1)) p.2.1)
    (mul_le_mul_of_nonneg_left (hf hab) (sub_nonneg.mpr p.2.2))

/-- Mutually exclusive unit increments give a nonpositive covariance for
increasing functions. Neither independence nor a coupling is assumed. -/
theorem integral_product_le_of_exclusive_bernoulli
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : Ω → ℕ} {d e : ℕ} {p : unitInterval}
    (hX : HasLaw X (bernoulliMeasure (d + 1) d p) μ)
    (hY : HasLaw Y (bernoulliMeasure (e + 1) e p) μ)
    (hsX : ∀ᵐ ω ∂μ, X ω = d ∨ X ω = d + 1)
    (hsY : ∀ᵐ ω ∂μ, Y ω = e ∨ Y ω = e + 1)
    (hex : ∀ᵐ ω ∂μ, X ω = d ∨ Y ω = e)
    {f g : ℕ → ℝ} (hf : Monotone f) (hg : Monotone g) :
    Integrable (fun ω => f (X ω) * g (Y ω)) μ ∧
      ∫ ω, f (X ω) * g (Y ω) ∂μ ≤
        bernoulliAverage p f d * bernoulliAverage p g e := by
  have hif := hX.integrable_fun_comp (integrable_bernoulliMeasure _ _ p f)
  have hig := hY.integrable_fun_comp (integrable_bernoulliMeasure _ _ p g)
  have heq : (fun ω => f (X ω) * g (Y ω)) =ᵐ[μ]
      fun ω => f (X ω) * g e + f d * g (Y ω) - f d * g e := by
    filter_upwards [hsX, hsY, hex] with ω hωX hωY hω
    rcases hω with hω | hω <;> rw [hω] <;> ring
  have hi := ((hif.mul_const (g e)).add (hig.const_mul (f d))).sub
    (integrable_const (f d * g e))
  refine ⟨hi.congr heq.symm, ?_⟩
  have hisum : Integrable (fun ω => f (X ω) * g e + f d * g (Y ω)) μ :=
    (hif.mul_const (g e)).add (hig.const_mul (f d))
  have hi1 : Integrable (fun ω => f (X ω) * g e) μ := hif.mul_const (g e)
  have hi2 : Integrable (fun ω => f d * g (Y ω)) μ := hig.const_mul (f d)
  rw [integral_congr_ae heq, integral_sub hisum (integrable_const _),
    integral_add hi1 hi2, integral_mul_const, integral_const_mul,
    integral_const, probReal_univ, one_smul]
  have hfint := hX.integral_comp (measurable_of_countable f).aestronglyMeasurable
  have hgint := hY.integral_comp (measurable_of_countable g).aestronglyMeasurable
  simp only [Function.comp_def, integral_bernoulliMeasure, smul_eq_mul] at hfint hgint
  rw [hfint, hgint]
  have hp2 : 0 ≤ (p : ℝ) ^ 2 := sq_nonneg _
  have hdiff : 0 ≤ (p : ℝ) ^ 2 * (f (d + 1) - f d) * (g (e + 1) - g e) :=
    mul_nonneg (mul_nonneg hp2 (sub_nonneg.mpr (hf (Nat.le_succ _))))
      (sub_nonneg.mpr (hg (Nat.le_succ _)))
  dsimp [bernoulliAverage]
  nlinarith only [hdiff]

namespace Reverse

/-- Two distinct components cannot both increase in a single actual step. -/
theorem transitionLaw_exclusive_depth_increments {x : SignSequence} {n i : ℕ}
    {F : Forest} (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    ∀ᵐ F' ∂transitionLaw x i F, F'.depth u = F.depth u ∨ F'.depth v = F.depth v := by
  cases hx : x (i + 1)
  · have hs := transitionLaw_present_depth_support hn hi hF hu
    have hfresh : Sum.inr i ∉ F.vertices := hF.vertices_eq.symm ▸ fresh_freezing_label x n i
    simp only [transitionLaw, hx, Bool.false_eq_true, ↓reduceIte]
    apply (ae_dirac_iff (by trivial)).mpr
    left
    rw [insertLabel, dite_eq_right hfresh]
    exact RootedForest.adjoin_depth_old F hfresh hu
  · have htwo : 2 ≤ F.roots.card :=
      (show F.roots.Nontrivial from
        ⟨F.root u, F.root_mem_roots hu, F.root v, F.root_mem_roots hv, huv⟩).two_le_card
    simp only [transitionLaw, hx, ↓reduceIte]
    apply F.joinLaw_ae htwo
    intro pair hpair
    rw [RootedForest.joinChoice_depth F hpair, RootedForest.joinChoice_depth F hpair]
    by_cases h : F.root u = pair.2
    · right
      have hvp : F.root v ≠ pair.2 := fun h' => huv (h.trans h'.symm)
      simp only [hvp, ↓reduceIte, Nat.add_zero]
    · left
      simp only [h, ↓reduceIte, Nat.add_zero]

/-- The actual two-height kernel is dominated on increasing products by two
independent Bernoulli increments with the original masked parameter. -/
theorem transitionLaw_product_le {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v)
    {f g : ℕ → ℝ} (hf : Monotone f) (hg : Monotone g) :
    Integrable (fun F' => f (F'.depth u) * g (F'.depth v)) (transitionLaw x i F) ∧
      ∫ F', f (F'.depth u) * g (F'.depth v) ∂transitionLaw x i F ≤
        bernoulliAverage (attachmentParameter x n hn ⟨i, hi⟩) f (F.depth u) *
        bernoulliAverage (attachmentParameter x n hn ⟨i, hi⟩) g (F.depth v) := by
  have hsU := (transitionLaw_present_depth_support hn hi hF hu).mono fun _ h => h.2
  have hsV := (transitionLaw_present_depth_support hn hi hF hv).mono fun _ h => h.2
  have hlaw (w : ℕ ⊕ ℕ) (hw : w ∈ F.vertices) :
      HasLaw (fun F' : Forest => F'.depth w)
        (bernoulliMeasure (F.depth w + 1) (F.depth w)
          (attachmentParameter x n hn ⟨i, hi⟩)) (transitionLaw x i F) := by
    apply hasLaw_nat_succ_of_support measurable_from_top
      ((transitionLaw_present_depth_support hn hi hF hw).mono fun _ h => h.2)
    rw [transitionLaw_height_increment hn hi hF hw, attachmentParameter_coe]
  exact integral_product_le_of_exclusive_bernoulli (hlaw u hu) (hlaw v hv)
    hsU hsV (transitionLaw_exclusive_depth_increments hn hi hF hu hv huv) hf hg

/-- Killing at coalescence yields a genuine kernel inequality, including
states whose two components have already coalesced. -/
theorem transitionLaw_killed_product_le {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    {f g : ℕ → ℝ} (hf : Monotone f) (hg : Monotone g)
    (hf0 : ∀ d, 0 ≤ f d) (hg0 : ∀ d, 0 ≤ g d) :
    Integrable (fun F' => if F'.root u ≠ F'.root v then
      f (F'.depth u) * g (F'.depth v) else 0) (transitionLaw x i F) ∧
      (∫ F', if F'.root u ≠ F'.root v then f (F'.depth u) * g (F'.depth v) else 0
        ∂transitionLaw x i F) ≤
      if F.root u ≠ F.root v then
        bernoulliAverage (attachmentParameter x n hn ⟨i, hi⟩) f (F.depth u) *
        bernoulliAverage (attachmentParameter x n hn ⟨i, hi⟩) g (F.depth v) else 0 := by
  by_cases huv : F.root u ≠ F.root v
  · rw [ite_eq_left huv]
    obtain ⟨hiProd, hle⟩ := transitionLaw_product_le hn hi hF hu hv huv hf hg
    have hiKill : Integrable (fun F' => if F'.root u ≠ F'.root v then
        f (F'.depth u) * g (F'.depth v) else 0) (transitionLaw x i F) := by
      apply (hiProd.indicator (s := {F' | F'.root u ≠ F'.root v}) (by trivial)).congr
      apply Filter.Eventually.of_forall
      intro F'
      by_cases h : F'.root u ≠ F'.root v <;> simp [h]
    refine ⟨hiKill, (integral_mono hiKill hiProd ?_).trans hle⟩
    intro F'
    dsimp only
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hf0 _) (hg0 _)
  · rw [ite_eq_right huv]
    have heq : ∀ᵐ F' ∂transitionLaw x i F, F'.root u = F'.root v :=
      (ae_iff_prob_eq_one measurable_from_top).mpr
        ((ENNReal.toReal_eq_one_iff _).mp
          (transitionLaw_coalescence_of_eq x i F hu hv (not_ne_iff.mp huv)))
    have hzero : (fun F' => if F'.root u ≠ F'.root v then
        f (F'.depth u) * g (F'.depth v) else 0) =ᵐ[transitionLaw x i F] fun _ => 0 := by
      filter_upwards [heq] with F' h
      simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
    exact ⟨(integrable_const (0 : ℝ)).congr hzero.symm, by rw [integral_congr_ae hzero]; simp⟩

end Reverse
end Freezing1
