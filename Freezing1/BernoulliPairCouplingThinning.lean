module

public import Freezing1.BernoulliPairCouplingWords
public import Freezing1.BernoulliPairCouplingActual

/-! Genuine independent thinning of the enlarged Bernoulli driver array. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem bind_bernoulli_nat {α : Type*} [MeasurableSpace α]
    (p : unitInterval) (K : ℕ → Measure α) :
    (bernoulliMeasure (1 : ℕ) 0 p).bind K =
      unitInterval.toNNReal p • K 1 + unitInterval.toNNReal (unitInterval.symm p) • K 0 := by
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_countable _).aemeasurable]
  simp [bernoulliMeasure_def, lintegral_add_measure, Measure.add_apply, Measure.smul_apply]

theorem bernoulli_product_mul (p q r : unitInterval)
    (hpqr : (q : ℝ) * (r : ℝ) = p) :
    ((bernoulliMeasure (1 : ℕ) 0 q).prod (bernoulliMeasure (1 : ℕ) 0 r)).map
        (fun z => z.1 * z.2) = bernoulliMeasure (1 : ℕ) 0 p := by
  rw [Measure.prod_eq_of_sfinite,
    Measure.map_bind (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  have he : (fun x : ℕ =>
      ((bernoulliMeasure (1 : ℕ) 0 r).map (Prod.mk x)).map (fun z => z.1 * z.2)) =
      (fun x => bernoulliMeasure x 0 r) := by
    funext x
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      map_bernoulliMeasure]
    simp only [Function.comp_def, mul_one, mul_zero]
  rw [he, bind_bernoulli_nat, bernoulliMeasure_self_eq_dirac]
  have h1 : unitInterval.toNNReal q * unitInterval.toNNReal r = unitInterval.toNNReal p := by
    apply NNReal.coe_injective
    simpa only [NNReal.coe_mul, unitInterval.coe_toNNReal] using hpqr
  have h0 : unitInterval.toNNReal q * unitInterval.toNNReal (unitInterval.symm r) +
      unitInterval.toNNReal (unitInterval.symm q) = unitInterval.toNNReal (unitInterval.symm p) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, NNReal.coe_mul, unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    linarith only [hpqr]
  rw [bernoulliMeasure_def, smul_add, smul_smul, smul_smul, add_assoc, ← add_smul, h1, h0]
  rfl

def thinningWord {k : ℕ} (z : Word k × Word k) : Word k := fun j => z.1 j * z.2 j

/-- This is a product probability space of the enlarged drivers and fresh
independent retention coins. -/
noncomputable def thinningLaw (p q : ℕ → unitInterval) (a k : ℕ) :
    Measure (Word k × Word k) :=
  (wordLaw q a k).prod (wordLaw (fun i => unitInterval.symm (p i)) a k)

instance thinningLaw_probability (p q : ℕ → unitInterval) (a k : ℕ) :
    IsProbabilityMeasure (thinningLaw p q a k) := by unfold thinningLaw; infer_instance

theorem thinningLaw_map (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) :
    (thinningLaw p q a k).map thinningWord = wordLaw p a k := by
  let μ := fun j : Fin k => bernoulliMeasure (1 : ℕ) 0 (descendingParameter q a k j)
  let ν := fun j : Fin k => bernoulliMeasure (1 : ℕ) 0
    (descendingParameter (fun i => unitInterval.symm (p i)) a k j)
  have hp (j : Fin k) :
      (descendingParameter q a k j : ℝ) *
          (descendingParameter (fun i => unitInterval.symm (p i)) a k j : ℝ) =
        descendingParameter p a k j := by
    dsimp only [descendingParameter]
    rw [unitInterval.coe_symm_eq, mul_comm]
    exact hpq _ (by have := j.isLt; omega) (by have := j.isLt; omega)
  have hprod := (measurePreserving_arrowProdEquivProdArrow ℕ ℕ (Fin k) μ ν).map_eq
  have hm := (measurePreserving_pi (fun j => (μ j).prod (ν j))
    (fun j => bernoulliMeasure (1 : ℕ) 0 (descendingParameter p a k j))
    (f := fun _ z => z.1 * z.2) (fun j =>
      ⟨measurable_of_countable _, bernoulli_product_mul _ _ _ (hp j)⟩)).map_eq
  change ((Measure.pi μ).prod (Measure.pi ν)).map thinningWord = wordLaw p a k
  rw [← hprod, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  exact hm

theorem wordLaw_binary (p : ℕ → unitInterval) (a k : ℕ) :
    ∀ᵐ w ∂wordLaw p a k, ∀ j, w j = 0 ∨ w j = 1 := by
  rw [ae_all_iff]
  intro j
  have hj := wordLaw_coordinate p a k j
  apply ae_of_ae_map (f := fun w : Word k => w j)
    (p := fun y : ℕ => y = 0 ∨ y = 1) hj.aemeasurable
  rw [hj.map_eq]
  apply (ae_iff_prob_eq_one (measurable_of_countable _)).mpr
  simp

/-- The thinned coordinates are pointwise below the enlarged coordinates. -/
theorem thinningLaw_le (p q : ℕ → unitInterval) (a k : ℕ) :
    ∀ᵐ z ∂thinningLaw p q a k, ∀ j, thinningWord z j ≤ z.1 j := by
  have hν : ∀ᵐ z ∂thinningLaw p q a k, ∀ j, z.2 j = 0 ∨ z.2 j = 1 := by
    apply ae_of_ae_map (f := Prod.snd) (p := fun w : Word k => ∀ j, w j = 0 ∨ w j = 1)
      measurable_snd.aemeasurable
    rw [thinningLaw, Measure.map_snd_prod, measure_univ, one_smul]
    exact wordLaw_binary _ _ _
  exact hν.mono fun z hz j => by rcases hz j with h | h <;> simp [thinningWord, h]

end Freezing1.BernoulliPairCoupling
