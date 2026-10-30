module

public import Freezing1.BernoulliPairCouplingThinning
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The source's exact discrepancy expectation and tail comparison on its thinning space. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

def wordSum {k : ℕ} (w : Word k) : ℕ := ∑ j, w j

theorem wordLaw_coordinate_integrable (p : ℕ → unitInterval) (a k : ℕ) (j : Fin k) :
    Integrable (fun w : Word k => (w j : ℝ)) (wordLaw p a k) :=
  (wordLaw_coordinate p a k j).integrable_fun_comp
    (integrable_bernoulliMeasure _ _ _ (fun m : ℕ => (m : ℝ)))

theorem wordLaw_coordinate_integral (p : ℕ → unitInterval) (a k : ℕ) (j : Fin k) :
    (∫ w : Word k, (w j : ℝ) ∂wordLaw p a k) = descendingParameter p a k j := by
  have h := (wordLaw_coordinate p a k j).integral_comp
    (f := fun m : ℕ => (m : ℝ)) (measurable_of_countable _).aestronglyMeasurable
  simpa only [Function.comp_def, integral_bernoulliMeasure, Nat.cast_one, Nat.cast_zero,
    smul_eq_mul, mul_one, mul_zero, add_zero] using h

theorem wordLaw_sum_integrable (p : ℕ → unitInterval) (a k : ℕ) :
    Integrable (fun w : Word k => (wordSum w : ℝ)) (wordLaw p a k) := by
  simpa only [wordSum, Nat.cast_sum] using
    integrable_finsetSum Finset.univ (fun j _ => wordLaw_coordinate_integrable p a k j)

theorem wordLaw_sum_integral (p : ℕ → unitInterval) (a k : ℕ) :
    (∫ w : Word k, (wordSum w : ℝ) ∂wordLaw p a k) =
      ∑ j : Fin k, (descendingParameter p a k j : ℝ) := by
  simp only [wordSum, Nat.cast_sum]
  rw [integral_finsetSum _ (fun j _ => wordLaw_coordinate_integrable p a k j)]
  exact Finset.sum_congr rfl fun j _ => wordLaw_coordinate_integral p a k j

def thinningDiscrepancy {k : ℕ} (z : Word k × Word k) : ℕ :=
  wordSum z.1 - wordSum (thinningWord z)

theorem thinningLaw_sum_le (p q : ℕ → unitInterval) (a k : ℕ) :
    ∀ᵐ z ∂thinningLaw p q a k, wordSum (thinningWord z) ≤ wordSum z.1 :=
  (thinningLaw_le p q a k).mono fun _ hz => Finset.sum_le_sum fun j _ => hz j

theorem thinningLaw_fst_hasLaw (p q : ℕ → unitInterval) (a k : ℕ) :
    HasLaw Prod.fst (wordLaw q a k) (thinningLaw p q a k) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [thinningLaw, Measure.map_fst_prod, measure_univ, one_smul]

theorem thinningLaw_discrepancy_integrable (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) :
    Integrable (fun z => (thinningDiscrepancy z : ℝ)) (thinningLaw p q a k) := by
  have hQ := (thinningLaw_fst_hasLaw p q a k).integrable_fun_comp (wordLaw_sum_integrable q a k)
  have hT : HasLaw thinningWord (wordLaw p a k) (thinningLaw p q a k) :=
    ⟨(measurable_of_countable _).aemeasurable, thinningLaw_map p q a k hpq⟩
  apply (hQ.sub (hT.integrable_fun_comp (wordLaw_sum_integrable p a k))).congr
  filter_upwards [thinningLaw_sum_le p q a k] with z hz
  exact (Nat.cast_sub hz).symm

/-- No rare-small-mean issue is hidden: the expectation is the exact finite
sum of the scalar discrepancies on the constructed monotone coupling. -/
theorem thinningLaw_discrepancy_integral (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) :
    (∫ z, (thinningDiscrepancy z : ℝ) ∂thinningLaw p q a k) =
      ∑ j : Fin k, ((descendingParameter q a k j : ℝ) - descendingParameter p a k j) := by
  have hQlaw := thinningLaw_fst_hasLaw p q a k
  have hTlaw : HasLaw thinningWord (wordLaw p a k) (thinningLaw p q a k) :=
    ⟨(measurable_of_countable _).aemeasurable, thinningLaw_map p q a k hpq⟩
  have he : (fun z => (thinningDiscrepancy z : ℝ)) =ᵐ[thinningLaw p q a k]
      (fun z => (wordSum z.1 : ℝ) - (wordSum (thinningWord z) : ℝ)) :=
    (thinningLaw_sum_le p q a k).mono fun z hz => Nat.cast_sub hz
  rw [integral_congr_ae he,
    integral_sub (hQlaw.integrable_fun_comp (wordLaw_sum_integrable q a k))
      (hTlaw.integrable_fun_comp (wordLaw_sum_integrable p a k))]
  have hQ := hQlaw.integral_comp (f := fun w => (wordSum w : ℝ))
    (measurable_of_countable _).aestronglyMeasurable
  have hT := hTlaw.integral_comp (f := fun w => (wordSum w : ℝ))
    (measurable_of_countable _).aestronglyMeasurable
  rw [show (∫ z, (wordSum z.1 : ℝ) ∂thinningLaw p q a k) =
      ∫ w, (wordSum w : ℝ) ∂wordLaw q a k from hQ,
    show (∫ z, (wordSum (thinningWord z) : ℝ) ∂thinningLaw p q a k) =
      ∫ w, (wordSum w : ℝ) ∂wordLaw p a k from hT,
    wordLaw_sum_integral, wordLaw_sum_integral, Finset.sum_sub_distrib]

theorem nat_tail_gap_eq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (X Y : α → ℕ)
    (hY : Measurable Y) (hle : ∀ᵐ z ∂μ, Y z ≤ X z) (t : ℝ) :
    μ.real {z | t < (X z : ℝ)} - μ.real {z | t < (Y z : ℝ)} =
      μ.real {z | t < (X z : ℝ) ∧ (Y z : ℝ) ≤ t} := by
  let A := {z | t < (X z : ℝ)}
  let B := {z | t < (Y z : ℝ)}
  have hB : MeasurableSet B :=
    hY ((Set.to_countable {m : ℕ | t < (m : ℝ)}).measurableSet)
  have he : μ.real (A ∪ B) = μ.real A := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    filter_upwards [hle] with z hz
    have hz' : (Y z : ℝ) ≤ (X z : ℝ) := by exact_mod_cast hz
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq]
    exact propext ⟨fun h => h.elim id (fun h => h.trans_le hz'), Or.inl⟩
  have hd := measureReal_sdiff' (μ := μ) (s := A) (t := B) hB
  rw [he] at hd
  rw [← hd]
  congr 1
  ext z
  simp only [A, B, Set.mem_sdiff, Set.mem_ofPred_eq, not_lt]

theorem probability_positive_nat_le_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (D : α → ℕ) (hD : Measurable D)
    (hi : Integrable (fun z => (D z : ℝ)) μ) :
    μ.real {z | 0 < D z} ≤ ∫ z, (D z : ℝ) ∂μ := by
  have hm : MeasurableSet {z | 0 < D z} := hD (by measurability)
  have hle : ∀ᵐ z ∂μ, ({z | 0 < D z}.indicator (fun _ => (1 : ℝ))) z ≤ (D z : ℝ) := by
    apply Eventually.of_forall
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with hz
    · exact_mod_cast hz
    · positivity
  have h := integral_mono_ae ((integrable_const (1 : ℝ)).indicator hm) hi hle
  rw [integral_indicator_const (1 : ℝ) hm] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Exact source crossing-event identity, on the constructed coupling. -/
theorem thinningLaw_tail_difference (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) (t : ℝ) :
    (wordLaw q a k).real {w | t < (wordSum w : ℝ)} -
        (wordLaw p a k).real {w | t < (wordSum w : ℝ)} =
      (thinningLaw p q a k).real
        {z | t < (wordSum z.1 : ℝ) ∧ (wordSum (thinningWord z) : ℝ) ≤ t} := by
  have hQ := (thinningLaw_fst_hasLaw p q a k).measureReal_eq
    (p := fun w : Word k => t < (wordSum w : ℝ)) ((Set.to_countable _).measurableSet)
  have hTlaw : HasLaw thinningWord (wordLaw p a k) (thinningLaw p q a k) :=
    ⟨(measurable_of_countable _).aemeasurable, thinningLaw_map p q a k hpq⟩
  have hT := hTlaw.measureReal_eq
    (p := fun w : Word k => t < (wordSum w : ℝ)) ((Set.to_countable _).measurableSet)
  rw [← hQ, ← hT]
  exact nat_tail_gap_eq _ _ _ (measurable_of_countable _)
    (thinningLaw_sum_le p q a k) t

/-- Source A61's expectation/Markov argument, with no coupling assumed. -/
theorem thinningLaw_tail_difference_le (p q : ℕ → unitInterval) (a k : ℕ)
    (hpq : ∀ i, a ≤ i → i < a + k → (1 - (p i : ℝ)) * (q i : ℝ) = p i) (t : ℝ) :
    (wordLaw q a k).real {w | t < (wordSum w : ℝ)} -
        (wordLaw p a k).real {w | t < (wordSum w : ℝ)} ≤
      ∑ j : Fin k, ((descendingParameter q a k j : ℝ) - descendingParameter p a k j) := by
  rw [thinningLaw_tail_difference p q a k hpq t]
  have hs : {z : Word k × Word k | t < (wordSum z.1 : ℝ) ∧
      (wordSum (thinningWord z) : ℝ) ≤ t} ⊆ {z | 0 < thinningDiscrepancy z} := by
    intro z hz
    apply Nat.sub_pos_of_lt
    exact_mod_cast hz.2.trans_lt hz.1
  apply (measureReal_mono hs).trans
  rw [← thinningLaw_discrepancy_integral p q a k hpq]
  exact probability_positive_nat_le_integral _ _ (measurable_of_countable _)
    (thinningLaw_discrepancy_integrable p q a k hpq)

end Freezing1.BernoulliPairCoupling
