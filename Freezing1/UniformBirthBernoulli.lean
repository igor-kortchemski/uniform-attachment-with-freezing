module

public import Freezing1.UniformBirthBernoulliParameters
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Actual uniform-vertex heights and an independent birth-truncated array

The equality is joint in birth time and height. The comparison probability
space is explicitly the product of the actual uniform birth law and an
unmasked independent Bernoulli array; independence is proved from this law.
-/

@[expose] public section

namespace Freezing1.UniformBirth

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Classical BigOperators

set_option backward.isDefEq.respectTransparency false

noncomputable def birthLaw (x : SignSequence) (n : ℕ) : Measure ℕ :=
  (uniformVertex x n).map (birthTime n)

theorem birthLaw_probability (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    IsProbabilityMeasure (birthLaw x n) := by
  have : IsProbabilityMeasure (uniformVertex x n) :=
    uniformVertex_isProbabilityMeasure (le_of_lt (h n le_rfl))
  exact Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable
    |>.mpr inferInstance

noncomputable def auxiliaryLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    Measure (ℕ × (Fin n → ℕ)) :=
  (birthLaw x n).prod (bernoulliProductLaw (reciprocalParameter x n h))

instance auxiliaryLaw_probability (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    IsProbabilityMeasure (auxiliaryLaw x n h) := by
  have := birthLaw_probability x n h
  unfold auxiliaryLaw
  infer_instance

theorem auxiliary_array_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    HasLaw Prod.snd (bernoulliProductLaw (reciprocalParameter x n h)) (auxiliaryLaw x n h) := by
  have := birthLaw_probability x n h
  refine ⟨measurable_snd.aemeasurable, ?_⟩
  rw [auxiliaryLaw, Measure.map_snd_prod]
  simp

theorem auxiliary_birth_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    HasLaw Prod.fst (birthLaw x n) (auxiliaryLaw x n h) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [auxiliaryLaw, Measure.map_fst_prod]
  simp

theorem auxiliary_coordinate_hasLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    HasLaw (fun z : ℕ × (Fin n → ℕ) => z.2 i)
      (bernoulliMeasure (1 : ℕ) 0 (reciprocalParameter x n h i)) (auxiliaryLaw x n h) :=
  (bernoulliProductLaw_coordinate _ i).fun_comp (auxiliary_array_hasLaw x n h)

theorem auxiliary_coordinates_independent (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    iIndepFun (fun i : Fin n => fun z : ℕ × (Fin n → ℕ) => z.2 i) (auxiliaryLaw x n h) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun _ => (measurable_of_countable _).aemeasurable)]
  simp_rw [(auxiliary_coordinate_hasLaw x n h _).map_eq]
  exact (auxiliary_array_hasLaw x n h).map_eq

theorem auxiliary_birth_indep_array (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    IndepFun Prod.fst Prod.snd (auxiliaryLaw x n h) := by
  have := birthLaw_probability x n h
  exact indepFun_prod measurable_id measurable_id

noncomputable def actualBirthHeightLaw (x : SignSequence) (n : ℕ) : Measure (ℕ × ℕ) :=
  (Reverse.treeLaw x n).bind fun F =>
    (Measure.uniformOfFinset F.vertices).map (fun v => (birthTime n v, F.depth v))

noncomputable def auxiliaryBirthHeightLaw (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    Measure (ℕ × ℕ) :=
  (auxiliaryLaw x n h).map (fun z => (z.1, truncatedSum x z.1 z.2))

theorem auxiliaryBirthHeightLaw_eq_birth_bind (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    auxiliaryBirthHeightLaw x n h = (birthLaw x n).bind fun b =>
      (bernoulliProductLaw (reciprocalParameter x n h)).map (fun Y => (b, truncatedSum x b Y)) := by
  rw [auxiliaryBirthHeightLaw, auxiliaryLaw, Measure.prod_eq_of_sfinite,
    Measure.map_bind (measurable_of_countable _).aemeasurable (measurable_of_countable _).aemeasurable]
  congr 1
  funext b
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  rfl

theorem actualBirthHeightLaw_eq_uniform_label_bind (x : SignSequence) (n : ℕ)
    (h : PositiveThrough x n) :
    actualBirthHeightLaw x n = (uniformVertex x n).bind fun v =>
      (Reverse.treeLaw x n).map (fun F => (birthTime n v, F.depth v)) := by
  calc
    _ = (Reverse.treeLaw x n).bind (fun F =>
        (uniformVertex x n).map (fun v => (birthTime n v, F.depth v))) := by
      apply Measure.bind_congr_right
      filter_upwards [Reverse.treeLaw_vertices_and_root x n (horizon_le_extinction h)] with F hF
      rw [hF.1]
      rfl
    _ = (Reverse.treeLaw x n).bind (fun F => (uniformVertex x n).bind
        (fun v => Measure.dirac (birthTime n v, F.depth v))) := by
      congr 1
      funext F
      exact (Measure.bind_dirac_eq_map _ (measurable_of_countable _)).symm
    _ = (uniformVertex x n).bind (fun v => (Reverse.treeLaw x n).bind
        (fun F => Measure.dirac (birthTime n v, F.depth v))) := by
      apply Measure.bind_comm
      exact measurable_from_prod_countable_left (fun _ => measurable_from_top)
    _ = _ := by
      congr 1
      funext v
      exact Measure.bind_dirac_eq_map _ measurable_from_top

/-- The source's actual joint `(birth,height)` representation, with an
independent unmasked Bernoulli driving array and no representation premise. -/
theorem actualBirthHeightLaw_eq_auxiliary (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    actualBirthHeightLaw x n = auxiliaryBirthHeightLaw x n h := by
  rw [actualBirthHeightLaw_eq_uniform_label_bind x n h, auxiliaryBirthHeightLaw_eq_birth_bind,
    birthLaw, Measure.bind_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aemeasurable]
  apply Measure.bind_congr_right
  have hv : ∀ᵐ v ∂uniformVertex x n, v ∈ vertexLabels x n := by
    rw [ae_iff]
    simp [uniformVertex, Measure.uniformOfFinset_apply]
  filter_upwards [hv] with v hv
  have hd := Reverse.treeLaw_depth_hasLaw x n (horizon_le_extinction h) hv
  have hz := truncatedSum_hasLaw x n h (birthTime n v)
  have he := (hd.identDistrib hz).comp
    (u := fun d : ℕ => (birthTime n v, d)) (measurable_of_countable _)
  simpa only [Function.comp_def] using he.map_eq

end Freezing1.UniformBirth
