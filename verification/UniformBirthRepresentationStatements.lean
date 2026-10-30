module

import Freezing1.UniformBirthRandomMean
import Freezing1.UniformBirthTail

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Classical ProbabilityTheory

namespace UniformBirthAudit

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    ((Reverse.treeLaw x n).bind fun F =>
      (Measure.uniformOfFinset F.vertices).map (fun v => (birthTime n v, F.depth v))) =
    (((uniformVertex x n).map (birthTime n)).prod
      (bernoulliProductLaw (UniformBirth.reciprocalParameter x n h))).map
        (fun z => (z.1, UniformBirth.truncatedSum x z.1 z.2)) :=
  UniformBirth.actualBirthHeightLaw_eq_auxiliary x n h

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (i : Fin n) :
    (UniformBirth.reciprocalParameter x n h i : ℝ) =
      1 / (activeCount x (i.val + 1) : ℝ) := rfl

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    IndepFun Prod.fst Prod.snd
      (((uniformVertex x n).map (birthTime n)).prod
        (bernoulliProductLaw (UniformBirth.reciprocalParameter x n h))) :=
  UniformBirth.auxiliary_birth_indep_array x n h

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) :
    (UniformBirth.auxiliaryLaw x n h)[UniformBirth.randomSum x |
      (inferInstance : MeasurableSpace ℕ).comap Prod.fst] =ᵐ[UniformBirth.auxiliaryLaw x n h]
      (fun z => UniformBirth.truncatedMean x n h z.1) :=
  UniformBirth.randomMean_condExp x n h

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) (hn : 1 ≤ n) :
    ∀ᵐ z ∂UniformBirth.auxiliaryLaw x n h,
      1 / 2 ≤ UniformBirth.randomMean x n h z :=
  UniformBirth.randomMean_ge_half x n h hn

example (x : SignSequence) (n : ℕ) (h : PositiveThrough x n) {b : ℕ} (hb : b ≤ n) :
    heightScale x n - UniformBirth.truncatedMean x n h b =
      heightScaleOn x (Finset.Ioc b n) :=
  UniformBirth.heightScale_sub_truncatedMean x n h hb

example (rows : ℕ → SignSequence) (hrows : ∀ n, PositiveThrough (rows n) n)
    (cutoff : ℕ → ℕ)
    (hsmall : Tendsto (fun n : ℕ => (cutoff n : ℝ) / n) atTop (nhds 0)) :
    Tendsto (fun n => (UniformBirth.auxiliaryLaw (rows n) n (hrows n)).real
      {z | z.1 < cutoff n}) atTop (nhds 0) :=
  UniformBirth.auxiliary_sublinear_birth_tendsto rows hrows cutoff hsmall

#print axioms UniformBirth.actualBirthHeightLaw_eq_auxiliary
#print axioms UniformBirth.auxiliary_coordinates_independent
#print axioms UniformBirth.auxiliary_birth_indep_array
#print axioms UniformBirth.randomMean_condExp
#print axioms UniformBirth.randomMean_eq_heightScale_birth
#print axioms UniformBirth.randomMean_ge_half
#print axioms UniformBirth.heightScale_sub_truncatedMean
#print axioms UniformBirth.printed_inclusive_birth_tail_false
#print axioms UniformBirth.auxiliary_sublinear_birth_tendsto

end UniformBirthAudit
