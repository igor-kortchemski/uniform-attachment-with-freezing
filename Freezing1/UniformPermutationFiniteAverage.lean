module

public import Freezing1.UniformPermutationMoments

/-! Finite averaging with any enumeration of the permutation carrier.
This avoids unfolding distinct computable/classical permutation enumerations
when the underlying finite type is instantiated by Fin m. -/

@[expose] public section

namespace Freezing1

open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem integral_uniformPermutation_fintype {ι : Type*} [Fintype ι]
    [Fintype (Equiv.Perm ι)] (f : Equiv.Perm ι → ℝ) :
    (∫ σ, f σ ∂uniformPermutationLaw ι) =
      (Fintype.card (Equiv.Perm ι) : ℝ)⁻¹ * ∑ σ, f σ := by
  have hLaw : uniformPermutationLaw ι = Measure.uniformOfFinset
      (Finset.univ : Finset (Equiv.Perm ι)) := by
    unfold uniformPermutationLaw
    apply congrArg Measure.uniformOfFinset
    ext σ
    simp only [Finset.mem_univ]
  rw [integral_fintype (uniformPermutation_integrable f), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp [hLaw, measureReal_def]

end Freezing1
