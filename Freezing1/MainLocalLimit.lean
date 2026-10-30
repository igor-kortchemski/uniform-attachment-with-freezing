module

public import Freezing1.MainLocalNecessity
public import Freezing1.ForwardDiagonalLocalLimit
public import Freezing1.LocalTreeGraph

/-!
# The Introduction's local-limit theorem

For schedules agreeing eventually at each positive index, with an infinite
limiting schedule, diagonal weak convergence, almost-sure local convergence
of the fixed process, and divergence of the printed freezing sum are
equivalent. The limiting law is the law of the genuine pathwise limit.
No survival assumption is imposed on the approximating schedules.
-/

@[expose] public section

namespace Freezing1

open Forward ForwardInfiniteHistory Filter MeasureTheory
open scoped Topology BigOperators Classical

noncomputable def freezingReciprocalSum (x : SignSequence) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, if x i then 0 else 1 / (activeCount x i : ℝ)

theorem freezingReciprocalSum_eq_range (x : SignSequence) (n : ℕ) :
    freezingReciprocalSum x n = ∑ i ∈ Finset.range n, printedFreezingReciprocal x i := by
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    apply Finset.mem_Icc.mpr
    have := Finset.mem_range.mp hi
    omega
  · intro i hi j hj he
    omega
  · intro j hj
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.mp hj
    refine ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

theorem freezingReciprocalSum_tendsto_iff (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    Tendsto (freezingReciprocalSum x) atTop atTop ↔
      ¬Summable (printedFreezingReciprocal x) := by
  simp only [funext (freezingReciprocalSum_eq_range x)]
  exact (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (printedFreezingReciprocal_nonneg x hτ)).symm

def DiagonalLocalConvergence (x : ℕ → SignSequence) : Prop :=
  ∃ ν : ProbabilityMeasure LocalTree.Tree,
    Tendsto (fun n => localProbabilityLaw (x n) n) atTop (𝓝 ν)

def AlmostSureLocalConvergence (x : SignSequence) : Prop :=
  ∀ᵐ H ∂fullLaw x, ∃ t : LocalTree.Tree,
    Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 t)

theorem local_convergence_almostSure_iff_freezing_divergence (x : SignSequence)
    (hτ : extinctionTime x = ⊤) :
    AlmostSureLocalConvergence x ↔ Tendsto (freezingReciprocalSum x) atTop atTop := by
  rw [freezingReciprocalSum_tendsto_iff x hτ]
  constructor
  · intro hc
    exact not_summable_freezing_of_local_tendsto x hτ
      (tendsto_localProbabilityLaw_of_ae_exists x hc)
  · intro hdiv
    exact (fullLaw_tendsto_localLimit x hτ hdiv).mono fun H hH => ⟨localLimit H, hH⟩

theorem local_convergence_diagonal_iff_freezing_divergence
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) :
    DiagonalLocalConvergence x ↔ Tendsto (freezingReciprocalSum y) atTop atTop := by
  rw [freezingReciprocalSum_tendsto_iff y hτ]
  constructor
  · rintro ⟨ν, hc⟩
    exact not_summable_freezing_of_diagonal_local_tendsto x y hxy hτ hc
  · intro hdiv
    exact ⟨localLimitLaw y, tendsto_diagonal_localProbabilityLaw x y hxy hτ hdiv⟩

/-- The three assertions (I), (II), and (III) in Theorem T01, with the
literal sum over positive freezing times and the actual constructed laws. -/
theorem local_convergence_equivalences
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤) :
    (DiagonalLocalConvergence x ↔ AlmostSureLocalConvergence y) ∧
    (AlmostSureLocalConvergence y ↔ Tendsto (freezingReciprocalSum y) atTop atTop) := by
  have hI := local_convergence_diagonal_iff_freezing_divergence x y hxy hτ
  have hII := local_convergence_almostSure_iff_freezing_divergence y hτ
  exact ⟨hI.trans hII.symm, hII⟩

/-- Identification of the common limit, including measurability of the
pathwise tree. The approximating trees may become extinct before time n. -/
theorem local_convergence_common_limit
    (x : ℕ → SignSequence) (y : SignSequence)
    (hxy : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, x n i = y i)
    (hτ : extinctionTime y = ⊤)
    (hdiv : Tendsto (freezingReciprocalSum y) atTop atTop) :
    AEMeasurable localLimit (fullLaw y) ∧
    (∀ᵐ H ∂fullLaw y,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H))) ∧
    Tendsto (localProbabilityLaw y) atTop (𝓝 (localLimitLaw y)) ∧
    Tendsto (fun n => localProbabilityLaw (x n) n) atTop (𝓝 (localLimitLaw y)) := by
  have hd := (freezingReciprocalSum_tendsto_iff y hτ).mp hdiv
  exact ⟨aemeasurable_localLimit y hτ hd, fullLaw_tendsto_localLimit y hτ hd,
    tendsto_localProbabilityLaw y hτ hd, tendsto_diagonal_localProbabilityLaw x y hxy hτ hd⟩

end Freezing1
