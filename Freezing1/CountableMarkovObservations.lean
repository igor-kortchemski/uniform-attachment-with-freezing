module

public import Freezing1.InterleavedChainKernel

/-!
# Finite observations of the genuine Markov path

The conditional-integration formula below follows from the actual joint
past/next-state law. It can be applied to growing finite observation lists,
without postulating their independence or an auxiliary coupling.
-/

@[expose] public section

namespace Freezing1.CountableMarkovChain

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

variable {E A : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- A deterministic statistic accumulated along a finite path, with the
initial state deliberately excluded from the update list. -/
def accumulatePrefix (a : A) (update : A → E → A) :
    (n : ℕ) → ((i : Finset.Iic n) → E) → A
  | 0, _ => a
  | n + 1, H => update
      (accumulatePrefix a update n (Preorder.frestrictLe₂ (π := fun _ => E) n.le_succ H))
      (H ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩)

def accumulate (a : A) (update : A → E → A) (H : ℕ → E) (n : ℕ) : A :=
  accumulatePrefix a update n (Preorder.frestrictLe n H)

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem accumulate_zero (a : A) (update : A → E → A) (H : ℕ → E) :
    accumulate a update H 0 = a := rfl

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem accumulate_succ (a : A) (update : A → E → A) (H : ℕ → E) (n : ℕ) :
    accumulate a update H (n + 1) = update (accumulate a update H n) (H (n + 1)) := rfl

theorem lintegral_accumulate_succ (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (a : A) (update : A → E → A) (f : A → E → ℝ≥0∞) (n : ℕ) :
    ∫⁻ H, f (accumulate a update H (n + 1)) (H (n + 1)) ∂fullLaw α x =
      ∫⁻ H, ∫⁻ z, f (update (accumulate a update H n) z) z ∂α (H n) ∂fullLaw α x := by
  let F : (((i : Finset.Iic n) → E) × E) → ℝ≥0∞ :=
    fun q => f (update (accumulatePrefix a update n q.1) q.2) q.2
  calc
    _ = ∫⁻ q, F q ∂(fullLaw α x).map
        (fun H => (Preorder.frestrictLe n H, H (n + 1))) := by
      rw [lintegral_map (measurable_of_countable _) (by fun_prop)]
      rfl
    _ = ∫⁻ H, ∫⁻ z, F (H, z) ∂historyKernel α n H
        ∂(fullLaw α x).map (Preorder.frestrictLe n) := by
      rw [map_prefix_next, Measure.lintegral_compProd (measurable_of_countable _)]
    _ = _ := by
      rw [lintegral_map (measurable_of_countable _) (by fun_prop)]
      rfl

/-- A bounded or unbounded nonnegative harmonic observation has its initial
expectation at every finite time. The hypothesis is a kernel integral along
the actual path, rather than an independence premise. -/
theorem lintegral_accumulate_of_harmonic (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (a : A) (update : A → E → A) (f : A → E → ℝ≥0∞)
    (h : ∀ n, ∀ᵐ H ∂fullLaw α x,
      ∫⁻ z, f (update (accumulate a update H n) z) z ∂α (H n) =
        f (accumulate a update H n) (H n)) (n : ℕ) :
    ∫⁻ H, f (accumulate a update H n) (H n) ∂fullLaw α x = f a x := by
  induction n with
  | zero =>
    calc
      _ = ∫⁻ _ : ℕ → E, f a x ∂fullLaw α x := by
        apply lintegral_congr_ae
        filter_upwards [fullLaw_initial α x] with H hH
        simp [hH]
      _ = _ := by simp
  | succ n ih =>
    rw [lintegral_accumulate_succ]
    exact (lintegral_congr_ae (h n)).trans ih

/-- Every almost-sure one-step relation holds simultaneously along the
entire genuine chain. -/
theorem fullLaw_steps (α : Kernel E E) [IsMarkovKernel α] (x : E)
    (R : E → E → Prop) (hR : ∀ z, ∀ᵐ z' ∂α z, R z z') :
    ∀ᵐ H ∂fullLaw α x, ∀ n, R (H n) (H (n + 1)) := by
  apply ae_all_iff.mpr
  intro n
  have hh : ∀ᵐ q ∂(fullLaw α x).map (Preorder.frestrictLe n) ⊗ₘ historyKernel α n,
      R (q.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) q.2 := by
    apply Measure.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
    exact Filter.Eventually.of_forall fun H => hR (H ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  rw [← map_prefix_next] at hh
  exact ae_of_ae_map (by fun_prop) hh

end Freezing1.CountableMarkovChain
