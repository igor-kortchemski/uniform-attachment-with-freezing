module

public import Freezing1.InterleavedWordResolution
public import Freezing1.CountableMarkovObservations

/-!
# Finite cylinders of the genuine homogeneous Markov path

The scalar product of transition masses is identified with the actual
probability of each prescribed future word under Ionescu--Tulcea.
-/

@[expose] public section

namespace Freezing1.CountableMarkovChain

open MeasureTheory ProbabilityTheory InterleavedChain
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

def futureWord (H : ℕ → E) (n : ℕ) : List E :=
  List.ofFn (fun i : Fin n => H (i.val + 1))

theorem measurable_futureWord (n : ℕ) : Measurable (fun H : ℕ → E => futureWord H n) :=
  (measurable_of_countable (List.ofFn : (Fin n → E) → List E)).comp (by fun_prop)

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem accumulate_append_eq_futureWord (H : ℕ → E) (n : ℕ) :
    accumulate [] (fun l z => l ++ [z]) H n = futureWord H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [accumulate_succ, ih]
    simp only [futureWord, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last]

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
theorem futureWord_getLastD (H : ℕ → E) (n : ℕ) :
    (futureWord H n).getLastD (H 0) = H n := by
  cases n with
  | zero => rfl
  | succ n =>
    rw [futureWord, List.ofFn_succ', List.concat_eq_append, List.getLastD_concat]
    rfl

theorem lintegral_completion_futureWord (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (u : List E) (n : ℕ) :
    ∫⁻ H, completion α x (futureWord H n) u ∂fullLaw α x = wordProbability α x u := by
  have hh : ∀ k, ∀ᵐ H ∂fullLaw α x,
      ∫⁻ z, completion α x (accumulate [] (fun l z => l ++ [z]) H k ++ [z]) u ∂α (H k) =
        completion α x (accumulate [] (fun l z => l ++ [z]) H k) u := by
    intro k
    filter_upwards [fullLaw_initial α x] with H hzero
    rw [accumulate_append_eq_futureWord]
    have hlast : (futureWord H k).getLastD x = H k := by rw [← hzero, futureWord_getLastD]
    rw [← hlast]
    exact lintegral_completion_append α x _ u
  simpa only [accumulate_append_eq_futureWord, completion_nil_observed] using
    lintegral_accumulate_of_harmonic α x [] (fun l z => l ++ [z])
      (fun l _ => completion α x l u) hh n

/-- Probability of a prescribed future word, excluding the fixed initial
state and including every transition in its stated order. -/
theorem futureWord_probability (α : Kernel E E) [IsMarkovKernel α] (x : E) (u : List E) :
    (fullLaw α x) {H | futureWord H u.length = u} = wordProbability α x u := by
  have hm : MeasurableSet {H : ℕ → E | futureWord H u.length = u} :=
    ((measurable_futureWord u.length).eq measurable_const).setOf
  have hcomp : ∀ H : ℕ → E,
      completion α x (futureWord H u.length) u =
        ({H | futureWord H u.length = u} : Set (ℕ → E)).indicator 1 H := by
    intro H
    have hlen : (futureWord H u.length).length = u.length := List.length_ofFn
    rw [completion_resolved α x _ u (Or.inl hlen.ge)]
    have hp : paddedWord ((futureWord H u.length).getLastD x) (futureWord H u.length) u.length =
        futureWord H u.length := by
      unfold paddedWord
      simp only [futureWord]
      apply congrArg List.ofFn
      funext i
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt)]
      simp
    rw [hp]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  calc
    _ = ∫⁻ H, completion α x (futureWord H u.length) u ∂fullLaw α x := by
      simp_rw [hcomp]
      exact (lintegral_indicator_one hm).symm
    _ = _ := lintegral_completion_futureWord α x u u.length

end Freezing1.CountableMarkovChain
