module

public import Freezing1.InterleavedChainCylinders
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD

/-!
# Resolving a partially observed cylinder

A completion probability becomes the indicator of the actual finite word
once enough states have been observed, or once the last state is absorbing.
The latter case is essential for the source's fallback convention.
-/

@[expose] public section

namespace Freezing1.InterleavedChain

open MeasureTheory ProbabilityTheory CountableMarkovChain
open scoped ENNReal Classical

variable {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/-- Read a finite word, padding it by a fixed value if it is too short. -/
def paddedWord (d : E) (zs : List E) (n : ℕ) : List E :=
  List.ofFn (fun i : Fin n => zs.getD i.val d)

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem paddedWord_zero (d : E) (zs : List E) : paddedWord d zs 0 = [] := rfl

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem paddedWord_nil (d : E) (n : ℕ) :
    paddedWord d [] n = List.replicate n d := by simp [paddedWord]

omit [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E] in
@[simp] theorem paddedWord_cons_succ (d z : E) (zs : List E) (n : ℕ) :
    paddedWord d (z :: zs) (n + 1) = z :: paddedWord d zs n := by
  simp [paddedWord, List.ofFn_succ]

omit [Countable E] in
/-- An absorbing Markov state has exactly the constant future word. -/
theorem wordProbability_of_absorbing (α : Kernel E E) [IsMarkovKernel α]
    {x : E} (hx : Absorbing α x) (ys : List E) :
    wordProbability α x ys = if ys = List.replicate ys.length x then 1 else 0 := by
  induction ys with
  | nil => simp [wordProbability]
  | cons y ys ih =>
    have hdir := (absorbing_iff_eq_dirac α x).mp hx
    by_cases hy : y = x
    · subst y
      simp [wordProbability, hdir, ih, List.replicate_succ]
    · have hxy : x ≠ y := Ne.symm hy
      simp [wordProbability, hdir, hy, hxy, List.replicate_succ]

omit [Countable E] in
/-- Either the requested cylinder has been fully seen or the unseen part is
forced by absorption. In both cases the completion is the exact indicator. -/
theorem completion_resolved (α : Kernel E E) [IsMarkovKernel α]
    (x : E) (zs ys : List E)
    (h : ys.length ≤ zs.length ∨ Absorbing α (zs.getLastD x)) :
    completion α x zs ys =
      if paddedWord (zs.getLastD x) zs ys.length = ys then 1 else 0 := by
  induction zs generalizing x ys with
  | nil =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have hx : Absorbing α x := by simpa using h
      rw [completion_nil_observed, wordProbability_of_absorbing α hx]
      simp only [List.getLastD_nil, paddedWord_nil, eq_comm]
  | cons z zs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      have ht : ys.length ≤ zs.length ∨ Absorbing α (zs.getLastD z) := by
        simpa only [List.length_cons, Nat.add_le_add_iff_right, List.getLastD_cons] using h
      by_cases hzy : z = y
      · subst z
        simpa only [completion, ite_true, List.length_cons, paddedWord_cons_succ,
          List.cons.injEq, true_and, List.getLastD_cons] using ih y ys ht
      · simp [completion, hzy, paddedWord_cons_succ]

end Freezing1.InterleavedChain
