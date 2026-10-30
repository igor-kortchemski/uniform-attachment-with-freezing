module

public import Freezing1.BernoulliProductLaw

/-!
# Restricting the coordinates of an actual Bernoulli product sum

Finite insertion identifies the laws under an injective change of coordinates.
This avoids any assumption about a joint representation of forest heights.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped Classical

/-- An injective reindexing preserves the law of the selected Bernoulli sum. -/
theorem bernoulliPartialSumLaw_map {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ) (p : κ → unitInterval) (s : Finset ι) :
    bernoulliPartialSumLaw p (s.map e) = bernoulliPartialSumLaw (p ∘ e) s := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hnot : e i ∉ s.map e := by
      intro h
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp h
      exact hi (e.injective hji ▸ hj)
    rw [Finset.map_insert, bernoulliPartialSumLaw_insert p (s.map e) hnot,
      bernoulliPartialSumLaw_insert (p ∘ e) s hi, ih]
    simp only [Function.comp_apply]

/-- The same paper block `(a,b]` can be indexed either inside `Fin n` or
inside its prefix `Fin b`, without changing the actual independent-sum law. -/
theorem bernoulliPartialSumLaw_fin_restrict {n : ℕ} (p : Fin n → unitInterval)
    (a b : ℕ) (hbn : b ≤ n) :
    bernoulliPartialSumLaw p
      (Finset.univ.filter fun i : Fin n => a ≤ i.val ∧ i.val < b) =
      bernoulliPartialSumLaw
        (fun i : Fin b => p ⟨i.val, i.isLt.trans_le hbn⟩)
        (Finset.univ.filter fun i : Fin b => a ≤ i.val) := by
  let e : Fin b ↪ Fin n :=
    ⟨fun i => ⟨i.val, i.isLt.trans_le hbn⟩, fun i j h => Fin.ext (congrArg (fun z : Fin n => z.val) h)⟩
  have he : (Finset.univ.filter fun i : Fin b => a ≤ i.val).map e =
      Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b) := by
    ext j
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hai, rfl⟩
      exact ⟨hai, i.isLt⟩
    · rintro ⟨haj, hjb⟩
      refine ⟨⟨j.val, hjb⟩, haj, ?_⟩
      exact Fin.ext rfl
  rw [← he]
  exact bernoulliPartialSumLaw_map e p _

end Freezing1
