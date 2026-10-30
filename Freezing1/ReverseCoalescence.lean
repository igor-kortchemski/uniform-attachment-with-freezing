module

public import Freezing1.ReverseForest
public import Freezing1.RootedForestCoalescence

/-!
# The actual reverse-transition coalescence hazard

For existing vertices in different components, an attachment sign merges them
with probability `1 / choose(S, 2)` and a freezing sign leaves them separate.
Already-coalesced vertices remain together under both operations. These are
one-step laws of Algorithm 2; the joint-history coalescence-time product in
Lemma `loi du temps de coalescence` remains a separate obligation.
-/

@[expose] public section

namespace Freezing1.Reverse

open MeasureTheory
open scoped ENNReal Classical

/-- Inserting a new singleton does not change the root of any existing vertex. -/
theorem insertLabel_root_old (F : Forest) (i : ℕ) {v : ℕ ⊕ ℕ}
    (hv : v ∈ F.vertices) : (insertLabel F i).root v = F.root v := by
  unfold insertLabel
  split_ifs with hi
  · rfl
  · have hvi : v ≠ Sum.inr i := fun h => hi (h ▸ hv)
    simp only [RootedForest.adjoin, hvi, ↓reduceIte]

/-- The actual reverse kernel's hazard in terms of its number of components. -/
theorem transitionLaw_coalescence_roots (x : SignSequence) (i : ℕ) (F : Forest)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huv : F.root u ≠ F.root v) :
    (transitionLaw x i F).real {F' | F'.root u = F'.root v} =
      if x (i + 1) then 1 / (F.roots.card.choose 2 : ℝ) else 0 := by
  cases hx : x (i + 1)
  · simp [transitionLaw, hx, Measure.real, insertLabel_root_old F i hu,
      insertLabel_root_old F i hv, huv]
  · simp only [transitionLaw, hx, ↓reduceIte]
    exact F.joinLaw_coalescence hu hv huv

/-- The exact `1 / choose(S_(i+1), 2)` hazard on a legal reverse state.
Validity supplies the component count, rather than assuming the hazard. -/
theorem transitionLaw_coalescence {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    (transitionLaw x i F).real {F' | F'.root u = F'.root v} =
      if x (i + 1) then 1 / ((activeCount x (i + 1)).toNat.choose 2 : ℝ) else 0 := by
  rw [transitionLaw_coalescence_roots x i F hu hv huv, hF.roots_card]

/-- The ordered-pair form of the same hazard uses the original integer walk
without truncation; distinct existing roots force its value to be at least two. -/
theorem transitionLaw_coalescence_mul {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    (transitionLaw x i F).real {F' | F'.root u = F'.root v} =
      if x (i + 1) then
        2 / ((activeCount x (i + 1) : ℝ) * ((activeCount x (i + 1) : ℝ) - 1)) else 0 := by
  have htwo : 2 ≤ F.roots.card :=
    (show F.roots.Nontrivial from
      ⟨F.root u, F.root_mem_roots hu, F.root v, F.root_mem_roots hv, huv⟩).two_le_card
  have hs : 0 ≤ activeCount x (i + 1) := by
    rw [hF.roots_card] at htwo
    omega
  have hc : ((activeCount x (i + 1)).toNat : ℝ) = (activeCount x (i + 1) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hs
  cases hx : x (i + 1)
  · simpa only [hx, Bool.false_eq_true, ↓reduceIte] using
      transitionLaw_coalescence hF hu hv huv
  · simp only [transitionLaw, hx, ↓reduceIte]
    rw [F.joinLaw_coalescence_mul hu hv huv, hF.roots_card, hc]

/-- The complementary survival factor, including the value one at a
singleton-insertion step. -/
theorem transitionLaw_noncoalescence {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) (huv : F.root u ≠ F.root v) :
    (transitionLaw x i F).real {F' | F'.root u ≠ F'.root v} =
      if x (i + 1) then 1 - 1 / ((activeCount x (i + 1)).toNat.choose 2 : ℝ) else 1 := by
  change (transitionLaw x i F).real ({F' | F'.root u = F'.root v}ᶜ) = _
  rw [probReal_compl_eq_one_sub (by trivial), transitionLaw_coalescence hF hu hv huv]
  cases x (i + 1) <;> simp

/-- Coalescence is permanent under both actual reverse operations. This
includes the equal-vertex case, where the distinct-component hazard is invalid. -/
theorem transitionLaw_coalescence_of_eq (x : SignSequence) (i : ℕ) (F : Forest)
    {u v : ℕ ⊕ ℕ} (hu : u ∈ F.vertices) (hv : v ∈ F.vertices)
    (huv : F.root u = F.root v) :
    (transitionLaw x i F).real {F' | F'.root u = F'.root v} = 1 := by
  cases hx : x (i + 1)
  · simp [transitionLaw, hx, Measure.real, insertLabel_root_old F i hu,
      insertLabel_root_old F i hv, huv]
  · simp only [transitionLaw, hx, ↓reduceIte]
    exact F.joinLaw_coalescence_of_eq huv

/-- A single formula exposes both the already-coalesced and distinct cases. -/
theorem transitionLaw_coalescence_cases {x : SignSequence} {n i : ℕ} {F : Forest}
    (hF : ValidAt x n (i + 1) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    (transitionLaw x i F).real {F' | F'.root u = F'.root v} =
      if F.root u = F.root v then 1 else
        if x (i + 1) then 1 / ((activeCount x (i + 1)).toNat.choose 2 : ℝ) else 0 := by
  by_cases huv : F.root u = F.root v
  · rw [ite_eq_left huv]
    exact transitionLaw_coalescence_of_eq x i F hu hv huv
  · rw [ite_eq_right huv]
    exact transitionLaw_coalescence hF hu hv huv

end Freezing1.Reverse
