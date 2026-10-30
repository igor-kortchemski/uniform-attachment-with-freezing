module

public import Freezing1.ReverseTimestampSupport

/-!
# Exact probabilities of timestamped reverse transitions

Distinct ordered root pairs produce distinct timestamped forests. Thus the
actual kernel assigns mass `1 / (S * (S - 1))` to each legal merge output.
This verifies the local factor in A16; uniqueness of a whole terminal history
and the terminal point-mass formula remain separate obligations.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open MeasureTheory
open scoped Classical ENNReal

/-- The new nonzero timestamp identifies the child root; its new parent then
identifies the first root. Hence no two legal ordered choices coincide. -/
theorem joinChoice_injective_on (F : Forest) {t : ℕ} (ht : t ≠ 0)
    (hzero : ∀ v ∈ F.forest.roots, F.edgeTime v = 0) :
    Set.InjOn (joinChoice F t) (↑F.forest.roots.offDiag : Set ((ℕ ⊕ ℕ) × (ℕ ⊕ ℕ))) := by
  intro p hp q hq he
  change p ∈ F.forest.roots.offDiag at hp
  change q ∈ F.forest.roots.offDiag at hq
  have hp' := Finset.mem_offDiag.mp hp
  have hq' := Finset.mem_offDiag.mp hq
  have hb : p.2 = q.2 := by
    by_contra hne
    have htime := congrArg (fun G : Forest => G.edgeTime p.2) he
    simp only [joinChoice, dite_eq_left hp, dite_eq_left hq,
      Function.update_self, Function.update_of_ne hne] at htime
    exact ht (htime.trans (hzero p.2 hp'.2.1))
  have ha : p.1 = q.1 := by
    have hparent := congrArg (fun G : Forest => G.forest.parent p.2) he
    simpa only [joinChoice, dite_eq_left hp, dite_eq_left hq,
      RootedForest.join, hb, ↓reduceIte] using hparent
  exact Prod.ext ha hb

set_option backward.isDefEq.respectTransparency false in
/-- A legal ordered-root choice has exactly the uniform ordered-pair mass in
the actual timestamped kernel. -/
theorem joinLaw_singleton (F : Forest) {t : ℕ} (ht : t ≠ 0)
    (hzero : ∀ v ∈ F.forest.roots, F.edgeTime v = 0)
    (htwo : 2 ≤ F.forest.roots.card) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    joinLaw F t {joinChoice F t p} = 1 / (F.forest.roots.offDiag.card : ℝ≥0∞) := by
  rw [joinLaw_apply F t htwo]
  have hf : F.forest.roots.offDiag.filter (fun q => joinChoice F t q ∈ ({joinChoice F t p} : Set Forest)) =
      {p} := by
    ext q
    simp only [Finset.mem_filter, Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hq, he⟩
      exact joinChoice_injective_on F ht hzero hq hp he
    · rintro rfl
      exact ⟨hp, rfl⟩
  rw [hf]
  simp

/-- Real-valued normalization of the exact local A16 merge probability. -/
theorem joinLaw_real_singleton (F : Forest) {t : ℕ} (ht : t ≠ 0)
    (hzero : ∀ v ∈ F.forest.roots, F.edgeTime v = 0)
    (htwo : 2 ≤ F.forest.roots.card) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    (joinLaw F t).real {joinChoice F t p} =
      1 / ((F.forest.roots.card : ℝ) * (F.forest.roots.card - 1)) := by
  rw [Measure.real, joinLaw_singleton F ht hzero htwo hp, ENNReal.toReal_div]
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast]
  rw [card_offDiag_real _ (by omega)]

/-- Under the exact source schedule hypotheses, the actual reverse plus-step
point mass has denominator `S_(i+1) (S_(i+1)-1)`. -/
theorem transitionLaw_attachment_singleton {x : SignSequence} {n i : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hx : x (i + 1) = true) (hF : Reverse.ValidAt x n (i + 1) F.forest)
    (ht : TimesValidAt x n (i + 1) F) {p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)}
    (hp : p ∈ F.forest.roots.offDiag) :
    (transitionLaw x i F).real {joinChoice F (i + 1) p} =
      1 / ((activeCount x (i + 1) : ℝ) * (activeCount x (i + 1) - 1)) := by
  have hiτ : ((i + 1 : ℕ) : ℕ∞) ≤ extinctionTime x :=
    le_trans (show ((i + 1 : ℕ) : ℕ∞) ≤ n by exact_mod_cast (Nat.succ_le_of_lt hi)) hn
  have htwo : 2 ≤ F.forest.roots.card := by
    rw [hF.roots_card]
    exact two_le_activeCount_toNat_succ_of_attachment hiτ hx
  have hc : ((activeCount x (i + 1)).toNat : ℝ) = (activeCount x (i + 1) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime hiτ)
  simp only [transitionLaw, hx, ↓reduceIte]
  rw [joinLaw_real_singleton F (by omega)
    (fun v hv => (ht.root_zero v (RootedForest.mem_roots.mp hv).1).mpr hv) htwo hp,
    hF.roots_card, hc]

/-- A freezing step inserts its prescribed singleton with probability one. -/
theorem transitionLaw_freezing_singleton {x : SignSequence} {i : ℕ} (F : Forest)
    (hx : x (i + 1) = false) :
    (transitionLaw x i F).real {insertLabel F i} = 1 := by
  simp [transitionLaw, hx, Measure.real]

end Freezing1.ReverseStamped
