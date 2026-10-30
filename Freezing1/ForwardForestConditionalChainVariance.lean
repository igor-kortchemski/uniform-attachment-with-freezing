module

public import Freezing1.ForwardForestConditionalVariance
public import Freezing1.ForwardForestConditionalChainMean
public import Mathlib.Probability.CondVar

/-! The literal source conditional variance bound for the actual good chain. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem condVar_markedTallCount_given_forest (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (G : State → Finset ℕ)
    (hG : ∀ s, HasHistory x a s → G s ⊆ s.active) {t : ℝ} (ht : 0 ≤ t) :
    condVar (MeasurableSpace.comap (pastBareForest x a) inferInstance)
      (fun q => (markedTallCount G a t q : ℝ)) (treeLaw x b) ≤ᵐ[treeLaw x b]
      (fun q => (componentMaximum q a : ℝ) *
        (treeLaw x b)[(fun r => (markedTallCount G a t r : ℝ)) |
          MeasurableSpace.comap (pastBareForest x a) inferInstance] q) := by
  have hmean := condExp_markedTallCount x hab hb G hG ht
  have hbound := condExp_markedTallCount_centered_sq_le x hab hb G hG ht
  have hsquare :
      (((fun q => (markedTallCount G a t q : ℝ)) -
        (treeLaw x b)[(fun q => (markedTallCount G a t q : ℝ)) |
          MeasurableSpace.comap (pastBareForest x a) inferInstance]) ^ 2) =ᵐ[treeLaw x b]
        (fun q => ((markedTallCount G a t q : ℝ) -
          ((G (truncateAt q a)).card : ℝ) / (activeCount x a).toNat * blockTallCount q a b t) ^ 2) := by
    filter_upwards [hmean] with q hq
    simp only [Pi.pow_apply, Pi.sub_apply, hq]
  have hvar := condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x a) inferInstance) hsquare
  change condVar (MeasurableSpace.comap (pastBareForest x a) inferInstance)
    (fun q => (markedTallCount G a t q : ℝ)) (treeLaw x b) =ᵐ[treeLaw x b] _ at hvar
  filter_upwards [hvar, hbound, hmean] with q hv hbq hmq
  rw [hv, hmq]
  exact hbq

/-- Source 14/07/19hb, including the complete unlabelled all-star forest
in the conditioning and its marked-root component maximum. -/
theorem condVar_goodSet_succ_given_forest (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ} (ht : 0 ≤ t) :
    condVar (MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance)
      (fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)) (treeLaw x (C ^ (k + 1))) ≤ᵐ[treeLaw x (C ^ (k + 1))]
      (fun q => (componentMaximum q (C ^ k) : ℝ) *
        (treeLaw x (C ^ (k + 1)))[(fun r => ((goodSet r C k₀ (k + 1) t).card : ℝ)) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q) := by
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have hgood := treeLaw_goodSet_succ_eq_markedTallCount x hC hk hb t
  have hgoodReal : (fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)) =ᵐ[treeLaw x (C ^ (k + 1))]
      (fun q => (markedTallCount (fun s => goodSet s C k₀ k t) (C ^ k) t q : ℝ)) :=
    hgood.mono (fun _ hq => congrArg Nat.cast hq)
  have hv := condVar_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hgoodReal
  have he := condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hgoodReal
  have hbound := condVar_markedTallCount_given_forest x hab hb (fun s => goodSet s C k₀ k t)
    (fun s _ => goodSet_subset s C k₀ k t) ht
  filter_upwards [hv, he, hbound] with q hvq heq hbq
  rw [hvq, heq]
  exact hbq

end Freezing1.Forward
