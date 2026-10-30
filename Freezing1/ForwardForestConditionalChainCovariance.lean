module

public import Freezing1.ForwardForestConditionalVertexCovariance
public import Freezing1.ForwardForestChainVertexEvents

/-! Source A52: actual good-chain events in distinct forest components are conditionally negatively correlated. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Conditional covariance is nonpositive for distinct components of the
source's bare all-star forest. Old marked roots have height zero and are
handled explicitly rather than silently counted as genuinely active. -/
theorem goodVertices_conditionally_negatively_correlated (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ} (ht : 0 ≤ t) (v w : ℕ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)),
      v ∈ (starForest q (C ^ k)).active → w ∈ (starForest q (C ^ k)).active →
      cutAncestor q (C ^ k) v ≠ cutAncestor q (C ^ k) w →
      (treeLaw x (C ^ (k + 1)))[(fun r =>
        goodVertexIndicator C k₀ (k + 1) t v r * goodVertexIndicator C k₀ (k + 1) t w r) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q -
        (treeLaw x (C ^ (k + 1)))[goodVertexIndicator C k₀ (k + 1) t v |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q *
        (treeLaw x (C ^ (k + 1)))[goodVertexIndicator C k₀ (k + 1) t w |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤ 0 := by
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have haτ : ((C ^ k : ℕ) : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : ((C ^ k : ℕ) : ℕ∞) ≤ C ^ (k + 1)).trans hb
  have hm : (activeCount x (C ^ k)).toNat ≤ C ^ k + 1 := by
    have hnon := activeCount_nonneg_of_le_extinctionTime haτ
    have hu := activeCount_le_plusCount_add_one x (C ^ k)
    have hp := plusCount_le x (C ^ k)
    omega
  by_cases hv : C ^ k < v
  · by_cases hw : C ^ k < w
    · have hgoodV := goodVertexIndicator_succ_eq_marked x hC hk hb t hv
      have hgoodW := goodVertexIndicator_succ_eq_marked x hC hk hb t hw
      have hgoodPair : (fun r => goodVertexIndicator C k₀ (k + 1) t v r *
          goodVertexIndicator C k₀ (k + 1) t w r) =ᵐ[treeLaw x (C ^ (k + 1))]
          (fun r => markedVertexIndicator (fun s => goodSet s C k₀ k t) (C ^ k) t v r *
            markedVertexIndicator (fun s => goodSet s C k₀ k t) (C ^ k) t w r) := by
        filter_upwards [hgoodV, hgoodW] with q hvq hwq
        rw [hvq, hwq]
      have hpair := condExp_markedVertexIndicators_pair_le x hab hb (fun s => goodSet s C k₀ k t)
        (fun s _ => goodSet_subset s C k₀ k t) hm t v hv w hw
      filter_upwards [hpair,
        condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hgoodV,
        condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hgoodW,
        condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hgoodPair,
        treeLaw_hasHistory x (C ^ (k + 1)) hb] with q hpairq hcv hcw hcp hq
      intro hvStar hwStar hsep
      have hvq := (starForest_active_after_iff q hv).mp hvStar
      have hwq := (starForest_active_after_iff q hw).mp hwStar
      apply sub_nonpos.mpr
      rw [hcv, hcw, hcp]
      exact hpairq (forestVertexSeparated_slotForest_of_actual hq hb hv hw hvq hwq hsep)
    · have hzero := goodVertexIndicator_succ_zero_before_cut x hk ht (Nat.le_of_not_gt hw)
      have hprodZero : (fun r => goodVertexIndicator C k₀ (k + 1) t v r *
          goodVertexIndicator C k₀ (k + 1) t w r) =ᵐ[treeLaw x (C ^ (k + 1))] (fun _ => 0) := by
        filter_upwards [hzero] with q hq
        rw [hq, mul_zero]
      have hcw := condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hzero
      have hcp := condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hprodZero
      filter_upwards [hcw, hcp] with q hwq hpq
      intro _ _ _
      rw [hpq, hwq]
      change (treeLaw x (C ^ (k + 1)))[(0 : State → ℝ) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q -
        (treeLaw x (C ^ (k + 1)))[goodVertexIndicator C k₀ (k + 1) t v |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q *
        (treeLaw x (C ^ (k + 1)))[(0 : State → ℝ) |
          MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤ 0
      simp only [condExp_zero, Pi.zero_apply, mul_zero, sub_zero, le_refl]
  · have hzero := goodVertexIndicator_succ_zero_before_cut x hk ht (Nat.le_of_not_gt hv)
    have hprodZero : (fun r => goodVertexIndicator C k₀ (k + 1) t v r *
        goodVertexIndicator C k₀ (k + 1) t w r) =ᵐ[treeLaw x (C ^ (k + 1))] (fun _ => 0) := by
      filter_upwards [hzero] with q hq
      rw [hq, zero_mul]
    have hcv := condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hzero
    have hcp := condExp_congr_ae (m := MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance) hprodZero
    filter_upwards [hcv, hcp] with q hvq hpq
    intro _ _ _
    rw [hpq, hvq]
    change (treeLaw x (C ^ (k + 1)))[(0 : State → ℝ) |
      MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q -
      (treeLaw x (C ^ (k + 1)))[(0 : State → ℝ) |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q *
      (treeLaw x (C ^ (k + 1)))[goodVertexIndicator C k₀ (k + 1) t w |
        MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] q ≤ 0
    simp only [condExp_zero, Pi.zero_apply, zero_mul, sub_zero, le_refl]

end Freezing1.Forward
