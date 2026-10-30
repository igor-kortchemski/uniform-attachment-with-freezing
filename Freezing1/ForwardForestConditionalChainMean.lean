module

public import Freezing1.ForwardForestConditionalMean
public import Freezing1.ForwardGoodChainPropagation

/-! The literal full-forest conditional mean for the source's good chain. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem treeLaw_goodSet_succ_eq_markedTallCount (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)), (goodSet q C k₀ (k + 1) t).card =
      markedTallCount (fun s => goodSet s C k₀ k t) (C ^ k) t q := by
  let a := C ^ k
  let b := C ^ (k + 1)
  have hab : a ≤ b := pow_le_pow_right₀ hC (Nat.le_succ k)
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have hn : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  have hμ : treeLaw x b = (treeLaw x a).bind (continuationLaw x a (b - a)) := by
    rw [← treeLaw_add_eq_bind_continuation, he]
  change ∀ᵐ q ∂treeLaw x b, _
  rw [hμ]
  apply ae_bind_of_ae measurable_from_top.aemeasurable (by trivial)
  filter_upwards [treeLaw_hasHistory x a haτ] with past hpast
  filter_upwards [continuationLaw_goodSet_succ x hpast.current.valid hC hk t,
    continuationLaw_hasHistory hpast hn, continuationLaw_truncate_self hpast hn]
    with q hgood hq hprefix
  have hqb : HasHistory x b q := by simpa only [he] using hq
  rw [markedTallCount_eq_actual hqb hb (fun s => goodSet s C k₀ k t) a t, hprefix]
  exact congrArg Finset.card hgood

/-- Source 14/07/19h, now conditioned on the whole actual earlier tree and
complete bare forest. The population denominator includes the initial root. -/
theorem condExp_goodSet_succ_given_forest (x : SignSequence)
    {C k₀ k : ℕ} (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) {t : ℝ} (ht : 0 ≤ t) :
    (treeLaw x (C ^ (k + 1)))[(fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)) |
      MeasurableSpace.comap (pastBareForest x (C ^ k)) inferInstance] =ᵐ[treeLaw x (C ^ (k + 1))]
      (fun q => ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) *
        blockTallCount q (C ^ k) (C ^ (k + 1)) t / (activeCount x (C ^ k) : ℝ)) := by
  have hab : C ^ k ≤ C ^ (k + 1) := pow_le_pow_right₀ hC (Nat.le_succ k)
  have haτ : ((C ^ k : ℕ) : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : ((C ^ k : ℕ) : ℕ∞) ≤ C ^ (k + 1)).trans hb
  have hcast : ((activeCount x (C ^ k)).toNat : ℝ) = (activeCount x (C ^ k) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (activeCount_nonneg_of_le_extinctionTime haτ)
  have hgood := treeLaw_goodSet_succ_eq_markedTallCount x hC hk hb t
  have hgoodReal : (fun q => ((goodSet q C k₀ (k + 1) t).card : ℝ)) =ᵐ[treeLaw x (C ^ (k + 1))]
      (fun q => (markedTallCount (fun s => goodSet s C k₀ k t) (C ^ k) t q : ℝ)) :=
    hgood.mono (fun _ hq => congrArg Nat.cast hq)
  have hmean := condExp_markedTallCount x hab hb (fun s => goodSet s C k₀ k t)
    (fun s _ => goodSet_subset s C k₀ k t) ht
  filter_upwards [condExp_congr_ae hgoodReal, hmean] with q hq hm
  rw [hq, hm, hcast]
  ring

end Freezing1.Forward
