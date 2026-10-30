module

public import Freezing1.ForwardForestMarkedVertexGeometry
public import Freezing1.ForwardForestConditionalChainMean

/-! The source's individual good-chain events, including marked roots. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def goodVertexIndicator (C k₀ k : ℕ) (t : ℝ) (v : ℕ) (q : State) : ℝ :=
  if v ∈ goodSet q C k₀ k t then 1 else 0

theorem treeLaw_goodSet_succ_eq_filter (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k) (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x) (t : ℝ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)), goodSet q C k₀ (k + 1) t =
      q.active.filter fun v => cutAncestor q (C ^ k) v ∈ goodSet (truncateAt q (C ^ k)) C k₀ k t ∧
        t < (cutHeight q (C ^ k) v : ℝ) := by
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
    continuationLaw_truncate_self hpast hn] with q hgood hprefix
  rw [hprefix]
  exact hgood

theorem goodVertexIndicator_succ_eq_marked (x : SignSequence) {C k₀ k v : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k) (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (t : ℝ) (hv : C ^ k < v) :
    goodVertexIndicator C k₀ (k + 1) t v =ᵐ[treeLaw x (C ^ (k + 1))]
      markedVertexIndicator (fun s => goodSet s C k₀ k t) (C ^ k) t v := by
  filter_upwards [treeLaw_goodSet_succ_eq_filter x hC hk hb t,
    treeLaw_hasHistory x (C ^ (k + 1)) hb] with q hset hq
  rw [markedVertexIndicator_eq_actual hq hb _ (C ^ k) t v hv]
  unfold goodVertexIndicator
  rw [hset]
  simp only [Finset.mem_filter]

theorem goodVertexIndicator_succ_zero_before_cut (x : SignSequence) {C k₀ k v : ℕ}
    (hk : k₀ ≤ k) {t : ℝ} (ht : 0 ≤ t) (hv : v ≤ C ^ k) :
    goodVertexIndicator C k₀ (k + 1) t v =ᵐ[treeLaw x (C ^ (k + 1))] (fun _ => 0) := by
  filter_upwards [treeLaw_valid x (C ^ (k + 1))] with q hq
  have hn : v ∉ goodSet q C k₀ (k + 1) t := by
    intro hg
    have hh := ((goodSet_succ_iff hk hq t v).mp hg).2
    have hz : cutHeight q (C ^ k) v = 0 := cutHeightAux_eq_zero_of_le _ _ _ v hv
    rw [hz, Nat.cast_zero] at hh
    exact not_lt_of_ge ht hh
  simp only [goodVertexIndicator, hn, ite_false]

/-- Same-component vertices share exactly the old good mark; this is the
source's remaining deterministic explanation in the covariance argument. -/
theorem goodVertexIndicators_same_component (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k) (hb : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (t : ℝ) (v w : ℕ) :
    ∀ᵐ q ∂treeLaw x (C ^ (k + 1)), v ∈ q.active → w ∈ q.active →
      t < (cutHeight q (C ^ k) v : ℝ) → t < (cutHeight q (C ^ k) w : ℝ) →
      cutAncestor q (C ^ k) v = cutAncestor q (C ^ k) w →
      goodVertexIndicator C k₀ (k + 1) t v q = goodVertexIndicator C k₀ (k + 1) t w q := by
  filter_upwards [treeLaw_goodSet_succ_eq_filter x hC hk hb t] with q hset
  intro hv hw htv htw hanc
  unfold goodVertexIndicator
  rw [hset]
  simp only [Finset.mem_filter, hv, hw, htv, htw, and_true, true_and, hanc]

end Freezing1.Forward
