module

public import Freezing1.ForwardVertexDegree

/-! Positive-probability divergence of any actual vertex degree leaves
one positive mass above every finite degree threshold. -/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Filter MeasureTheory Forward
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

def degreeUnbounded (r : ℕ) : Set History :=
  {H | ∀ d : ℕ, ∃ n : ℕ, d < vertexDegree (H n) r}

theorem measurableSet_degreeUnbounded (r : ℕ) : MeasurableSet (degreeUnbounded r) := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.forall
  intro d
  apply Measurable.exists
  intro n
  exact (measurable_from_top : Measurable (fun s : State => d < vertexDegree s r)).comp
    (measurable_pi_apply n)

theorem degreeUnbounded_iff_tendsto {H : History} {r : ℕ}
    (hm : Monotone (fun n => vertexDegree (H n) r)) :
    H ∈ degreeUnbounded r ↔ Tendsto (fun n => vertexDegree (H n) r) atTop atTop := by
  constructor
  · intro h
    apply tendsto_atTop.2
    intro d
    obtain ⟨n, hn⟩ := h d
    filter_upwards [eventually_ge_atTop n] with m hnm
    exact hn.le.trans (hm hnm)
  · intro h d
    exact (h.eventually (eventually_gt_atTop d)).exists

theorem treeLaw_vertexDegree_tail_mono (x : SignSequence) (r d : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    (treeLaw x a) {s | d < vertexDegree s r} ≤ (treeLaw x b) {s | d < vertexDegree s r} := by
  rw [← map_eval x a, ← map_eval x b,
    Measure.map_apply (measurable_pi_apply a) (by trivial),
    Measure.map_apply (measurable_pi_apply b) (by trivial)]
  apply measure_mono_ae
  exact (fullLaw_all_vertexDegree_monotone x).mono fun H hH h =>
    lt_of_lt_of_le h (hH r hab)

theorem treeLaw_vertexDegree_tail_real_mono (x : SignSequence) (r d : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    (treeLaw x a).real {s | d < vertexDegree s r} ≤
      (treeLaw x b).real {s | d < vertexDegree s r} :=
  ENNReal.toReal_mono (measure_ne_top _ _) (treeLaw_vertexDegree_tail_mono x r d hab)

theorem degree_tails_positive_of_unbounded_probability (x : SignSequence) (r : ℕ)
    (hE : (fullLaw x) (degreeUnbounded r) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (treeLaw x n).real {s | d < vertexDegree s r} := by
  let δ := ((fullLaw x) (degreeUnbounded r)).toReal / 2
  have hpos : 0 < ((fullLaw x) (degreeUnbounded r)).toReal :=
    ENNReal.toReal_pos hE (measure_ne_top _ _)
  refine ⟨δ, half_pos hpos, fun d => ?_⟩
  let A : ℕ → Set History := fun n => {H | ∃ k ≤ n, d < vertexDegree (H k) r}
  have hm : Monotone A := by
    intro a b hab H hH
    obtain ⟨k, hka, hk⟩ := hH
    exact ⟨k, hka.trans hab, hk⟩
  have hsub : degreeUnbounded r ⊆ ⋃ n, A n := by
    intro H hH
    obtain ⟨n, hn⟩ := hH d
    exact Set.mem_iUnion.mpr ⟨n, n, le_rfl, hn⟩
  have hmeasure : ((fullLaw x) (degreeUnbounded r)).toReal ≤
      ((fullLaw x) (⋃ n, A n)).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top (fullLaw x) (⋃ n, A n))).comp
    (tendsto_measure_iUnion_atTop (μ := fullLaw x) hm)
  have heq (n : ℕ) : (fullLaw x) (A n) = (treeLaw x n) {s | d < vertexDegree s r} := by
    rw [← map_eval x n, Measure.map_apply (measurable_pi_apply n) (by trivial)]
    apply measure_congr
    filter_upwards [fullLaw_all_vertexDegree_monotone x] with H hH
    apply propext
    constructor
    · rintro ⟨k, hkn, hk⟩
      exact hk.trans_le (hH r hkn)
    · intro hn
      exact ⟨n, le_rfl, hn⟩
  have hgap : δ < ((fullLaw x) (⋃ n, A n)).toReal := by dsimp only [δ]; linarith
  filter_upwards [hlim.eventually (lt_mem_nhds hgap)] with n hn
  change δ < ((fullLaw x) (A n)).toReal at hn
  rw [heq n] at hn
  exact hn.le

end Freezing1.ForwardInfiniteHistory
