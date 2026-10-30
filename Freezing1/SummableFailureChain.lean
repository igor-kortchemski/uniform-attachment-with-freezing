module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-!
# Chaining a summable family of one-step failures

The finite estimate uses joint events `good k` and `not good (k+1)`; it never
divides by the probability of a conditioning event. A diverging starting
scale and a summable uniform bound then force terminal success. Tree-specific
base and transition bounds must be supplied separately.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory Filter
open scoped BigOperators Topology Classical

theorem finite_failure_chain_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (G : ℕ → Ω → Prop)
    {a b : ℕ} (hab : a ≤ b) :
    μ.real {ω | ¬G b ω} ≤ μ.real {ω | ¬G a ω} +
      ∑ k ∈ Finset.Ico a b, μ.real {ω | G k ω ∧ ¬G (k + 1) ω} := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    have hsub : {ω | ¬G (b + 1) ω} ⊆
        {ω | ¬G b ω} ∪ {ω | G b ω ∧ ¬G (b + 1) ω} := by
      intro ω hω
      by_cases hg : G b ω
      · exact Or.inr ⟨hg, hω⟩
      · exact Or.inl hg
    calc
      _ ≤ μ.real ({ω | ¬G b ω} ∪ {ω | G b ω ∧ ¬G (b + 1) ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ μ.real {ω | ¬G b ω} + μ.real {ω | G b ω ∧ ¬G (b + 1) ω} :=
        measureReal_union_le _ _
      _ ≤ (μ.real {ω | ¬G a ω} +
          ∑ k ∈ Finset.Ico a b, μ.real {ω | G k ω ∧ ¬G (k + 1) ω}) +
            μ.real {ω | G b ω ∧ ¬G (b + 1) ω} := add_le_add ih le_rfl
      _ = _ := by rw [Finset.sum_Ico_succ_top hab]; ring

theorem finite_failure_chain_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (G : ℕ → Ω → Prop)
    {a b : ℕ} (hab : a ≤ b) (q : ℕ → ℝ)
    (hstep : ∀ k ∈ Finset.Ico a b, μ.real {ω | G k ω ∧ ¬G (k + 1) ω} ≤ q k) :
    μ.real {ω | ¬G b ω} ≤ μ.real {ω | ¬G a ω} + ∑ k ∈ Finset.Ico a b, q k := by
  exact (finite_failure_chain_le μ G hab).trans
    (add_le_add le_rfl (Finset.sum_le_sum hstep))

/-- Uniform summable transition errors are sufficient even when the laws
and the two endpoint scales vary with n. -/
theorem tendsto_failure_chain_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) [∀ n, IsFiniteMeasure (μ n)] (G : ℕ → ℕ → Ω → Prop)
    (a b : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (hab : ∀ᶠ n in atTop, a n ≤ b n) (q : ℕ → ℝ)
    (hq0 : ∀ k, 0 ≤ q k) (hq : Summable q)
    (hbase : Tendsto (fun n => (μ n).real {ω | ¬G n (a n) ω}) atTop (𝓝 0))
    (hstep : ∀ᶠ n in atTop, ∀ k ∈ Finset.Ico (a n) (b n),
      (μ n).real {ω | G n k ω ∧ ¬G n (k + 1) ω} ≤ q k) :
    Tendsto (fun n => (μ n).real {ω | ¬G n (b n) ω}) atTop (𝓝 0) := by
  have htail : Tendsto (fun n => (∑' k, q k) - ∑ k ∈ Finset.range (a n), q k)
      atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => ∑' k, q k) atTop (𝓝 (∑' k, q k)) :=
      tendsto_const_nhds
    simpa using hconst.sub (hq.hasSum.tendsto_sum_nat.comp ha)
  have hup := hbase.add htail
  simp only [zero_add] at hup
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hup
  filter_upwards [hab, hstep] with n hn hsn
  refine (finite_failure_chain_bound (μ n) (G n) hn q hsn).trans ?_
  apply add_le_add le_rfl
  have hpartial := hq.sum_le_tsum (Finset.range (b n)) (fun k _ => hq0 k)
  have hsplit := Finset.sum_range_add_sum_Ico q hn
  linarith

end Freezing1
