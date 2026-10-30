module

public import Freezing1.ForwardBlockIndependence
public import Freezing1.ForwardGoodChainStep
public import Mathlib.Probability.ConditionalProbability

/-!
# Conditional good-chain failure, with zero-probability events explicit

The independence of the actual pair `(N,M)` from the earlier tree and the
true continuation growth bound give the source's conditional one-step
estimate. Conditioning is Mathlib's normalized restriction; it is the zero
measure when the conditioning event has probability zero.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem treeLaw_prefix_inter_event_le (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x)
    (A : Set State) (hA : MeasurableSet A) (B : Set State) {r : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ s, HasHistory x a s → s ∈ A →
      (continuationLaw x a (b - a) s).real B ≤ r) :
    (treeLaw x b).real {q | truncateAt q a ∈ A ∧ q ∈ B} ≤
      r * (treeLaw x a).real A := by
  have he : a + (b - a) = b := Nat.add_sub_of_le hab
  have hτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by rw [he]; exact hb
  have ha : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab : (a : ℕ∞) ≤ b).trans hb
  have htree : treeLaw x b = (treeLaw x a).bind (continuationLaw x a (b - a)) := by
    calc
      _ = treeLaw x (a + (b - a)) := congrArg (treeLaw x) he.symm
      _ = _ := treeLaw_add_eq_bind_continuation x a (b - a)
  have hprob : (treeLaw x b) {q | truncateAt q a ∈ A ∧ q ∈ B} ≤
      ENNReal.ofReal r * (treeLaw x a) A := by
    rw [htree, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ ≤ ∫⁻ s, A.indicator (fun _ => ENNReal.ofReal r) s ∂treeLaw x a := by
        apply lintegral_mono_ae
        filter_upwards [treeLaw_hasHistory x a ha] with s hs
        have hset : (continuationLaw x a (b - a) s) {q | truncateAt q a ∈ A ∧ q ∈ B} =
            (continuationLaw x a (b - a) s) {q | s ∈ A ∧ q ∈ B} := by
          apply measure_congr
          filter_upwards [continuationLaw_truncate_self hs hτ] with q hq
          simp only [hq]
        rw [hset]
        by_cases hsA : s ∈ A
        · simp only [hsA, true_and, Set.ofPred_mem_eq, Set.indicator_of_mem hsA]
          rw [← ofReal_measureReal]
          exact ENNReal.ofReal_le_ofReal (hbound s hs hsA)
        · simp only [hsA, false_and, Set.ofPred_false, measure_empty,
            Set.indicator_of_notMem hsA, le_refl]
      _ = _ := lintegral_indicator_const hA _
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hprob
  simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr] using hh

theorem treeLaw_prefix_blockStatistics_factorization_at_endpoint (x : SignSequence)
    {a b : ℕ} (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) (t : ℝ)
    (A : Set State) (hA : MeasurableSet A) (B : Set (ℕ × ℕ)) (hB : MeasurableSet B) :
    (treeLaw x b).real {q | truncateAt q a ∈ A ∧
        (blockTallCount q a b t, componentMaximum q a) ∈ B} =
      (treeLaw x b).real {q | truncateAt q a ∈ A} *
        (treeLaw x b).real {q | (blockTallCount q a b t, componentMaximum q a) ∈ B} := by
  have hpair := treeLaw_prefix_blockStatistics_event_at_endpoint x hab hb t A hA B hB
  have hsecond := treeLaw_prefix_blockStatistics_event_at_endpoint x hab hb t
    Set.univ MeasurableSet.univ B hB
  simp only [Set.mem_univ, true_and, measure_univ, one_mul] at hsecond
  have hfirst := treeLaw_prefix_event x hb hab (fun s => s ∈ A)
  change (treeLaw x b) {q | truncateAt q a ∈ A} = (treeLaw x a) A at hfirst
  have hh := congrArg ENNReal.toReal hpair
  rw [← hfirst, ← hsecond, ENNReal.toReal_mul] at hh
  exact hh

theorem treeLaw_goodChain_failure_inter_le (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : (3 : ℝ) ≤ (C ^ k : ℕ)) (t : ℝ) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) :
    (treeLaw x (C ^ (k + 1))).real {q |
      b ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ) ∧
      ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤
      ((treeLaw x (C ^ (k + 1))).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)} +
       (treeLaw x (C ^ (k + 1))).real {q | M < (componentMaximum q (C ^ k) : ℝ)} +
       3 * M / b) *
      (treeLaw x (C ^ (k + 1))).real {q |
        b ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)} := by
  let a := C ^ k
  let z := C ^ (k + 1)
  let μ := treeLaw x z
  let A : Set State := {s | b ≤ ((goodSet s C k₀ k t).card : ℝ)}
  let Old : Set State := {q | truncateAt q a ∈ A}
  let Bad : Set State := {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b}
  let Nbad : Set State := {q | (blockTallCount q a z t : ℝ) ≤ 4 * (a : ℝ)}
  let Mbad : Set State := {q | M < (componentMaximum q a : ℝ)}
  let R : Set State := {q | 4 * (a : ℝ) ≤ (blockTallCount q a z t : ℝ) ∧
    (componentMaximum q a : ℝ) ≤ M ∧ q ∈ Bad}
  have haz : a ≤ z := pow_le_pow_right₀ hC (Nat.le_succ k)
  have hR : μ.real (Old ∩ R) ≤ 3 * M / b * μ.real Old := by
    have hh := treeLaw_prefix_inter_event_le x haz hτ A (by trivial) R
      (show 0 ≤ 3 * M / b by positivity) (fun s hs hsA =>
        continuationLaw_goodSet_growth_failure_le hs hC hk hτ ha t hb hM hsA)
    have he := treeLaw_prefix_event_real x hτ haz (fun s => s ∈ A)
    change μ.real Old = (treeLaw x a).real A at he
    rw [← he] at hh
    exact hh
  have hN : μ.real (Old ∩ Nbad) = μ.real Old * μ.real Nbad := by
    simpa only [μ, Old, Nbad, Set.inter_def, Set.mem_ofPred_eq] using
      treeLaw_prefix_blockStatistics_factorization_at_endpoint x haz hτ t A (by trivial)
        {p : ℕ × ℕ | (p.1 : ℝ) ≤ 4 * (a : ℝ)} (by measurability)
  have hM' : μ.real (Old ∩ Mbad) = μ.real Old * μ.real Mbad := by
    simpa only [μ, Old, Mbad, Set.inter_def, Set.mem_ofPred_eq] using
      treeLaw_prefix_blockStatistics_factorization_at_endpoint x haz hτ t A (by trivial)
        {p : ℕ × ℕ | M < (p.2 : ℝ)} (by measurability)
  have hsub : Old ∩ Bad ⊆ (Old ∩ Nbad) ∪ (Old ∩ Mbad) ∪ (Old ∩ R) := by
    intro q hq
    by_cases hNq : q ∈ Nbad
    · exact Or.inl (Or.inl ⟨hq.1, hNq⟩)
    by_cases hMq : q ∈ Mbad
    · exact Or.inl (Or.inr ⟨hq.1, hMq⟩)
    exact Or.inr ⟨hq.1, (not_le.mp hNq).le, not_lt.mp hMq, hq.2⟩
  calc
    _ = μ.real (Old ∩ Bad) := rfl
    _ ≤ μ.real ((Old ∩ Nbad) ∪ (Old ∩ Mbad) ∪ (Old ∩ R)) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (μ.real (Old ∩ Nbad) + μ.real (Old ∩ Mbad)) + μ.real (Old ∩ R) :=
      (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ (μ.real Old * μ.real Nbad + μ.real Old * μ.real Mbad) + 3 * M / b * μ.real Old := by
      rw [hN, hM']
      exact add_le_add le_rfl hR
    _ = _ := by
      change (μ.real Old * μ.real Nbad + μ.real Old * μ.real Mbad) +
        3 * M / b * μ.real Old = (μ.real Nbad + μ.real Mbad + 3 * M / b) * μ.real Old
      ring

/-- A null conditioning event gives the zero measure, as specified by
Mathlib's conditional-probability convention. Positive events use the usual
ratio, with no lower bound on the conditioning probability required. -/
theorem cond_real_le_of_inter_le_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A B : Set Ω) (hA : MeasurableSet A)
    {r : ℝ} (hr : 0 ≤ r) (h : μ.real (A ∩ B) ≤ r * μ.real A) :
    (ProbabilityTheory.cond μ A).real B ≤ r := by
  by_cases hz : μ A = 0
  · rw [cond_eq_zero_of_meas_eq_zero hz]
    simpa only [Measure.real, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero] using hr
  · have hp : 0 < (μ A).toReal := ENNReal.toReal_pos hz (measure_ne_top _ _)
    change ((ProbabilityTheory.cond μ A) B).toReal ≤ r
    rw [cond_apply hA, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hp).mpr h

theorem treeLaw_cond_goodChain_failure_le (x : SignSequence) {C k₀ k : ℕ}
    (hC : 1 ≤ C) (hk : k₀ ≤ k)
    (hτ : ((C ^ (k + 1) : ℕ) : ℕ∞) ≤ extinctionTime x)
    (ha : (3 : ℝ) ≤ (C ^ k : ℕ)) (t : ℝ) {b M : ℝ} (hb : 0 < b) (hM : 0 ≤ M) :
    (ProbabilityTheory.cond (treeLaw x (C ^ (k + 1)))
      {q | b ≤ ((goodSet (truncateAt q (C ^ k)) C k₀ k t).card : ℝ)}).real
      {q | ((goodSet q C k₀ (k + 1) t).card : ℝ) < 2 * b} ≤
      (treeLaw x (C ^ (k + 1))).real {q |
        (blockTallCount q (C ^ k) (C ^ (k + 1)) t : ℝ) ≤ 4 * (C ^ k : ℕ)} +
      (treeLaw x (C ^ (k + 1))).real {q | M < (componentMaximum q (C ^ k) : ℝ)} +
      3 * M / b := by
  apply cond_real_le_of_inter_le_mul _ _ _ (by trivial) (by positivity)
  exact treeLaw_goodChain_failure_inter_le x hC hk hτ ha t hb hM

end Freezing1.Forward
