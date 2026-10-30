module

public import Freezing1.ReversePairHeightBlocks
public import Freezing1.CoalescenceBounds

/-!
# Two-root block tails with a proved coalescence error

All probabilities below use the continuation of the actual reverse kernel
from a supplied valid phase. The comparison term is the genuine independent
Bernoulli block law. The error is a sum of actual one-step coalescence hazards,
uniform in the starting forest and in the selected distinct roots.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical BigOperators

noncomputable def heightTailTest (t : ℝ) (d : ℕ) : ℝ := if t < (d : ℝ) then 1 else 0

theorem heightTailTest_bounds (t : ℝ) (d : ℕ) :
    0 ≤ heightTailTest t d ∧ heightTailTest t d ≤ 1 := by
  unfold heightTailTest
  split_ifs <;> norm_num

theorem heightTailTest_mono (t : ℝ) : Monotone (heightTailTest t) := by
  intro a b hab
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  by_cases ha : t < (a : ℝ)
  · simp [heightTailTest, ha, ha.trans_le hab']
  · simp [heightTailTest, ha]
    split_ifs <;> norm_num

theorem integral_ite_indicator {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (P : α → Prop) [DecidablePred P] (hP : MeasurableSet {x | P x}) :
    (∫ x, (if P x then (1 : ℝ) else 0) ∂μ) = μ.real {x | P x} := by
  have he : (fun x => if P x then (1 : ℝ) else 0) = {x | P x}.indicator (fun _ => 1) := by
    funext x
    by_cases hx : P x <;> simp [hx]
  rw [he, integral_indicator_const (1 : ℝ) hP]
  simp only [smul_eq_mul, mul_one]

theorem integral_heightTailTest (μ : Measure ℕ) (t : ℝ) :
    (∫ j, heightTailTest t j ∂μ) = μ.real {j | t < (j : ℝ)} :=
  integral_ite_indicator μ _ ((measurable_of_countable (fun j : ℕ => (j : ℝ))) measurableSet_Ioi)

namespace Reverse

noncomputable def blockTailProbability (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (a k : ℕ) (t : ℝ) : ℝ :=
  (bernoulliPartialSumLaw (attachmentParameter x n hn) (blockIndices n a k)).real
    {j : ℕ | t < (j : ℝ)}

theorem blockAverage_tail_zero (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) {a k : ℕ} (hk : a + k ≤ n) (t : ℝ) :
    blockAverage (stepParameter x n hn) a k (heightTailTest t) 0 =
      blockTailProbability x n hn a k t := by
  rw [blockAverage_eq_integral_partialSum x n hn hk (heightTailTest_bounds t)]
  simpa only [Nat.zero_add, blockTailProbability] using integral_heightTailTest _ t

theorem integral_killed_heightTailTest (μ : Measure Forest) (u v : ℕ ⊕ ℕ) (t : ℝ) :
    (∫ F, killedProduct u v (heightTailTest t) (heightTailTest t) F ∂μ) =
      μ.real {F | F.root u ≠ F.root v ∧ t < (F.depth u : ℝ) ∧ t < (F.depth v : ℝ)} := by
  have he : killedProduct u v (heightTailTest t) (heightTailTest t) =
      fun F => if F.root u ≠ F.root v ∧ t < (F.depth u : ℝ) ∧ t < (F.depth v : ℝ)
        then (1 : ℝ) else 0 := by
    funext F
    by_cases hr : F.root u ≠ F.root v <;> by_cases hu : t < (F.depth u : ℝ) <;>
      by_cases hv : t < (F.depth v : ℝ) <;> simp [killedProduct, heightTailTest, hr, hu, hv]
  rw [he, integral_ite_indicator _ _ (by trivial)]

/-- The two-root tail on surviving trajectories is bounded by the square
of the original Bernoulli block tail, with no changed parameters. -/
theorem blockLaw_separated_pair_tail_le {x : SignSequence} {n a k : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hF : ValidAt x n (a + k) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.roots) (hv : v ∈ F.roots) (huv : u ≠ v) (t : ℝ) :
    (blockLaw x a k F).real
      {F' | F'.root u ≠ F'.root v ∧ t < (F'.depth u : ℝ) ∧ t < (F'.depth v : ℝ)} ≤
        blockTailProbability x n hn a k t ^ 2 := by
  have hu' := RootedForest.mem_roots.mp hu
  have hv' := RootedForest.mem_roots.mp hv
  have hdu := (F.depth_eq_zero_iff hu'.1).mpr hu'.2
  have hdv := (F.depth_eq_zero_iff hv'.1).mpr hv'.2
  have hne : F.root u ≠ F.root v := by rwa [hu'.2, hv'.2]
  have h := blockLaw_killed_product_le hn hk hF hu'.1 hv'.1
    (heightTailTest_mono t) (heightTailTest_mono t)
    (heightTailTest_bounds t) (heightTailTest_bounds t)
  rw [integral_killed_heightTailTest] at h
  simpa only [killedProduct, ite_eq_left hne, hdu, hdv,
    blockAverage_tail_zero x n hn hk, pow_two] using h

noncomputable def coalescedTest (u v : ℕ ⊕ ℕ) (F : Forest) : ℝ :=
  if F.root u = F.root v then 1 else 0

theorem coalescedTest_bounds (u v : ℕ ⊕ ℕ) (F : Forest) :
    0 ≤ coalescedTest u v F ∧ coalescedTest u v F ≤ 1 := by
  unfold coalescedTest
  split_ifs <;> norm_num

theorem integral_coalescedTest (μ : Measure Forest) (u v : ℕ ⊕ ℕ) :
    (∫ F, coalescedTest u v F ∂μ) = μ.real {F | F.root u = F.root v} :=
  integral_ite_indicator μ _ (by trivial)

noncomputable def blockCoalescenceRisk (x : SignSequence) (a k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Ioc a (a + k), coalescenceHazard x i

theorem blockCoalescenceRisk_nonneg (x : SignSequence) (a k : ℕ) :
    0 ≤ blockCoalescenceRisk x a k :=
  Finset.sum_nonneg fun i _ => coalescenceHazard_nonneg x i

theorem blockCoalescenceRisk_succ (x : SignSequence) (a k : ℕ) :
    blockCoalescenceRisk x a (k + 1) =
      blockCoalescenceRisk x a k + coalescenceHazard x (a + k + 1) := by
  simp only [blockCoalescenceRisk, ← Nat.add_assoc,
    Finset.sum_Ioc_succ_top (Nat.le_add_right a k)]

/-- Uniform conditional coalescence error from any valid starting forest.
The initial indicator covers pairs that already share a component. -/
theorem blockLaw_coalesced_integral_le {x : SignSequence} {n a k : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hF : ValidAt x n (a + k) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.vertices) (hv : v ∈ F.vertices) :
    (∫ F', coalescedTest u v F' ∂blockLaw x a k F) ≤
      coalescedTest u v F + blockCoalescenceRisk x a k := by
  induction k generalizing F with
  | zero => simp [blockLaw, blockCoalescenceRisk]
  | succ k ih =>
    have hi : a + k < n := by omega
    have hF' : ValidAt x n (a + k + 1) F := by simpa [Nat.add_assoc] using hF
    have hint : Integrable (coalescedTest u v) (blockLaw x a (k + 1) F) :=
      integrable_unitInterval_function _ measurable_from_top (coalescedTest_bounds u v)
    rw [blockLaw, integral_bind_of_integrable _ _ measurable_from_top hint]
    have hiInner : Integrable (fun F' => ∫ F'', coalescedTest u v F'' ∂blockLaw x a k F')
        (transitionLaw x (a + k) F) :=
      integrable_unitInterval_function _ measurable_from_top fun F' =>
        integral_unitInterval_bounds _ measurable_from_top (coalescedTest_bounds u v)
    have hiCoal : Integrable (coalescedTest u v) (transitionLaw x (a + k) F) :=
      integrable_unitInterval_function _ measurable_from_top (coalescedTest_bounds u v)
    have hiRhs : Integrable (fun F' => coalescedTest u v F' + blockCoalescenceRisk x a k)
        (transitionLaw x (a + k) F) := hiCoal.add (integrable_const _)
    refine (integral_mono_ae hiInner hiRhs ?_).trans ?_
    · filter_upwards [transitionLaw_valid hn hi hF',
        transitionLaw_present_depth_support hn hi hF' hu,
        transitionLaw_present_depth_support hn hi hF' hv] with F' hvalid hu' hv'
      exact ih (by omega) hvalid hu'.1 hv'.1
    · rw [integral_add hiCoal (integrable_const _), integral_coalescedTest,
        integral_const, probReal_univ, one_smul, transitionLaw_coalescence_cases hF' hu hv,
        blockCoalescenceRisk_succ]
      by_cases h : F.root u = F.root v
      · simp only [h, ↓reduceIte, coalescedTest]
        have hnonneg := coalescenceHazard_nonneg x (a + k + 1)
        linarith
      · simp only [h, ↓reduceIte, coalescedTest, zero_add, coalescenceHazard]
        linarith

/-- Starting from two distinct actual roots, the only extra error in the
joint upper tail is the explicitly bounded probability of coalescence. -/
theorem blockLaw_pair_tail_le {x : SignSequence} {n a k : ℕ} {F : Forest}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hF : ValidAt x n (a + k) F) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ F.roots) (hv : v ∈ F.roots) (huv : u ≠ v) (t : ℝ) :
    (blockLaw x a k F).real {F' | t < (F'.depth u : ℝ) ∧ t < (F'.depth v : ℝ)} ≤
      blockTailProbability x n hn a k t ^ 2 + blockCoalescenceRisk x a k := by
  have hu' := RootedForest.mem_roots.mp hu
  have hv' := RootedForest.mem_roots.mp hv
  have hne : F.root u ≠ F.root v := by rwa [hu'.2, hv'.2]
  have hcoal := blockLaw_coalesced_integral_le hn hk hF hu'.1 hv'.1
  rw [integral_coalescedTest] at hcoal
  simp only [coalescedTest, ite_eq_right hne, zero_add] at hcoal
  calc
    _ ≤ (blockLaw x a k F).real
        ({F' | F'.root u ≠ F'.root v ∧ t < (F'.depth u : ℝ) ∧ t < (F'.depth v : ℝ)} ∪
          {F' | F'.root u = F'.root v}) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro F' h
      by_cases he : F'.root u = F'.root v
      · exact Or.inr he
      · exact Or.inl ⟨he, h⟩
    _ ≤ _ := (measureReal_union_le _ _).trans
      (add_le_add (blockLaw_separated_pair_tail_le hn hk hF hu hv huv t) hcoal)

end Reverse
end Freezing1
