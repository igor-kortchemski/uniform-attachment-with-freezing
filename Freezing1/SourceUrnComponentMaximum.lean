module

public import Freezing1.SourceUrnComponentTail
public import Freezing1.ForwardContinuationPrefix
public import Freezing1.ForwardForestMaximumStatistics

/-! Source A64: the genuine infinite-urn concentration estimate controls
each actual marked component, then the exact cut roots are union-bounded.
No independence between components or finite exponential-moment estimate
is assumed or called. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

theorem positiveExtension_continuation_maximum_tail_le {x : SignSequence} {a b k : ℕ}
    {s : State} (hs : HasHistory x a s) (hd : PhaseData x a s)
    (ha : 1 ≤ a) (hab : a < b) (hb : PositiveThrough x b) {K : ℝ} (hK : 0 < K)
    (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤
      (k : ℝ) ^ 3) :
    (continuationLaw x a (b - a) s).real
        {q | (k : ℝ) ^ 3 < (componentMaximum q a : ℝ)} ≤
      (activeCount x a : ℝ) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K)))) := by
  have hτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by
    simpa only [Nat.add_sub_of_le hab.le] using ((lt_extinctionTime_iff x b).mpr hb).le
  have hroots : ∀ᵐ q ∂continuationLaw x a (b - a) s, cutRoots q a = s.active := by
    filter_upwards [continuationLaw_truncate_self hs hτ] with q hq
    exact congrArg State.active hq
  have hevent : (continuationLaw x a (b - a) s).real
      {q | (k : ℝ) ^ 3 < (componentMaximum q a : ℝ)} ≤
      (continuationLaw x a (b - a) s).real
        (⋃ r ∈ s.active, {q | (k : ℝ) ^ 3 < (componentPopulationWithRoot q a r : ℝ)}) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hroots] with q hq hmax
    have hne : s.active.Nonempty := by
      have hSa0 : 0 < activeCount x a := hb a hab.le
      have hc := hd.count
      exact Finset.card_pos.mp (by omega)
    obtain ⟨r, hr, hsup⟩ := Finset.exists_mem_eq_sup s.active hne (componentPopulationWithRoot q a)
    change (k : ℝ) ^ 3 < (((cutRoots q a).sup (componentPopulationWithRoot q a) : ℕ) : ℝ) at hmax
    rw [hq, hsup] at hmax
    exact Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hr, hmax⟩⟩
  have hcard : (s.active.card : ℝ) = activeCount x a := by exact_mod_cast hd.count
  calc
    _ ≤ _ := hevent
    _ ≤ ∑ r ∈ s.active, (continuationLaw x a (b - a) s).real
        {q | (k : ℝ) ^ 3 < (componentPopulationWithRoot q a r : ℝ)} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _r ∈ s.active, 2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K))) := by
      apply Finset.sum_le_sum
      intro r hr
      exact positiveExtension_component_cubic_tail_le hd hr ha hab hb hK hSa hD hE hk hthreshold
    _ = _ := by simp [hcard]

/-- The source factor is the actual initial population, not a hypothesized
number of independent components. The positive extension supplies every
component bound before the actual union and past-state mixture. -/
theorem positiveExtension_treeLaw_maximum_tail_le (x : SignSequence) {a b k : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hb : PositiveThrough x b) {K : ℝ} (hK : 0 < K)
    (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤
      (k : ℝ) ^ 3) :
    (treeLaw x b).real {q | (k : ℝ) ^ 3 < (componentMaximum q a : ℝ)} ≤
      (activeCount x a : ℝ) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K)))) := by
  let B := (activeCount x a : ℝ) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K))))
  have hSa0 : 0 < (activeCount x a : ℝ) := by exact_mod_cast hb a hab.le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have haτ : (a : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hab.le : (a : ℕ∞) ≤ b).trans ((lt_extinctionTime_iff x b).mpr hb).le
  have hmeasure : (treeLaw x b) {q | (k : ℝ) ^ 3 < (componentMaximum q a : ℝ)} ≤ ENNReal.ofReal B := by
    rw [← Nat.add_sub_of_le hab.le, treeLaw_add_eq_bind_continuation,
      Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ ≤ ∫⁻ _s, ENNReal.ofReal B ∂treeLaw x a := by
        apply lintegral_mono_ae
        filter_upwards [treeLaw_hasHistory x a haτ, treeLaw_phaseData x a haτ] with s hs hd
        apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hB).mpr
        exact positiveExtension_continuation_maximum_tail_le hs hd ha hab hb hK hSa hD hE hk hthreshold
      _ = _ := by simp
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmeasure
  rwa [ENNReal.toReal_ofReal hB] at hh

/-- The actual number of cut roots agrees with the source initial
population, including roots that subsequently froze. -/
theorem positiveExtension_treeLaw_root_count (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : PositiveThrough x b) :
    ∀ᵐ q ∂treeLaw x b, (cutRoots q a).card = (activeCount x a).toNat := by
  have hτ := ((lt_extinctionTime_iff x b).mpr hb).le
  filter_upwards [treeLaw_hasHistory x b hτ] with q hq
  exact cutRoots_card_eq_activeCount hq hτ hab

end Forward

/-- L11 through the source infinite positive-extension argument, with the
original geometric window, one common set of constants, and actual M. -/
theorem linear_geometric_componentMaximum_tail_via_positiveExtension
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∀ᶠ n in atTop, ∀ k : ℕ, A n ≤ ((C ^ k : ℕ) : ℝ) →
      ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (Forward.treeLaw (x n) (C ^ (k + 1))).real
        {q | (k : ℝ) ^ 3 < (Forward.componentMaximum q (C ^ k) : ℝ)} ≤ 1 / (k : ℝ) ^ 2 := by
  obtain ⟨K, hK, hparameters⟩ := uniform_positiveExtension_component_parameters
    x A hc hc1 hA hAinf hτ hnear hbulk C hC
  have hβ : 0 < 1 / (16 * K) := by positivity
  obtain ⟨m, hm⟩ := eventually_atTop.mp (eventually_geometric_exp_square_le_inv_sq C (by omega) hβ)
  filter_upwards [hparameters, eventually_geometric_index_ge A hAinf C (by omega) m]
    with n hn hkn k hAk hupper
  have hp := hn k hAk hupper
  have ha : 1 ≤ C ^ k := Nat.succ_le_of_lt (pow_pos (by omega) k)
  have hab := SignedUrn.positiveExtension_geometricBlock_lt C hC k
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hbN : C ^ (k + 1) ≤ n := by
    have hh := (le_div_iff₀ hC0).mp hupper
    rw [pow_succ]
    exact_mod_cast hh
  have hb : PositiveThrough (x n) (C ^ (k + 1)) :=
    fun i hi => (lt_extinctionTime_iff (x n) n).mp (hτ n) i (hi.trans hbN)
  have htail := Forward.positiveExtension_treeLaw_maximum_tail_le (x n) ha hab hb hK
    hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.1 hp.2.2.2.2
  calc
    _ ≤ (activeCount (x n) (C ^ k) : ℝ) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K)))) := htail
    _ ≤ (((C ^ k : ℕ) : ℝ) + 1) * (2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K)))) :=
      mul_le_mul_of_nonneg_right hp.2.1 (by positivity)
    _ = (((C ^ k : ℕ) : ℝ) + 1) * (2 * Real.exp (-(1 / (16 * K)) * (k : ℝ) ^ 2)) := by
      congr 3
      ring
    _ ≤ _ := hm k (hkn k hAk)

end Freezing1
