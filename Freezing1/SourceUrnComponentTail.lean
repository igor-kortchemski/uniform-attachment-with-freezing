module

public import Freezing1.SourceUrnComponentTailScalar
public import Freezing1.LinearComponentTailBounds

/-! Actual finite component endpoints controlled by the source's infinite
positive-extension urn. Only pure cutoff bookkeeping is reused from the
older finite-moment module; its concentration estimates are not called. -/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem positiveExtension_urn_cubic_tail_le (x : SignSequence) {a b k : ℕ}
    (ha : 1 ≤ a) (hab : a < b) (hb : PositiveThrough x b) {K : ℝ} (hK : 0 < K)
    (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤
      (k : ℝ) ^ 3) :
    (SignedUrn.continuationLaw (activeCount x) a (b - a) 1).real
        {u : ℤ | (k : ℝ) ^ 3 < (u : ℝ) + 1} ≤
      2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K))) := by
  have hSa0 : 0 < (activeCount x a : ℝ) := by exact_mod_cast hb a hab.le
  have hSb0 : 0 < (activeCount x b : ℝ) := by exact_mod_cast hb b le_rfl
  have hexp := source_urn_exponent_lower (by exact_mod_cast ha) hSa0 hSa hK
    (SignedUrn.positiveExtension_square_budget_pos x hab.le hb) hD hE
    (by exact_mod_cast hk : (1 : ℝ) ≤ k)
  calc
    _ ≤ (SignedUrn.continuationLaw (activeCount x) a (b - a) 1).real {u : ℤ |
        (1 + (k : ℝ) ^ 2) / (activeCount x a : ℝ) < (u : ℝ) / activeCount x b} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro u hu
      change (k : ℝ) ^ 3 < (u : ℝ) + 1 at hu
      apply (lt_div_iff₀ hSb0).mpr
      have hh : (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a < u := by
        linarith
      convert hh using 1; ring
    _ ≤ 2 * Real.exp (-(((k : ℝ) ^ 4 / 4) * (activeCount x a : ℝ)⁻¹) /
        (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) +
          (k : ℝ) ^ 2 * max (SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b))
            (SignedUrn.sourceEpsilon x a b hab))) := by
      simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num] using
        SignedUrn.positiveExtension_urn_endpoint_upper x hab hb (sq_nonneg (k : ℝ))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
      have hh := neg_le_neg hexp
      convert hh using 1; ring

/-- The original marked component, conditional on any genuine lower-cut
state and active root, has the same cubic tail bound. -/
theorem positiveExtension_component_cubic_tail_le {x : SignSequence} {a b k : ℕ}
    {s : Forward.State} (hs : Forward.PhaseData x a s) {r : ℕ} (hr : r ∈ s.active)
    (ha : 1 ≤ a) (hab : a < b) (hb : PositiveThrough x b) {K : ℝ} (hK : 0 < K)
    (hSa : (activeCount x a : ℝ) ≤ (a : ℝ) + 1)
    (hD : SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation x a b) ≤ K / a)
    (hE : SignedUrn.sourceEpsilon x a b hab ≤ K / a) (hk : 1 ≤ k)
    (hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount x b : ℝ) / activeCount x a ≤
      (k : ℝ) ^ 3) :
    (Forward.continuationLaw x a (b - a) s).real {q |
      (k : ℝ) ^ 3 < (Forward.componentPopulationWithRoot q a r : ℝ)} ≤
      2 * Real.exp (-((k : ℝ) ^ 2 / (16 * K))) := by
  have hlaw := Forward.continuationLaw_componentPopulation_of_root (k := b - a) hs
    (by simpa only [Nat.add_sub_of_le hab.le] using ((lt_extinctionTime_iff x b).mpr hb).le) hr
  have hm := congrArg (fun μ : Measure ℤ => μ {u | (k : ℝ) ^ 3 < (u : ℝ) + 1}) hlaw
  rw [Measure.map_apply measurable_from_top (by trivial)] at hm
  have hmR := congrArg ENNReal.toReal hm
  calc
    _ ≤ (Forward.continuationLaw x a (b - a) s).real {q |
        (k : ℝ) ^ 3 < (Forward.componentPopulation q a r : ℝ) + 1} := by
      apply measureReal_mono _ (measure_ne_top _ _)
      intro q hq
      have hh : (Forward.componentPopulationWithRoot q a r : ℝ) ≤
          (Forward.componentPopulation q a r : ℝ) + 1 := by
        exact_mod_cast Forward.componentPopulationWithRoot_le q a r
      exact lt_of_lt_of_le hq hh
    _ = _ := hmR
    _ ≤ _ := positiveExtension_urn_cubic_tail_le x ha hab hb hK hSa hD hE hk hthreshold

/-- The one common source constant and all sufficient deterministic
parameters, with the marked-root correction still present. -/
theorem uniform_positiveExtension_component_parameters
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      1 ≤ k ∧ (activeCount (x n) (C ^ k) : ℝ) ≤ ((C ^ k : ℕ) : ℝ) + 1 ∧
      SignedUrn.infiniteSquareBudget (SignedUrn.positiveExtensionPopulation (x n) (C ^ k) (C ^ (k + 1))) ≤
        K / ((C ^ k : ℕ) : ℝ) ∧
      SignedUrn.sourceEpsilon (x n) (C ^ k) (C ^ (k + 1))
          (SignedUrn.positiveExtension_geometricBlock_lt C hC k) ≤ K / ((C ^ k : ℕ) : ℝ) ∧
      1 + (1 + (k : ℝ) ^ 2) * (activeCount (x n) (C ^ (k + 1)) : ℝ) /
        activeCount (x n) (C ^ k) ≤ (k : ℝ) ^ 3 := by
  obtain ⟨K, hK, hbudgets⟩ := SignedUrn.linear_positiveExtension_source_budgets
    x A hc hc1 hA hAinf hτ hnear hbulk C hC
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  obtain ⟨m, hm⟩ := eventually_atTop.mp
    (eventually_cubic_ge_marked_threshold (K * ((C : ℝ) + 1)))
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbudgets, eventually_geometric_index_ge A hAinf C (by omega) m]
    with n hn hkn k hAk hupper
  have hbud := hn k hAk hupper
  have hki := hm k (hkn k hAk)
  have ha : 1 ≤ C ^ k := Nat.succ_le_of_lt (pow_pos (by omega) k)
  have haR : (1 : ℝ) ≤ (C ^ k : ℕ) := by exact_mod_cast ha
  have ha0 : (0 : ℝ) < (C ^ k : ℕ) := by linarith
  have hab := SignedUrn.positiveExtension_geometricBlock_lt C hC k
  have hbN : C ^ (k + 1) ≤ n := by
    have hh := (le_div_iff₀ hC0).mp hupper
    rw [pow_succ]
    exact_mod_cast hh
  have hb : PositiveThrough (x n) (C ^ (k + 1)) :=
    fun i hi => (lt_extinctionTime_iff (x n) n).mp (hτ n) i (hi.trans hbN)
  have hSa : 0 < (activeCount (x n) (C ^ k) : ℝ) := by exact_mod_cast hb _ hab.le
  have hSb : (activeCount (x n) (C ^ (k + 1)) : ℝ) ≤ ((C : ℝ) + 1) * (C ^ k : ℕ) := by
    have hu : (activeCount (x n) (C ^ (k + 1)) : ℝ) ≤ ((C ^ (k + 1) : ℕ) : ℝ) + 1 := by
      have hcount : (plusCount (x n) (C ^ (k + 1)) : ℤ) ≤ ((C ^ (k + 1) : ℕ) : ℤ) := by
        exact_mod_cast plusCount_le (x n) (C ^ (k + 1))
      have hh := (activeCount_le_plusCount_add_one (x n) (C ^ (k + 1))).trans
        (Int.add_le_add_right hcount 1)
      exact_mod_cast hh
    have hpow : ((C ^ (k + 1) : ℕ) : ℝ) = ((C ^ k : ℕ) : ℝ) * C := by
      rw [pow_succ, Nat.cast_mul]
    rw [hpow] at hu
    nlinarith
  have hratio : (activeCount (x n) (C ^ (k + 1)) : ℝ) / activeCount (x n) (C ^ k) ≤
      K * ((C : ℝ) + 1) := by
    calc
      _ = (activeCount (x n) (C ^ (k + 1)) : ℝ) * (activeCount (x n) (C ^ k) : ℝ)⁻¹ :=
        div_eq_mul_inv _ _
      _ ≤ (((C : ℝ) + 1) * (C ^ k : ℕ)) * (K / (C ^ k : ℕ)) :=
        mul_le_mul hSb hbud.2.1 (inv_nonneg.mpr hSa.le) (by positivity)
      _ = _ := by field_simp
  have hthreshold : 1 + (1 + (k : ℝ) ^ 2) * (activeCount (x n) (C ^ (k + 1)) : ℝ) /
      activeCount (x n) (C ^ k) ≤ (k : ℝ) ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 1 + (k : ℝ) ^ 2)
    calc
      _ = 1 + (1 + (k : ℝ) ^ 2) * ((activeCount (x n) (C ^ (k + 1)) : ℝ) /
          activeCount (x n) (C ^ k)) := by ring
      _ ≤ 1 + (1 + (k : ℝ) ^ 2) * (K * ((C : ℝ) + 1)) := add_le_add le_rfl hh
      _ ≤ _ := hki.2
  exact ⟨hki.1, hbud.1, hbud.2.2.2, hbud.2.2.1, hthreshold⟩

/-- One source constant gives quadratic exponential decay for every
allowed geometric block, with no tail-estimate premise. -/
theorem uniform_positiveExtension_urn_cubic_tail
    (x : ℕ → SignSequence) (A : ℕ → ℝ) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hA : ∀ n, 0 < A n)
    (hAinf : Tendsto A atTop atTop) (hτ : ∀ n : ℕ, (n : ℕ∞) < extinctionTime (x n))
    (hnear : NearOriginLimsup x A c) (hbulk : BulkLiminf x) (C : ℕ) (hC : 2 ≤ C) :
    ∃ β : ℝ, 0 < β ∧ ∀ᶠ n in atTop, ∀ k : ℕ,
      A n ≤ ((C ^ k : ℕ) : ℝ) → ((C ^ k : ℕ) : ℝ) ≤ (n : ℝ) / C →
      (SignedUrn.continuationLaw (activeCount (x n)) (C ^ k) (C ^ (k + 1) - C ^ k) 1).real
        {u : ℤ | (k : ℝ) ^ 3 < (u : ℝ) + 1} ≤ 2 * Real.exp (-β * (k : ℝ) ^ 2) := by
  obtain ⟨K, hK, hparameters⟩ := uniform_positiveExtension_component_parameters
    x A hc hc1 hA hAinf hτ hnear hbulk C hC
  refine ⟨1 / (16 * K), by positivity, ?_⟩
  filter_upwards [hparameters] with n hn k hAk hupper
  have hpar := hn k hAk hupper
  have ha : 1 ≤ C ^ k := Nat.succ_le_of_lt (pow_pos (by omega) k)
  have hab := SignedUrn.positiveExtension_geometricBlock_lt C hC k
  have hbN : C ^ (k + 1) ≤ n := by
    have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
    have hh := (le_div_iff₀ hC0).mp hupper
    rw [pow_succ]
    exact_mod_cast hh
  have hb : PositiveThrough (x n) (C ^ (k + 1)) :=
    fun i hi => (lt_extinctionTime_iff (x n) n).mp (hτ n) i (hi.trans hbN)
  have ht := positiveExtension_urn_cubic_tail_le (x n) ha hab hb hK hpar.2.1
    hpar.2.2.1 hpar.2.2.2.1 hpar.1 hpar.2.2.2.2
  have he : -((k : ℝ) ^ 2 / (16 * K)) = -(1 / (16 * K)) * (k : ℝ) ^ 2 := by ring
  simpa only [he] using ht

end Freezing1
