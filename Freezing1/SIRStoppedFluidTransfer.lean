module

public import Freezing1.SIRStoppedCoupling
public import Freezing1.SIRSusceptibleFluid

/-!
# One early survival gate for the stopped SIR fluid path

The stopped and unstopped populations live on their actual joint Markov law.
A concavity secant inequality controls every time after the first extinction.
The probability of the early survival gate is a separate obligation.
-/

@[expose] public section

namespace Freezing1.SIR.StoppedCoupling

open Filter Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical Topology

set_option backward.isDefEq.respectTransparency false

/-- A concave function vanishing at the origin has nonincreasing secant
slopes. The integer form avoids rounding its two observation times. -/
theorem concave_origin_nat_secant {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ univ f) (h0 : f 0 = 0)
    {n j k : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    (j : ℝ) * f ((k : ℝ) / n) ≤ (k : ℝ) * f ((j : ℝ) / n) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (hj.trans_le hjk)
  have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
  have ha : 0 ≤ (1 : ℝ) - (j : ℝ) / k := by
    linarith [(div_le_one hk).mpr hjkR]
  have hb : 0 ≤ (j : ℝ) / k := by positivity
  have hh := hf.2 (mem_univ (0 : ℝ)) (mem_univ ((k : ℝ) / n)) ha hb (by ring)
  have he : ((j : ℝ) / k) * ((k : ℝ) / n) = (j : ℝ) / n := by
    field_simp [hk.ne']
  simp only [smul_eq_mul, h0, mul_zero, zero_add, he] at hh
  have hh' : (j : ℝ) * f ((k : ℝ) / n) / k ≤ f ((j : ℝ) / n) := by
    simpa only [div_mul_eq_mul_div] using hh
  have := (div_le_iff₀ hk).mp hh'
  nlinarith

theorem legalHistory_infectious_le_succ {C : ℕ → Counts} {n : ℕ}
    (h0 : C 0 = initialCounts n) (hl : ∀ k, (C k).LegalNext (C (k + 1))) :
    ∀ k, (C k).infectious ≤ k + 1 := by
  intro k
  induction k with
  | zero => simp [h0, initialCounts]
  | succ k ih =>
    rcases hl k with ⟨_, he⟩ | ⟨_, ⟨_, he⟩ | he⟩
    · rw [he]; omega
    · rw [he]; simp only [infectCounts]; omega
    · rw [he]; simp only [recoverCounts]; omega

theorem legalHistory_positive_before {C : ℕ → Counts}
    (hl : ∀ k, (C k).LegalNext (C (k + 1))) {k : ℕ} (hk : 0 < (C k).infectious) :
    ∀ j ≤ k, 0 < (C j).infectious := by
  intro j hj
  by_contra hn
  have hz : (C j).infectious = 0 := by omega
  have he := legalHistory_absorbed_persists hl hz k hj
  rw [he, hz] at hk
  omega

noncomputable def gatedProfile (lam : ℝ) (n a : ℕ) (H : ℕ → State) (k : ℕ) : ℝ :=
  if 0 < (H a).1.infectious then max (infectiousProfile lam ((k : ℝ) / n)) 0 else 0

/-- A pathwise stopping comparison. One and the same early survival gate is
used for every observation time. The approximation premise concerns the
actual auxiliary integer coordinate, not an assumed stopped fluid limit. -/
theorem gated_path_error_bound {lam : ℝ} (hlam : 0 < lam) {n a N : ℕ}
    (hn : 0 < n) (ha : 0 < a) {eta : ℝ} (heta : 0 ≤ eta)
    (H : ℕ → State) (h0 : (H 0).1 = initialCounts n)
    (hlegal : ∀ k, (H k).1.LegalNext (H (k + 1)).1)
    (hagree : ∀ k, (∀ j < k, 0 < (H j).1.infectious) →
      ((H k).1.infectious : ℤ) = Susceptible.infectious n k (fun j => (H j).2))
    (hfluid : ∀ k ≤ N,
      |(Susceptible.infectious n k (fun j => (H j).2) : ℝ) / n -
        infectiousProfile lam ((k : ℝ) / n)| ≤ eta) :
    ∀ k ≤ N, |((H k).1.infectious : ℝ) / n - gatedProfile lam n a H k| ≤
      ((a : ℝ) + 1) / n + (1 + (N : ℝ) / a) * eta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hsmall : 0 ≤ ((a : ℝ) + 1) / n := by positivity
  have hfactor : eta ≤ (1 + (N : ℝ) / a) * eta := by
    have : 0 ≤ (N : ℝ) / a := by positivity
    nlinarith
  intro k hk
  by_cases hgate : 0 < (H a).1.infectious
  · rw [gatedProfile, ite_eq_left hgate]
    by_cases hi : 0 < (H k).1.infectious
    · have hp := legalHistory_positive_before hlegal hi
      have he : ((H k).1.infectious : ℝ) =
          (Susceptible.infectious n k (fun j => (H j).2) : ℝ) := by
        exact_mod_cast hagree k (fun j hj => hp j hj.le)
      have hh := abs_max_sub_max_le_abs (((H k).1.infectious : ℝ) / n)
        (infectiousProfile lam ((k : ℝ) / n)) 0
      rw [max_eq_left (by positivity)] at hh
      have hclose : |((H k).1.infectious : ℝ) / n -
          infectiousProfile lam ((k : ℝ) / n)| ≤ eta := by
        simpa only [he] using hfluid k hk
      exact hh.trans (hclose.trans (by linarith))
    · have hzero : (H k).1.infectious = 0 := by omega
      let hex : ∃ j, (H j).1.infectious = 0 := ⟨k, hzero⟩
      let j := Nat.find hex
      have hj0 : (H j).1.infectious = 0 := Nat.find_spec hex
      have hjk : j ≤ k := Nat.find_min' hex hzero
      have haj : a < j := by
        by_contra hh
        have hh' := legalHistory_absorbed_persists hlegal hj0 a (by omega)
        rw [hh', hj0] at hgate
        omega
      have hj : 0 < j := by omega
      have hp : ∀ i < j, 0 < (H i).1.infectious := by
        intro i hi
        have hh := Nat.find_min hex hi
        omega
      have he : ((H j).1.infectious : ℝ) =
          (Susceptible.infectious n j (fun i => (H i).2) : ℝ) := by
        exact_mod_cast hagree j hp
      have hh := hfluid j (hjk.trans hk)
      rw [← he, hj0, Nat.cast_zero, zero_div, zero_sub, abs_neg] at hh
      have hf : infectiousProfile lam ((j : ℝ) / n) ≤ eta := (abs_le.mp hh).2
      have hs := concave_origin_nat_secant (infectiousProfile_strictConcave hlam).concaveOn
        (infectiousProfile_zero hlam) hj hjk (n := n)
      have hs' := hs.trans (mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg k : (0 : ℝ) ≤ k))
      have hajR : (a : ℝ) ≤ j := by exact_mod_cast haj.le
      have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
      have hNk : (k : ℝ) * eta ≤ (N : ℝ) * eta := mul_le_mul_of_nonneg_right hkR heta
      have hupper : infectiousProfile lam ((k : ℝ) / n) ≤ (N : ℝ) / a * eta := by
        by_cases hf0 : infectiousProfile lam ((k : ℝ) / n) ≤ 0
        · exact hf0.trans (by positivity)
        · have hf0' : 0 ≤ infectiousProfile lam ((k : ℝ) / n) := by linarith
          have hh' := mul_le_mul_of_nonneg_right hajR hf0'
          have hdiv : (a : ℝ) * infectiousProfile lam ((k : ℝ) / n) ≤ (N : ℝ) * eta := by
            linarith
          rw [div_mul_eq_mul_div]
          apply (le_div_iff₀ haR).mpr
          nlinarith
      have hmax : max (infectiousProfile lam ((k : ℝ) / n)) 0 ≤ (N : ℝ) / a * eta :=
        max_le hupper (by positivity)
      rw [hzero, Nat.cast_zero, zero_div, zero_sub, abs_neg,
        abs_of_nonneg (le_max_right (infectiousProfile lam ((k : ℝ) / n)) 0)]
      exact hmax.trans (by nlinarith)
  · rw [gatedProfile, ite_eq_right hgate, sub_zero, abs_of_nonneg (by positivity)]
    have hz : (H a).1.infectious = 0 := by omega
    by_cases hka : k ≤ a
    · have hg := legalHistory_infectious_le_succ h0 hlegal k
      have hh : ((H k).1.infectious : ℝ) ≤ (a : ℝ) + 1 := by exact_mod_cast (by omega : (H k).1.infectious ≤ a + 1)
      have hd := div_le_div_of_nonneg_right hh hnR.le
      exact hd.trans (by nlinarith)
    · have he := legalHistory_absorbed_persists hlegal hz k (by omega)
      rw [he, hz, Nat.cast_zero, zero_div]
      positivity

theorem measurableSet_unstopped_fluid_error (lam : ℝ) (n N : ℕ) (eta : ℝ) :
    MeasurableSet {U : ℕ → ℕ | ∃ k ≤ N,
      eta ≤ |(Susceptible.infectious n k U : ℝ) / n -
        infectiousProfile lam ((k : ℝ) / n)|} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : k ≤ N
  · simp only [hk, true_and]
    let f : ℕ → ℝ := fun u =>
      |((2 * ((n : ℤ) - u) - k + 1 : ℤ) : ℝ) / n - infectiousProfile lam ((k : ℝ) / n)|
    exact measurableSet_le measurable_const
      ((measurable_of_countable f).comp (measurable_pi_apply k))
  · simp only [hk, false_and, ofPred_false]
    exact MeasurableSet.empty

/-- The true unstopped fluid estimate remains valid on the constructed joint
law by its proved full-path marginal identity. -/
theorem joint_unstopped_fluid_tendsto (rate : ℕ → ℝ≥0) {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n {H | ∃ k ≤ n * m,
      eta ≤ |(Susceptible.infectious n k (fun j => (H j).2) : ℝ) / n -
        infectiousProfile lam ((k : ℝ) / n)|}) atTop (𝓝 0) := by
  apply (Susceptible.uniform_infectious_fluid_tendsto rate hlam hrate m heta).congr
  intro n
  rw [← map_fullLaw_unstopped (rate n) n]
  have hm : Measurable (fun H : ℕ → State => fun k => (H k).2) :=
    measurable_pi_iff.mpr fun k => measurable_snd.comp (measurable_pi_apply k)
  rw [Measure.map_apply hm (measurableSet_unstopped_fluid_error lam n (n * m) eta)]
  rfl

/-- Uniform stopped-path approximation with a single early survival gate.
For each desired error, every sufficiently small fixed positive `delta`
works as population size tends to infinity. No limiting survival probability
is assumed or concluded here. -/
theorem gated_stopped_fluid_tendsto (rate : ℕ → ℝ≥0) {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (hsmall : delta < eps / 2) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n {H | ∃ k ≤ n * m,
      eps ≤ |((H k).1.infectious : ℝ) / n -
        gatedProfile lam n ⌊delta * n⌋₊ H k|}) atTop (𝓝 0) := by
  let D : ℝ := 1 + 2 * (m : ℝ) / delta
  let eta : ℝ := eps / (4 * D)
  have hD : 0 < D := by dsimp [D]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have heq : D * eta = eps / 4 := by dsimp [eta]; field_simp
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hscale : Tendsto (fun n : ℕ => delta * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hdelta tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop,
      fullLaw (rate n) n {H | ∃ k ≤ n * m,
        eps ≤ |((H k).1.infectious : ℝ) / n -
          gatedProfile lam n ⌊delta * n⌋₊ H k|} ≤
      fullLaw (rate n) n {H | ∃ k ≤ n * m,
        eta ≤ |(Susceptible.infectious n k (fun j => (H j).2) : ℝ) / n -
          infectiousProfile lam ((k : ℝ) / n)|} := by
    filter_upwards [eventually_gt_atTop 0, hscale.eventually_ge_atTop 2,
      hinv.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eps / 4))] with n hn hnlarge hnsmall
    let a := ⌊delta * (n : ℝ)⌋₊
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have ha : 0 < a := Nat.floor_pos.mpr (by linarith)
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hfloor := Nat.floor_le (by positivity : 0 ≤ delta * (n : ℝ))
    have hfloor' := Nat.lt_floor_add_one (delta * (n : ℝ))
    have hhalf : delta * (n : ℝ) / 2 ≤ (a : ℝ) := by dsimp [a]; linarith
    have haratio : (a : ℝ) / n ≤ delta := (div_le_iff₀ hnR).mpr (by simpa [a] using hfloor)
    have hratio : ((n * m : ℕ) : ℝ) / a ≤ 2 * (m : ℝ) / delta := by
      apply (div_le_div_iff₀ haR hdelta).mpr
      push_cast
      have hh := mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
      nlinarith
    have htotal : ((a : ℝ) + 1) / n + (1 + ((n * m : ℕ) : ℝ) / a) * eta < eps := by
      have hh := mul_le_mul_of_nonneg_right (add_le_add_left hratio 1) heta.le
      have hh' : (1 + ((n * m : ℕ) : ℝ) / a) * eta ≤ eps / 4 := by
        calc
          _ ≤ D * eta := by simpa only [D, add_comm] using hh
          _ = _ := heq
      rw [add_div]
      linarith
    apply measure_mono_ae
    filter_upwards [fullLaw_initial (rate n) n, fullLaw_counts_legal (rate n) n,
      fullLaw_agree_until_extinction (rate n) n] with H h0 hl hagree
    intro hbad
    by_contra hnoise
    simp only [not_exists, not_and, not_le] at hnoise
    have hpath := gated_path_error_bound hlam hn ha heta.le H
      (by rw [h0]; rfl) hl (fun k hp => (hagree k hp).2)
      (fun k hk => (hnoise k hk).le)
    rcases hbad with ⟨k, hk, he⟩
    exact (not_lt_of_ge he) ((hpath k hk).trans_lt htotal)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (joint_unstopped_fluid_tendsto rate hlam hrate m heta)
    (Eventually.of_forall fun _ => bot_le) hbound

/-- The unrestricted profile and its positive part have Lipschitz constant
one. This controls the rounding error in the actual step paths. -/
theorem infectiousProfile_lipschitz {lam : ℝ} (hlam : 0 < lam) (s t : ℝ) :
    |infectiousProfile lam t - infectiousProfile lam s| ≤ |t - s| := by
  have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := infectiousProfile lam) (C := 1)
    (fun x _ => (infectiousProfile_hasDerivAt hlam x).differentiableAt)
    (fun x _ => by
      rw [Real.norm_eq_abs, (infectiousProfile_hasDerivAt hlam x).deriv]
      have hg : 0 ≤ lam * fluidProfile lam x := mul_nonneg hlam.le (fluidProfile_pos hlam x).le
      have hd : 0 < 1 + lam * fluidProfile lam x := by linarith
      apply abs_le.mpr
      constructor
      · apply (le_div_iff₀ hd).mpr
        linarith
      · apply (div_le_iff₀ hd).mpr
        linarith) (mem_univ s) (mem_univ t)
  simpa only [Real.norm_eq_abs, one_mul] using hh

theorem floor_time_index_le {n m : ℕ} {t : ℝ} (ht : t ≤ m) :
    ⌊(n : ℝ) * t⌋₊ ≤ n * m := by
  apply Nat.floor_le_of_le
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)

theorem floor_time_distance {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    |(⌊(n : ℝ) * t⌋₊ : ℝ) / n - t| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) ht)
  have hf' := Nat.lt_floor_add_one ((n : ℝ) * t)
  have hle : (⌊(n : ℝ) * t⌋₊ : ℝ) / n ≤ t := (div_le_iff₀ hnR).mpr (by nlinarith)
  calc
    _ = ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hnR.le

theorem rounded_gated_profile_error {lam : ℝ} (hlam : 0 < lam) {n : ℕ} (hn : 0 < n)
    (a : ℕ) (H : ℕ → State) {t : ℝ} (ht : 0 ≤ t) :
    |gatedProfile lam n a H ⌊(n : ℝ) * t⌋₊ -
      (if 0 < (H a).1.infectious then max (infectiousProfile lam t) 0 else 0)| ≤ 1 / n := by
  unfold gatedProfile
  split_ifs
  · exact (abs_max_sub_max_le_abs _ _ 0).trans
      ((infectiousProfile_lipschitz hlam t _).trans (floor_time_distance hn ht))
  · simp only [sub_self, abs_zero]
    positivity

/-- Every finite-observation event is measurable, even if its definition
contains quantification over a real compact interval. -/
theorem measurableSet_of_finite_observations (L : ℕ) (s : Set (ℕ → State))
    (hs : ∀ H G, (∀ k ≤ L, H k = G k) → (H ∈ s ↔ G ∈ s)) : MeasurableSet s := by
  let extend : CountableMarkovChain.Prefix (E := State) L → (ℕ → State) := fun P k =>
    if hk : k ≤ L then P ⟨k, Finset.mem_Iic.mpr hk⟩ else initial 0
  have he : s = (Preorder.frestrictLe L) ⁻¹' {P | extend P ∈ s} := by
    ext H
    apply hs
    intro k hk
    simp [extend, hk, Preorder.frestrictLe]
  rw [he]
  exact (Set.to_countable _).measurableSet.preimage (by fun_prop)

theorem measurableSet_gated_real_error (lam eps delta : ℝ) (n m : ℕ) :
    MeasurableSet {H : ℕ → State | ∃ t ∈ Icc (0 : ℝ) (m : ℝ),
      eps ≤ |((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n -
        (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)|} := by
  apply measurableSet_of_finite_observations (max ⌊delta * n⌋₊ (n * m))
  intro H G hHG
  have hgate := hHG ⌊delta * n⌋₊ (le_max_left _ _)
  simp only [mem_ofPred_eq]
  apply exists_congr
  intro t
  by_cases ht : t ∈ Icc (0 : ℝ) (m : ℝ)
  · have hi := hHG ⌊(n : ℝ) * t⌋₊ ((floor_time_index_le ht.2).trans (le_max_right _ _))
    simp only [ht, true_and, hgate, hi]
  · simp only [ht, false_and]

/-- The stopped step path is uniformly approximated on the entire real
compact interval, using one gate shared by every time. The limit of the
probability of that gate is deliberately a separate obligation. -/
theorem gated_stopped_real_fluid_tendsto (rate : ℕ → ℝ≥0) {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta)
    (hsmall : delta < eps / 4) :
    Tendsto (fun n : ℕ => fullLaw (rate n) n {H | ∃ t ∈ Icc (0 : ℝ) (m : ℝ),
      eps ≤ |((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n -
        (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)|})
      atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hbound : ∀ᶠ n : ℕ in atTop,
      fullLaw (rate n) n {H | ∃ t ∈ Icc (0 : ℝ) (m : ℝ),
        eps ≤ |((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n -
          (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)|} ≤
      fullLaw (rate n) n {H | ∃ k ≤ n * m,
        eps / 2 ≤ |((H k).1.infectious : ℝ) / n -
          gatedProfile lam n ⌊delta * n⌋₊ H k|} := by
    filter_upwards [eventually_gt_atTop 0,
      hinv.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < eps / 2))] with n hn hsmalln
    apply measure_mono
    rintro H ⟨t, ht, he⟩
    refine ⟨⌊(n : ℝ) * t⌋₊, floor_time_index_le ht.2, ?_⟩
    have hr := rounded_gated_profile_error hlam hn ⌊delta * n⌋₊ H ht.1
    have hh := abs_sub_le (((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n)
      (gatedProfile lam n ⌊delta * n⌋₊ H ⌊(n : ℝ) * t⌋₊)
      (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (gated_stopped_fluid_tendsto rate hlam hrate m (by positivity : 0 < eps / 2)
      hdelta (by linarith)) (Eventually.of_forall fun _ => bot_le) hbound

/-- Explicit order of limits: first the population tends to infinity, and
then the shared early observation time tends to zero from above. -/
theorem gated_stopped_real_fluid_two_stage (rate : ℕ → ℝ≥0) {lam : ℝ} (hlam : 0 < lam)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 lam))
    (m : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ),
      Tendsto (fun n : ℕ => fullLaw (rate n) n {H | ∃ t ∈ Icc (0 : ℝ) (m : ℝ),
        eps ≤ |((H ⌊(n : ℝ) * t⌋₊).1.infectious : ℝ) / n -
          (if 0 < (H ⌊delta * n⌋₊).1.infectious then max (infectiousProfile lam t) 0 else 0)|})
        atTop (𝓝 0) := by
  have hp : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), 0 < delta := self_mem_nhdsWithin
  have hs : ∀ᶠ delta : ℝ in 𝓝[>] (0 : ℝ), delta < eps / 4 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0 : ℝ) < eps / 4))
  filter_upwards [hp, hs] with delta hdelta hsmall
  exact gated_stopped_real_fluid_tendsto rate hlam hrate m heps hdelta hsmall

end Freezing1.SIR.StoppedCoupling
