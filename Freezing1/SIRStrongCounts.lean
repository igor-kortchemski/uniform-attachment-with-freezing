module

public import Freezing1.SIRCountLaw
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Quantitative early survival for the actual stopped SIR count chain

The bounds here concern the constructed history-dependent SIR kernel. In
particular, they do not impose survival, independence of the event signs,
or convergence of an unstopped random walk as additional hypotheses.
-/

@[expose] public section

namespace Freezing1.SIR

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

private theorem bernoulli_power_superharmonic (p : unitInterval) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hodds : 1 - (p : ℝ) ≤ (p : ℝ) * r)
    {i : ℕ} (hi : 0 < i) :
    (p : ℝ) * r ^ (i + 1) + (1 - (p : ℝ)) * r ^ (i - 1) ≤ r ^ i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  simp only [Nat.succ_sub_one, pow_succ]
  have hsign : (r - 1) * ((p : ℝ) * r - (1 - (p : ℝ))) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hr j) hsign
  nlinarith

theorem countsKernel_lintegral_power_le (rate : ℝ≥0) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) {c : Counts}
    (hodds : 1 ≤ r * (rate : ℝ) * c.susceptible) :
    ∫⁻ d, ENNReal.ofReal (r ^ d.infectious) ∂countsKernel rate c ≤
      ENNReal.ofReal (r ^ c.infectious) := by
  by_cases hi : c.infectious = 0
  · rw [countsKernel_absorbed rate hi]
    simp
  · rw [countsKernel_split rate (by omega), lintegral_add_measure,
      lintegral_smul_measure, lintegral_smul_measure]
    simp only [lintegral_dirac, infectCounts, recoverCounts]
    have hx : 0 ≤ (rate : ℝ) * c.susceptible := mul_nonneg rate.coe_nonneg (by positivity)
    have hp : 1 - (infectionProbability rate c.susceptible : ℝ) ≤
        (infectionProbability rate c.susceptible : ℝ) * r := by
      rw [infectionProbability_complement, infectionProbability_coe]
      calc
        _ ≤ (r * (rate : ℝ) * c.susceptible) /
            (1 + (rate : ℝ) * c.susceptible) :=
          div_le_div_of_nonneg_right hodds (by positivity)
        _ = _ := by ring
    have he := bernoulli_power_superharmonic (infectionProbability rate c.susceptible)
      hr hr1 hp (show 0 < c.infectious by omega)
    calc
      _ = ENNReal.ofReal ((infectionProbability rate c.susceptible : ℝ) *
          r ^ (c.infectious + 1) + (1 - (infectionProbability rate c.susceptible : ℝ)) *
          r ^ (c.infectious - 1)) := by
        rw [ENNReal.ofReal_add (mul_nonneg (unitInterval.nonneg _) (pow_nonneg hr _))
          (mul_nonneg (unitInterval.one_sub_nonneg _) (pow_nonneg hr _)),
          ENNReal.ofReal_mul (unitInterval.nonneg _),
          ENNReal.ofReal_mul (unitInterval.one_sub_nonneg _)]
        simp only [ENNReal.smul_def, smul_eq_mul, ← ENNReal.ofReal_coe_nnreal,
          unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
      _ ≤ _ := ENNReal.ofReal_le_ofReal he

theorem countsFullLaw_lintegral_succ (rate : ℝ≥0) (n k : ℕ) (f : Counts → ℝ≥0∞) :
    ∫⁻ H, f (H (k + 1)) ∂countsFullLaw rate n =
      ∫⁻ H, ∫⁻ d, f d ∂countsKernel rate (H k) ∂countsFullLaw rate n := by
  exact CountableMarkovChain.lintegral_accumulate_succ (countsKernel rate)
    (initialCounts n) () (fun _ _ => ()) (fun _ => f) k

/-- A finite-horizon exponential moment for the actual stopped chain. -/
theorem countsFullLaw_lintegral_power_le (rate : ℝ≥0) (n m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) :
    ∀ k ≤ m, ∫⁻ H, ENNReal.ofReal (r ^ (H k).infectious) ∂countsFullLaw rate n ≤
      ENNReal.ofReal r := by
  intro k hk
  induction k with
  | zero =>
    calc
      _ = ∫⁻ _ : ℕ → Counts, ENNReal.ofReal r ∂countsFullLaw rate n := by
        apply lintegral_congr_ae
        filter_upwards [countsFullLaw_initial rate n] with H hH
        simp [hH, initialCounts]
      _ = _ := by simp
      _ ≤ _ := le_rfl
  | succ k ih =>
    rw [countsFullLaw_lintegral_succ rate n k (fun c => ENNReal.ofReal (r ^ c.infectious))]
    refine (lintegral_mono_ae ?_).trans (ih (by omega))
    filter_upwards [countsFullLaw_susceptible_bounds rate n] with H hH
    apply countsKernel_lintegral_power_le rate hr hr1
    have hu : (n - m : ℕ) ≤ (H k).susceptible := by have := (hH k).1; omega
    exact hodds.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hu)
      (mul_nonneg hr rate.coe_nonneg))

/-- Absorption before a finite early horizon has a quantitative bound, with
no conditioning on survival. -/
theorem countsFullLaw_early_absorption_le (rate : ℝ≥0) (n m : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) :
    countsFullLaw rate n {H | (H m).infectious = 0} ≤ ENNReal.ofReal r := by
  calc
    _ = ∫⁻ H, {H : ℕ → Counts | (H m).infectious = 0}.indicator
        (fun _ => (1 : ℝ≥0∞)) H ∂countsFullLaw rate n := by
      rw [lintegral_indicator_const (by measurability), one_mul]
    _ ≤ ∫⁻ H, ENNReal.ofReal (r ^ (H m).infectious) ∂countsFullLaw rate n := by
      apply lintegral_mono
      intro H
      by_cases h : (H m).infectious = 0 <;> simp [h]
    _ ≤ _ := countsFullLaw_lintegral_power_le rate n m hr hr1 hodds m le_rfl

theorem countsFullLaw_early_absorption_inv_le (rate : ℝ≥0) (n m : ℕ)
    (hx : 1 ≤ (rate : ℝ) * (n - m : ℕ)) :
    countsFullLaw rate n {H | (H m).infectious = 0} ≤
      ENNReal.ofReal (((rate : ℝ) * (n - m : ℕ))⁻¹) := by
  have hx0 : 0 < (rate : ℝ) * (n - m : ℕ) := by linarith
  apply countsFullLaw_early_absorption_le rate n m (inv_nonneg.mpr hx0.le)
    ((inv_le_one₀ hx0).mpr hx)
  rw [mul_assoc, inv_mul_cancel₀ hx0.ne']

/-- Any early horizons retaining a diverging infection pressure have
vanishing unconditional absorption probability. -/
theorem countsFullLaw_early_absorption_tendsto_zero (rate : ℕ → ℝ≥0) (m : ℕ → ℕ)
    (hpressure : Tendsto (fun n => (rate n : ℝ) * (n - m n : ℕ)) atTop atTop) :
    Tendsto (fun n => (countsFullLaw (rate n) n).real
      {H | (H (m n)).infectious = 0}) atTop (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
  · filter_upwards [hpressure.eventually (eventually_ge_atTop 1)] with n hn
    have h := countsFullLaw_early_absorption_inv_le (rate n) n (m n) hn
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  · exact tendsto_inv_atTop_zero.comp hpressure

/-- A step which did not consume a susceptible individual. After
absorption every held step is included, so this statistic is total. -/
def missedInfection (c d : Counts) : ℕ := if d.susceptible = c.susceptible then 1 else 0

def missedInfections (H : ℕ → Counts) : ℕ → ℕ
  | 0 => 0
  | k + 1 => missedInfections H k + missedInfection (H k) (H (k + 1))

@[fun_prop] theorem measurable_missedInfections (m : ℕ) :
    Measurable (fun H : ℕ → Counts => missedInfections H m) := by
  induction m with
  | zero => exact measurable_const
  | succ m ih =>
    simp only [missedInfections]
    apply ih.add
    exact (measurable_of_countable fun q : Counts × Counts =>
      missedInfection q.1 q.2).comp
        (show Measurable (fun H : ℕ → Counts => (H m, H (m + 1))) from by fun_prop)

theorem countsFullLaw_lintegral_transition (rate : ℝ≥0) (n k : ℕ)
    (f : Counts → Counts → ℝ≥0∞) :
    ∫⁻ H, f (H k) (H (k + 1)) ∂countsFullLaw rate n =
      ∫⁻ H, ∫⁻ d, f (H k) d ∂countsKernel rate (H k) ∂countsFullLaw rate n := by
  let F : (((i : Finset.Iic k) → Counts) × Counts) → ℝ≥0∞ :=
    fun q => f (q.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩) q.2
  change _ = _
  calc
    _ = ∫⁻ q, F q ∂(countsFullLaw rate n).map
        (fun H => (Preorder.frestrictLe k H, H (k + 1))) := by
      rw [lintegral_map (measurable_of_countable _) (by fun_prop)]
      rfl
    _ = ∫⁻ H, ∫⁻ d, F (H, d) ∂CountableMarkovChain.historyKernel
        (countsKernel rate) k H ∂(countsFullLaw rate n).map (Preorder.frestrictLe k) := by
      rw [countsFullLaw, CountableMarkovChain.map_prefix_next,
        Measure.lintegral_compProd (measurable_of_countable _)]
    _ = _ := by
      rw [lintegral_map (measurable_of_countable _) (by fun_prop)]
      rfl

theorem countsKernel_lintegral_missedInfection_le (rate : ℝ≥0) {u : ℕ}
    (hu : 0 < u) {c : Counts} (huc : u ≤ c.susceptible) (r : ℝ) :
    ∫⁻ d, (missedInfection c d : ℝ≥0∞) ∂countsKernel rate c ≤
      ENNReal.ofReal (1 / (1 + (rate : ℝ) * u)) +
        ENNReal.ofReal (r ^ c.infectious) := by
  by_cases hi : c.infectious = 0
  · rw [countsKernel_absorbed rate hi]
    simp [missedInfection, hi]
  · rw [countsKernel_split rate (by omega), lintegral_add_measure,
      lintegral_smul_measure, lintegral_smul_measure]
    have hne : c.susceptible - 1 ≠ c.susceptible := by omega
    simp only [lintegral_dirac, missedInfection, infectCounts, recoverCounts,
      ite_eq_right hne, ite_true, Nat.cast_zero, Nat.cast_one, smul_zero, zero_add,
      ENNReal.smul_one]
    apply le_trans ?_ (le_add_right le_rfl)
    rw [← ENNReal.ofReal_coe_nnreal, unitInterval.coe_toNNReal,
      unitInterval.coe_symm_eq, infectionProbability_complement]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (by positivity)
    have hmul := mul_le_mul_of_nonneg_left (show (u : ℝ) ≤ c.susceptible by exact_mod_cast huc)
      rate.coe_nonneg
    linarith

theorem countsFullLaw_lintegral_missedInfection_step_le (rate : ℝ≥0) (n m : ℕ)
    (hm : m < n) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) {k : ℕ} (hk : k ≤ m) :
    ∫⁻ H, (missedInfection (H k) (H (k + 1)) : ℝ≥0∞) ∂countsFullLaw rate n ≤
      ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r := by
  rw [countsFullLaw_lintegral_transition rate n k
    (fun c d => (missedInfection c d : ℝ≥0∞))]
  calc
    _ ≤ ∫⁻ H, ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) +
        ENNReal.ofReal (r ^ (H k).infectious) ∂countsFullLaw rate n := by
      apply lintegral_mono_ae
      filter_upwards [countsFullLaw_susceptible_bounds rate n] with H hH
      apply countsKernel_lintegral_missedInfection_le rate (show 0 < n - m by omega)
      have := (hH k).1
      omega
    _ = ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) +
        ∫⁻ H, ENNReal.ofReal (r ^ (H k).infectious) ∂countsFullLaw rate n := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ _ := add_le_add (le_refl _)
      (countsFullLaw_lintegral_power_le rate n m hr hr1 hodds k hk)

/-- Missed infections include both recoveries and held steps after early
absorption. The estimate therefore already pays for extinction. -/
theorem countsFullLaw_lintegral_missedInfections_le (rate : ℝ≥0) (n m : ℕ)
    (hm : m < n) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) :
    ∫⁻ H, (missedInfections H m : ℝ≥0∞) ∂countsFullLaw rate n ≤
      m * (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r) := by
  have haux : ∀ k ≤ m, ∫⁻ H, (missedInfections H k : ℝ≥0∞) ∂countsFullLaw rate n ≤
      k * (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r) := by
    intro k hk
    induction k with
    | zero => simp [missedInfections]
    | succ k ih =>
      simp only [missedInfections, Nat.cast_add]
      have hmeas : Measurable (fun H : ℕ → Counts => (missedInfections H k : ℝ≥0∞)) :=
        (measurable_of_countable (fun a : ℕ => (a : ℝ≥0∞))).comp
          (measurable_missedInfections k)
      rw [lintegral_add_left hmeas]
      calc
        _ ≤ k * (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r) +
            (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r) :=
          add_le_add (ih (by omega))
            (countsFullLaw_lintegral_missedInfection_step_le rate n m hm hr hr1 hodds (by omega))
        _ = _ := by push_cast; ring
  exact haux m le_rfl

theorem Counts.LegalNext.susceptible_missedInfection {c d : Counts} (h : c.LegalNext d) :
    d.susceptible + 1 = c.susceptible + missedInfection c d := by
  rcases h with ⟨_, rfl⟩ | ⟨_, ⟨hu, rfl⟩ | rfl⟩
  · simp [missedInfection]
  · have hne : c.susceptible - 1 ≠ c.susceptible := by omega
    simp [missedInfection, infectCounts, hne]
    omega
  · simp [missedInfection, recoverCounts]

theorem legalHistory_susceptible_missedInfections {H : ℕ → Counts} {n : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ j, (H j).LegalNext (H (j + 1))) (m : ℕ) :
    (H m).susceptible + m = n + missedInfections H m := by
  induction m with
  | zero => simp [h0, initialCounts, missedInfections]
  | succ m ih =>
    have := (hl m).susceptible_missedInfection
    simp only [missedInfections]
    omega

theorem Counts.LegalNext.infectious_drop_le_one {c d : Counts} (h : c.LegalNext d) :
    c.infectious ≤ d.infectious + 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, ⟨_, rfl⟩ | rfl⟩ <;>
    (try simp only [infectCounts, recoverCounts]) <;> omega

theorem Counts.LegalNext.infectious_rise_le_one {c d : Counts} (h : c.LegalNext d) :
    d.infectious ≤ c.infectious + 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, ⟨_, rfl⟩ | rfl⟩ <;>
    (try simp only [infectCounts, recoverCounts]) <;> omega

theorem Counts.LegalNext.potential_drop_le_one {c d : Counts} (h : c.LegalNext d) :
    c.potential ≤ d.potential + 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨hi, ⟨hu, rfl⟩ | rfl⟩ <;>
    simp only [Counts.potential, infectCounts, recoverCounts] <;> omega

theorem legalHistory_potential_lower {H : ℕ → Counts} {n : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ j, (H j).LegalNext (H (j + 1))) (k : ℕ) :
    2 * n + 1 ≤ (H k).potential + k := by
  induction k with
  | zero => simp [h0, Counts.potential, initialCounts]
  | succ k ih => have := (hl k).potential_drop_le_one; omega

theorem legalHistory_infectious_upper {H : ℕ → Counts} {n : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ j, (H j).LegalNext (H (j + 1))) (k : ℕ) :
    (H k).infectious ≤ k + 1 := by
  induction k with
  | zero => simp [h0, initialCounts]
  | succ k ih => have := (hl k).infectious_rise_le_one; omega

theorem legalHistory_infectious_drop {H : ℕ → Counts}
    (hl : ∀ j, (H j).LegalNext (H (j + 1))) {a b : ℕ} (hab : a ≤ b) :
    (H a).infectious ≤ (H b).infectious + (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih => have := (hl b).infectious_drop_le_one; omega

theorem legalHistory_susceptible_drop {H : ℕ → Counts}
    (hl : ∀ j, (H j).LegalNext (H (j + 1))) {a b : ℕ} (hab : a ≤ b) :
    (H a).susceptible ≤ (H b).susceptible + (b - a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih => have := (hl b).susceptible_drop_le_one; omega

/-- A deterministic bound on the entire discrete triangular profile. It
also holds for paths absorbed before the comparison time. -/
theorem legalHistory_triangle_error {H : ℕ → Counts} {n m : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ j, (H j).LegalNext (H (j + 1)))
    (hm : m ≤ n) {k : ℕ} (hk : k ≤ 2 * n) :
    |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)| ≤
      2 * (H m).susceptible + 1 := by
  have hup : (H k).infectious ≤ min k (2 * n - k) + 1 := by
    have hleft := legalHistory_infectious_upper h0 hl k
    have hright : (H k).infectious ≤ 2 * n - k + 1 := by
      by_cases hi : (H k).infectious = 0
      · omega
      · have hc := legalHistory_count_identity h0 hl (show 0 < (H k).infectious by omega)
        omega
    omega
  have hlo : min k (2 * n - k) ≤ (H k).infectious + 2 * (H m).susceptible := by
    by_cases hkm : k ≤ m
    · by_cases hi : (H k).infectious = 0
      · have he := legalHistory_absorbed_persists hl hi m hkm
        have hp := legalHistory_potential_lower h0 hl k
        simp only [Counts.potential, hi, add_zero] at hp
        rw [he]
        omega
      · have hc := legalHistory_count_identity h0 hl (show 0 < (H k).infectious by omega)
        have hu := legalHistory_susceptible_drop hl hkm
        omega
    · have hp := legalHistory_potential_lower h0 hl m
      have hd := legalHistory_infectious_drop hl (show m ≤ k by omega)
      simp only [Counts.potential] at hp
      omega
  rw [abs_le]
  constructor
  · have h : (↑(min k (2 * n - k)) : ℝ) ≤ (H k).infectious + 2 * (H m).susceptible := by
      exact_mod_cast hlo
    linarith
  · have h : ((H k).infectious : ℝ) ≤ (min k (2 * n - k) : ℕ) + 1 := by
      exact_mod_cast hup
    have hu : (0 : ℝ) ≤ (H m).susceptible := by positivity
    linarith

theorem countsFullLaw_lintegral_susceptible_early_le (rate : ℝ≥0) (n m : ℕ)
    (hm : m < n) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) :
    ∫⁻ H, ((H m).susceptible : ℝ≥0∞) ∂countsFullLaw rate n ≤
      (n - m : ℕ) + m *
        (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r) := by
  calc
    _ = ∫⁻ H, ((n - m : ℕ) : ℝ≥0∞) + (missedInfections H m : ℝ≥0∞)
        ∂countsFullLaw rate n := by
      apply lintegral_congr_ae
      filter_upwards [countsFullLaw_initial rate n, countsFullLaw_legal rate n] with H h0 hl
      have hh := legalHistory_susceptible_missedInfections h0 hl m
      have he : (H m).susceptible = n - m + missedInfections H m := by omega
      simp [he]
    _ = ((n - m : ℕ) : ℝ≥0∞) +
        ∫⁻ H, (missedInfections H m : ℝ≥0∞) ∂countsFullLaw rate n := by
      rw [lintegral_add_left measurable_const]
      simp
    _ ≤ _ := add_le_add (le_refl _)
      (countsFullLaw_lintegral_missedInfections_le rate n m hm hr hr1 hodds)

/-- A quantitative bound on a failure of the full triangular profile over
the entire discrete interval `0,...,2n`. -/
theorem countsFullLaw_triangle_error_le (rate : ℝ≥0) (n m : ℕ)
    (hm : m < n) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) {e : ℝ} (he : 0 < e) :
    countsFullLaw rate n
      {H | ∃ k ≤ 2 * n, e ≤ |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} ≤
      (2 * (((n - m : ℕ) : ℝ≥0∞) + m *
        (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r)) + 1) /
        ENNReal.ofReal e := by
  have hmeas : Measurable (fun H : ℕ → Counts => (2 : ℝ≥0∞) * (H m).susceptible + 1) :=
    (measurable_of_countable (fun c : Counts => (2 : ℝ≥0∞) * c.susceptible + 1)).comp
      (measurable_pi_apply m)
  calc
    _ ≤ countsFullLaw rate n
        {H | ENNReal.ofReal e ≤ (2 : ℝ≥0∞) * (H m).susceptible + 1} := by
      apply measure_mono_ae
      filter_upwards [countsFullLaw_initial rate n, countsFullLaw_legal rate n] with H h0 hl
      rintro ⟨k, hk, hbad⟩
      have hh := hbad.trans (legalHistory_triangle_error h0 hl hm.le hk)
      have hhNat : e ≤ ((2 * (H m).susceptible + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh
      have hh' : ENNReal.ofReal e ≤ ((2 * (H m).susceptible + 1 : ℕ) : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal hhNat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hh'
    _ ≤ (∫⁻ H, (2 : ℝ≥0∞) * (H m).susceptible + 1 ∂countsFullLaw rate n) /
        ENNReal.ofReal e :=
      meas_ge_le_lintegral_div hmeas.aemeasurable (by positivity) ENNReal.ofReal_ne_top
    _ ≤ _ := by
      apply ENNReal.div_le_div_right
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num)]
      simp only [lintegral_const, measure_univ, mul_one]
      exact add_le_add (mul_le_mul_of_nonneg_left (countsFullLaw_lintegral_susceptible_early_le
        rate n m hm hr hr1 hodds) (by positivity)) (le_refl _)

theorem countsFullLaw_triangle_error_real_le (rate : ℝ≥0) (n m : ℕ)
    (hm : m < n) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hodds : 1 ≤ r * (rate : ℝ) * (n - m : ℕ)) {e : ℝ} (he : 0 < e) :
    (countsFullLaw rate n).real
      {H | ∃ k ≤ 2 * n, e ≤ |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} ≤
      (2 * ((n - m : ℕ) + (m : ℝ) *
        (1 / (1 + (rate : ℝ) * (n - m : ℕ)) + r)) + 1) / e := by
  have h := countsFullLaw_triangle_error_le rate n m hm hr hr1 hodds he
  have h' := ENNReal.toReal_mono (show
      (2 * (((n - m : ℕ) : ℝ≥0∞) + m *
        (ENNReal.ofReal (1 / (1 + (rate : ℝ) * (n - m : ℕ))) + ENNReal.ofReal r)) + 1) /
        ENNReal.ofReal e ≠ ∞ by finiteness) h
  have hq : 0 ≤ 1 / (1 + (rate : ℝ) * (n - m : ℕ)) := by positivity
  rw [ENNReal.toReal_div, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)] at h'
  simpa only [Measure.real, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
    ENNReal.toReal_one, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal he.le,
    ENNReal.toReal_ofReal hq] using h'

private theorem earlyHorizon_ceil_bounds {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) {n : ℕ}
    (hn : 0 < n) :
    n - (n - ⌈d * n⌉₊) = ⌈d * n⌉₊ ∧ n - ⌈d * n⌉₊ < n := by
  have hu : ⌈d * n⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  have hu0 : 0 < ⌈d * n⌉₊ := Nat.ceil_pos.mpr (by positivity)
  omega

private theorem earlyHorizon_pressure_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    Tendsto (fun n : ℕ => (rate n : ℝ) * (n - (n - ⌈d * n⌉₊) : ℕ)) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ (hstrong.const_mul_atTop hd)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  rw [(earlyHorizon_ceil_bounds hd hd1 hn).1]
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil (d * (n : ℝ))) (rate n).coe_nonneg
  nlinarith

private theorem strong_triangle_probability_bound (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {d e : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (he : 0 < e) :
    ∃ B : ℕ → ℝ, Tendsto B atTop (nhds (2 * d / e)) ∧ ∀ᶠ n in atTop,
      (countsFullLaw (rate n) n).real
        {H | ∃ k ≤ 2 * n, e * n ≤
          |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} ≤ B n := by
  let x : ℕ → ℝ := fun n => (rate n : ℝ) * (n - (n - ⌈d * n⌉₊) : ℕ)
  let B : ℕ → ℝ := fun n =>
    (2 * ((⌈d * n⌉₊ : ℝ) / n + (1 / (1 + x n) + (x n)⁻¹)) + (n : ℝ)⁻¹) / e
  have hx : Tendsto x atTop atTop := earlyHorizon_pressure_tendsto rate hstrong hd hd1
  have hq : Tendsto (fun n => 1 / (1 + x n)) atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_left atTop 1 hx) using 1
    funext n
    rw [Function.comp_apply, one_div]
  have hr : Tendsto (fun n => (x n)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp hx
  have hu : Tendsto (fun n : ℕ => (⌈d * n⌉₊ : ℝ) / n) atTop (nhds d) :=
    (tendsto_nat_ceil_mul_div_atTop hd.le).comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  refine ⟨B, ?_, ?_⟩
  · have hh : Tendsto (fun n : ℕ => (2 * ((⌈d * n⌉₊ : ℝ) / n +
        (1 / (1 + x n) + (x n)⁻¹)) + (n : ℝ)⁻¹) / e) atTop
        (nhds ((2 * (d + (0 + 0)) + 0) / e)) :=
      ((tendsto_const_nhds.mul (hu.add (hq.add hr))).add hi).div_const e
    simpa only [add_zero] using hh
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hx.eventually (eventually_ge_atTop 1)]
      with n hn hxn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hxm : 0 < x n := by linarith
    have hu_eq := (earlyHorizon_ceil_bounds hd hd1 hn).1
    have hm := (earlyHorizon_ceil_bounds hd hd1 hn).2
    have hodds : 1 ≤ (x n)⁻¹ * (rate n : ℝ) * (n - (n - ⌈d * n⌉₊) : ℕ) := by
      rw [mul_assoc]
      change 1 ≤ (x n)⁻¹ * x n
      rw [inv_mul_cancel₀ hxm.ne']
    have hb := countsFullLaw_triangle_error_real_le (rate n) n (n - ⌈d * n⌉₊) hm
      (inv_nonneg.mpr hxm.le) ((inv_le_one₀ hxm).mpr hxn) hodds (mul_pos he hnR)
    apply hb.trans
    change (2 * ((n - (n - ⌈d * n⌉₊) : ℕ) + ((n - ⌈d * n⌉₊ : ℕ) : ℝ) *
      (1 / (1 + x n) + (x n)⁻¹)) + 1) / (e * n) ≤ B n
    rw [hu_eq]
    have hC : 0 ≤ 1 / (1 + x n) + (x n)⁻¹ := by positivity
    have hmn : (((n - ⌈d * n⌉₊ : ℕ) : ℝ) / n) ≤ 1 :=
      (div_le_one hnR).mpr (by exact_mod_cast Nat.sub_le n ⌈d * n⌉₊)
    calc
      _ = (2 * ((⌈d * n⌉₊ : ℝ) / n + (((n - ⌈d * n⌉₊ : ℕ) : ℝ) / n) *
          (1 / (1 + x n) + (x n)⁻¹)) + (n : ℝ)⁻¹) / e := by
        field_simp [hnR.ne', he.ne', hxm.ne', show 1 + x n ≠ 0 by linarith]
      _ ≤ B n := by
        dsimp only [B]
        apply div_le_div_of_nonneg_right _ he.le
        apply add_le_add _ (le_refl _)
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        apply add_le_add (le_refl _)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hmn hC

/-- Uniform convergence in probability on the complete discrete time grid
for the genuine stopped chain in the strong-infection regime. -/
theorem countsFullLaw_triangle_tendsto_zero (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {e : ℝ} (he : 0 < e) :
    Tendsto (fun n => (countsFullLaw (rate n) n).real
      {H | ∃ k ≤ 2 * n, e * n ≤
        |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|}) atTop (nhds 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le ENNReal.toReal_nonneg
  · intro b hb
    let d : ℝ := min (1 / 2) (b * e / 8)
    have hd : 0 < d := lt_min (by norm_num) (by positivity)
    have hd1 : d ≤ 1 := (min_le_left _ _).trans (by norm_num)
    have hdb : 2 * d / e < b := by
      rw [div_lt_iff₀ he]
      have hdle : d ≤ b * e / 8 := min_le_right _ _
      have hbe : 0 < b * e := mul_pos hb he
      nlinarith
    obtain ⟨B, hB, hbound⟩ := strong_triangle_probability_bound rate hstrong hd hd1 he
    filter_upwards [hbound, hB.eventually (eventually_lt_nhds hdb)] with n hn hn'
    exact hn.trans_lt hn'

private theorem triangle_lipschitz (s t : ℝ) :
    |min s (2 - s) - min t (2 - t)| ≤ |s - t| := by
  have hh := abs_min_sub_min_le_max s (2 - s) t (2 - t)
  have he : (2 - s) - (2 - t) = t - s := by ring
  simpa only [he, abs_sub_comm t s, max_self] using hh

private theorem triangle_floor_index_le (n : ℕ) {t : ℝ} (ht : t ≤ 2) :
    ⌊(n : ℝ) * t⌋₊ ≤ 2 * n := by
  apply Nat.floor_le_of_le
  have hh := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hh

private theorem triangle_floor_distance {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 ≤ t) :
    |(⌊(n : ℝ) * t⌋₊ : ℝ) / n - t| ≤ 1 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) ht)
  have hf' := Nat.lt_floor_add_one ((n : ℝ) * t)
  have hle : (⌊(n : ℝ) * t⌋₊ : ℝ) / n ≤ t :=
    (div_le_iff₀ hnR).mpr (by nlinarith)
  calc
    _ = ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) / n := by
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      field_simp
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hnR.le

private theorem triangle_grid_value {n k : ℕ} (hn : 0 < n) (hk : k ≤ 2 * n) :
    ((min k (2 * n - k) : ℕ) : ℝ) / n = min ((k : ℝ) / n) (2 - (k : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_min, ← min_div_div_right hnR.le, Nat.cast_sub hk, Nat.cast_mul,
    Nat.cast_ofNat, sub_div, mul_div_cancel_right₀ _ hnR.ne']

private theorem triangle_rounded_profile_error {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 2) :
    |((min ⌊(n : ℝ) * t⌋₊ (2 * n - ⌊(n : ℝ) * t⌋₊) : ℕ) : ℝ) / n -
      min t (2 - t)| ≤ 1 / n := by
  rw [triangle_grid_value hn (triangle_floor_index_le n ht.2)]
  exact (triangle_lipschitz _ _).trans (triangle_floor_distance hn ht.1)

private theorem counts_measurableSet_of_finite_observations (L : ℕ)
    (s : Set (ℕ → Counts))
    (hs : ∀ H G, (∀ k ≤ L, H k = G k) → (H ∈ s ↔ G ∈ s)) : MeasurableSet s := by
  let extend : ((i : Finset.Iic L) → Counts) → (ℕ → Counts) := fun P k =>
    if hk : k ≤ L then P ⟨k, Finset.mem_Iic.mpr hk⟩ else initialCounts 0
  have he : s = (Preorder.frestrictLe L) ⁻¹' {P | extend P ∈ s} := by
    ext H
    apply hs
    intro k hk
    simp [extend, hk, Preorder.frestrictLe]
  rw [he]
  exact (Set.to_countable _).measurableSet.preimage (by fun_prop)

/-- The event defining the real-interval uniform error is a finite
observation event, despite its quantifier over all real times. -/
theorem measurableSet_triangle_uniform_error (n : ℕ) (e : ℝ) :
    MeasurableSet {H : ℕ → Counts | ∃ t ∈ Set.Icc (0 : ℝ) 2,
      e ≤ |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|} := by
  apply counts_measurableSet_of_finite_observations (2 * n)
  intro H G hHG
  apply exists_congr
  intro t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 2
  · have hi := hHG ⌊(n : ℝ) * t⌋₊ (triangle_floor_index_le n ht.2)
    simp only [ht, true_and, hi]
  · simp only [ht, false_and]

/-- The strong-infection fluid limit for the actual stopped embedded SIR
chain, uniformly over the full real time interval `[0,2]`. -/
theorem countsFullLaw_strong_uniform_tendsto (rate : ℕ → ℝ≥0)
    (hstrong : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop atTop)
    {e : ℝ} (he : 0 < e) :
    Tendsto (fun n => (countsFullLaw (rate n) n).real
      {H | ∃ t ∈ Set.Icc (0 : ℝ) 2, e ≤
        |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|}) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    convert tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1
    funext n
    rw [Function.comp_apply, one_div]
  have hbound : ∀ᶠ n : ℕ in atTop,
      (countsFullLaw (rate n) n).real
        {H | ∃ t ∈ Set.Icc (0 : ℝ) 2, e ≤
          |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n - min t (2 - t)|} ≤
      (countsFullLaw (rate n) n).real
        {H | ∃ k ≤ 2 * n, (e / 2) * n ≤
          |((H k).infectious : ℝ) - (min k (2 * n - k) : ℕ)|} := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),
      hinv.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < e / 2))]
      with n hn hsmall
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    apply measureReal_mono ?_ (measure_ne_top _ _)
    rintro H ⟨t, ht, hbad⟩
    refine ⟨⌊(n : ℝ) * t⌋₊, triangle_floor_index_le n ht.2, ?_⟩
    have hr := triangle_rounded_profile_error hn ht
    have hh := abs_sub_le (((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n)
      (((min ⌊(n : ℝ) * t⌋₊ (2 * n - ⌊(n : ℝ) * t⌋₊) : ℕ) : ℝ) / n)
      (min t (2 - t))
    have hgrid : e / 2 ≤
        |((H ⌊(n : ℝ) * t⌋₊).infectious : ℝ) / n -
          ((min ⌊(n : ℝ) * t⌋₊ (2 * n - ⌊(n : ℝ) * t⌋₊) : ℕ) : ℝ) / n| := by
      linarith
    rw [← sub_div, abs_div, abs_of_pos hnR] at hgrid
    exact (le_div_iff₀ hnR).mp hgrid
  exact squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hbound
    (countsFullLaw_triangle_tendsto_zero rate hstrong (by positivity : 0 < e / 2))

end Freezing1.SIR
