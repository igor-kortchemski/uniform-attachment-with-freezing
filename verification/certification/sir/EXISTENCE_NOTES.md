# Non-vacuity of `PoissonSIRData` (existence of independent Poisson clock data)

## Result

The following modules are built and imported by `Freezing1.lean` in the candidate.
`exists_data` and `exists_family` are selected SIR comparison targets. Earlier
implementation notes and the unchanged Challenge header contain historical
pending-work wording; that is superseded by this status and the config.

| Module | Lines | Content |
| --- | --- | --- |
| `Freezing1/SIRPoissonExistenceSums.lean` | about 265 | law of the partial sums of iid exponential waiting times (`waiting`, `S`, `tail`, `waiting_sum_le_eq_tail`), a.s. positivity and unboundedness |
| `Freezing1/SIRPoissonExistenceProcess.lean` | about 145 | arrival path built from waiting times, Poisson counting law, `exists_hasPoissonCounts` |
| `Freezing1/SIRPoissonExistence.lean` | about 120 | product space, `PoissonSIRData.exists_data` and companions |

Main statement (namespace `Freezing1.SIR`):

```lean
theorem PoissonSIRData.exists_data (n : ℕ) (rate : ℝ≥0) (hrate : 0 < rate) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (mu : Measure Ω) (_ : IsProbabilityMeasure mu)
      (X : (c : ClockSlot n) → Ω → ClockDatum c), PoissonSIRData mu n rate X
```

The hypothesis `0 < rate` is necessary, not a convenience. Companion theorems:

* `PoissonContact.not_hasPoissonCounts_zero`: no probability measure on `ArrivalPath` has
  `HasPoissonCounts nu 0` (a.s. `count a N = 0` for all `N : ℕ`, but `count a N > 0` once `N ≥ first a`).
* `PoissonSIRData.false_of_rate_zero`: `¬ PoissonSIRData mu n 0 X` for every probability `mu`.
* `PoissonSIRData.exists_data_iff`: the existence statement holds exactly when `0 < rate`.
* `PoissonSIRData.exists_family`: for `rate : ℕ → ℝ≥0` eventually positive there are
  `Ω n`, `mu n`, `X n` with `∀ᶠ n in atTop, PoissonSIRData (mu n) n (rate n) (X n)`, i.e. the
  exact shape of the hypothesis `hdata` of the nine physical theorems. The nine theorems derive
  `0 < rate n` eventually from their rate hypotheses (`hratio`), so the positivity assumption is
  consistent with them. The remaining hypotheses (`hlam`, `hratio`) concern only the real
  sequence `rate`, for instance `rate n = lam / n`.
* `PoissonExistence.exists_hasPoissonCounts (r) (hr : 0 < r)`: a probability measure on
  `ArrivalPath` with `HasPoissonCounts nu r`.

`#print axioms` for all five theorems above and `exists_family`: `propext`, `Classical.choice`,
`Quot.sound` only. No `sorry`, no `native_decide`, no `bv_decide`, no new axiom. Each module was built with
the lock wrapper (`Freezing1.SIRPoissonExistenceSums`, `...Process`, `...SIRPoissonExistence`), with no
warnings from these files.

## Proof route

1. Waiting times: `waiting r := Measure.infinitePi (fun _ : ℕ => expMeasure r)` on `ℕ → ℝ`;
   coordinates are `iIndepFun` (`iIndepFun_iff_map_fun_eq_infinitePi_map`).
2. `S k E = ∑ i < k, E i`. For `u ≥ 0`: `P(S k ≤ u) = ∑'_{j} ofReal (pmass r (j + k) u)` with
   `pmass r j u = exp (-(r u)) (r u)^j / j!` (the Poisson tail), and `0` for `u < 0`.
   Induction on `k`: base `∑ j pmass = 1` (`hasSum_one_poissonMeasure`); step uses
   `IndepFun (S k) (E k)` (`iIndepFun.indepFun_sum_range_succ`), the product law and
   `Measure.prod_apply_symm`, giving `P(S (k+1) ≤ t) = ∫ P(S k ≤ t - s) d expMeasure r (s)`.
   The convolution identity is checked termwise on the series: the explicit integral
   `∫_0^t pmass r j (t - s) · r e^{-rs} ds = pmass r (j+1) t` (`lintegral_exp_convolve`, via
   `intervalIntegral.integral_comp_sub_left` and `integral_pow`) and `lintegral_tsum`. This avoids
   Gamma convolution, which Mathlib does not have, and needs no subtraction in `ℝ≥0∞`.
3. Divergence of partial sums: for fixed `M ≥ 0`, `P(∀ k, S k ≤ M) ≤ P(S k ≤ M)` which is a Poisson tail
   and tends to `0` (`ENNReal.tendsto_sum_nat_add`), so the partial sums are a.s. unbounded; no Borel-Cantelli
   or law of large numbers is needed. Positivity of each waiting time is a.s. from `expMeasure_Ioi_of_nonneg`.
4. Arrival path: `good` is the measurable set of waiting sequences with positive entries and unbounded partial sums
   (probability one). `pathOf E` is `k ↦ S (k+1) E` on `good` and the fallback path `k ↦ k + 1` elsewhere; it is
   a measurable map into `ArrivalPath`. On `good`, `count (pathOf E) t = k ↔ S k E ≤ t < S (k+1) E`, so
   `P(count = k) = tail k t - tail (k+1) t = pmass r k t` (peeling the first term of the tail series).
   Hence `(waiting r).map pathOf` has `HasPoissonCounts` (`Measure.ext_of_singleton`).
5. Assembly: `Ω := (c : ClockSlot n) → ClockDatum c`, `mu := Measure.pi law` with `law (v, none) = expMeasure 1`,
   `law (v, some w) = nu`; `X c ω := ω c`. Independence is `iIndepFun_pi`, marginals are
   `measurePreserving_eval`. `ClockSlot n` is finite, so `Measure.pi` applies; self-contacts `(v, some v)` are included.

## Departures from the suggested route

* No Gamma distribution and no Borel-Cantelli II / SLLN; the Poisson tail series is used instead, which turns the
  convolution step into the identity `Φ(pmass_j) = pmass_{j+1}`.
* The target holds only for `0 < rate`, proved sharp by `exists_data_iff`.
* The fallback arrival path is used only on a `waiting`-null set; it does not affect any law.
