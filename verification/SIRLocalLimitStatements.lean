module

import Freezing1.MainSIREmbedded

/-!
Independent source reconstruction of T06.I--II (source lines 2023--2072).
The examples concern the actual constructed embedded count/infection-tree
chain. They do not assert that the independent exponential/Poisson physical
construction has this law; that remains source obligation A65/A66.
-/

open Freezing1 Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

-- The paper's asymptotic-rate hypothesis, in its explicit ratio form,
-- implies the normalization used by the main embedded-chain theorem.
private theorem scaled_rate_of_source_ratio (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hlam : 0 < lam)
    (h : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)) := by
  have hh := h.mul_const (lam : ℝ)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hl0 : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam.ne'
  field_simp

-- The source's recovery/offspring parameter is exactly 1/(1+lambda).
example (lam : ℝ≥0) :
    (unitInterval.symm (SIR.infectionProbability lam 1) : ℝ) = 1 / (1 + (lam : ℝ)) := by
  change 1 - (SIR.infectionProbability lam 1 : ℝ) = _
  simpa only [Nat.cast_one, mul_one] using SIR.infectionProbability_complement lam 1

-- The stopped count chain has exactly the printed two transitions at a
-- nonabsorbed state; impossible infection at susceptible zero has mass0.
example (rate : ℝ≥0) (c : SIR.Counts) (hi : 0 < c.infectious) :
    SIR.countsKernel rate c =
      unitInterval.toNNReal (SIR.infectionProbability rate c.susceptible) •
        Measure.dirac ({ susceptible := c.susceptible - 1,
                         infectious := c.infectious + 1 } : SIR.Counts) +
      unitInterval.toNNReal (unitInterval.symm (SIR.infectionProbability rate c.susceptible)) •
        Measure.dirac ({ susceptible := c.susceptible,
                         infectious := c.infectious - 1 } : SIR.Counts) :=
  SIR.countsKernel_split rate hi

example (rate : ℝ≥0) (c : SIR.Counts) (hi : c.infectious = 0) :
    SIR.countsKernel rate c = Measure.dirac c := SIR.countsKernel_absorbed rate hi

-- The infectious count is the ACTUAL active-vertex cardinality along the
-- full infection-tree history, not an assumed numerical process identity.
example (rate : ℝ≥0) (n : ℕ) :
    (SIR.treeFullLaw rate n).map
      (fun H k => ({ susceptible := (H k).susceptible, infectious := (H k).tree.active.card } : SIR.Counts)) =
      SIR.countsFullLaw rate n := SIR.map_treeFullLaw_counts rate n

-- The terminal state has been reached by2n+1 and the entire state is held.
example (rate : ℝ≥0) (n : ℕ) :
    ∀ᵐ H ∂SIR.treeFullLaw rate n,
      (H (2*n+1)).tree.active = ∅ ∧
        ∀ k ≥ 2*n+1, H k = H (2*n+1) := SIR.treeFullLaw_absorbed_by rate n

-- Exact source-rate version of T06.I for the constructed embedded model.
-- The target expands both the terminal horizon and the concrete iid
-- geometric offspring/pruning law. Lambda>0 is the source premise.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0) (hlam : 0 < lam)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / ((lam : ℝ) / (n : ℝ))) atTop (𝓝 1)) :
    Tendsto
      (fun n : ℕ => ProbabilityMeasure.map
        (⟨SIR.treeFullLaw (rate n) n, inferInstance⟩ : ProbabilityMeasure (ℕ → SIR.TreeState))
        (fun H : ℕ → SIR.TreeState => PlaneForward.shape (H (2*n+1)).tree)) atTop
      (𝓝 (⟨(Measure.infinitePi (fun _ : PlaneTree.Address =>
        geometricMeasure (unitInterval.symm (SIR.infectionProbability lam 1)))).map PlaneTree.prune,
          inferInstance⟩ : ProbabilityMeasure PlaneTree.Tree)) :=
  SIR.embedded_sir_geometric_local_limit rate lam (scaled_rate_of_source_ratio rate lam hlam hratio)

-- The same weak limit explicitly controls every COMPLETE finite rooted
-- plane ball, hence uses the source's local topology at every radius.
example (rate : ℕ → ℝ≥0) (lam : ℝ≥0)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * rate n) atTop (𝓝 (lam : ℝ)))
    (h : ℕ) (B : PlaneTree.Ball) :
    Tendsto (fun n => SIR.embeddedTerminalTreeLaw (rate n) n (PlaneTree.cylinder h B)) atTop
      (𝓝 (SIR.geometricProbabilityLaw (SIR.infectionProbability lam 1) (PlaneTree.cylinder h B))) :=
  ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto
    (SIR.embedded_sir_geometric_local_limit rate lam hrate) (PlaneTree.cylinder_isClopen h B)

-- The broader zero-rate boundary is valid too; no survival premise appears.
example : Tendsto (fun n => SIR.embeddedTerminalTreeLaw 0 n) atTop
    (𝓝 (SIR.geometricProbabilityLaw 0)) := by
  have h := SIR.embedded_sir_geometric_local_limit (fun _ => 0) 0
    (by simp)
  simpa using h

-- Exact source-rate version of T06.II, with the actual deterministic
-- terminal horizon expanded. The premise is rate/(1/n)→infinity, and
-- neither a survival premise nor rate→infinity is imposed.
example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop) :
    ¬IsTightMeasureSet (Set.range fun n =>
      (SIR.treeFullLaw (rate n) n).map
        (fun H : ℕ → SIR.TreeState => PlaneForward.shape (H (2*n+1)).tree)) := by
  change ¬IsTightMeasureSet (Set.range fun n =>
    (SIR.embeddedTerminalTreeLaw (rate n) n : Measure PlaneTree.Tree))
  exact SIR.embedded_sir_not_tight_of_source_ratio rate hratio

-- The proved obstruction is stronger: every fixed bound on the ACTUAL
-- terminal root offspring count has probability tending to zero.
example (rate : ℕ → ℝ≥0)
    (hratio : Tendsto (fun n : ℕ => (rate n : ℝ) / (1 / (n : ℝ))) atTop atTop)
    (d : ℕ) :
    Tendsto (fun n =>
      ((SIR.treeFullLaw (rate n) n).map
        (fun H : ℕ → SIR.TreeState => PlaneForward.shape (H (2*n+1)).tree)).real
          {T | T.val [] ≤ d}) atTop (𝓝 0) := by
  change Tendsto (fun n => (SIR.embeddedTerminalTreeLaw (rate n) n : Measure PlaneTree.Tree).real
    {T | PlaneTree.degree T ≤ d}) atTop (𝓝 0)
  exact SIR.terminal_bounded_degree_tendsto_zero rate
    (SIR.scaled_rate_atTop_of_source_ratio rate hratio) d

-- The terminal horizon dominates every earlier prefix root degree,
-- including prefixes beyond time n. This is a supported path statement,
-- not an identification with the continuous-time Poisson process.
example (rate : ℝ≥0) (n k d : ℕ) (hk : k ≤ 2*n+1) :
    (SIR.embeddedTerminalTreeLaw rate n : Measure PlaneTree.Tree).real
      {T | PlaneTree.degree T ≤ d} ≤
    ((SIR.treeFullLaw rate n).map (fun H => (H k).tree)).real
      {s | PlaneForward.childCount s [] ≤ d} :=
  SIR.terminal_bounded_degree_le_prefix rate n k d hk

-- Constant per-pair infection intensity one is a strong scaled-rate
-- example, even though that unscaled rate does not tend to infinity.
example (d : ℕ) :
    Tendsto (fun n => (SIR.embeddedTerminalTreeLaw 1 n : Measure PlaneTree.Tree).real
      {T | PlaneTree.degree T ≤ d}) atTop (𝓝 0) := by
  exact SIR.terminal_bounded_degree_tendsto_zero (fun _ => 1)
    (by simpa only [NNReal.coe_one, mul_one] using
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) d

#print axioms Freezing1.SIR.countsKernel
#print axioms Freezing1.SIR.treeKernel
#print axioms Freezing1.SIR.treeFullLaw
#print axioms Freezing1.SIR.map_treeFullLaw_counts
#print axioms Freezing1.SIR.treeFullLaw_absorbed_by
#print axioms Freezing1.SIR.embeddedTerminalTreeLaw
#print axioms Freezing1.SIR.treeFullLaw_plane_word_mixture
#print axioms Freezing1.SIR.treeFullLaw_plane_events_tendsto
#print axioms Freezing1.SIR.terminal_cylinder_error_le
#print axioms Freezing1.SIR.tendsto_embeddedTerminalTreeLaw
#print axioms Freezing1.SIR.embedded_sir_geometric_local_limit

#print axioms Freezing1.SIR.scaled_rate_of_source_ratio
#print axioms Freezing1.SIR.scaled_rate_atTop_of_source_ratio
#print axioms Freezing1.SIR.embedded_sir_geometric_local_limit_of_source_ratio
#print axioms Freezing1.SIR.root_children_mono_of_updates
#print axioms Freezing1.SIR.terminal_bounded_degree_le_prefix
#print axioms Freezing1.SIR.terminal_bounded_degree_tendsto_zero
#print axioms Freezing1.PlaneTree.not_tight_of_bounded_degree_tendsto_zero
#print axioms Freezing1.SIR.embeddedTerminalTreeLaw_not_tight
#print axioms Freezing1.SIR.embedded_sir_not_tight_of_source_ratio
