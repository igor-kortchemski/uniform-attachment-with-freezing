module

import Freezing1.MainLocalDegreeNecessity

/-! Independently reconstructed A24 all-vertex marginal obstruction.
No common joint coupling of all rows is assumed or concluded here. -/

open Filter MeasureTheory
open scoped Topology ENNReal Classical
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

set_option backward.isDefEq.respectTransparency false

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hrows : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n,
      n ≤ φ n ∧ ∀ i, 1 ≤ i → i ≤ n → rows (φ n) i = y i :=
  exists_strictMono_matching_prefixes rows y hrows

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hrows : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n,
      (prefixCoupling y (rows (φ n)) n).map Prod.fst = fullLaw y ∧
      (prefixCoupling y (rows (φ n)) n).map Prod.snd = fullLaw (rows (φ n)) ∧
      ∀ᵐ p ∂prefixCoupling y (rows (φ n)) n, ∀ r,
        ((p.1 n).vertices.filter fun v => (p.1 n).graph.Adj r v).card ≤
          ((p.2 (φ n)).vertices.filter fun v => (p.2 (φ n)).graph.Adj r v).card :=
  exists_matching_degree_couplings rows y hrows

example (x : SignSequence) (r : ℕ) :
    ∀ᵐ H ∂fullLaw x,
      (∀ d : ℕ, ∃ n : ℕ, d < ((H n).vertices.filter fun v => (H n).graph.Adj r v).card) ↔
        Tendsto (fun n => ((H n).vertices.filter fun v => (H n).graph.Adj r v).card)
          atTop atTop := by
  filter_upwards [fullLaw_all_vertexDegree_monotone x] with H hH
  exact degreeUnbounded_iff_tendsto (hH r)

/-- Independently reconstruct the source's first displayed limiting union
identity; monotonicity of actual degrees then identifies its limit event
with divergence, as checked immediately above. -/
example (x : SignSequence) (r : ℕ) :
    Tendsto (fun d : ℕ => (fullLaw x).real
      {H | ∃ n : ℕ, d < ((H n).vertices.filter fun v => (H n).graph.Adj r v).card})
      atTop (𝓝 ((fullLaw x) (degreeUnbounded r)).toReal) := by
  let U : ℕ → Set History := fun d => {H | ∃ n : ℕ, d < vertexDegree (H n) r}
  have hm (d : ℕ) : MeasurableSet (U d) := by
    apply measurableSet_setOfPred.mpr
    apply Measurable.exists
    intro n
    exact (measurable_from_top : Measurable (fun s : State => d < vertexDegree s r)).comp
      (measurable_pi_apply n)
  have ha : Antitone U := by
    intro a b hab H hH
    obtain ⟨n, hn⟩ := hH
    exact ⟨n, lt_of_le_of_lt hab hn⟩
  have he : (⋂ d : ℕ, U d) = degreeUnbounded r := by
    ext H
    simp only [Set.mem_iInter, U, degreeUnbounded, Set.mem_ofPred_eq]
  have hh := tendsto_measure_iInter_atTop (μ := fullLaw x)
    (fun d => (hm d).nullMeasurableSet) ha ⟨0, measure_ne_top _ _⟩
  rw [he] at hh
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hh

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hrows : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) (r : ℕ)
    (hpos : (fullLaw y) {H | ∀ d : ℕ, ∃ n : ℕ,
      d < ((H n).vertices.filter fun v => (H n).graph.Adj r v).card} ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (localProbabilityLaw (rows n) n : Measure LocalTree.Tree).real
        {T | d < (T.val (r + 1)).card} :=
  diagonal_ballCard_not_tight_of_degree_unbounded rows y hrows r hpos

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hrows : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    (ν : ProbabilityMeasure LocalTree.Tree)
    (hweak : Tendsto (fun n => localProbabilityLaw (rows n) n) atTop (𝓝 ν)) :
    ∀ r : ℕ, (fullLaw y) {H | ∀ d : ℕ, ∃ n : ℕ,
      d < ((H n).vertices.filter fun v => (H n).graph.Adj r v).card} = 0 :=
  fun r => degreeUnbounded_null_of_diagonal_local_tendsto rows y hrows hweak r

example (rows : ℕ → SignSequence) (y : SignSequence)
    (hrows : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    (ν : ProbabilityMeasure LocalTree.Tree)
    (hweak : Tendsto (fun n => localProbabilityLaw (rows n) n) atTop (𝓝 ν)) :
    ∀ᵐ H ∂fullLaw y, ∃ T : LocalTree.Tree,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T) :=
  ae_local_limit_of_diagonal_tendsto_via_degrees rows y hrows hweak

example {n : ℕ} {s : State} (hs : ValidAt n s) (r : ℕ) :
    (s.vertices.filter fun v => s.graph.Adj r v).card ≤
      ((localTreeOfState s).val (r + 1)).card :=
  hs.vertexDegree_le_ballCard r

example (μ : ℕ → ProbabilityMeasure LocalTree.Tree) (ν : ProbabilityMeasure LocalTree.Tree)
    (hweak : Tendsto μ atTop (𝓝 ν)) (r : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ d : ℕ, ∀ᶠ n in atTop, (μ n : Measure LocalTree.Tree).real
      {T | d < (T.val r).card} < δ :=
  LocalTree.eventually_natObservable_tail_lt_of_tendsto hweak
    (LocalTree.ballCard r) (LocalTree.continuous_ballCard r) hδ

#print axioms exists_strictMono_matching_prefixes
#print axioms exists_matching_degree_couplings
#print axioms prefixCoupling_vertexDegree_le
#print axioms degreeUnbounded_iff_tendsto
#print axioms degree_tails_positive_of_unbounded_probability
#print axioms LocalTree.continuous_ballCard
#print axioms LocalTree.natObservable_tail_tendsto_zero
#print axioms LocalTree.eventually_natObservable_tail_lt_of_tendsto
#print axioms ValidAt.vertexDegree_le_ballCard
#print axioms diagonal_ballCard_not_tight_of_degree_unbounded
#print axioms degreeUnbounded_null_of_diagonal_local_tendsto
#print axioms ae_local_limit_of_diagonal_tendsto_via_degrees
