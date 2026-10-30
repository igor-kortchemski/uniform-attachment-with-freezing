module

import Freezing1.MainLocalDegreeNecessity

/-! Author-created exact-source checks for the new all-vertex route. -/

open Filter MeasureTheory
open scoped Topology ENNReal Classical
open Freezing1 Freezing1.Forward Freezing1.ForwardInfiniteHistory

example (rows : ℕ → SignSequence) (y : SignSequence)
    (agreement : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n,
      n ≤ φ n ∧ (∀ i, 1 ≤ i → i ≤ n → rows (φ n) i = y i) :=
  exists_strictMono_matching_prefixes rows y agreement

example (x y : SignSequence) (a b r : ℕ)
    (agreement : ∀ i, 1 ≤ i → i ≤ a → x i = y i) (timeOrder : a ≤ b) :
    ∀ᵐ p ∂prefixCoupling x y a,
      ((p.1 a).vertices.filter fun v => (p.1 a).graph.Adj r v).card ≤
        ((p.2 b).vertices.filter fun v => (p.2 b).graph.Adj r v).card :=
  prefixCoupling_vertexDegree_le agreement timeOrder r

example (x : SignSequence) (r : ℕ)
    (positive : (fullLaw x) {H | ∀ d : ℕ, ∃ n : ℕ,
      d < ((H n).vertices.filter fun v => (H n).graph.Adj r v).card} ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ d : ℕ, ∀ᶠ n in atTop,
      δ ≤ (treeLaw x n).real {s | d < (s.vertices.filter fun v => s.graph.Adj r v).card} :=
  degree_tails_positive_of_unbounded_probability x r positive

example (rows : ℕ → SignSequence) (y : SignSequence)
    (agreement : ∀ i, 1 ≤ i → ∀ᶠ n in atTop, rows n i = y i)
    (ν : ProbabilityMeasure LocalTree.Tree)
    (converges : Tendsto (fun n => localProbabilityLaw (rows n) n) atTop (𝓝 ν)) :
    ∀ᵐ H ∂fullLaw y, ∃ T : LocalTree.Tree,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 T) :=
  ae_local_limit_of_diagonal_tendsto_via_degrees rows y agreement converges

#print axioms exists_strictMono_matching_prefixes
#print axioms prefixCoupling_vertexDegree_le
#print axioms exists_matching_degree_couplings
#print axioms degree_tails_positive_of_unbounded_probability
#print axioms LocalTree.eventually_natObservable_tail_lt_of_tendsto
#print axioms diagonal_ballCard_not_tight_of_degree_unbounded
#print axioms degreeUnbounded_null_of_diagonal_local_tendsto
#print axioms ae_local_limit_of_diagonal_tendsto_via_degrees
