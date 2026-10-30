module

public import Freezing1.SIRIidCountProjection
public import Freezing1.SIRBiasedWalkExtinction
public import Freezing1.PlaneChainLimit
public import Freezing1.PlaneFrozenLimit
public import Freezing1.PlaneTreeCylinders
public import Freezing1.MainGeometricLimit

/-!
# Finite plane limits and genuine extinction

Finiteness refers to the entire Ulam--Harris vertex set. Under the actual
plane-chain law it is equivalent to hitting an empty active set. The
probability is obtained from the already projected absorbed count walk.
-/

@[expose] public section

namespace Freezing1.PlaneTree

open MeasureTheory Filter
open scoped Classical

def FiniteVertices (T : Tree) : Prop := {u : Address | Present T u}.Finite

theorem finiteVertices_iff_heightBound (T : Tree) :
    FiniteVertices T ↔ ∃ D : ℕ, ∀ u, Present T u → u.length ≤ D := by
  constructor
  · intro hfin
    refine ⟨hfin.toFinset.sup List.length, ?_⟩
    intro u hu
    exact Finset.le_sup (hfin.mem_toFinset.mpr hu)
  · rintro ⟨D, hD⟩
    apply (ball T D).finite_toSet.subset
    intro u hu
    exact (mem_ball T D u).mpr ⟨hu, hD u hu⟩

@[fun_prop] theorem measurable_present (u : Address) : Measurable (fun T : Tree => Present T u) := by
  apply measurableSet_setOfPred.mp
  have he : {T : Tree | Present T u} =
      (fun T : Tree => ball T u.length) ⁻¹' {B : Ball | u ∈ B} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_ball, le_refl, and_true]
  rw [he]
  exact (Set.to_countable _).measurableSet.preimage (measurable_ball u.length)

theorem measurableSet_finiteVertices : MeasurableSet {T : Tree | FiniteVertices T} := by
  simp only [finiteVertices_iff_heightBound]
  apply measurableSet_setOfPred.mpr
  apply Measurable.exists
  intro D
  apply Measurable.forall
  intro u
  exact (measurable_present u).imp measurable_const

end Freezing1.PlaneTree

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory Filter PlaneTree
open scoped ENNReal NNReal Classical

set_option backward.isDefEq.respectTransparency false

theorem finiteVertices_shape {s : State} (hs : Valid s) : FiniteVertices (shape s) := by
  have he : {u : Address | Present (shape s) u} = (s.vertices : Set Address) := by
    ext u
    exact (hs.mem_vertices_iff_present u).symm
  rw [FiniteVertices, he]
  exact s.vertices.finite_toSet

theorem Valid.lengths_le_of_ball_eq {s : State} (hs : Valid s) {T : Tree} {D : ℕ}
    (hD : ∀ u, Present T u → u.length ≤ D)
    (hball : ball (shape s) (D + 1) = ball T (D + 1)) :
    ∀ u ∈ s.vertices, u.length ≤ D := by
  intro u hu
  by_contra hn
  let v := u.take (D + 1)
  have hvlen : v.length = D + 1 := by
    simp only [v, List.length_take, Nat.min_eq_left (by omega : D + 1 ≤ u.length)]
  have hv : Present (shape s) v :=
    present_of_prefix (u.take_prefix (D + 1)) ((hs.mem_vertices_iff_present u).mp hu)
  have hvmem : v ∈ ball (shape s) (D + 1) := (mem_ball _ _ _).mpr ⟨hv, hvlen.le⟩
  rw [hball] at hvmem
  have hlen := hD v ((mem_ball _ _ _).mp hvmem).1
  omega

theorem fullLaw_held_after_empty (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p initial,
      ∀ k, (H k).active = ∅ → H (k + 1) = H k := by
  apply CountableMarkovChain.fullLaw_steps (transition p) initial
    (fun s t => s.active = ∅ → t = s)
  intro s
  apply transition_ae
  · intro _ _
    rfl
  · intro sign u hu hempty
    simp [hempty] at hu

theorem held_after_empty_persists {H : ℕ → State}
    (hheld : ∀ k, (H k).active = ∅ → H (k + 1) = H k) {a : ℕ}
    (ha : (H a).active = ∅) : ∀ k ≥ a, H k = H a := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [hheld k (by rw [ih]; exact ha), ih]

/-- A finite limiting tree is extinct, even when the raw state space also
contains malformed or artificially held histories. Those histories have
already been excluded by the genuine path law. -/
theorem fullLaw_finite_chainLimit_iff_absorbed (p : unitInterval) (hp : (p : ℝ) < 1) :
    ∀ᵐ H ∂fullLaw p initial,
      FiniteVertices (chainLimit H) ↔ ∃ k, (H k).active.card = 0 := by
  have hfrozen : ∀ᵐ H ∂fullLaw p initial,
      ∀ D, ∃ a, ∀ k ≥ a, FrozenBall (H k) D :=
    ae_all_iff.mpr (fun D => fullLaw_eventually_frozenBall p hp D)
  filter_upwards [SIR.planeFullLaw_valid p, fullLaw_tendsto_chainLimit p hp,
    hfrozen, fullLaw_held_after_empty p] with H hvalid hlim hfrozen hheld
  constructor
  · intro hfin
    obtain ⟨D, hD⟩ := (finiteVertices_iff_heightBound _).mp hfin
    obtain ⟨a, ha⟩ := hfrozen D
    obtain ⟨b, hb⟩ := eventually_atTop.mp ((tendsto_iff_balls _ _).mp hlim (D + 1))
    refine ⟨max a b, Finset.card_eq_zero.mpr ?_⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hlen := (hvalid (max a b)).lengths_le_of_ball_eq hD
      (hb (max a b) (le_max_right _ _)) u ((hvalid _).active_subset hu)
    exact ha (max a b) (le_max_left _ _) u ((hvalid _).active_subset hu) hlen hu
  · rintro ⟨a, ha⟩
    have haempty : (H a).active = ∅ := Finset.card_eq_zero.mp ha
    have hevent : ∀ᶠ k in atTop, shape (H k) = shape (H a) := by
      filter_upwards [eventually_ge_atTop a] with k hk
      rw [held_after_empty_persists hheld haempty k hk]
    have hconst : Tendsto (fun k => shape (H k)) atTop (nhds (shape (H a))) :=
      tendsto_const_nhds.congr' (hevent.mono fun _ hk => hk.symm)
    rw [tendsto_nhds_unique hlim hconst]
    exact finiteVertices_shape (hvalid a)

theorem measurableSet_ever_absorbed :
    MeasurableSet {H : ℕ → State | ∃ k, (H k).active.card = 0} := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.exists
  intro k
  exact ((measurable_of_countable (fun s : State => s.active.card = 0)).comp
    (measurable_pi_apply k))

theorem fullLaw_zero_probability_eq_walk (p : unitInterval) (k : ℕ) :
    fullLaw p initial {H | (H k).active.card = 0} =
      SIR.BiasedWalk.fullLaw p {H | H k = 0} := by
  rw [← SIR.map_planeFullLaw_activeCard,
    Measure.map_apply (by fun_prop) (by measurability)]
  rfl

theorem fullLaw_ever_absorbed_probability (p : unitInterval) (hp : (1 : ℝ) / 2 < p) :
    fullLaw p initial {H | ∃ k, (H k).active.card = 0} =
      ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  have hm : ∀ k, MeasurableSet {H : ℕ → State | (H k).active.card = 0} := by
    intro k
    exact (measurableSet_singleton 0).preimage
      ((measurable_of_countable (fun s : State => s.active.card)).comp (measurable_pi_apply k))
  have hlimit := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (μ := fullLaw p initial) (A := {H | ∃ k, (H k).active.card = 0})
    measurableSet_ever_absorbed hm (by
      filter_upwards [fullLaw_held_after_empty p] with H hheld
      by_cases hever : ∃ a, (H a).active.card = 0
      · obtain ⟨a, ha⟩ := hever
        filter_upwards [eventually_ge_atTop a] with k hk
        have hz : (H k).active.card = 0 := by
          rw [held_after_empty_persists hheld (Finset.card_eq_zero.mp ha) k hk]
          exact ha
        simp only [hz, true_iff]
        exact ⟨a, ha⟩
      · exact Eventually.of_forall fun k => by
          have hz : (H k).active.card ≠ 0 := fun hk => hever ⟨k, hk⟩
          simp only [hever, hz, iff_self])
  have hwalk : Tendsto (fun k => fullLaw p initial {H | (H k).active.card = 0}) atTop
      (nhds (ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)))) := by
    simpa only [fullLaw_zero_probability_eq_walk] using SIR.BiasedWalk.zero_probability_tendsto p hp
  exact tendsto_nhds_unique hlimit hwalk

theorem planeLimitLaw_finite_probability (p : unitInterval)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1) :
    (ForwardAnnealed.planeLimitLaw p : Measure Tree) {T | FiniteVertices T} =
      ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  rw [← map_fullLaw_chainLimit p hp1,
    Measure.map_apply_of_aemeasurable (aemeasurable_chainLimit p hp1) measurableSet_finiteVertices]
  calc
    _ = fullLaw p initial {H | ∃ k, (H k).active.card = 0} := by
      apply measure_congr
      filter_upwards [fullLaw_finite_chainLimit_iff_absorbed p hp1] with H hH
      exact propext hH
    _ = _ := fullLaw_ever_absorbed_probability p hp0

theorem geometricBienayme_finite_probability (p : unitInterval)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1) :
    PlaneTree.geometricBienaymeLaw p {T | FiniteVertices T} =
      ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  rw [← ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw p hp1]
  exact planeLimitLaw_finite_probability p hp0 hp1

theorem geometricBienayme_survival_probability (p : unitInterval)
    (hp0 : (1 : ℝ) / 2 < p) (hp1 : (p : ℝ) < 1) :
    PlaneTree.geometricBienaymeLaw p {T | ¬FiniteVertices T} =
      1 - ENNReal.ofReal ((1 - (p : ℝ)) / (p : ℝ)) := by
  rw [← ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw p hp1]
  change (ForwardAnnealed.planeLimitLaw p : Measure Tree) {T | FiniteVertices T}ᶜ = _
  rw [measure_compl measurableSet_finiteVertices (by finiteness), measure_univ,
    planeLimitLaw_finite_probability p hp0 hp1]

end Freezing1.PlaneForward

namespace Freezing1.SIR

open MeasureTheory
open scoped ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

/-- The extinction probability of the concrete geometric Bienaymé tree
at the source SIR parameter is exactly `1/lam`. -/
theorem geometric_sir_finite_probability (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)
        {T | PlaneTree.FiniteVertices T} = ENNReal.ofReal (1 / (lam : ℝ)) := by
  have hp : (1 : ℝ) / 2 < (infectionProbability lam 1 : ℝ) := by
    rw [infectionProbability_coe]
    simp only [Nat.cast_one, mul_one]
    apply (lt_div_iff₀ (by positivity : 0 < 1 + (lam : ℝ))).mpr
    linarith
  have he : (1 - (infectionProbability lam 1 : ℝ)) / (infectionProbability lam 1 : ℝ) =
      1 / (lam : ℝ) := by
    rw [infectionProbability_complement, infectionProbability_coe]
    simp only [Nat.cast_one, mul_one]
    field_simp
  rw [PlaneForward.geometricBienayme_finite_probability _ hp
    (infectionProbability_lt_one lam 1), he]

theorem geometric_sir_survival_probability (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)
        {T | ¬PlaneTree.FiniteVertices T} = 1 - ENNReal.ofReal (1 / (lam : ℝ)) := by
  have hp1 := infectionProbability_lt_one lam 1
  rw [← ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw _ hp1]
  change (ForwardAnnealed.planeLimitLaw (infectionProbability lam 1) : Measure PlaneTree.Tree)
    {T | PlaneTree.FiniteVertices T}ᶜ = _
  rw [measure_compl PlaneTree.measurableSet_finiteVertices (by finiteness), measure_univ,
    ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw _ hp1,
    geometric_sir_finite_probability lam hlam]

theorem geometric_sir_survival_real (lam : ℝ≥0) (hlam : 1 < (lam : ℝ)) :
    (PlaneTree.geometricBienaymeLaw (infectionProbability lam 1)).real
        {T | ¬PlaneTree.FiniteVertices T} = 1 - 1 / (lam : ℝ) := by
  have hle : ENNReal.ofReal (1 / (lam : ℝ)) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr ((div_le_one (by linarith : 0 < (lam : ℝ))).mpr hlam.le)
  rw [Measure.real, geometric_sir_survival_probability lam hlam,
    ENNReal.toReal_sub_of_le hle (by simp), ENNReal.toReal_one,
    ENNReal.toReal_ofReal (by positivity)]

end Freezing1.SIR
