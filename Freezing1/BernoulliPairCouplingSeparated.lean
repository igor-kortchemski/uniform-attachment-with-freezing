module

public import Freezing1.BernoulliPairCouplingBlock
public import Freezing1.ReverseCoalescenceTime

/-! Source A60 domination on the actual event of distinct bottom components. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal BigOperators

set_option backward.isDefEq.respectTransparency false

theorem stepLaw_depth_root_support {x : SignSequence} {n i : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hi : i < n)
    (hH : Reverse.ValidAt x n (i + 1) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ s ∂stepLaw x n hn u v i H,
      H.current.depth u ≤ s.history.current.depth u ∧
      H.current.depth v ≤ s.history.current.depth v ∧
      (H.current.root u = H.current.root v →
        s.history.current.root u = s.history.current.root v) := by
  apply ae_of_ae_map (f := StepSample.history)
    (p := fun H' : Base => H.current.depth u ≤ H'.current.depth u ∧
      H.current.depth v ≤ H'.current.depth v ∧
      (H.current.root u = H.current.root v → H'.current.root u = H'.current.root v))
    measurable_from_top.aemeasurable
  rw [stepLaw_map_history, ReverseHistory.transitionLaw]
  apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
  filter_upwards [Reverse.transitionLaw_present_depth_support hn hi hH hu,
    Reverse.transitionLaw_present_depth_support hn hi hH hv,
    ReverseHistory.transitionLaw_root_eq_ae x i H.current u v] with F hu' hv' he
  change H.current.depth u ≤ F.depth u ∧ H.current.depth v ≤ F.depth v ∧
    (H.current.root u = H.current.root v → F.root u = F.root v)
  exact ⟨by rcases hu'.2 with h | h <;> omega,
    by rcases hv'.2 with h | h <;> omega, he hu hv⟩

/-- Genuine actual block heights are compared on the same coupled history.
The distinct-root event is retained and is never declared independent. -/
theorem coupledBlockLaw_geometry {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ t ∂coupledBlockLaw x n hn u v a k H,
      H.current.depth u + (∑ j, t.first j) = t.history.current.depth u ∧
      (H.current.root u = H.current.root v →
        t.history.current.root u = t.history.current.root v) ∧
      (t.history.current.root u ≠ t.history.current.root v →
        t.history.current.depth v ≤ H.current.depth v + ∑ j, t.second j) := by
  induction k generalizing H with
  | zero =>
    rw [coupledBlockLaw]
    apply (ae_dirac_iff (by trivial)).mpr
    refine ⟨by simp, fun h => h, fun _ => ?_⟩
    simp
  | succ k ih =>
    have hi : a + k < n := by omega
    have hH' : Reverse.ValidAt x n (a + k + 1) H.current := by
      simpa only [Nat.add_assoc] using hH
    rw [coupledBlockLaw]
    apply ae_bind_of_ae measurable_from_top.aemeasurable (by trivial)
    filter_upwards [stepLaw_support hn hi hH' hu hv,
      stepLaw_depth_root_support hn hi hH' hu hv, stepLaw_relation hn hi hH' hu hv,
      stepLaw_previous x n hn u v (a + k) H] with s hs hd hrel hprev
    apply (ae_map_iff measurable_from_top.aemeasurable (by trivial)).mpr
    filter_upwards [ih (H := s.history) (by omega) hs.1 hs.2.1 hs.2.2] with t ht
    have hdu : H.current.depth u + ReverseHistory.heightIncrement u s.history =
        s.history.current.depth u := by
      change H.current.depth u + (s.history.current.depth u -
        (ReverseHistory.previous s.history).current.depth u) = _
      rw [hprev]
      omega
    have hdv : H.current.depth v + ReverseHistory.heightIncrement v s.history =
        s.history.current.depth v := by
      change H.current.depth v + (s.history.current.depth v -
        (ReverseHistory.previous s.history).current.depth v) = _
      rw [hprev]
      omega
    simp only [prependSample, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    refine ⟨by omega, fun he => ht.2.1 (hd.2.2 he), ?_⟩
    intro hsep
    have hmid : s.history.current.root u ≠ s.history.current.root v :=
      fun he => hsep (ht.2.1 he)
    have hbefore : H.current.root u ≠ H.current.root v := fun he => hmid (hd.2.2 he)
    have hz : ReverseHistory.heightIncrement v s.history ≤ s.auxiliary := by
      rw [hrel, ite_eq_right hbefore]
      exact (Nat.mul_le_mul_left s.auxiliary (Nat.sub_le 1 _)).trans_eq (Nat.mul_one _)
    have htail := ht.2.2 hsep
    omega

end Freezing1.BernoulliPairCoupling
