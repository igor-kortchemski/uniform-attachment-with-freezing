module

public import Freezing1.BernoulliPairCouplingBlock
public import Freezing1.BernoulliPairCouplingThinning

/-! One probability space carries the actual full history and all source auxiliary coins. -/

@[expose] public section

namespace Freezing1.BernoulliPairCoupling

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

noncomputable def completeLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    Measure (BlockSample k × Word k) :=
  (coupledBlockLaw x n hn u v a k H).prod
    (wordLaw (fun i => unitInterval.symm (Reverse.stepParameter x n hn i)) a k)

instance completeLaw_probability (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    IsProbabilityMeasure (completeLaw x n hn u v a k H) := by unfold completeLaw; infer_instance

theorem completeLaw_fst_hasLaw (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    HasLaw Prod.fst (coupledBlockLaw x n hn u v a k H) (completeLaw x n hn u v a k H) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  rw [completeLaw, Measure.map_fst_prod, measure_univ, one_smul]

theorem completeLaw_map_history (x : SignSequence) (n : ℕ)
    (hn : (n : ℕ∞) ≤ extinctionTime x) (u v : ℕ ⊕ ℕ) (a k : ℕ) (H : Base) :
    (completeLaw x n hn u v a k H).map (fun z => z.1.history) =
      ReverseHistory.blockHistoryLaw x a k H := by
  have h := completeLaw_fst_hasLaw x n hn u v a k H
  have hh : HasLaw BlockSample.history (ReverseHistory.blockHistoryLaw x a k H)
      (coupledBlockLaw x n hn u v a k H) :=
    ⟨measurable_from_top.aemeasurable, coupledBlockLaw_map_history x n hn u v a k H⟩
  exact (hh.fun_comp h).map_eq

/-- All enlarged coins and fresh retention coins are jointly independent of
the actual first-increment word. This is an equality of constructed measures. -/
theorem completeLaw_map_drivers {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (completeLaw x n hn u v a k H).map (fun z => (z.1.first, (z.1.second, z.2))) =
      (wordLaw (Reverse.stepParameter x n hn) a k).prod
        (thinningLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k) := by
  have hpair : (completeLaw x n hn u v a k H).map
      (fun z => ((z.1.first, z.1.second), z.2)) =
      (pairWordLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k).prod
        (wordLaw (fun i => unitInterval.symm (Reverse.stepParameter x n hn i)) a k) := by
    change ((coupledBlockLaw x n hn u v a k H).prod _).map
      (Prod.map (fun t => (t.first, t.second)) id) = _
    rw [← Measure.map_prod_map _ _ measurable_from_top measurable_id,
      Measure.map_id, coupledBlockLaw_map_drivers hn hk hH hu hv]
  have hassoc := congrArg
    (fun μ : Measure ((Word k × Word k) × Word k) => μ.map MeasurableEquiv.prodAssoc) hpair
  have hm : Measurable (fun z : BlockSample k × Word k => ((z.1.first, z.1.second), z.2)) :=
    ((show Measurable (fun s : BlockSample k => (s.first, s.second)) from
      measurable_from_top).comp measurable_fst).prodMk measurable_snd
  rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hm,
    pairWordLaw, Measure.prodAssoc_prod] at hassoc
  exact hassoc

/-- The thinned word is another independent original-parameter Bernoulli
word on this very same space carrying the actual history. -/
theorem completeLaw_map_first_thinned {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    (completeLaw x n hn u v a k H).map
        (fun z => (z.1.first, thinningWord (z.1.second, z.2))) =
      (wordLaw (Reverse.stepParameter x n hn) a k).prod
        (wordLaw (Reverse.stepParameter x n hn) a k) := by
  have h := congrArg (fun μ : Measure (Word k × (Word k × Word k)) =>
      μ.map (Prod.map id thinningWord)) (completeLaw_map_drivers hn hk hH hu hv)
  have hm : Measurable (fun z : BlockSample k × Word k => (z.1.first, (z.1.second, z.2))) :=
    ((show Measurable (fun s : BlockSample k => s.first) from
      measurable_from_top).comp measurable_fst).prodMk
        (((show Measurable (fun s : BlockSample k => s.second) from
          measurable_from_top).comp measurable_fst).prodMk measurable_snd)
  rw [Measure.map_map (measurable_of_countable _) hm,
    ← Measure.map_prod_map _ _ measurable_id (measurable_of_countable _), Measure.map_id,
    thinningLaw_map _ _ _ _ (fun i _ hi => step_parameters_relation x n hn (hi.trans_le hk))] at h
  exact h

theorem completeLaw_thinning_le {x : SignSequence} {n a k : ℕ} {H : Base}
    (hn : (n : ℕ∞) ≤ extinctionTime x) (hk : a + k ≤ n)
    (hH : Reverse.ValidAt x n (a + k) H.current) {u v : ℕ ⊕ ℕ}
    (hu : u ∈ H.current.vertices) (hv : v ∈ H.current.vertices) :
    ∀ᵐ z ∂completeLaw x n hn u v a k H, ∀ j,
      thinningWord (z.1.second, z.2) j ≤ z.1.second j := by
  have hd : HasLaw (fun z : BlockSample k × Word k => (z.1.first, (z.1.second, z.2)))
      ((wordLaw (Reverse.stepParameter x n hn) a k).prod
        (thinningLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k))
      (completeLaw x n hn u v a k H) :=
    ⟨((measurable_from_top.comp measurable_fst).prodMk
      ((measurable_from_top.comp measurable_fst).prodMk measurable_snd)).aemeasurable,
      completeLaw_map_drivers hn hk hH hu hv⟩
  have hs : HasLaw Prod.snd
      (thinningLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k)
      ((wordLaw (Reverse.stepParameter x n hn) a k).prod
        (thinningLaw (Reverse.stepParameter x n hn) (auxiliaryParameter x n hn) a k)) := by
    refine ⟨measurable_snd.aemeasurable, ?_⟩
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  apply ae_of_ae_map (f := fun z : BlockSample k × Word k => (z.1.second, z.2))
    (p := fun w : Word k × Word k => ∀ j, thinningWord w j ≤ w.1 j)
    (hs.fun_comp hd).aemeasurable
  rw [(hs.fun_comp hd).map_eq]
  exact thinningLaw_le _ _ _ _

end Freezing1.BernoulliPairCoupling
