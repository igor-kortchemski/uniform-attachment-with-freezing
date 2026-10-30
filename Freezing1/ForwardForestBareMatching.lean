module

public import Freezing1.ForwardForestUniformMatching
public import Freezing1.ForwardForestStarOrbit

/-! The bare source forest retained jointly in the actual matching law. -/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

/-- Root clocks are hidden from the observed forest. They are retained in
the independent augmented driving forest, so this is a full-state joint law,
not a claim of deterministic reconstruction from bare star data alone. -/
theorem treeLaw_uniform_root_matching_bare (x : SignSequence) {a b : ℕ}
    (hab : a ≤ b) (hb : (b : ℕ∞) ≤ extinctionTime x) :
    let m := (activeCount x a).toNat
    (treeLaw x b).map (fun t => (truncateAt t a, bareSlotOrbit m (slotForest t a), t)) =
      (treeLaw x a).bind (fun past => (forestSlotLaw x a (b - a) m).bind
        (fun F => (uniformPermutationLaw (Fin m)).map
          (fun σ => (past, bareSlotOrbit m F,
            reconstructSlotForest x a b past (F.relabel (rootSlotPermutation m σ)))))) := by
  dsimp only
  let m := (activeCount x a).toNat
  let φ : State × RootErasedForest m × State → State × RootErasedForest m × State :=
    fun z => (z.1, starErasedCoarsening m z.2.1, z.2.2)
  have hφ : Measurable φ := measurable_fst.prodMk
    ((measurable_from_top.comp (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have hh := congrArg (fun μ : Measure (State × RootErasedForest m × State) => μ.map φ)
    (treeLaw_uniform_root_matching x hab hb)
  rw [Measure.map_map hφ measurable_from_top,
    Measure.map_bind measurable_from_top.aemeasurable hφ.aemeasurable] at hh
  simp_rw [Measure.map_bind measurable_from_top.aemeasurable hφ.aemeasurable,
    Measure.map_map hφ measurable_from_top] at hh
  simpa only [Function.comp_def, φ, bareSlotOrbit, m] using hh

end Freezing1.Forward
