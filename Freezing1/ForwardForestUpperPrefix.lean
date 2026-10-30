module

public import Freezing1.ForwardForestSlots
public import Freezing1.ForwardForestStarOrbit

/-! The complete forest between two cuts observed inside any later actual terminal tree. -/

@[expose] public section

namespace Freezing1.Forward

open Filter MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

set_option backward.isDefEq.respectTransparency false

theorem treeLaw_prefix_slotForest_at_upper (x : SignSequence) {n a b : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    (treeLaw x n).map (fun q => (truncateAt q a, slotForest (truncateAt q b) a)) =
      (treeLaw x a).prod (forestSlotLaw x a (b - a) (activeCount x a).toNat) := by
  have hb : (b : ℕ∞) ≤ extinctionTime x :=
    (by exact_mod_cast hbn : (b : ℕ∞) ≤ n).trans hn
  calc
    _ = ((treeLaw x n).map (fun q => truncateAt q b)).map
        (fun q => (truncateAt q a, slotForest q a)) := by
      rw [Measure.map_map measurable_from_top measurable_from_top]
      apply Measure.map_congr
      filter_upwards [treeLaw_historyShape x n hn] with q hq
      dsimp only [Function.comp_def]
      rw [hq.truncate_truncate hn hab hbn]
    _ = _ := by rw [treeLaw_map_truncate x hn hbn, treeLaw_prefix_slotForest x hab hb]

theorem indepFun_prefix_slotForest_at_upper (x : SignSequence) {n a b : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun q => truncateAt q a) (fun q => slotForest (truncateAt q b) a) (treeLaw x n) := by
  have hj := treeLaw_prefix_slotForest_at_upper x hab hbn hn
  have hf := congrArg (fun μ : Measure (State × State) => μ.map Prod.fst) hj
  have hg := congrArg (fun μ : Measure (State × State) => μ.map Prod.snd) hj
  rw [Measure.map_map measurable_fst measurable_from_top, Measure.map_fst_prod,
    measure_univ, one_smul] at hf
  rw [Measure.map_map measurable_snd measurable_from_top, Measure.map_snd_prod,
    measure_univ, one_smul] at hg
  change (treeLaw x n).map (fun q => truncateAt q a) = treeLaw x a at hf
  change (treeLaw x n).map (fun q => slotForest (truncateAt q b) a) =
    forestSlotLaw x a (b - a) (activeCount x a).toNat at hg
  apply (indepFun_iff_map_prod_eq_prod_map_map measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable).mpr
  rw [hj, hf, hg]

/-- The literal complete bare forest F_{a,b} is independent of T_a also
when all data are observed in the source's later terminal T_n. -/
theorem indepFun_prefix_bareForest_at_upper (x : SignSequence) {n a b : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) (hn : (n : ℕ∞) ≤ extinctionTime x) :
    IndepFun (fun q => truncateAt q a)
      (fun q => bareSlotOrbit (activeCount x a).toNat (slotForest (truncateAt q b) a)) (treeLaw x n) := by
  have hh := (indepFun_prefix_slotForest_at_upper x hab hbn hn).comp (φ := fun q : State => q)
    (ψ := bareSlotOrbit (activeCount x a).toNat) measurable_id measurable_from_top
  simpa only [Function.comp_def] using hh

end Freezing1.Forward
