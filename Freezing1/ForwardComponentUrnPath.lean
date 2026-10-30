module

public import Freezing1.ForwardContinuationPrefix
public import Freezing1.SignedUrnPositiveExtensionPath
public import Freezing1.SignedUrnPositiveExtension

/-!
# Complete actual component records have the signed-urn path law

The terminal forward state retains all timestamps, so its canonical
truncations recover every earlier state. The proof projects the genuine
tree transition kernels onto the component count at every step. It does
not infer a joint law from a family of endpoint identities.
-/

@[expose] public section

namespace Freezing1

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Forward

noncomputable def componentPrefixRecord (cut r start k : ℕ) (q : State) : SignedUrn.Trajectory :=
  SignedUrn.record (fun i q => componentPopulation (truncateAt q i) cut r) start k q

theorem continuationLaw_componentPrefixRecord {x : SignSequence} {a k cut : ℕ} {s : State}
    (hs : HasHistory x a s) (hcut : cut ≤ a)
    (hτ : ((a + k : ℕ) : ℕ∞) ≤ extinctionTime x) (r : ℕ) :
    (continuationLaw x a k s).map (componentPrefixRecord cut r a k) =
      SignedUrn.pathLaw (activeCount x) a k (componentPopulation s cut r) := by
  induction k generalizing a s with
  | zero =>
    have haτ : (a : ℕ∞) ≤ extinctionTime x := by simpa only [Nat.add_zero] using hτ
    have he := (hs.historyShape haτ).prefix_self
    rw [continuationLaw, Measure.map_dirac' measurable_from_top]
    simp only [componentPrefixRecord, SignedUrn.record, he, SignedUrn.pathLaw]
  | succ k ih =>
    have haτ : (a : ℕ∞) < extinctionTime x :=
      lt_of_lt_of_le (by exact_mod_cast (show a < a + (k + 1) by omega)) hτ
    have hpos := ((lt_extinctionTime_iff x a).mp haτ) a le_rfl
    have hne : s.active.Nonempty := by
      have hc := hs.current.count
      exact Finset.card_pos.mp (by omega)
    have hrest : (((a + 1) + k : ℕ) : ℕ∞) ≤ extinctionTime x := by
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hτ
    have hnext : ∀ᵐ t ∂transitionLaw s (a + 1) (x (a + 1)), HasHistory x (a + 1) t := by
      apply transitionLaw_ae s _ _ _
      · intro he
        exact (hne.ne_empty he).elim
      · intro v hv
        exact hs.extend (hs.current.step hv) ⟨v, hv, rfl⟩
    have hhead : ∀ᵐ q ∂continuationLaw x a (k + 1) s,
        componentPrefixRecord cut r a (k + 1) q =
          SignedUrn.prepend (componentPopulation s cut r) (componentPrefixRecord cut r (a + 1) k q) := by
      filter_upwards [continuationLaw_truncate_self hs hτ] with q hq
      change SignedUrn.prepend (componentPopulation (truncateAt q a) cut r)
        (componentPrefixRecord cut r (a + 1) k q) = _
      rw [hq]
    calc
      _ = (continuationLaw x a (k + 1) s).map
          ((SignedUrn.prepend (componentPopulation s cut r)) ∘ componentPrefixRecord cut r (a + 1) k) :=
        Measure.map_congr hhead
      _ = (transitionLaw s (a + 1) (x (a + 1))).bind
          (fun t => (continuationLaw x (a + 1) k t).map
            ((SignedUrn.prepend (componentPopulation s cut r)) ∘ componentPrefixRecord cut r (a + 1) k)) := by
        rw [continuationLaw, Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
      _ = (transitionLaw s (a + 1) (x (a + 1))).bind
          (fun t => (SignedUrn.pathLaw (activeCount x) (a + 1) k (componentPopulation t cut r)).map
            (SignedUrn.prepend (componentPopulation s cut r))) := by
        apply Measure.bind_congr_right
        filter_upwards [hnext] with t ht
        rw [← Measure.map_map measurable_from_top measurable_from_top,
          ih ht (hcut.trans (Nat.le_succ a)) hrest]
      _ = ((transitionLaw s (a + 1) (x (a + 1))).map (fun t => componentPopulation t cut r)).bind
          (fun u => (SignedUrn.pathLaw (activeCount x) (a + 1) k u).map
            (SignedUrn.prepend (componentPopulation s cut r))) := by
        rw [Measure.bind_map measurable_from_top.aemeasurable (measurable_of_countable _).aemeasurable]
      _ = _ := by
        rw [transitionLaw_componentPopulation hs.current.valid hcut r _ hne, hs.current.count,
          SignedUrn.pathLaw, activeCount_succ]
        congr 2
        omega

end Forward

namespace SignedUrn

theorem pathLaw_shift (Z : ℕ → ℤ) (offset a k : ℕ) (u : ℤ) :
    pathLaw (fun i => Z (offset + i)) a k u = pathLaw Z (offset + a) k u := by
  induction k generalizing a u with
  | zero => rfl
  | succ k ih =>
    simp only [pathLaw, Nat.add_assoc]
    congr 1
    funext v
    rw [ih]

theorem pathLaw_congr_population {Z W : ℕ → ℤ} (a k : ℕ) (u : ℤ)
    (h : ∀ i ∈ Finset.Icc a (a + k), Z i = W i) :
    pathLaw Z a k u = pathLaw W a k u := by
  induction k generalizing a u with
  | zero => rfl
  | succ k ih =>
    rw [pathLaw, pathLaw, h a (by simp), h (a + 1) (by simp)]
    congr 1
    funext v
    rw [ih (a + 1) v]
    intro i hi
    exact h i (by simp only [Finset.mem_Icc] at hi ⊢; omega)

end SignedUrn

namespace Forward

/-- Complete joint source record, including the initial one-ball count,
for the original finite tree continuation and its positive urn extension. -/
theorem positiveExtension_componentPrefixRecord {x : SignSequence} {a b : ℕ} {s : State}
    (hs : HasHistory x a s) (hab : a ≤ b) (hb : PositiveThrough x b)
    {r : ℕ} (hr : r ∈ s.active) :
    (continuationLaw x a (b - a) s).map (componentPrefixRecord a r a (b - a)) =
      SignedUrn.pathLaw (SignedUrn.positiveExtensionPopulation x a b) 0 (b - a) 1 := by
  have hτ : ((a + (b - a) : ℕ) : ℕ∞) ≤ extinctionTime x := by
    simpa only [Nat.add_sub_of_le hab] using ((lt_extinctionTime_iff x b).mpr hb).le
  rw [continuationLaw_componentPrefixRecord hs le_rfl hτ,
    componentPopulation_at_cut hs.current.valid hr]
  change SignedUrn.pathLaw (activeCount x) a (b - a) 1 =
    SignedUrn.pathLaw (fun i => activeCount (positiveExtension x b) (a + i)) 0 (b - a) 1
  rw [SignedUrn.pathLaw_shift, Nat.add_zero]
  apply SignedUrn.pathLaw_congr_population
  intro i hi
  exact (activeCount_positiveExtension_prefix x b (by have := (Finset.mem_Icc.mp hi).2; omega)).symm

end Forward
end Freezing1
