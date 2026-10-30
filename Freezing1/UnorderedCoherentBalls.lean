module

public import Freezing1.UnorderedFiniteTruncation
public import Mathlib.Topology.Compactness.Compact

/-!
# Coherent finite unordered balls and compatible actual representatives

The closed tower is an intermediate carrier. Compactness of the finite
representative fibers constructs genuinely compatible ordered finite
trees. Identifying the tower with infinite labelled trees is a later step;
Polishness of the tower alone is not advertised as the source's theorem.
-/

@[expose] public section

namespace Freezing1.UnorderedLocal

open BinaryBijection Filter Set
open scoped Topology Classical

def Coherent (B : ℕ → FiniteTree) : Prop :=
  ∀ h, truncate h (B (h + 1)) = B h

theorem isClosed_coherent : IsClosed {B : ℕ → FiniteTree | Coherent B} := by
  have hset : {B : ℕ → FiniteTree | Coherent B} =
      ⋂ h, {B : ℕ → FiniteTree | truncate h (B (h + 1)) = B h} := by
    ext B
    simp only [Coherent, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [hset]
  apply isClosed_iInter
  intro h
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (truncate h)).comp (continuous_apply (h + 1)))
    (continuous_apply h)

abbrev BallTower := {B : ℕ → FiniteTree // Coherent B}

instance : PolishSpace BallTower := isClosed_coherent.polishSpace

theorem BallTower.truncate_self (B : BallTower) (h : ℕ) : truncate h (B.val h) = B.val h := by
  calc
    truncate h (B.val h) = truncate h (truncate h (B.val (h + 1))) :=
      congrArg (truncate h) (B.property h).symm
    _ = truncate h (B.val (h + 1)) := truncate_truncate h h le_rfl _
    _ = B.val h := B.property h

theorem BallTower.truncate_ball (B : BallTower) {h H : ℕ} (hh : h ≤ H) :
    truncate h (B.val H) = B.val h := by
  induction H, hh using Nat.le_induction with
  | base => exact B.truncate_self h
  | succ H hH ih => rw [← truncate_truncate h H hH (B.val (H + 1)), B.property H, ih]

theorem tendsto_iff_balls {ι : Type*} {l : Filter ι} (S : ι → BallTower) (T : BallTower) :
    Tendsto S l (𝓝 T) ↔ ∀ h, ∀ᶠ i in l, (S i).val h = T.val h := by
  rw [tendsto_subtype_rng, tendsto_pi_nhds]
  simp only [nhds_discrete, tendsto_pure]

instance : TopologicalSpace Rooted := ⊥
instance : DiscreteTopology Rooted := ⟨rfl⟩

theorem exists_coherent_representatives (B : BallTower) :
    ∃ r : ℕ → Rooted, (∀ h, ofRooted (r h) = B.val h) ∧
      ∀ h, (r (h + 1)).truncate h = r h := by
  let Space := ∀ h, Representative (B.val h)
  let C : ℕ → Set Space := fun h => {r | (r (h + 1)).val.truncate h = (r h).val}
  have hclosed (h : ℕ) : IsClosed (C h) := by
    exact isClosed_eq
      ((continuous_of_discreteTopology : Continuous (Rooted.truncate h)).comp
        (continuous_subtype_val.comp (continuous_apply (h + 1))))
      (continuous_subtype_val.comp (continuous_apply h))
  have hfinite (F : Finset ℕ) : (⋂ h ∈ F, C h).Nonempty := by
    let N := F.sup (fun h => h + 1)
    have hrep (h : ℕ) (hh : h ≤ N) :
        ofRooted ((B.val N).out.truncate h) = B.val h := by
      calc
        ofRooted ((B.val N).out.truncate h) = truncate h (ofRooted (B.val N).out) := rfl
        _ = truncate h (B.val N) := congrArg (truncate h) (Quotient.out_eq _)
        _ = B.val h := B.truncate_ball hh
    let candidate : Space := fun h => if hh : h ≤ N then
      ⟨(B.val N).out.truncate h, hrep h hh⟩ else Classical.choice (representative_nonempty (B.val h))
    refine ⟨candidate, Set.mem_iInter.mpr (fun h => Set.mem_iInter.mpr (fun hf => ?_))⟩
    have hsucc : h + 1 ≤ N := Finset.le_sup (f := fun h => h + 1) hf
    have hle : h ≤ N := by omega
    change (candidate (h + 1)).val.truncate h = (candidate h).val
    simp only [candidate, dite_eq_left hsucc, dite_eq_left hle]
    exact Rooted.truncate_truncate h (h + 1) (by omega) _
  have : CompactSpace Space := inferInstance
  obtain ⟨r, hr⟩ := CompactSpace.iInter_nonempty hclosed hfinite
  refine ⟨fun h => (r h).val, fun h => (r h).property, ?_⟩
  intro h
  exact Set.mem_iInter.mp hr h

theorem raw_truncate_self (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) (h : ℕ) : (r h).truncate h = r h := by
  calc
    (r h).truncate h = ((r (h + 1)).truncate h).truncate h :=
      congrArg (Rooted.truncate h) (hr h).symm
    _ = (r (h + 1)).truncate h := Rooted.truncate_truncate h h le_rfl _
    _ = r h := hr h

theorem raw_truncate_ball (r : ℕ → Rooted)
    (hr : ∀ h, (r (h + 1)).truncate h = r h) {h H : ℕ} (hh : h ≤ H) :
    (r H).truncate h = r h := by
  induction H, hh using Nat.le_induction with
  | base => exact raw_truncate_self r hr h
  | succ H hH ih => rw [← Rooted.truncate_truncate h H hH (r (H + 1)), hr H, ih]

end Freezing1.UnorderedLocal
