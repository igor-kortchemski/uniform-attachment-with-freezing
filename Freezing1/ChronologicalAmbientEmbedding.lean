module

public import Freezing1.ChronologicalBallIso

/-!
# The chronological model as a closed subspace of the source ambient

The generic unordered ambient allows arbitrary repeated labels. The image of
the chronological model is nevertheless closed: every finite ball in a limit
is a chronological ball, and their unique record representatives glue to an
actual coherent chronological tree. No restriction on the ambient is assumed.
-/

@[expose] public section

namespace Freezing1.LocalTree

open Filter Set Topology
open scoped Topology Classical

theorem toUnordered_injective : Function.Injective toUnordered := by
  intro T U hTU
  apply Subtype.ext
  funext h
  apply (finiteBall_toUnordered_eq_iff T U h).mp
  exact congrArg (fun q => UnorderedLocal.finiteBall q h) hTU

theorem tendsto_toUnordered_iff {ι : Type*} {L : Filter ι} (S : ι → Tree) (T : Tree) :
    Tendsto (fun i => toUnordered (S i)) L (𝓝 (toUnordered T)) ↔ Tendsto S L (𝓝 T) := by
  rw [UnorderedLocal.tree_tendsto_iff_balls, tendsto_iff_balls]
  exact forall_congr' (fun h => eventually_congr
    (Eventually.of_forall fun i => finiteBall_toUnordered_eq_iff (S i) T h))

theorem continuous_toUnordered : Continuous toUnordered :=
  UnorderedLocal.continuous_ofPlane.comp continuous_toLabelledPlaneTree

theorem isEmbedding_toUnordered : IsEmbedding toUnordered := by
  refine ⟨isInducing_iff_nhds.mpr (fun T => ?_), toUnordered_injective⟩
  apply le_antisymm continuous_toUnordered.continuousAt.le_comap
  exact (tendsto_toUnordered_iff (L := comap toUnordered (𝓝 (toUnordered T))) id T).mp
    tendsto_comap

theorem exists_chronological_of_finite_support (q : UnorderedLocal.Tree)
    (hq : ∀ h, ∃ T : Tree,
      UnorderedLocal.finiteBall (toUnordered T) h = UnorderedLocal.finiteBall q h) :
    ∃ T : Tree, toUnordered T = q := by
  choose A hA using hq
  have hab (h : ℕ) : (A (h + 1)).val h = (A h).val h := by
    apply (finiteBall_toUnordered_eq_iff _ _ h).mp
    calc
      UnorderedLocal.finiteBall (toUnordered (A (h + 1))) h =
          UnorderedLocal.truncate h
            (UnorderedLocal.finiteBall (toUnordered (A (h + 1))) (h + 1)) :=
        (UnorderedLocal.finiteBall_restrict _ (by omega : h ≤ h + 1)).symm
      _ = UnorderedLocal.truncate h (UnorderedLocal.finiteBall q (h + 1)) := by rw [hA]
      _ = UnorderedLocal.finiteBall q h :=
        UnorderedLocal.finiteBall_restrict q (by omega : h ≤ h + 1)
      _ = UnorderedLocal.finiteBall (toUnordered (A h)) h := (hA h).symm
  let T : Tree := ⟨fun h => (A h).val h, fun h =>
    ⟨((A h).property h).1,
      ((A (h + 1)).restrict_ball (by omega : h ≤ h + 1)).trans (hab h)⟩⟩
  refine ⟨T, ?_⟩
  apply UnorderedLocal.localTreeEquiv.injective
  apply Subtype.ext
  funext h
  change UnorderedLocal.finiteBall (toUnordered T) h = UnorderedLocal.finiteBall q h
  exact ((finiteBall_toUnordered_eq_iff T (A h) h).mpr rfl).trans (hA h)

theorem range_toUnordered_eq :
    range toUnordered = ⋂ h : ℕ, (fun q => UnorderedLocal.finiteBall q h) ⁻¹'
      range (fun T : Tree => UnorderedLocal.finiteBall (toUnordered T) h) := by
  ext q
  constructor
  · rintro ⟨T, rfl⟩
    exact mem_iInter.mpr (fun _ => ⟨T, rfl⟩)
  · intro hq
    exact exists_chronological_of_finite_support q (fun h => mem_iInter.mp hq h)

theorem isClosed_range_toUnordered : IsClosed (range toUnordered) := by
  rw [range_toUnordered_eq]
  apply isClosed_iInter
  intro h
  exact (isClosed_discrete (s := range
    (fun T : Tree => UnorderedLocal.finiteBall (toUnordered T) h))).preimage
      (UnorderedLocal.continuous_finiteBall h)

theorem isClosedEmbedding_toUnordered : IsClosedEmbedding toUnordered :=
  ⟨isEmbedding_toUnordered, isClosed_range_toUnordered⟩

theorem exists_localLimit_iff_ambient {ι : Type*} {L : Filter ι} [L.NeBot] (S : ι → Tree) :
    (∃ T : Tree, Tendsto S L (𝓝 T)) ↔
      ∃ q : UnorderedLocal.Tree, Tendsto (fun i => toUnordered (S i)) L (𝓝 q) := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨toUnordered T, (tendsto_toUnordered_iff S T).mpr hT⟩
  · rintro ⟨q, hq⟩
    obtain ⟨T, rfl⟩ := isClosed_range_toUnordered.mem_of_tendsto hq
      (Eventually.of_forall fun i => ⟨S i, rfl⟩)
    exact ⟨T, (tendsto_toUnordered_iff S T).mp hq⟩

end Freezing1.LocalTree
