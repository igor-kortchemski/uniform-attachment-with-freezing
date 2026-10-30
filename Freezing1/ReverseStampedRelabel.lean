module

public import Freezing1.RootedForestRelabel
public import Freezing1.ReverseStampedHistoryExistence
public import Mathlib.Data.Fintype.Perm

/-!
# Renaming active reverse labels

The finite set of permutations supported on the terminal active labels has
exactly `S_n!` elements. Each acts on actual stamped forests, fixing every
frozen label and transporting parent pointers and edge timestamps. Legal
reverse transitions commute with this action. No quotient probability or
forward/reverse equality is assumed.
-/

@[expose] public section

namespace Freezing1.ReverseStamped

open scoped Classical

def relabel (F : Forest) (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ)) : Forest :=
  ⟨F.forest.relabel e, fun v => F.edgeTime (e.symm v)⟩

@[simp] theorem relabel_time (F : Forest) (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ)) (v : ℕ ⊕ ℕ) :
    (relabel F e).edgeTime (e v) = F.edgeTime v := by simp [relabel]

theorem relabel_pair_mem (F : Forest) (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ))
    (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    (e p.1, e p.2) ∈ (relabel F e).forest.roots.offDiag ↔
      p ∈ F.forest.roots.offDiag := by
  simp [ReverseStamped.relabel, RootedForest.relabel_roots, Finset.mem_offDiag]

theorem relabel_joinChoice (F : Forest) (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ))
    (t : ℕ) (p : (ℕ ⊕ ℕ) × (ℕ ⊕ ℕ)) :
    relabel (joinChoice F t p) e = joinChoice (relabel F e) t (e p.1, e p.2) := by
  by_cases hp : p ∈ F.forest.roots.offDiag
  · have hp' := (relabel_pair_mem F e p).mpr hp
    apply Forest.ext_data
    · simp only [joinChoice, dite_eq_left hp, dite_eq_left hp']
      exact F.forest.relabel_join e (Finset.mem_offDiag.mp hp).1
        (Finset.mem_offDiag.mp hp).2.1 (Finset.mem_offDiag.mp hp).2.2
    · funext w
      obtain ⟨v, rfl⟩ := e.surjective w
      by_cases h : v = p.2 <;> simp only [joinChoice, dite_eq_left hp, dite_eq_left hp']
      <;> simp [relabel, h]
  · have hp' := mt (relabel_pair_mem F e p).mp hp
    simp [joinChoice, hp, hp']

theorem relabel_insertLabel (F : Forest) (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ)) (i : ℕ)
    (he : e (.inr i) = .inr i) :
    relabel (insertLabel F i) e = insertLabel (relabel F e) i := by
  have hmem : Sum.inr i ∈ (relabel F e).forest.vertices ↔ Sum.inr i ∈ F.forest.vertices := by
    calc
      _ ↔ e (.inr i) ∈ (relabel F e).forest.vertices := by rw [he]
      _ ↔ _ := F.forest.relabel_mem_vertices e (.inr i)
  by_cases hi : Sum.inr i ∈ F.forest.vertices
  · simp [insertLabel, hi, hmem.mpr hi]
  · have hi' := mt hmem.mp hi
    apply Forest.ext_data
    · simp only [insertLabel, dite_eq_right hi, dite_eq_right hi']
      simpa only [relabel, he] using F.forest.relabel_adjoin e hi
    · funext w
      obtain ⟨v, rfl⟩ := e.surjective w
      have heq : e v = Sum.inr i ↔ v = Sum.inr i := by
        calc
          _ ↔ e v = e (.inr i) := by rw [he]
          _ ↔ _ := e.injective.eq_iff
      have hs : e.symm (.inr i) = .inr i := by
        apply e.injective
        simp [he]
      by_cases hv : v = Sum.inr i <;> simp only [insertLabel, dite_eq_right hi, dite_eq_right hi']
      <;> simp [relabel, heq, hv, he, hs]

theorem CanonicalDefaults.relabel {F : Forest} (hd : CanonicalDefaults F)
    (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ)) : CanonicalDefaults (relabel F e) := by
  constructor
  intro w hw
  obtain ⟨v, rfl⟩ := e.surjective w
  have hv : v ∉ F.forest.vertices := by simpa [ReverseStamped.relabel] using hw
  obtain ⟨hp, hr, hd, ht⟩ := hd.outside v hv
  simp [ReverseStamped.relabel, RootedForest.relabel, hp, hr, hd, ht]

theorem TimesValidAt.relabel {x : SignSequence} {n i : ℕ} {F : Forest}
    (ht : TimesValidAt x n i F) (e : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ)) :
    TimesValidAt x n i (relabel F e) := by
  constructor
  · intro w hw
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa [ReverseStamped.relabel, RootedForest.relabel_roots] using ht.root_zero v (by simpa [ReverseStamped.relabel] using hw)
  · intro w hw hzero
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [relabel_time] using ht.range v (by simpa [ReverseStamped.relabel] using hw)
      (by simpa only [relabel_time] using hzero)
  · intro u hu v hv hu0 hv0 heq
    obtain ⟨a, rfl⟩ := e.surjective u
    obtain ⟨b, rfl⟩ := e.surjective v
    apply congrArg e
    exact ht.injective a (by simpa [ReverseStamped.relabel] using hu) b (by simpa [ReverseStamped.relabel] using hv)
      (by simpa only [relabel_time] using hu0) (by simpa only [relabel_time] using hv0)
      (by simpa only [relabel_time] using heq)
  · rw [← ht.image_eq]
    ext t
    simp only [Finset.mem_image, positiveEdgeVertices, Finset.mem_filter]
    constructor
    · rintro ⟨w, ⟨hw, hz⟩, htime⟩
      obtain ⟨v, rfl⟩ := e.surjective w
      exact ⟨v, ⟨by simpa [ReverseStamped.relabel] using hw, by simpa using hz⟩, by simpa using htime⟩
    · rintro ⟨v, ⟨hv, hz⟩, htime⟩
      exact ⟨e v, ⟨by simpa [ReverseStamped.relabel] using hv, by simpa using hz⟩, by simpa using htime⟩

/-- Rename only the active side; freezing labels retain their original names. -/
def activeEquiv (σ : Equiv.Perm ℕ) : (ℕ ⊕ ℕ) ≃ (ℕ ⊕ ℕ) :=
  Equiv.sumCongr σ (Equiv.refl ℕ)

@[simp] theorem activeEquiv_inl (σ : Equiv.Perm ℕ) (j : ℕ) :
    activeEquiv σ (.inl j) = .inl (σ j) := rfl

@[simp] theorem activeEquiv_inr (σ : Equiv.Perm ℕ) (j : ℕ) :
    activeEquiv σ (.inr j) = .inr j := rfl

def activePermutations (k : ℕ) : Finset (Equiv.Perm ℕ) := permsOfFinset (Finset.range k)

theorem card_activePermutations (k : ℕ) : (activePermutations k).card = k.factorial := by
  simp [activePermutations, card_perms_of_finset]

theorem activePermutation_fixed {k : ℕ} {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ activePermutations k) {j : ℕ} (hj : k ≤ j) : σ j = j := by
  by_contra h
  have := mem_perms_of_finset_iff.mp hσ h
  simp only [Finset.mem_range] at this
  omega

theorem activePermutation_lt_iff {k : ℕ} {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ activePermutations k) (j : ℕ) : σ j < k ↔ j < k := by
  constructor
  · intro hj
    by_contra h
    rw [activePermutation_fixed hσ (Nat.le_of_not_gt h)] at hj
    omega
  · intro hj
    by_contra h
    have he := activePermutation_fixed hσ (Nat.le_of_not_gt h)
    have : σ j = j := σ.injective he
    omega

theorem activePermutation_phaseLabels {x : SignSequence} {n i : ℕ} {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ activePermutations (activeCount x n).toNat) :
    (Reverse.phaseLabels x n i).map (activeEquiv σ).toEmbedding = Reverse.phaseLabels x n i := by
  ext w
  obtain ⟨v, rfl⟩ := (activeEquiv σ).surjective w
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  cases v with
  | inl j => simp [Reverse.phaseLabels, activePermutation_lt_iff hσ]
  | inr j => simp [Reverse.phaseLabels]

theorem relabel_initial {x : SignSequence} {n : ℕ} {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ activePermutations (activeCount x n).toNat) :
    relabel (initial x n) (activeEquiv σ) = initial x n := by
  apply Forest.ext_data
  · change (Reverse.initial x n).relabel (activeEquiv σ) = Reverse.initial x n
    unfold Reverse.initial
    rw [RootedForest.relabel_isolated]
    congr 1
    rw [← Reverse.phaseLabels_top, activePermutation_phaseLabels hσ]
  · rfl

theorem LegalStep.relabel {x : SignSequence} {i : ℕ} {F H : Forest}
    (hs : LegalStep x i F H) (σ : Equiv.Perm ℕ) :
    LegalStep x i (relabel F (activeEquiv σ)) (relabel H (activeEquiv σ)) := by
  cases hx : x (i + 1)
  · simp only [LegalStep, hx, Bool.false_eq_true, ↓reduceIte] at hs ⊢
    rw [hs, relabel_insertLabel _ _ _ rfl]
  · simp only [LegalStep, hx, ↓reduceIte] at hs ⊢
    obtain ⟨p, hp, rfl⟩ := hs
    exact ⟨((activeEquiv σ) p.1, (activeEquiv σ) p.2),
      (relabel_pair_mem _ _ _).mpr hp, relabel_joinChoice _ _ _ _⟩

theorem PhaseData.relabel {x : SignSequence} {n i : ℕ} {F : Forest}
    (hd : PhaseData x n i F) {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ activePermutations (activeCount x n).toNat) :
    PhaseData x n i (relabel F (activeEquiv σ)) := by
  refine ⟨?_, hd.times.relabel _, hd.defaults.relabel _⟩
  constructor
  · change F.forest.vertices.map (activeEquiv σ).toEmbedding = _
    rw [hd.valid.vertices_eq, activePermutation_phaseLabels hσ]
  · change (F.forest.relabel _).roots.card = _
    rw [RootedForest.relabel_roots, Finset.card_map, hd.valid.roots_card]
  · exact (F.forest.relabelGraphIso (activeEquiv σ)).isAcyclic_iff.mp hd.valid.acyclic

/-- Renaming terminal active labels preserves an actual legal history, not
merely the terminal graph shape. -/
theorem HasPartialHistory.relabel {x : SignSequence} {n k : ℕ} {F : Forest}
    (hh : HasPartialHistory x n k F) {σ : Equiv.Perm ℕ}
    (hσ : σ ∈ activePermutations (activeCount x n).toNat) :
    HasPartialHistory x n k (relabel F (activeEquiv σ)) := by
  obtain ⟨H, hcur, hinit, hd, hs⟩ := hh
  refine ⟨fun i => ReverseStamped.relabel (H i) (activeEquiv σ), ?_, ?_, ?_, ?_⟩
  · dsimp only
    rw [hcur]
  · dsimp only
    rw [hinit, relabel_initial hσ]
  · exact fun i hi hin => (hd i hi hin).relabel hσ
  · exact fun i hi hin => (hs i hi hin).relabel σ

/-- Distinct active permutations give distinct timestamped terminal states.
Injectivity of incoming-edge IDs prevents nontrivial label stabilizers. -/
theorem relabel_injectiveOn_activePermutations {x : SignSequence} {n : ℕ} {F : Forest}
    (hv : F.forest.vertices = Reverse.phaseLabels x n 0)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    Set.InjOn (fun σ => relabel F (activeEquiv σ))
      (activePermutations (activeCount x n).toNat : Set (Equiv.Perm ℕ)) := by
  intro σ hσ τ hτ he
  apply Equiv.ext
  intro j
  by_cases hj : j < (activeCount x n).toNat
  · have hjv : Sum.inl j ∈ F.forest.vertices := by simp [hv, Reverse.phaseLabels, hj]
    have hs : σ j < (activeCount x n).toNat := (activePermutation_lt_iff hσ j).mpr hj
    have ht : τ.symm (σ j) < (activeCount x n).toNat := by
      apply (activePermutation_lt_iff hτ _).mp
      simpa using hs
    have htv : Sum.inl (τ.symm (σ j)) ∈ F.forest.vertices := by
      simp [hv, Reverse.phaseLabels, ht]
    have heq := congrArg (fun G : Forest => G.edgeTime (.inl (σ j))) he
    have hid : Sum.inl j = (Sum.inl (τ.symm (σ j)) : ℕ ⊕ ℕ) :=
      hinj _ hjv _ htv (by simpa [relabel, activeEquiv] using heq)
    have hj' : j = τ.symm (σ j) := Sum.inl.inj hid
    simpa using (congrArg τ hj').symm
  · rw [activePermutation_fixed hσ (Nat.le_of_not_gt hj),
      activePermutation_fixed hτ (Nat.le_of_not_gt hj)]

theorem card_activeOrbit {x : SignSequence} {n : ℕ} {F : Forest}
    (hv : F.forest.vertices = Reverse.phaseLabels x n 0)
    (hinj : ∀ u ∈ F.forest.vertices, ∀ v ∈ F.forest.vertices,
      F.edgeTime u = F.edgeTime v → u = v) :
    ((activePermutations (activeCount x n).toNat).image
      (fun σ => relabel F (activeEquiv σ))).card = (activeCount x n).toNat.factorial := by
  rw [Finset.card_image_of_injOn (relabel_injectiveOn_activePermutations hv hinj),
    card_activePermutations]

end Freezing1.ReverseStamped
