module

public import Freezing1.LocalTreeRootDegree
public import Freezing1.ForwardLifetimeEvents

/-!
# Stabilization of actual finite balls after freezing

Once every vertex in a ball is frozen, no further step can change that
ball, including its displayed labels. Moreover the vertex set of the next
ball can no longer grow. This proves simultaneous stabilization from the
eventual freezing of every vertex, without assuming finite limiting degrees.
-/

@[expose] public section

namespace Freezing1

open Filter MeasureTheory
open scoped Topology Classical

namespace Forward

def heightVertices (s : State) (h : ℕ) : Finset ℕ :=
  s.vertices.filter (fun v => s.height v ≤ h)

def BallFrozen (s : State) (h : ℕ) : Prop :=
  ∀ v ∈ s.vertices, s.height v ≤ h → v ∉ s.active

theorem BallFrozen.active_height {s : State} {h p : ℕ}
    (hf : BallFrozen s h) (hp : p ∈ s.active) (hv : p ∈ s.vertices) :
    h < s.height p := by
  by_contra hn
  exact hf p hv (by omega) hp

theorem localRecord_attach_old {n : ℕ} {s : State} (hs : ValidAt n s)
    {v : ℕ} (hv : v ∈ s.vertices) (p : ℕ) :
    localRecord (attach s (n + 1) p) v = localRecord s v := by
  have hn : v ≠ n + 1 := by have := hs.vertices_le v hv; omega
  simp [localRecord, attach, hn]

theorem localRecord_freeze_of_ne (s : State) {v p : ℕ} (hvp : v ≠ p) (t : ℕ) :
    localRecord (freeze s t p) v = localRecord s v := by
  simp [localRecord, freeze, hvp]

theorem heightVertices_attach_of_ballFrozen {n : ℕ} {s : State}
    (hs : ValidAt n s) {h p : ℕ} (hf : BallFrozen s h) (hp : p ∈ s.active)
    {q : ℕ} (hq : q ≤ h + 1) :
    heightVertices (attach s (n + 1) p) q = heightVertices s q := by
  have hph := hf.active_height hp (hs.active_subset hp)
  ext v
  change v ∈ ((insert (n + 1) s.vertices).filter fun w =>
      Function.update s.height (n + 1) (s.height p + 1) w ≤ q) ↔
    v ∈ (s.vertices.filter fun w => s.height w ≤ q)
  rw [Finset.mem_filter, Finset.mem_filter]
  by_cases hn : v = n + 1
  · subst v
    have hnew : n + 1 ∉ s.vertices := by intro hn; have := hs.vertices_le _ hn; omega
    simp only [Finset.mem_insert,
      Function.update_self, true_or, true_and, hnew, false_and, iff_false]
    omega
  · simp only [Finset.mem_insert,
      Function.update_of_ne hn, hn, false_or]

theorem heightVertices_freeze (s : State) (t p h : ℕ) :
    heightVertices (freeze s t p) h = heightVertices s h := rfl

theorem BallFrozen.attach {n h : ℕ} {s : State} (hf : BallFrozen s h)
    (hs : ValidAt n s) {p : ℕ} (hp : p ∈ s.active) :
    BallFrozen (Forward.attach s (n + 1) p) h := by
  intro v hv hh ha
  have hph := hf.active_height hp (hs.active_subset hp)
  by_cases hn : v = n + 1
  · subst v
    simp only [Forward.attach, Function.update_self] at hh
    omega
  · have hv' : v ∈ s.vertices := by simpa [Forward.attach, hn] using hv
    have hh' : s.height v ≤ h := by simpa [Forward.attach, hn] using hh
    have ha' : v ∈ s.active := by simpa [Forward.attach, hn] using ha
    exact hf v hv' hh' ha'

theorem BallFrozen.freeze {s : State} {h : ℕ} (hf : BallFrozen s h) (t p : ℕ) :
    BallFrozen (Forward.freeze s t p) h := by
  intro v hv hh ha
  exact hf v hv hh (Finset.mem_of_mem_erase ha)

theorem localBall_attach_of_ballFrozen {n : ℕ} {s : State} (hs : ValidAt n s)
    {h p : ℕ} (hf : BallFrozen s h) (hp : p ∈ s.active) :
    localBall (attach s (n + 1) p) h = localBall s h := by
  rw [localBall_eq_image, localBall_eq_image]
  change (heightVertices (attach s (n + 1) p) h).image _ =
    (heightVertices s h).image _
  rw [heightVertices_attach_of_ballFrozen hs hf hp (Nat.le_succ h)]
  apply Finset.image_congr
  intro v hv
  exact localRecord_attach_old hs (Finset.mem_filter.mp hv).1 p

theorem localBall_freeze_of_ballFrozen {s : State} {h p : ℕ}
    (hf : BallFrozen s h) (hp : p ∈ s.active) (t : ℕ) :
    localBall (freeze s t p) h = localBall s h := by
  rw [localBall_eq_image, localBall_eq_image]
  apply Finset.image_congr
  intro v hv
  have hvp : v ≠ p := by
    intro he
    subst v
    exact hf p (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2 hp
  exact localRecord_freeze_of_ne s hvp t

end Forward

namespace ForwardInfiniteHistory

open Forward

theorem LegalOrHeld.ballFrozen {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) (hs : ValidAt n s) {h : ℕ} (hf : BallFrozen s h) :
    BallFrozen q h := by
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · exact hf
  · rw [step, ite_eq_left hp]
    cases hx : x (n + 1)
    · exact hf.freeze _ _
    · exact hf.attach hs hp

theorem LegalOrHeld.localBall {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) (hs : ValidAt n s) {h : ℕ} (hf : BallFrozen s h) :
    localBall q h = localBall s h := by
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · rfl
  · rw [step, ite_eq_left hp]
    cases hx : x (n + 1)
    · exact localBall_freeze_of_ballFrozen hf hp _
    · exact localBall_attach_of_ballFrozen hs hf hp

theorem LegalOrHeld.heightVertices_succ {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) (hs : ValidAt n s) {h : ℕ} (hf : BallFrozen s h) :
    heightVertices q (h + 1) = heightVertices s (h + 1) := by
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, rfl⟩
  · rfl
  · rw [step, ite_eq_left hp]
    cases hx : x (n + 1)
    · rfl
    · exact heightVertices_attach_of_ballFrozen hs hf hp le_rfl

theorem ballFrozen_persists {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    {a h : ℕ} (hf : BallFrozen (H a) h) :
    ∀ n ≥ a, BallFrozen (H n) h ∧ localBall (H n) h = localBall (H a) h ∧
      heightVertices (H n) (h + 1) = heightVertices (H a) (h + 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨hf, rfl, rfl⟩
  | succ n hn ih =>
    exact ⟨(hl n).ballFrozen (hv n) ih.1,
      ((hl n).localBall (hv n) ih.1).trans ih.2.1,
      ((hl n).heightVertices_succ (hv n) ih.1).trans ih.2.2⟩

theorem all_balls_eventually_frozen {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hf : ∀ r n, r ∈ (H n).vertices → ∃ a j, ∀ m ≥ a, (H m).frozenAt r = some j) :
    ∀ h, ∃ a, BallFrozen (H a) h := by
  intro h
  induction h with
  | zero =>
    obtain ⟨a, j, ha⟩ := hf 0 0 (hv 0).root_mem
    refine ⟨a, ?_⟩
    intro r hr hh hactive
    have he : r = 0 := by
      have hh' : (H a).graph.dist 0 r = 0 := by rw [← (hv a).height_eq_dist r hr]; omega
      exact ((hv a).reachable r hr |>.dist_eq_zero_iff.mp hh').symm
    subst r
    have hn := ((hv a).active_iff 0 hr).mp hactive
    rw [ha a le_rfl] at hn
    contradiction
  | succ h ih =>
    obtain ⟨a, ha⟩ := ih
    have hfinite : ∀ r ∈ heightVertices (H a) (h + 1),
        ∃ b, ∀ m ≥ b, (H m).frozenAt r ≠ none := by
      intro r hr
      obtain ⟨b, j, hb⟩ := hf r a (Finset.mem_filter.mp hr).1
      exact ⟨b, fun m hm => by rw [hb m hm]; simp⟩
    choose b hb using hfinite
    let M := max a ((heightVertices (H a) (h + 1)).attach.sup fun r => b r.val r.property)
    have haM : a ≤ M := le_max_left _ _
    refine ⟨M, ?_⟩
    intro r hr hh hactive
    have hmem : r ∈ heightVertices (H a) (h + 1) := by
      rw [← (ballFrozen_persists hv hl ha M haM).2.2]
      exact Finset.mem_filter.mpr ⟨hr, hh⟩
    have hbM : b r hmem ≤ M :=
      (Finset.le_sup (f := fun q => b q.val q.property)
        (Finset.mem_attach _ ⟨r, hmem⟩)).trans (le_max_right _ _)
    exact hb r hmem M hbM (((hv M).active_iff r hr).mp hactive)

theorem all_balls_stabilize {x : SignSequence} {H : History}
    (hv : ∀ n, ValidAt n (H n)) (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1)))
    (hf : ∀ r n, r ∈ (H n).vertices → ∃ a j, ∀ m ≥ a, (H m).frozenAt r = some j) :
    ∀ h, ∃ a, ∀ n ≥ a, localBall (H n) h = localBall (H a) h := by
  intro h
  obtain ⟨a, ha⟩ := all_balls_eventually_frozen hv hl hf h
  exact ⟨a, fun n hn => (ballFrozen_persists hv hl ha n hn).2.1⟩

theorem fullLaw_all_balls_stabilize (x : SignSequence)
    (hτ : extinctionTime x = ⊤) (hdiv : ¬Summable (printedFreezingReciprocal x)) :
    ∀ᵐ H ∂fullLaw x, ∀ h, ∃ a, ∀ n ≥ a, localBall (H n) h = localBall (H a) h := by
  filter_upwards [fullLaw_valid x, fullLaw_legalOrHeld x,
    fullLaw_all_vertices_eventually_frozen x hτ hdiv] with H hv hl hf
  exact all_balls_stabilize hv hl hf

end ForwardInfiniteHistory
end Freezing1
