module

public import Freezing1.FinitePlaneConditionalGeometry
public import Freezing1.SIRIidCountProjection
public import Freezing1.PlaneFiniteExtinction

/-!
# First active-zero time and vertex count of the actual plane chain

Along the genuine iid-sign chain, every legal step of a nonempty active set
changes $2|V|-|A|$ by exactly one, whether it attaches or freezes. Hence
the first time $\tau$ with no active vertex satisfies $2|V(\tau)|=\tau+1$,
so $\tau$ is odd and the terminal tree has $(\tau+1)/2$ vertices. Absorbed
histories are held, so the limiting tree is that terminal tree.
-/

@[expose] public section

namespace Freezing1.PlaneForward

open MeasureTheory ProbabilityTheory Filter PlaneTree
open scoped Classical Topology

set_option backward.isDefEq.respectTransparency false

/-- The first active-zero time of the history is exactly `n`. -/
def ExtinctionTimeIs (n : ℕ) (H : ℕ → State) : Prop :=
  (H n).active.card = 0 ∧ ∀ k < n, (H k).active.card ≠ 0

theorem measurableSet_extinctionTimeIs (n : ℕ) :
    MeasurableSet {H : ℕ → State | ExtinctionTimeIs n H} := by
  apply measurableSet_setOfPred.mpr
  apply Measurable.and
  · exact (measurable_of_countable (fun s : State => s.active.card = 0)).comp
      (measurable_pi_apply n)
  · apply Measurable.forall
    intro k
    apply Measurable.imp measurable_const
    exact (measurable_of_countable (fun s : State => s.active.card ≠ 0)).comp
      (measurable_pi_apply k)

theorem step_vertices_active_count {s : State} (hs : Valid s) {u : Address}
    (hu : u ∈ s.active) (sign : Bool) :
    2 * (step s sign u).vertices.card + s.active.card =
      2 * s.vertices.card + (step s sign u).active.card + 1 := by
  have hcard : 0 < s.active.card := Finset.card_pos.mpr ⟨u, hu⟩
  have hfresh : newChild s u ∉ s.vertices := hs.newChild_not_mem (hs.active_subset hu)
  have hfresh' : newChild s u ∉ s.active := fun h => hfresh (hs.active_subset h)
  cases sign
  · simp only [step, hu, ite_true, Bool.false_eq_true, ite_false, freeze,
      Finset.card_erase_of_mem hu]
    omega
  · simp only [step, hu, ite_true, attach, Finset.card_insert_of_notMem hfresh,
      Finset.card_insert_of_notMem hfresh']
    omega

/-- Almost surely every history is made of valid states, is held after absorption,
and satisfies the exact vertex/active/time count before its first extinction. -/
theorem ae_vertex_active_time_count (p : unitInterval) :
    ∀ᵐ H ∂fullLaw p initial,
      ∀ k, (∀ j < k, (H j).active.card ≠ 0) →
        2 * (H k).vertices.card = (H k).active.card + 1 + k := by
  have hstep : ∀ s : State, ∀ᵐ t ∂transition p s,
      Valid s → s.active.card ≠ 0 →
        2 * t.vertices.card + s.active.card =
          2 * s.vertices.card + t.active.card + 1 := by
    intro s
    apply transition_ae
    · intro hempty _ hne
      exact absurd (by simp [hempty]) hne
    · intro sign u hu hs _
      exact step_vertices_active_count hs hu sign
  filter_upwards [CountableMarkovChain.fullLaw_initial (transition p) initial,
    CountableMarkovChain.fullLaw_steps (transition p) initial _ hstep,
    SIR.planeFullLaw_valid p] with H h0 hl hvalid
  intro k
  induction k with
  | zero =>
    intro _
    rw [h0]
    simp [initial]
  | succ k ih =>
    intro hall
    have hk : ∀ j < k, (H j).active.card ≠ 0 := fun j hj => hall j (by omega)
    have hne : (H k).active.card ≠ 0 := hall k (by omega)
    have h1 := hl k (hvalid k) hne
    have h2 := ih hk
    omega

theorem extinctionTimeIs_vertices {H : ℕ → State}
    (hcount : ∀ k, (∀ j < k, (H j).active.card ≠ 0) →
      2 * (H k).vertices.card = (H k).active.card + 1 + k)
    {n : ℕ} (h : ExtinctionTimeIs n H) : 2 * (H n).vertices.card = n + 1 := by
  have := hcount n h.2
  rw [h.1] at this
  omega

theorem extinctionTimeIs_odd {H : ℕ → State}
    (hcount : ∀ k, (∀ j < k, (H j).active.card ≠ 0) →
      2 * (H k).vertices.card = (H k).active.card + 1 + k)
    {n : ℕ} (h : ExtinctionTimeIs n H) : n % 2 = 1 := by
  have := extinctionTimeIs_vertices hcount h
  omega

theorem finiteVertexCount_shape {s : State} (hs : Valid s) :
    finiteVertexCount (shape s) = s.vertices.card := by
  have he : {u : Address | Present (shape s) u} = (s.vertices : Set Address) := by
    ext u
    exact (hs.mem_vertices_iff_present u).symm
  rw [finiteVertexCount, he, Set.ncard_coe_finset]

theorem chainLimit_eq_shape_of_absorbed {H : ℕ → State}
    (hheld : ∀ k, (H k).active = ∅ → H (k + 1) = H k)
    (hlim : Tendsto (fun k => shape (H k)) atTop (𝓝 (chainLimit H)))
    {a : ℕ} (ha : (H a).active.card = 0) : chainLimit H = shape (H a) := by
  have haempty : (H a).active = ∅ := Finset.card_eq_zero.mp ha
  have hevent : ∀ᶠ k in atTop, shape (H k) = shape (H a) := by
    filter_upwards [eventually_ge_atTop a] with k hk
    rw [held_after_empty_persists hheld haempty k hk]
  have hconst : Tendsto (fun k => shape (H k)) atTop (𝓝 (shape (H a))) :=
    tendsto_const_nhds.congr' (hevent.mono fun _ hk => hk.symm)
  exact tendsto_nhds_unique hlim hconst

/-- Almost surely, the first extinction time is `n` exactly when the actual limiting
plane tree is finite with `(n+1)/2` vertices, for `n = 2m-1`. -/
theorem ae_extinctionTimeIs_iff_finiteVertexCount (p : unitInterval) (hp : (p : ℝ) < 1)
    (m : ℕ) (hm : 1 ≤ m) :
    ∀ᵐ H ∂fullLaw p initial,
      ExtinctionTimeIs (2 * m - 1) H ↔
        (FiniteVertices (chainLimit H) ∧ finiteVertexCount (chainLimit H) = m) := by
  filter_upwards [ae_vertex_active_time_count p, SIR.planeFullLaw_valid p,
    fullLaw_tendsto_chainLimit p hp, fullLaw_held_after_empty p,
    fullLaw_finite_chainLimit_iff_absorbed p hp] with H hcount hvalid hlim hheld habs
  constructor
  · intro h
    have hlimeq := chainLimit_eq_shape_of_absorbed hheld hlim h.1
    have hv := extinctionTimeIs_vertices hcount h
    refine ⟨?_, ?_⟩
    · rw [hlimeq]
      exact finiteVertices_shape (hvalid _)
    · rw [hlimeq, finiteVertexCount_shape (hvalid _)]
      omega
  · rintro ⟨hfin, hcard⟩
    obtain ⟨k, hk⟩ := habs.mp hfin
    classical
    have hex : ∃ k, (H k).active.card = 0 := ⟨k, hk⟩
    set τ := Nat.find hex with hτ
    have hτzero : (H τ).active.card = 0 := Nat.find_spec hex
    have hτmin : ∀ j < τ, (H j).active.card ≠ 0 := fun j hj => Nat.find_min hex hj
    have hext : ExtinctionTimeIs τ H := ⟨hτzero, hτmin⟩
    have hlimeq := chainLimit_eq_shape_of_absorbed hheld hlim hτzero
    have hv := extinctionTimeIs_vertices hcount hext
    rw [hlimeq, finiteVertexCount_shape (hvalid _)] at hcard
    have hτeq : τ = 2 * m - 1 := by omega
    rw [← hτeq]
    exact hext

/-- Even times cannot be first extinction times; the parity obstruction holds for every
valid history, not only almost surely. -/
theorem ae_not_extinctionTimeIs_of_even (p : unitInterval) {n : ℕ} (hn : n % 2 = 0) :
    ∀ᵐ H ∂fullLaw p initial, ¬ExtinctionTimeIs n H := by
  filter_upwards [ae_vertex_active_time_count p] with H hcount h
  have := extinctionTimeIs_odd hcount h
  omega

end Freezing1.PlaneForward
