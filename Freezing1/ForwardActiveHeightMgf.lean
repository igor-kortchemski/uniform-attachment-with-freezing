module

public import Freezing1.ForwardUniformHeight

/-!
# Exact exponential-moment recursion for the height of a uniform active vertex

For a fixed schedule and a given forward state `s` at time `n`, the height of
a uniformly chosen active vertex at time `n+k` has, conditionally on the
state at time `n`, the moment generating function of the height at time `n`
multiplied by the Bernoulli factors $1+(c-1)/S_i$ over the attachment steps
$i=n+1,\dots,n+k$, with $S_i$ the active count. Freezing steps leave the law
unchanged. Equivalently the height is that of a uniform active vertex at
time `n` plus independent Bernoulli$(1/S_i)$ increments. A vertex born at
time `m` has height one more than that of a uniform active vertex at time
`m-1`. This is the exact conditional domination used in the late-height
estimate, for the fixed word.
-/

@[expose] public section

namespace Freezing1.Forward

open MeasureTheory
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- Sum of `f ∘ height` over the active vertices. -/
noncomputable def activeHSum (s : State) (f : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a ∈ s.active, f (s.height a)

/-- Mean of `f ∘ height` over a uniformly chosen active vertex. -/
noncomputable def activeHMean (s : State) (f : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  (s.active.card : ℝ≥0∞)⁻¹ * activeHSum s f

theorem lintegral_uniformOfFinset_eq {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (A : Finset α) (g : α → ℝ≥0∞) :
    ∫⁻ a, g a ∂Measure.uniformOfFinset A = (A.card : ℝ≥0∞)⁻¹ * ∑ a ∈ A, g a := by
  unfold Measure.uniformOfFinset
  rw [lintegral_finsetSum_measure, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

theorem lintegral_transitionLaw {s : State} (hne : s.active.Nonempty) (t : ℕ) (sign : Bool)
    (g : State → ℝ≥0∞) :
    ∫⁻ r, g r ∂transitionLaw s t sign =
      (s.active.card : ℝ≥0∞)⁻¹ * ∑ v ∈ s.active, g (step s t sign v) := by
  rw [transitionLaw, ite_eq_left hne, lintegral_map (by fun_prop) (by fun_prop),
    lintegral_uniformOfFinset_eq]

theorem activeHSum_attach {n : ℕ} {s : State} (hs : ValidAt n s) {v : ℕ} (f : ℕ → ℝ≥0∞) :
    activeHSum (attach s (n + 1) v) f = f (s.height v + 1) + activeHSum s f := by
  have hfresh : n + 1 ∉ s.vertices := by
    intro h; have := hs.vertices_le _ h; omega
  have hafresh : n + 1 ∉ s.active := fun h => hfresh (hs.active_subset h)
  unfold activeHSum
  change ∑ a ∈ insert (n + 1) s.active, f (Function.update s.height (n + 1) (s.height v + 1) a) = _
  rw [Finset.sum_insert hafresh, Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a ≠ n + 1 := fun h => hafresh (h ▸ ha)
  rw [Function.update_of_ne this]

theorem card_active_attach_H {n : ℕ} {s : State} (hs : ValidAt n s) (v : ℕ) :
    (attach s (n + 1) v).active.card = s.active.card + 1 := by
  have hfresh : n + 1 ∉ s.vertices := by
    intro h; have := hs.vertices_le _ h; omega
  have hafresh : n + 1 ∉ s.active := fun h => hfresh (hs.active_subset h)
  change (insert (n + 1) s.active).card = _
  rw [Finset.card_insert_of_notMem hafresh]

/-- One attachment step: the mean of `c ^ height` over a uniform active vertex is multiplied
by `(S + c) / (S + 1)`, i.e. one Bernoulli$(1/(S+1))$ increment. -/
theorem lintegral_activeHMean_pow_attach {n : ℕ} {s : State} (hs : ValidAt n s)
    (hne : s.active.Nonempty) (c : ℝ≥0∞) :
    ∫⁻ r, activeHMean r (fun h => c ^ h) ∂transitionLaw s (n + 1) true =
      (((s.active.card : ℝ≥0∞) + 1)⁻¹ * ((s.active.card : ℝ≥0∞) + c)) *
        activeHMean s (fun h => c ^ h) := by
  rw [lintegral_transitionLaw hne]
  have hS0 : (s.active.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hStop : (s.active.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hstep : ∀ v ∈ s.active, activeHMean (step s (n + 1) true v) (fun h => c ^ h) =
      ((s.active.card : ℝ≥0∞) + 1)⁻¹ * (c * c ^ s.height v + activeHSum s (fun h => c ^ h)) := by
    intro v hv
    unfold activeHMean
    rw [step, ite_eq_left hv]
    simp only [↓reduceIte]
    rw [activeHSum_attach hs, card_active_attach_H hs, pow_succ]
    push_cast
    rw [mul_comm (c ^ s.height v) c]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum]
  unfold activeHMean activeHSum
  generalize (s.active.card : ℝ≥0∞) = S at *
  generalize ∑ a ∈ s.active, c ^ s.height a = T
  have key1 : S⁻¹ * S = 1 := ENNReal.inv_mul_cancel hS0 hStop
  have key2 : S * S⁻¹ = 1 := ENNReal.mul_inv_cancel hS0 hStop
  calc
    S⁻¹ * ((S + 1)⁻¹ * (c * T + S * T))
        = (S + 1)⁻¹ * (c * (S⁻¹ * T) + (S⁻¹ * S) * T) := by ring
    _ = (S + 1)⁻¹ * (c * (S⁻¹ * T) + T) := by rw [key1, one_mul]
    _ = (S + 1)⁻¹ * ((S * S⁻¹) * T + c * (S⁻¹ * T)) := by rw [key2, one_mul]; ring
    _ = (S + 1)⁻¹ * (S + c) * (S⁻¹ * T) := by ring

/-- One freezing step leaves the mean unchanged (when the active set survives). -/
theorem lintegral_activeHMean_freeze {n : ℕ} {s : State} (h2 : 2 ≤ s.active.card)
    (f : ℕ → ℝ≥0∞) :
    ∫⁻ r, activeHMean r f ∂transitionLaw s (n + 1) false = activeHMean s f := by
  have hne : s.active.Nonempty := Finset.card_pos.mp (by omega)
  rw [lintegral_transitionLaw hne]
  obtain ⟨S', hS'⟩ : ∃ S', s.active.card = S' + 1 := ⟨s.active.card - 1, by omega⟩
  have hS'pos : 0 < S' := by omega
  have hstep : ∀ v ∈ s.active, activeHMean (step s (n + 1) false v) f =
      (S' : ℝ≥0∞)⁻¹ * ∑ a ∈ s.active.erase v, f (s.height a) := by
    intro v hv
    unfold activeHMean activeHSum
    rw [step, ite_eq_left hv]
    simp only [Bool.false_eq_true, ↓reduceIte]
    change ((s.active.erase v).card : ℝ≥0∞)⁻¹ * ∑ a ∈ s.active.erase v, f (s.height a) = _
    rw [Finset.card_erase_of_mem hv, hS']
    simp
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  have hswap : ∑ v ∈ s.active, ∑ a ∈ s.active.erase v, f (s.height a) =
      S' * ∑ a ∈ s.active, f (s.height a) := by
    rw [Finset.sum_comm' (t' := s.active) (s' := fun a => s.active.erase a)]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [Finset.sum_const, Finset.card_erase_of_mem ha, hS', nsmul_eq_mul]
      simp
    · intro v a
      simp only [Finset.mem_erase]
      tauto
  rw [hswap]
  unfold activeHMean activeHSum
  rw [hS']
  have hS'0 : (S' : ℝ≥0∞) ≠ 0 := by exact_mod_cast hS'pos.ne'
  have hS'top : (S' : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  generalize ∑ a ∈ s.active, f (s.height a) = T
  push_cast
  congr 1
  rw [← mul_assoc, ENNReal.inv_mul_cancel hS'0 hS'top, one_mul]

theorem attachFactor_eq (S : ℕ) {c : ℝ≥0∞} (hc : 1 ≤ c) :
    (((S : ℝ≥0∞) + 1)⁻¹ * ((S : ℝ≥0∞) + c)) = 1 + ((S : ℝ≥0∞) + 1)⁻¹ * (c - 1) := by
  have h1 : (S : ℝ≥0∞) + c = ((S : ℝ≥0∞) + 1) + (c - 1) := by
    rw [add_assoc, add_tsub_cancel_of_le hc]
  have hne : (S : ℝ≥0∞) + 1 ≠ 0 := by simp
  have htop : (S : ℝ≥0∞) + 1 ≠ ⊤ := by simp
  rw [h1, mul_add, ENNReal.inv_mul_cancel hne htop]

/-- The forward chain started from a given state at time `n`, with the fixed schedule `x`. -/
noncomputable def treeLawFrom (x : SignSequence) (n : ℕ) (s : State) : ℕ → Measure State
  | 0 => Measure.dirac s
  | k + 1 => (treeLawFrom x n s k).bind fun r => transitionLaw r (n + k + 1) (x (n + k + 1))

instance treeLawFrom_probability (x : SignSequence) (n : ℕ) (s : State) (k : ℕ) :
    IsProbabilityMeasure (treeLawFrom x n s k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac s); infer_instance
  | succ k ih =>
    exact isProbabilityMeasure_bind measurable_from_top.aemeasurable
      (Filter.Eventually.of_forall (fun r => transitionLaw_probability r _ _))

theorem card_active_step {m : ℕ} {r : State} (hr : ValidAt m r) {v : ℕ} (hv : v ∈ r.active)
    (sign : Bool) :
    ((step r (m + 1) sign v).active.card : ℤ) =
      r.active.card + (if sign then 1 else -1) := by
  have hcard : 0 < r.active.card := Finset.card_pos.mpr ⟨v, hv⟩
  cases sign
  · simp only [Forward.step, hv, ite_true, Bool.false_eq_true, ite_false, Forward.freeze]
    rw [Finset.card_erase_of_mem hv, Nat.cast_sub (by omega)]
    simp [sub_eq_add_neg]
  · simp only [Forward.step, hv, ite_true]
    rw [card_active_attach_H hr v]
    push_cast
    simp

theorem treeLawFrom_invariant {x : SignSequence} {n : ℕ} {s : State} (hs : ValidAt n s)
    (hc : (s.active.card : ℤ) = activeCount x n) (K : ℕ) (hpos : PositiveThrough x (n + K)) :
    ∀ k ≤ K, ∀ᵐ r ∂treeLawFrom x n s k,
      ValidAt (n + k) r ∧ (r.active.card : ℤ) = activeCount x (n + k) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact (ae_dirac_iff (by trivial)).mpr ⟨hs, hc⟩
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    apply (ae_iff_prob_eq_one measurable_from_top).mpr
    rw [treeLawFrom, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    calc
      _ = ∫⁻ _r, (1 : ℝ≥0∞) ∂treeLawFrom x n s k := by
        apply lintegral_congr_ae
        filter_upwards [ihk] with r hr
        apply (ae_iff_prob_eq_one measurable_from_top).mp
        apply transitionLaw_ae r _ _ _
        · intro he
          exfalso
          have h1 := hr.2
          have h2 := hpos (n + k) (by omega)
          rw [he] at h1
          simp only [Finset.card_empty, Nat.cast_zero] at h1
          omega
        · intro v hv
          refine ⟨hr.1.step _ _, ?_⟩
          rw [card_active_step hr.1 hv, hr.2]
          exact (activeCount_succ x (n + k)).symm
      _ = 1 := by simp

/-- The factor multiplying the exponential moment at step `j+1`: a Bernoulli$(1/S_{j+1})$ increment
at attachment steps and nothing at freezing steps. -/
noncomputable def attachFactor (x : SignSequence) (c : ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  if x (j + 1) = true then
    (((activeCount x j).toNat : ℝ≥0∞) + 1)⁻¹ * (((activeCount x j).toNat : ℝ≥0∞) + c)
  else 1

theorem lintegral_activeHMean_pow_treeLawFrom {x : SignSequence} {n : ℕ} {s : State}
    (hs : ValidAt n s) (hc : (s.active.card : ℤ) = activeCount x n) (K : ℕ)
    (hpos : PositiveThrough x (n + K)) (c : ℝ≥0∞) :
    ∀ k ≤ K, ∫⁻ r, activeHMean r (fun h => c ^ h) ∂treeLawFrom x n s k =
      (∏ i ∈ Finset.range k, attachFactor x c (n + i)) * activeHMean s (fun h => c ^ h) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [treeLawFrom, lintegral_dirac]
  | succ k ih =>
    intro hk
    have ihk := ih (by omega)
    have hinv := treeLawFrom_invariant hs hc K hpos k (by omega)
    rw [treeLawFrom, Measure.lintegral_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    have hstep : ∀ᵐ r ∂treeLawFrom x n s k,
        ∫⁻ r', activeHMean r' (fun h => c ^ h) ∂transitionLaw r (n + k + 1) (x (n + k + 1)) =
          attachFactor x c (n + k) * activeHMean r (fun h => c ^ h) := by
      filter_upwards [hinv] with r hr
      have hp0 := hpos (n + k) (by omega)
      have hp1 := hpos (n + k + 1) (by omega)
      have hcard : r.active.card = (activeCount x (n + k)).toNat := by
        have := hr.2
        omega
      have hne : r.active.Nonempty := Finset.card_pos.mp (by omega)
      unfold attachFactor
      cases hx : x (n + k + 1)
      · simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
        apply lintegral_activeHMean_freeze (n := n + k)
        have := hr.2
        rw [activeCount_succ, hx] at hp1
        simp only [Bool.false_eq_true, ↓reduceIte] at hp1
        omega
      · simp only [↓reduceIte]
        rw [lintegral_activeHMean_pow_attach hr.1 hne c, hcard]
    rw [lintegral_congr_ae hstep, lintegral_const_mul _ measurable_from_top, ihk,
      Finset.prod_range_succ]
    ring

/-- A vertex born at time `n+k+1` by attachment has exponential height moment `c` times the
mean over a uniform active vertex one step earlier. -/
theorem lintegral_newVertex_height_pow {x : SignSequence} {n : ℕ} {s : State}
    (hs : ValidAt n s) (hc : (s.active.card : ℤ) = activeCount x n) (K : ℕ)
    (hpos : PositiveThrough x (n + K)) (c : ℝ≥0∞) {k : ℕ} (hk : k + 1 ≤ K)
    (hx : x (n + k + 1) = true) :
    ∫⁻ r, c ^ r.height (n + k + 1) ∂treeLawFrom x n s (k + 1) =
      c * ((∏ i ∈ Finset.range k, attachFactor x c (n + i)) *
        activeHMean s (fun h => c ^ h)) := by
  have hinv := treeLawFrom_invariant hs hc K hpos k (by omega)
  rw [treeLawFrom, Measure.lintegral_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable]
  have hstep : ∀ᵐ r ∂treeLawFrom x n s k,
      ∫⁻ r', c ^ r'.height (n + k + 1) ∂transitionLaw r (n + k + 1) (x (n + k + 1)) =
        c * activeHMean r (fun h => c ^ h) := by
    filter_upwards [hinv] with r hr
    have hp0 := hpos (n + k) (by omega)
    have hne : r.active.Nonempty := Finset.card_pos.mp (by have := hr.2; omega)
    rw [lintegral_transitionLaw hne, hx]
    unfold activeHMean activeHSum
    have hstepv : ∀ v ∈ r.active, c ^ (step r (n + k + 1) true v).height (n + k + 1) =
        c * c ^ r.height v := by
      intro v hv
      rw [step, ite_eq_left hv]
      simp only [↓reduceIte]
      change c ^ (Function.update r.height (n + k + 1) (r.height v + 1) (n + k + 1)) = _
      rw [Function.update_self, pow_succ, mul_comm]
    rw [Finset.sum_congr rfl hstepv, ← Finset.mul_sum]
    ring
  rw [lintegral_congr_ae hstep, lintegral_const_mul _ measurable_from_top,
    lintegral_activeHMean_pow_treeLawFrom hs hc K hpos c k (by omega)]

/-- The attachment factor is exactly the exponential moment of a Bernoulli$(1/S)$ increment at an
attachment step, with `S` the active count after the step, and `1` at freezing steps. -/
theorem attachFactor_eq_bernoulli (x : SignSequence) {c : ℝ≥0∞} (hc : 1 ≤ c) (j : ℕ) :
    attachFactor x c j = 1 + (if x (j + 1) = true then
      (((activeCount x j).toNat : ℝ≥0∞) + 1)⁻¹ else 0) * (c - 1) := by
  unfold attachFactor
  by_cases hx : x (j + 1) = true
  · simp only [hx, ↓reduceIte]
    exact attachFactor_eq _ hc
  · simp [hx]

theorem activeHMean_pow_le {s : State} (hne : s.active.Nonempty) {c : ℝ≥0∞} (hc : 1 ≤ c) {H : ℕ}
    (hH : ∀ a ∈ s.active, s.height a ≤ H) : activeHMean s (fun h => c ^ h) ≤ c ^ H := by
  unfold activeHMean activeHSum
  have hS0 : (s.active.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
  have hStop : (s.active.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    (s.active.card : ℝ≥0∞)⁻¹ * ∑ a ∈ s.active, c ^ s.height a
        ≤ (s.active.card : ℝ≥0∞)⁻¹ * ∑ _a ∈ s.active, c ^ H := by
      gcongr with a ha
      exact hH a ha
    _ = c ^ H := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_comm _ (s.active.card : ℝ≥0∞),
        ENNReal.mul_inv_cancel hS0 hStop, one_mul]

/-- Conditional domination, in exponential moments, of the height of a vertex born at time
`n+k+1` by attachment: starting from the state `s` at time `n` whose active vertices have height
at most `H`, it is at most `H + 1` plus independent Bernoulli increments. -/
theorem newVertex_height_pow_le {x : SignSequence} {n : ℕ} {s : State}
    (hs : ValidAt n s) (hc : (s.active.card : ℤ) = activeCount x n) (K : ℕ)
    (hpos : PositiveThrough x (n + K)) {c : ℝ≥0∞} (hc1 : 1 ≤ c) {k : ℕ} (hk : k + 1 ≤ K)
    (hx : x (n + k + 1) = true) {H : ℕ} (hH : ∀ a ∈ s.active, s.height a ≤ H) :
    ∫⁻ r, c ^ r.height (n + k + 1) ∂treeLawFrom x n s (k + 1) ≤
      c * (∏ i ∈ Finset.range k, (1 + (if x (n + i + 1) = true then
        (((activeCount x (n + i)).toNat : ℝ≥0∞) + 1)⁻¹ else 0) * (c - 1))) * c ^ H := by
  have hne : s.active.Nonempty := Finset.card_pos.mp (by
    have := hpos n (by omega); omega)
  rw [lintegral_newVertex_height_pow hs hc K hpos c hk hx]
  simp only [attachFactor_eq_bernoulli x hc1]
  calc
    _ ≤ c * ((∏ i ∈ Finset.range k, (1 + (if x (n + i + 1) = true then
        (((activeCount x (n + i)).toNat : ℝ≥0∞) + 1)⁻¹ else 0) * (c - 1))) * c ^ H) := by
      gcongr
      exact activeHMean_pow_le hne hc1 hH
    _ = _ := by ring

end Freezing1.Forward
