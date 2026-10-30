module

public import Freezing1.ForwardLocalLimit
public import Freezing1.ForwardAbsorption

/-!
# Local limits in the finite extinction case

The genuine infinite trajectory is eventually the absorbed finite state.
Its local limit is therefore exactly that finite tree, including all labels.
This supplies the extinction cases needed by the random-sign model.
-/

@[expose] public section

namespace Freezing1.ForwardInfiniteHistory

open Forward Filter MeasureTheory
open scoped Topology Classical

theorem LegalOrHeld.eq_of_active_empty {x : SignSequence} {n : ℕ} {s q : State}
    (hl : LegalOrHeld x n s q) (he : s.active = ∅) : q = s := by
  rcases hl with ⟨_, rfl⟩ | ⟨p, hp, _⟩
  · rfl
  · rw [he] at hp
    exact (Finset.notMem_empty p hp).elim

theorem history_constant_of_active_empty {x : SignSequence} {H : History}
    (hl : ∀ n, LegalOrHeld x n (H n) (H (n + 1))) {a : ℕ}
    (ha : (H a).active = ∅) : ∀ n ≥ a, H n = H a := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih => exact ((hl n).eq_of_active_empty (by rwa [ih])).trans ih

theorem fullLaw_constant_after_extinction {x : SignSequence} {a : ℕ}
    (ha : extinctionTime x = a) :
    ∀ᵐ H ∂fullLaw x, ∀ n ≥ a, H n = H a := by
  have he : ∀ᵐ H ∂fullLaw x, (H a).active = ∅ := by
    apply ae_of_ae_map (μ := fullLaw x) (f := fun H : History => H a)
      (p := fun s : State => s.active = ∅) (measurable_pi_apply a).aemeasurable
    rw [map_eval]
    exact treeLaw_active_empty_at_extinction ha
  filter_upwards [fullLaw_legalOrHeld x, he] with H hl he
  exact history_constant_of_active_empty hl he

theorem fullLaw_tendsto_extinction_tree {x : SignSequence} {a : ℕ}
    (ha : extinctionTime x = a) :
    ∀ᵐ H ∂fullLaw x,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localTreeOfState (H a))) := by
  filter_upwards [fullLaw_constant_after_extinction ha] with H hH
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop a] with n hn
  exact congrArg localTreeOfState (hH n hn).symm

theorem fullLaw_localLimit_eq_extinction_tree {x : SignSequence} {a : ℕ}
    (ha : extinctionTime x = a) :
    ∀ᵐ H ∂fullLaw x, localLimit H = localTreeOfState (H a) := by
  filter_upwards [fullLaw_tendsto_extinction_tree ha] with H hH
  exact tendsto_nhds_unique (tendsto_localLimit_of_exists ⟨_, hH⟩) hH

theorem fullLaw_tendsto_localLimit_of_extinction {x : SignSequence} {a : ℕ}
    (ha : extinctionTime x = a) :
    ∀ᵐ H ∂fullLaw x,
      Tendsto (fun n => localTreeOfState (H n)) atTop (𝓝 (localLimit H)) := by
  filter_upwards [fullLaw_tendsto_extinction_tree ha] with H hH
  exact tendsto_localLimit_of_exists ⟨_, hH⟩

theorem localLimitLaw_eq_extinction_treeLaw {x : SignSequence} {a : ℕ}
    (ha : extinctionTime x = a) : localLimitLaw x = localProbabilityLaw x a := by
  apply Subtype.ext
  change (fullLaw x).map localLimit = localTreeLaw x a
  rw [← map_eval_localTree]
  exact Measure.map_congr (fullLaw_localLimit_eq_extinction_tree ha)

theorem tendsto_localProbabilityLaw_of_extinction {x : SignSequence} {a : ℕ}
    (ha : extinctionTime x = a) :
    Tendsto (localProbabilityLaw x) atTop (𝓝 (localLimitLaw x)) :=
  tendsto_localProbabilityLaw_of_ae_tendsto x (fullLaw_tendsto_localLimit_of_extinction ha)

end Freezing1.ForwardInfiniteHistory
