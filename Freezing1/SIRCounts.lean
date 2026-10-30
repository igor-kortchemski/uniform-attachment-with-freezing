module

public import Mathlib.Tactic
public import Mathlib.Tactic.DeriveCountable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The finite-population embedded SIR counts

Counts are stopped when no individual is infectious. An infection consumes
one susceptible individual; a recovery removes one infectious individual.
The guard at zero susceptible count totalizes the deterministic update, while
the stochastic kernel assigns probability zero to that impossible infection.
-/

@[expose] public section

namespace Freezing1.SIR

structure Counts where
  susceptible : ℕ
  infectious : ℕ
  deriving DecidableEq, Countable

instance : MeasurableSpace Counts := ⊤
instance : DiscreteMeasurableSpace Counts := ⟨fun _ => trivial⟩

def initialCounts (n : ℕ) : Counts := ⟨n, 1⟩
def infectCounts (c : Counts) : Counts := ⟨c.susceptible - 1, c.infectious + 1⟩
def recoverCounts (c : Counts) : Counts := ⟨c.susceptible, c.infectious - 1⟩

def countsStep (c : Counts) (sign : Bool) : Counts :=
  if c.infectious = 0 then c else
    if sign then if c.susceptible = 0 then c else infectCounts c else recoverCounts c

def Counts.Valid (n : ℕ) (c : Counts) : Prop := c.susceptible + c.infectious ≤ n + 1

def Counts.potential (c : Counts) : ℕ := 2 * c.susceptible + c.infectious

/-- Exactly the two possible events before absorption, and holding afterwards. -/
def Counts.LegalNext (c d : Counts) : Prop :=
  (c.infectious = 0 ∧ d = c) ∨
    (0 < c.infectious ∧
      ((0 < c.susceptible ∧ d = infectCounts c) ∨ d = recoverCounts c))

theorem initialCounts_valid (n : ℕ) : (initialCounts n).Valid n := by
  simp [Counts.Valid, initialCounts]

theorem Counts.Valid.infect {n : ℕ} {c : Counts} (hc : c.Valid n)
    (hu : 0 < c.susceptible) : (infectCounts c).Valid n := by
  simp only [Counts.Valid, infectCounts] at *
  omega

theorem Counts.Valid.recover {n : ℕ} {c : Counts} (hc : c.Valid n) :
    (recoverCounts c).Valid n := by
  simp only [Counts.Valid, recoverCounts] at *
  omega

theorem Counts.Valid.step {n : ℕ} {c : Counts} (hc : c.Valid n) (sign : Bool) :
    (countsStep c sign).Valid n := by
  unfold countsStep
  split_ifs with hi hs hu
  · exact hc
  · exact hc
  · exact hc.infect (by omega)
  · exact hc.recover

theorem countsStep_of_absorbed {c : Counts} (hi : c.infectious = 0) (sign : Bool) :
    countsStep c sign = c := by simp [countsStep, hi]

theorem Counts.LegalNext.valid {n : ℕ} {c d : Counts} (h : c.LegalNext d)
    (hc : c.Valid n) : d.Valid n := by
  rcases h with ⟨_, rfl⟩ | ⟨_, ⟨hu, rfl⟩ | rfl⟩
  · exact hc
  · exact hc.infect hu
  · exact hc.recover

theorem Counts.LegalNext.susceptible_le {c d : Counts} (h : c.LegalNext d) :
    d.susceptible ≤ c.susceptible := by
  rcases h with ⟨_, rfl⟩ | ⟨_, ⟨_, rfl⟩ | rfl⟩ <;>
    simp [infectCounts, recoverCounts]

theorem Counts.LegalNext.susceptible_drop_le_one {c d : Counts} (h : c.LegalNext d) :
    c.susceptible ≤ d.susceptible + 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, ⟨_, rfl⟩ | rfl⟩ <;>
    simp [infectCounts, recoverCounts] <;> omega

theorem Counts.LegalNext.absorbed {c d : Counts} (h : c.LegalNext d)
    (hi : c.infectious = 0) : d = c := by
  rcases h with ⟨_, he⟩ | ⟨hp, _⟩
  · exact he
  · omega

theorem Counts.LegalNext.potential_succ {c d : Counts} (h : c.LegalNext d)
    (hi : 0 < c.infectious) : d.potential + 1 = c.potential := by
  rcases h with ⟨hz, _⟩ | ⟨_, ⟨hu, rfl⟩ | rfl⟩
  · omega
  · simp only [Counts.potential, infectCounts]
    omega
  · simp only [Counts.potential, recoverCounts]
    omega

theorem Counts.LegalNext.infectious_pos_previous {c d : Counts} (h : c.LegalNext d)
    (hd : 0 < d.infectious) : 0 < c.infectious := by
  by_contra hn
  have hz : c.infectious = 0 := by omega
  rw [h.absorbed hz] at hd
  omega

theorem legalHistory_absorbed_persists {H : ℕ → Counts}
    (hl : ∀ k, (H k).LegalNext (H (k + 1))) {a : ℕ}
    (ha : (H a).infectious = 0) : ∀ k ≥ a, H k = H a := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [(hl k).absorbed (by rw [ih]; exact ha), ih]

theorem legalHistory_susceptible_bounds {H : ℕ → Counts} {n : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ k, (H k).LegalNext (H (k + 1))) (k : ℕ) :
    n - k ≤ (H k).susceptible ∧ (H k).susceptible ≤ n := by
  induction k with
  | zero => simp [h0, initialCounts]
  | succ k ih =>
    have hle := (hl k).susceptible_le
    have hdrop := (hl k).susceptible_drop_le_one
    constructor <;> omega

/-- The source's count identity is valid before absorption. The clock is
not extended beyond extinction in this statement. -/
theorem legalHistory_count_identity {H : ℕ → Counts} {n k : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ j, (H j).LegalNext (H (j + 1)))
    (hi : 0 < (H k).infectious) :
    (H k).infectious + 2 * (H k).susceptible + k = 2 * n + 1 := by
  induction k with
  | zero => simp [h0, initialCounts, Nat.add_comm]
  | succ k ih =>
    have hp := (hl k).infectious_pos_previous hi
    have hprev := ih hp
    have hpot := (hl k).potential_succ hp
    simp only [Counts.potential] at hpot
    omega

theorem legalHistory_absorbed_by {H : ℕ → Counts} {n : ℕ}
    (h0 : H 0 = initialCounts n) (hl : ∀ k, (H k).LegalNext (H (k + 1))) :
    (H (2 * n + 1)).infectious = 0 := by
  by_contra hn
  have hi : 0 < (H (2 * n + 1)).infectious := by omega
  have hc := legalHistory_count_identity h0 hl hi
  omega

end Freezing1.SIR
