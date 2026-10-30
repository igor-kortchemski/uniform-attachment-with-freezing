module

public import Freezing1.SIRRandomEnvironmentTransferUniform

/-!
# Uniformization from finite families of deterministic constraints

The index J records how many near-origin and bulk requirements are imposed.
No compactness or probabilistic coupling hypothesis is needed.
-/

@[expose] public section

namespace Freezing1.SIR.RandomEnvironment

open Filter
open scoped Classical

set_option backward.isDefEq.respectTransparency false

theorem uniform_bound_of_sequential_nat {α : Type*}
    (valid : ℕ → α → Prop) (good : ℕ → α → ℕ → Prop) (score : ℕ → α → ℝ)
    (base : ℕ → α) (hbase_valid : ∀ n, valid n (base n))
    (hbase_good : ∀ J, ∀ᶠ n in atTop, good n (base n) J)
    (hmono : ∀ n a {I J : ℕ}, I ≤ J → good n a J → good n a I)
    (hsequential : ∀ rows : ℕ → α, (∀ n, valid n (rows n)) →
      (∀ J, ∀ᶠ n in atTop, good n (rows n) J) →
      Tendsto (fun n => score n (rows n)) atTop (nhds 0))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ J N : ℕ, ∀ n ≥ N, ∀ a, valid n a → good n a J → score n a < eta := by
  by_contra hfail
  push Not at hfail
  have hchoice : ∀ J : ℕ, ∃ n : ℕ, J ≤ n ∧ ∃ a : α,
      valid n a ∧ good n a J ∧ eta ≤ score n a := fun J => hfail J J
  choose index hindex row hvalid hgood hscore using hchoice
  obtain ⟨sub, hsub, hindexsub⟩ := strictMono_subseq_of_id_le hindex
  let selected : ℕ → ℕ := index ∘ sub
  let selectedRows : ℕ → α := row ∘ sub
  let rows : ℕ → α := patchRows selected selectedRows base
  have hselected : StrictMono selected := hindexsub
  have hon (j : ℕ) : rows (selected j) = selectedRows j :=
    patchRows_on hselected.injective selectedRows base j
  have hrows_valid : ∀ n, valid n (rows n) := by
    intro n
    dsimp only [rows, patchRows]
    split_ifs with hex
    · have he := hex.choose_spec
      have hh := hvalid (sub hex.choose)
      change valid (selected hex.choose) (selectedRows hex.choose) at hh
      exact Eq.mp (congrArg (fun m => valid m (selectedRows hex.choose)) he) hh
    · exact hbase_valid n
  have hrows_good : ∀ J, ∀ᶠ n in atTop, good n (rows n) J := by
    intro J
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hbase_good J)
    filter_upwards [eventually_ge_atTop (max (selected J) N)] with n hn
    by_cases hex : ∃ j, selected j = n
    · obtain ⟨j, rfl⟩ := hex
      rw [hon]
      have hj : J ≤ j := hselected.le_iff_le.mp ((le_max_left _ _).trans hn)
      exact hmono _ _ (hj.trans (hsub.id_le j)) (hgood (sub j))
    · have hoff : rows n = base n := by simp only [rows, patchRows, dite_eq_right hex]
      rw [hoff]
      exact hN n ((le_max_right _ _).trans hn)
  have hlimit := (hsequential rows hrows_valid hrows_good).comp hselected.tendsto_atTop
  obtain ⟨j, hj⟩ := (hlimit.eventually (eventually_lt_nhds heta)).exists
  change score (selected j) (rows (selected j)) < eta at hj
  rw [hon] at hj
  exact (not_lt_of_ge (hscore (sub j))) hj

end Freezing1.SIR.RandomEnvironment
