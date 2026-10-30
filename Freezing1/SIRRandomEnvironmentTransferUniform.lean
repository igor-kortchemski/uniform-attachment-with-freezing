module

public import Freezing1.MainLinearDistance
public import Freezing1.BalancedSchedule

/-!
# A deterministic uniformization principle for random environments

Every bad sequence of increasingly accurate finite environments can be
inserted into distinct observation rows. Filling the remaining rows by a
verified reference environment lets a deterministic asymptotic theorem
rule out that bad sequence. No probabilistic coupling theorem is assumed.
-/

@[expose] public section

namespace Freezing1.SIR.RandomEnvironment

open Filter
open scoped Classical

set_option backward.isDefEq.respectTransparency false

noncomputable def patchRows {α : Type*} (index : ℕ → ℕ) (row base : ℕ → α) : ℕ → α :=
  fun n => if h : ∃ j, index j = n then row h.choose else base n

theorem patchRows_on {α : Type*} {index : ℕ → ℕ} (hindex : Function.Injective index)
    (row base : ℕ → α) (j : ℕ) : patchRows index row base (index j) = row j := by
  have hex : ∃ i, index i = index j := ⟨j, rfl⟩
  rw [patchRows, dite_eq_left hex]
  have hi : hex.choose = j := hindex hex.choose_spec
  rw [hi]

/-- Sequential deterministic asymptotics imply a finite uniform good-row
criterion. The reference rows satisfy every eventual accuracy constraint.
The accuracy predicate must increase with its error tolerance. -/
theorem uniform_bound_of_sequential {α : Type*}
    (valid : ℕ → α → Prop) (good : ℕ → α → ℝ → Prop) (score : ℕ → α → ℝ)
    (base : ℕ → α) (hbase_valid : ∀ n, valid n (base n))
    (hbase_good : ∀ e > 0, ∀ᶠ n in atTop, good n (base n) e)
    (hmono : ∀ n a {e d : ℝ}, e ≤ d → good n a e → good n a d)
    (hsequential : ∀ rows : ℕ → α, (∀ n, valid n (rows n)) →
      (∀ e > 0, ∀ᶠ n in atTop, good n (rows n) e) →
      Tendsto (fun n => score n (rows n)) atTop (nhds 0))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ e > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ a, valid n a → good n a e → score n a < eta := by
  by_contra hfail
  push Not at hfail
  have hchoice : ∀ j : ℕ, ∃ n : ℕ, j ≤ n ∧ ∃ a : α,
      valid n a ∧ good n a (1 / ((j : ℝ) + 1)) ∧ eta ≤ score n a := by
    intro j
    exact hfail (1 / ((j : ℝ) + 1)) (by positivity) j
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
  have htol : Tendsto (fun j : ℕ => 1 / ((sub j : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hsub.tendsto_atTop
  have hrows_good : ∀ e > 0, ∀ᶠ n in atTop, good n (rows n) e := by
    intro e he
    obtain ⟨J, hJ⟩ := eventually_atTop.mp (htol.eventually (eventually_lt_nhds he))
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hbase_good e he)
    filter_upwards [eventually_ge_atTop (max (selected J) N)] with n hn
    by_cases hex : ∃ j, selected j = n
    · obtain ⟨j, rfl⟩ := hex
      rw [hon]
      have hj : J ≤ j := hselected.le_iff_le.mp ((le_max_left _ _).trans hn)
      exact hmono _ _ (hJ j hj).le (hgood (sub j))
    · have hoff : rows n = base n := by simp only [rows, patchRows, dite_eq_right hex]
      rw [hoff]
      exact hN n ((le_max_right _ _).trans hn)
  have hlimit := (hsequential rows hrows_valid hrows_good).comp hselected.tendsto_atTop
  obtain ⟨j, hj⟩ := (hlimit.eventually (eventually_lt_nhds heta)).exists
  change score (selected j) (rows (selected j)) < eta at hj
  rw [hon] at hj
  exact (not_lt_of_ge (hscore (sub j))) hj

end Freezing1.SIR.RandomEnvironment
