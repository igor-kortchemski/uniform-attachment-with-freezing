module

import Freezing1

/-!
# Axiom closure of the exported main results T01–T07

One `#print axioms` per exported conclusion of Theorems `thm:cvlocale` (T01), `thm:BGW` (T02),
`thm:height` (T03), `thm:lineaire` (T04), `thm:samelaw` (T05), `thm:SIRlocallimit` (T06) and
`thm:SIR` (T07). Every line must report exactly `[propext, Classical.choice, Quot.sound]`.
This is an axiom-closure report of the pinned toolchain; it is not an independent kernel replay.
-/

-- T01
#print axioms Freezing1.local_convergence_equivalences
#print axioms Freezing1.local_convergence_common_limit
-- T02
#print axioms Freezing1.ForwardAnnealed.iid_signs_geometric_local_limit
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_isBienayme
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_eq_geometricBienaymeLaw
#print axioms Freezing1.ForwardAnnealed.planeLimitLaw_offspring_mass
-- T03
#print axioms Freezing1.uniform_active_height_tendsto_Lp
#print axioms Freezing1.maximum_height_window_tendsto_one
#print axioms Freezing1.maximum_height_tendsto_Lp
-- T04
#print axioms Freezing1.linear_heightScale_tendsto
#print axioms Freezing1.linear_uniform_height_tendsto_Lp
#print axioms Freezing1.linear_uniform_distance_tendsto_Lp
#print axioms Freezing1.linear_maximum_deviation_tendsto_zero
#print axioms Freezing1.linearHeightFactor_existsUnique
#print axioms Freezing1.linearHeightFactor_spec
-- T05
#print axioms Freezing1.CanonicalTree.construction_laws_eq
-- T06
#print axioms Freezing1.SIR.physical_sir_geometric_local_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_not_tight_of_source_ratio
-- T07
#print axioms Freezing1.SIR.physical_sir_fluid_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_uniform_height_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_uniform_distance_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_strong_uniform_fluid_limit_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_strong_terminal_uniform_height_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_strong_terminal_uniform_distance_of_source_ratio
#print axioms Freezing1.SIR.physical_sir_strong_terminal_maximum_of_source_ratio
-- non-vacuity of the physical SIR hypothesis (not a manuscript statement)
#print axioms Freezing1.SIR.PoissonSIRData.exists_data
