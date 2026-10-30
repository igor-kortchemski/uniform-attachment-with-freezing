module

import Freezing1
import Freezing1.BernoulliPairCouplingComplete
import Freezing1.SIRCaptureCoefficientBirthBridge
import Freezing1.SIRFirstContactIrrelevance
meta import Lean.Elab.Command
meta import Lean.Util.CollectAxioms

/-! Independent review check including every current proof module, even those
outside the default entry-point import closure. This is not kernel replay. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if (`Freezing1).isPrefixOf name then
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "Forbidden axiom {axiomName} in {name}"
      checked := checked + 1
  logInfo m!"Checked {checked} Freezing1 declarations across all proof modules; only propext, Classical.choice, Quot.sound."
