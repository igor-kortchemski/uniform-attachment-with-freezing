# SIR interface: Challenge and Solution notes

Files: `Challenge/Sir.lean` (module `Challenge.Sir`), `Solution/Sir.lean` (module `Solution.Sir`),
`comparator/sir.json`. Evidence of the local diagnostic: `compare.log`, `run.log`, `leanchecker.log`
in this directory. Generation and debugging helpers: `tools/`.

Size of the Challenge: 964 lines, 54,188 bytes (limits: 1000 lines, 100 KiB). Single module (no split
into weak/strong parts was needed). It contains about 150 declarations, 11 of them with `sorry` (the targets).

## Target theorems (11)

Manuscript: `attachement-uniforme-1-final.tex`, Theorem `thm:SIRlocallimit` (lines 2047-2054) and
Theorem `thm:SIR` (lines 2080-2104). All statements are the physical, full-contact versions in
namespace `Freezing1.SIR`, for clock data `X n c` on abstract probability spaces `Ω n` under
`PoissonSIRData (mu n) n (rate n) (X n)` (assumed only for large `n`).

| Lean target | Source module | Manuscript item |
| --- | --- | --- |
| `physical_sir_geometric_local_limit_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIRlocallimit` (I) |
| `physical_sir_not_tight_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIRlocallimit` (II) |
| `physical_sir_fluid_limit_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIR` (I)(a) |
| `physical_sir_uniform_height_limit_of_source_ratio` | `SIRPhysicalFiniteLimits` | `thm:SIR` (I)(b), height |
| `physical_sir_uniform_distance_limit_of_source_ratio` | `SIRPhysicalFiniteLimits` | `thm:SIR` (I)(b), distance |
| `physical_sir_strong_uniform_fluid_limit_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIR` (II)(a) |
| `physical_sir_strong_terminal_uniform_height_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIR` (II)(b), `H(V_1)/ln n` |
| `physical_sir_strong_terminal_uniform_distance_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIR` (II)(b), `d(V_1,V_2)/ln n` |
| `physical_sir_strong_terminal_maximum_of_source_ratio` | `SIRPhysicalLimits` | `thm:SIR` (II)(b), `Height/ln n` |

Two extra targets (sanity checks on the meaning of the hypothesis `PoissonSIRData`, not manuscript
statements; both are existing project theorems, compared by statement only):

* `Freezing1.SIR.PoissonContact.first_law` (`SIRPoissonFirstArrival`): Poisson counting marginals of
  intensity `r > 0` give an exponential(`r`) first arrival.
* `Freezing1.SIR.PoissonSIRData.treePathLaw_eq` (`SIRPhysicalLaws`): under `PoissonSIRData` and a positive
  rate, the physical history `(susceptible count, infection tree)` has the law `treeFullLaw rate n` of the
  chain "sign drawn with probability `lambda_n U/(1+lambda_n U)`, then applied at a uniformly chosen active
  vertex", i.e. the uniform attachment with freezing driven by the manuscript's Markov chain.

There is NO existence lemma for `PoissonSIRData` in the project (no construction of independent Poisson
processes on a common probability space), so the non-vacuity of the hypothesis is not established in Lean.
The theorem `PoissonSIRData.countsPathLaw_eq` (physical counts history = the manuscript's chain `(U, I)`) also
exists; it was not added because it costs about 70 more lines (the chain definitions `countsKernel`,
`countsFullLaw`, `CountableMarkovChain.fullLaw`, ...) and would exceed 1000 lines together with the tree law.
It can replace the tree law target (set `COUNTS=1 TREE=0` in `tools/sir_spec.py`; it needs `setMainModule` for
`Freezing1.SIRCounts`, already in the generator).

## Imports

Only Mathlib: `Mathlib.Tactic`, `Mathlib.Tactic.DeriveCountable`, `Mathlib.Topology.MetricSpace.Polish`,
`Mathlib.MeasureTheory.Constructions.BorelSpace.Basic`, `Mathlib.SetTheory.Descriptive.Tree`,
`Mathlib.Probability.Distributions.{Geometric,Bernoulli,Uniform,Exponential,Poisson.Basic}`,
`Mathlib.Probability.Independence.{InfinitePi,Basic}`, `Mathlib.Probability.Kernel.IonescuTulcea.Traj`,
`Mathlib.MeasureTheory.{Measure.Prod,Constructions.Pi,Measure.Tight,Measure.ProbabilityMeasure,
Integral.Lebesgue.DominatedConvergence}`, `Mathlib.Combinatorics.SimpleGraph.Metric`,
`Mathlib.Analysis.SpecialFunctions.{ExpDeriv,Log.Deriv}`,
`Mathlib.Analysis.Calculus.{Deriv.Inverse,ContDiff.Deriv}`, `Mathlib.Analysis.Convex.Deriv`,
`Mathlib.Analysis.SpecificLimits.Basic`, `Mathlib.Topology.Order.{IntermediateValue,MonotoneContinuity}`,
`Mathlib.Topology.UniformSpace.UniformConvergenceTopology`, `Mathlib.Topology.UnitInterval`,
`Mathlib.Order.Hom.Set` (the union of the Mathlib imports of the source modules involved).

## Copied declarations (verbatim source text, same `open`/`set_option` context as the source module)

* `PlaneTree`: `Address` (+ discrete measurable space), `Offspring`, `Canonical`, `Tree` (+ Borel), `degree`,
  `leaf`, `child`. `PlaneTreeGeometry`: `Present`. `PlaneTreePruning`: `pruneRaw`, `canonical_pruneRaw`,
  `prune`. `PlaneBienaymeLaw`: `offspringFieldLaw`, `bienaymeLaw`, `geometricBienaymeLaw` (+ `_probability`
  instances). `PlaneFiniteExtinction`: `FiniteVertices`.
* `PlaneFiniteState`: `State`, `initial`, `children`, `childCount`, `newChild`, `attach`, `freeze`.
  `PlaneStateValidity`: `Valid`, `children_eq_empty_of_not_mem`, `childCount_zero_of_not_mem`,
  `childCount_canonical`, `shape`. `FiniteUniformPairs`: `uniformOfFinset_probability`. `PlaneFiniteGraph`:
  `parentGraph`, `pairDataKernel`, `pairDataKernel_markov`. `ForwardPlaneKernel`: `uniform_active_probability`.
  `InterleavedChainCylinders`: `wordMeasurableSpace`, `wordMeasurableSingletonClass`.
  `MainSIRUniformHeightStrong`: `vertexHeightKernel`, `vertexHeightKernel_markov`.
* `SIRCounts`: `Counts`. `SIRTreeState`: `TreeState`, `initialTreeState`, `infectTreeState`,
  `recoverTreeState`, `treeStep`. `SIRClockPopulation`: `Individual`, `ClockSlot`, `PopulationState`,
  `project`, `initialPopulation`, `availableTargets`, `liveSlots`. `SIRClockPopulationUpdates`:
  `infectPopulation`, `recoverPopulation`, `populationStep`. `SIRProbability`: `infectionFraction`
  (+ two bounds), `infectionProbability`. `SIRFluidProfile`: `expLinear` (+ three lemmas), `expLinearIso`,
  `fluidProfile`, `infectiousProfile`. `SIRPathSpace`: `timeWindow(s)`, `PopulationPath` (+ Borel),
  `populationPathOfWord`, `scaledPopulationPath`, `positiveProfilePath`, `zeroPopulationPath`.
  `SIRGeometricSurvivalPath`/`Scalar`: `geometricSurvivalPath(Law)`, `geometricSurvivalScalar(Law)`.
  `MainSIRLocalLimit`: `geometricProbabilityLaw`.
* `InterleavedChainKernel`: `historyKernel` (+ Markov), `fullLaw`. `SIRTreeLaw`: `signedTreeLaw`
  (+ probability), `treeKernel` (+ Markov), `treeFullLaw`.
* `SIRPoissonFirstArrival`: `ArrivalPath` (+ sigma-algebra), `first`, `exists_later`, `count`,
  `HasPoissonCounts`. `SIRPreassignedClocks`: `ClockArray`, `StrictLiveWinner`, `firstLiveClock`,
  `ClockFrame` (+ projections), `initialClockFrame`, `remainingClock`, `advanceClockFrame`, `clockFrameStep`.
  `SIRPoissonClockArray`: `ClockDatum`, `clockDatum_measurableSpace`, `PoissonClockData`.
  `SIRPoissonFullContacts`: `PoissonContact.nextArrival`, `nextContactDelayArray`, `poissonFullContactStep`,
  `poissonFullContactRun`. `SIRPoissonFullContactLaw`: `poissonFullContactTreePath`.
  `SIRPhysicalLaws`: `PoissonSIRData`, `physicalTreePathLaw`, `physicalCountsPathLaw`,
  `physicalTerminalTreeLaw`, `physicalPopulationPathLaw`, `physicalUniformHeightLaw`, `physicalPairDataLaw`.
  `SIRPhysicalFiniteLimits`: `physical_sampleLaw_probability` (+ two instances),
  `physicalTerminalUniformHeightScaledLaw`, `physicalTerminalUniformDistanceScaledLaw`.

## Adjustments needed for the comparison (all invisible to the statements)

The first attempt (verbatim copy, one `namespace` block per source module) failed on 10 reachable
constants. Reason (checked with `tools/ListMismatch.lean`, which lists ALL mismatches instead of stopping
at the first): Lean derives some auxiliary names from the module being compiled, and the Challenge is a
single module while the development has about 40 modules. Two phenomena:

1. Private auxiliary declarations carry the module name (`_private.Freezing1.PlaneFiniteGraph.0...`,
   `..._hyg...` names). They come from `omega` and `simp` inside definition bodies
   (`parentGraph._proof_3`, `populationPathOfWord._proof_2`), from `simp` inside reachable theorems
   (`uniformOfFinset_probability`, `vertexHeightKernel_markov`, `uniform_active_probability`) and from
   `deriving Countable` (`instCountableState`, `instCountableTreeState`; also `instCountableCounts` if the
   counts chain is added). Fix: `run_cmd Lean.modifyEnv (·.setMainModule `Freezing1.<Module>)` before the
   corresponding block (modules `PlaneFiniteState`, `FiniteUniformPairs`, `PlaneFiniteGraph`,
   `ForwardPlaneKernel`, `MainSIRUniformHeightStrong`, `SIRTreeState`, `SIRPathSpace`) and the same command
   with `Challenge.Sir` at the end of the file. The text of the blocks is unchanged and the produced
   constants are then identical.
2. Within one module Lean reuses an earlier matcher or auxiliary proof with the same body, whereas the
   development, being split in modules, has one per module: `populationStep.match_1`, `ClockDatum.match_1`,
   `advanceClockFrame.match_1` (same shape `match c.2 with | none | some`), `Present.match_1`,
   `pruneRaw.match_1` (list patterns), and `geometricSurvivalPathLaw._proof_1` /
   `geometricSurvivalScalarLaw._proof_1` (same proof). Fixes:
   * `pruneRaw` is elaborated before `Present` (the Challenge's order of the two blocks is swapped), and
     `Present` and `ClockDatum` get `set_option bootstrap.genMatcherCode false in` (the matcher cache is keyed
     by this option, so they get their own matcher; no statement or kernel term is affected);
   * the matcher `advanceClockFrame.match_1` is written out (`abbrev`, `Option.casesOn`, universe
     `u_1`, exactly the kernel term of the generated matcher) and used explicitly in `advanceClockFrame`;
   * `geometricSurvivalScalarLaw._proof_1` is written out as a theorem (`inferInstance`) and used explicitly.
   `linter.style.haveILetI` and `linter.auxLemma` are turned off (warnings only).

Other differences with the development: several modules with the same context are merged into one block
(`PlaneFiniteState`+`PlaneStateValidity`, `SIRClockPopulation`+`SIRClockPopulationUpdates`,
`SIRGeometricSurvivalPath`+`Scalar`); declarations not reachable from the statements are omitted (e.g.
`PolishSpace Tree`, `T2Space PopulationPath`, `PopulationState.Valid`); docstrings were added; blank lines
were removed. None of this is visible to Comparator (checked by the diagnostic).

If the use of `run_cmd` in a Challenge is not acceptable for Palomar, the alternatives are in the
development: avoid `omega`/`simp`/`deriving` inside the bodies of reachable definitions and instances
(state them as named lemmas and add the named lemmas to `theorem_names`), and write the three `match`
expressions so that they do not produce identical matchers within one module.

## Diagnostic (local, not the official Comparator)

```
scripts/local-comparator-diagnostic.sh comparator/sir.json <scratch>/sir-diag
compare: statements and reachable constants match
axioms: only permitted axioms
leanchecker exit=0
```
(see `compare.log`, `run.log`, `leanchecker.log`; about 5 minutes). Direct check
`lake env lean -DautoImplicit=false Challenge/Sir.lean`: only the 11 `declaration uses sorry` warnings.
Build `bl.sh Challenge.Sir Solution.Sir`: success. Not run: the official `lake comparator` (needs the Linux
sandbox) and the other bundled checkers.

## Reproduction of the Challenge text

`tools/sir_spec.py` (specification: exact line ranges of the source modules plus docstrings) and
`tools/gen_sir.py`:
`BLANK_AFTER=12 COUNTS=0 TREE=1 FIRST=1 python3 tools/gen_sir.py tools/sir_spec.py Challenge/Sir.lean`.
`tools/ListMismatch.lean` (compile with `lake env lean --root=<its directory> -c x.c ListMismatch.lean` and
link as in `scripts/local-comparator-diagnostic.sh`) prints every reachable constant that differs, with
missing constants, instead of stopping at the first.

## Statement-fidelity remarks collected while copying (no fix attempted)

See the final report of the worker; summary: (a) the hypothesis `PoissonSIRData` is not shown satisfiable;
(b) it only prescribes marginals (`HasPoissonCounts` = law of the count at each fixed time), which suffices
for the protocol because only the first arrival after infection of a live pair matters; (c) the physical
protocol is totalized (holds when no strict live winner), ties have probability zero.

## After the independent review and the existence proof (30 October 2026)

* Non-vacuity closed: `Freezing1.SIR.PoissonSIRData.exists_data` and `exists_family` are targets of `comparator/sir.json`
  (13 names, 13 `sorry` bodies); proofs in `Freezing1/SIRPoissonExistence*.lean`, notes `EXISTENCE_NOTES.md`. The Challenge is now
  992 lines. The existence theorem requires `0 < rate`; at rate `0` the hypothesis is unsatisfiable (also proved in Lean:
  `PoissonSIRData.false_of_rate_zero`).
* Docstrings of `PoissonSIRData` and the header corrected (reviewer F7, F8, C3): positivity of the rate is forced; only count
  marginals are prescribed (enough because the protocol reads first points only); the counts history `(U, I)` is read as
  (susceptibles, active vertices) and is not pinned (F3, not done: `countsPathLaw_eq` would cost about 70 lines).
* The metaprogramming devices (F2) remain; disclosed in `formalization.yaml` and `../OPEN_OBLIGATIONS.md`.
