# A85 one-susceptible checkpoint

Stopped at the user's request on 2026-10-30. No new mathematical work or
artifact builds should be inferred from this checkpoint. The parent alone
coordinates artifact-writing builds and global coverage records.

## Verified foundation

- `Freezing1/SIROneSusceptibleLaw.lean` is frozen, actual-file direct Lean
  PASS0, and built by the parent. It derives the entire actual stopped
  counts-history law starting from susceptible count one and infectious
  count $m$ as the pushforward of a recursively constructed first-infection
  time law. The final theorem is `law_eq_firstTimeLaw_map`. No geometric
  word probabilities or path-law conclusion are assumed.
- `Freezing1/SIROneSusceptibleLastNegative.lean` is frozen, actual-file direct
  PASS0, and built by the parent. It proves last-negative-position and
  gate-complement probabilities from the actual unconditional iid sign
  law. Exports include `iid_lastNegative_probability` and
  `iid_lastNegativeGate_compl_probability`.

The root's current global build session 44711 includes these two modules
only from the new one-susceptible chain. Earlier five reverse-gap and
formulation modules were already integrated; see
`SIR_REVERSE_COUPLING_PROGRESS.md`.

## Newer source saved, integration not certified

All names below are in namespace `Freezing1.SIR.OneSusceptible`.

1. `Freezing1/SIROneSusceptibleFirstTime.lean` proves the recursively
   derived truncated-geometric masses, support, actual first zero of the
   explicit history `run`, and the reversed-birth identity
   `run_reverse_birth_iff`. A temporary exact-source concatenation passed
   with one unused-binder warning; that binder was renamed `_hj`.
   The subsequent ordinary actual-file direct check wrote
   `/tmp/sir-one-susceptible-first-time.log`, currently empty. Its final
   process exit was not collected before the stop; recheck this file
   normally before declaring it frozen.
2. `Freezing1/SIROneSusceptibleTimeCoupling.lean` defines the explicit
   noncausal joint measure `timeSignCoupling` on first-infection times and
   complete iid sign sequences. It proves its exact unconditional iid
   marginal, `timeSignCoupling_map_snd`, and required residual masses.
   The latest completed exact-source concatenation passed with only the
   now-corrected unused binder warning from FirstTime:
   `/tmp/sir-one-susceptible-time-coupling-concat3.log`.
3. `Freezing1/SIROneSusceptibleCouplingMarginals.lean` proves
   `timeSignCoupling_map_fst` for $m\geq2$ and
   `timeSignCoupling_probability`. Two local proof repairs were applied
   after the first concatenation: an explicit natural exponent identity,
   and evaluating the known iid marginal at the universe before invoking
   probability mass. The newest exact-source concatenation log is
   `/tmp/sir-one-susceptible-coupling-marginals-concat2.log`, currently
   empty. Its final process exit was not collected before the stop.

The two uncollected checks were launched before the stop request. Their
session IDs were lost in context compaction. Do not invent a session ID or
treat empty logs as collected PASS evidence. No further checks or proof
edits were started after the stop request. No one-susceptible axiom probe
or final imported coupling check has yet been run.

## Exact construction and remaining proof

Write $p=r/(1+r)$ and $q=1-p$. First-infection time zero means no infection;
its mass is $q^m$. Times $1\leq t\leq m$ have mass $pq^{t-1}$.
For an iid sign sequence with false probability $p$, let $L$ be its last
false position in $1,\ldots,m$, defaulting to zero. On $G=\{L\geq3\}$,
choose $t=m+3-L$ and retain mass $q^2$. This matches exactly the masses at
times $3,\ldots,m$.

The residual time measure is supported on $0,1,2$, with unnormalized
masses $q^m,p,pq$. Its total is $D=q^m+p+pq>0$. Pair its normalized version
with the residual auxiliary measure

$$
(1-q^2)\mu+q^2\mu\vert_{G^c},
$$

whose total is $D$ for $m\geq2$. The main and residual parts together have
the exact iid auxiliary marginal. This construction is saved in the
sources; the domination and actual-history wrapper remain unwritten.

Next proof steps:

1. Prove almost-everywhere reversed-birth domination on indices
   $1\leq j\leq m$ under `timeSignCoupling`. For the main part, the
   reversed-birth identity forces $j=L$, so the auxiliary sign is false.
   For the residual part, infection times at most two have no reversed
   birth in this index range, by
   `run_reverse_birth_impossible_of_le_two`.
2. Push the joint measure forward by `(t,x) ↦ (run m t,x)`. Derive its
   entire actual stopped-history marginal using
   `timeSignCoupling_map_fst` and `law_eq_firstTimeLaw_map`; retain the exact
   iid marginal using `timeSignCoupling_map_snd`. Express extinction with
   the proved `extinctionIndex m = boundedExtinctionIndex (m+2)` carrier.
3. Handle $m=0,1$ separately if an all-$m$ theorem is desired: the
   relevant reversed-birth range is empty, so an independent product
   coupling should suffice.
4. Ask the parent to build the newly frozen modules, then run ordinary
   imported statement reconstructions and permitted-axiom closures.

The general multi-susceptible/source-gate `SourceReverseIidCoupling`
existence assertion, A85, and the future-conditioned A86 argument remain
open. The proved window-hazard-inheritance counterexample does not
refute that weaker coupling. This one-susceptible construction is partial
progress, not a general coupling theorem or publication-completeness claim.
