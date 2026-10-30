# Independent review of the A28 probability assertions

The integrating agent independently read the unchanged source paragraph at
lines 973–979 and the coupling, critical extinction, infinite iid product,
drift, density and local-criterion proofs. This reviewer did not author
these modules. The author's separate self-review retains its provenance.

The exported law is `Measure.infinitePi` of the actual Bernoulli sign law.
The unused coordinate zero is ignored and the integer walk starts at one.
Raw zero crossing is distinguished from the absorbing natural-valued walk.
The finite-horizon raw event is transferred through the actual finite iid
word mixture and chronological forward projection. Increasing unions then
transfer ever-extinction probabilities. This justifies the critical endpoint
and is stronger evidence than comparing one-time means or postulating a
matching path law.

The monotone coupling uses an explicit three-atom joint sign law. Its two
complete projected walk laws are proved, as is pathwise order. Comparing
with supercritical probabilities approaching one proves extinction for
$p\le1/2$, including both boundary cases. This supplies the standard random
walk assertion the paper invokes without proof.

For $1/2<p<1$, Mathlib's strong law is applied to bounded observables of
the unconditional independent coordinates, giving drift $2p-1$ and freezing
frequency $1-p$. The deterministic density criterion proves divergence of
the exact printed freezing reciprocal series. Restricting these established
almost-sure assertions to nonextinction then discharges T01's assumptions.
There is no assumption of independence after conditioning on survival.
Actual holding after extinction handles the complementary event. Thus the
paper's two-case local-convergence argument is now checked, independently
of the earlier annealed hazard route.

`A28IndependentStatements.lean` reconstructs the actual infinite-product
extinction theorem and the source never-zero formulation of the conditional
local criterion. Its evidence is `a28-independent-statements.log`.
The broader author probe has five expanded examples and thirteen permitted
axiom closures in `a28-probability-statements.log`. Consecutive increasing
reindexing of labels is a distinct A28 obligation and is not certified here.
