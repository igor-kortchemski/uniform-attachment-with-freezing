# A24: all-vertex degree obstruction, implementing self-review

Source lines 912–921 use an increasing subsequence whose schedules agree
on longer prefixes, a prefix coupling, and positive-probability degree
divergence to rule out local weak convergence. This review is by the
author of the new modules and is explicitly self-review.

`ForwardDegreeCoupling` constructs a strictly increasing extraction
with both matching prefixes and `n ≤ φ n`. For every extracted row it
supplies an actual pair of full-history laws with the correct marginals;
their prefixes agree and each fixed-schedule degree is bounded above by
the row degree at its terminal horizon. This is a family of pair
couplings. A single joint coupling of all rows with one fixed trajectory
is not asserted.

`ForwardDegreeDivergence` uses actual monotonicity of each vertex degree,
including after absorption. A positive probability of an unbounded
degree yields one positive real mass above every finite threshold in all
sufficiently late marginals. Continuity from below is applied to finite
prefix unions, which monotonicity identifies with the last marginal.
Unboundedness is separately proved equivalent to divergence under this
monotonicity hypothesis.

`LocalBallTightness` proves continuity of the finite-ball cardinality and
tail tightness of any continuous natural-valued observable under weak
convergence. Every actual vertex with birth ID `r` has degree at most
the cardinality of the ball of radius `r + 1`: its height is at most its
birth ID and its neighbours lie in the next ball.

`MainLocalDegreeNecessity` transfers the positive tails to diagonal row
marginals using exact prefix laws and degree monotonicity, and contradicts
local-ball tightness. It obtains almost-sure existence of a local limit
for the fixed trajectory from boundedness of all actual vertex degrees.
No freezing-series criterion, root-specific obstruction or diagonal
nonextinction premise is used. The conclusion is almost-sure existence
of a chronological local limit; the earlier main theorem supplies the
measurable common limit law separately.

This follows the source's all-vertex degree obstruction and verifies its
increasing extraction and pair-coupling ingredients. The final
contradiction uses marginal tail tightness. It avoids inferring
divergence of a nonmonotone diagonal sequence merely from a positive
probability that its supremum is infinite. The manuscript's displayed
union-event argument is not certified literally.

The authored `A24AllVertexStatements.lean` contains four expanded
examples and eight axiom closures; its durable output is
`a24-all-vertex-statements.log`. All closures use only the three permitted
axioms. Focused artifact builds passed for the degree-divergence,
degree-coupling and final necessity modules; the final build is
`unordered-topology-source-geometry-local-necessity-build.log` (3,952 jobs).
The chronological-to-unordered ambient bridge remains a separate active
dependency. No whole-paper or publication completion is claimed.
