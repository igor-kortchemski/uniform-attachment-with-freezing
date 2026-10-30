# Independent review of the active-height tail integral

The integrating reviewer independently read source lines 1258–1270 and
the complete proofs in `ExponentialMomentTail` and `ActiveHeightTailIntegral`,
written by the source-argument worker. The manuscript hash/scope are unchanged.

The sampled height is the actual forward conditional-uniform-active law.
The normalized error expands to $H/h_n^+-1$; every positive-normalization
inequality assumes exactly $n\ge1$ and strict survival through $n$. The
layer-cake identity uses the closed event $|H/h_n^+-1|\ge u$, as printed.
Measurability and integrability of the actual real weighted tail are proved
from finite-height support and the extended layer-cake theorem. Thus the
actual identity does not rely on assigning zero to divergent real integrals.

The integral is split at 7. Its lower part uses only probability at most
one and the exact real-power integral; its upper part uses the previously
verified closed-threshold Bennett bound with the original rate $g(u)$.
Both parts and the comparison integrals have checked integrability. Open
half-lines change only Lebesgue-null endpoints.

The numerical inequality $e^2-1\le7$ is proved from a Mathlib exponential
bound. It supplies $g(u)\ge u$ for $u\ge7$. Positive dilation is an actual
change-of-variables theorem and proves the literal coefficient $1/m^p$
for $m>0$, with every real $p\ge1$ retained. The tail estimate has the
explicit bound

$$
0\le\int_7^\infty e^{-mu}u^{p-1}\,du
\le 2\,7^{p-1}\frac{e^{-7m}}m
\qquad\left(m>0,\quad m\ge\frac{2(p-1)}7\right).
$$

The constant depends on $p$ alone. The scalar big-O theorem is composed
with the already proved height-scale divergence for admissible varying
schedules. The asymptotic is not a new premise of the height result.

The uniform moment bound is obtained directly from the split-at-seven
integral and the proved $h_n^+\ge1/2$. The remaining constant is finite
by the proved Bennett/Gamma comparison. The $L^p$ upgrade uses this new
bound at exponent $p+1$, the exact probability limit and Hölder/truncation;
it does not invoke the earlier MGF moment estimate as an assumption.

The mathematical A34 claims are verified. A substantive proof departure
remains explicit: the tail asymptotic uses a logarithmic envelope centred
at 7 followed by an exact elementary exponential integral. The paper's
phrase “iterated integration by parts” is not certified as a proof route.
No integer-exponent restriction or omitted remainder is introduced.

`A34IndependentStatements.lean` reconstructs five expanded source types,
including the literal $1/m^p$ scaling, actual integral, varying-row big-O
and real-$p$ limit. Its direct check passes in
`a34-independent-statements.log`; eight axiom closures use only `propext`,
`Classical.choice`, and `Quot.sound`. The worker's separate twelve-example,
fourteen-closure probe is an authored check. Focused artifact builds are
in `labelled-coding-exponential-tail-build.log` and
`active-height-tail-integral-build.log`; the main report records subsequent
full integration evidence separately.
