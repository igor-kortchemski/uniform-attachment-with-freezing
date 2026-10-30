# Labelled clock race to infection-tree kernel: proof record

Date: 29 October 2026. Implemented module: `SIRClockTreeProjection.lean`.
Source scope: A65/A66, the count and tree law asserted after the physical
model at source lines 2026–2042. This is an implementation proof record;
independent statement reconstruction and the complete history transport
are separate.

For a valid labelled population state, write $A$ and $U$ for its numbers
of infectious and susceptible individuals. The already proved actual
clock-race law chooses each live recovery slot with probability
$1/(A(1+rU))$ and each live directed contact slot with probability
$r/(A(1+rU))$, where $r>0$. These are singleton laws derived from the
independent exponential race, rather than an assumed abstract selection
kernel.

The new export `clockChoiceLaw_project hr hz` proves exactly

$$
\operatorname{Law}(\operatorname{project}(\operatorname{step}(z,C)))
=P_r(\operatorname{project}(z),\cdot),
$$

where $C$ has the actual `clockChoiceLaw r z` and $P_r$ is the existing
`treeKernel` with parameter $\langle r,0\le r\rangle$. It has only positive
rate and valid-population hypotheses. It assumes neither an embedded
kernel equality nor a uniform infector conclusion.

The proof expands the finite actual choice law into singleton weights.
When $A>0$, the projection of a live contact depends on its source's
genealogical address and the infection sign; it does not depend on the
susceptible recipient's individual label. Summing over the $U$ recipients
therefore gives, for each active source, the coefficients

$$
\frac{rU}{A(1+rU)}
=\frac1A\frac{rU}{1+rU},
\qquad
\frac{1}{A(1+rU)}
=\frac1A\frac{1}{1+rU}.
$$

The independent helper `SIRPopulationUniformActor.lean` proves that the
valid injective address map sends a uniformly chosen active individual
to a uniformly chosen active genealogical vertex. Its exact signed-law
sum is then the same sum as the projected clock race, with the two
coefficients above. The susceptible-zero case is included: its contact
sum vanishes and recovery has probability one. If $A=0$, the actual
choice law selects holding, and both projected and existing tree kernels
are the same Dirac measure.

This theorem supplies the one-step intertwining needed by the separate
static-word/full-history transport. It does not infer whole-history
equality from this marginal alone. The independent residual and complete
word-history proofs must be used to identify the original static array's
history, which is the separate source worker's responsibility.

The actual-file direct check passes without diagnostics; evidence is
retained in `sir-clock-tree-projection-direct.log`. All four probed axiom
closures contain exactly `propext`, `Classical.choice`, and `Quot.sound`;
evidence is retained in `sir-clock-tree-projection-axioms.log`. Root
integration and independent statement reconstruction are recorded separately.
