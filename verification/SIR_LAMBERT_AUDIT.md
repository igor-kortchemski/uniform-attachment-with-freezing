# Independent audit of the principal Lambert inverse in A70

Audit target: `Freezing1/SIRLambertW.lean`, compared with
`attachement-uniforme-1-final.tex`, lines 2118–2121, and the already constructed
profile in `SIRFluidProfile.lean`. This review does not certify any stochastic
fluid-limit assertion in T07.

## Source and formal statements

The source uses the principal branch
$W:[-e^{-1},\infty)\to[-1,\infty)$ of the inverse of $w\mapsto we^w$. It states
the formula for $g_\lambda(t)$ for $t\geq0$, with the positive parameter
inherited from T07. The implemented formula has the stronger domain
$\lambda>0$ and $t\in\mathbb R$.

| Obligation | Implementation checked | Finding |
| --- | --- | --- |
| Principal branch, including the branch endpoint | `lambertMap_strictMonoOn`, `lambertMap_surjOn`, `lambertMapIso` | Correct: the inverse is constructed on $[-1,\infty)$, with image domain $[-e^{-1},\infty)$. |
| Inverse equation on the real domain | `lambertMap_principalLambertW`, `principalLambertW_eq_of_characterization`, `principalLambertW_lambertMap` | Correct: all inverse claims carry the necessary domain or branch premise. |
| Value at the branch endpoint | `principalLambertW_left_endpoint` | Correct: $W(-e^{-1})=-1$. |
| Monotonicity and continuity | `principalLambertW_strictMonoOn`, `principalLambertW_continuousOn` | Correct on the full closed real domain. |
| Interior derivative | `principalLambertW_hasDerivAt` | Correct for $x>-e^{-1}$; its expression $[e^{W(x)}(1+W(x))]^{-1}$ includes $x=0$. |
| Printed quotient derivative | `principalLambertW_deriv_quotient` | Correct for $x>-e^{-1}$ and $x\ne0$. These restrictions must be retained when citing the source. |
| Derivative at zero | `principalLambertW_hasDerivAt_zero` | Correct: $W'(0)=1$. |
| Explicit fluid profile | `fluidProfile_lambertW` | Correct: $g_\lambda(t)=\lambda^{-1}W(\lambda e^\lambda e^{-\lambda t})$ for every real $t$ and every $\lambda>0$. |

The function is totalized to $-1$ below $-e^{-1}$. The module states this
choice explicitly, and none of its inverse or derivative theorems silently
extends to that region. The all-real-time formula never uses that default:
its Lambert argument is strictly positive for every real $t$.

## Arguments independently checked

The forward-map derivative is $e^w(1+w)$. It is strictly positive in the
interior $w>-1$ and yields strict monotonicity on the closed branch interval.
Continuity, the value $-e^{-1}$ at $w=-1$, and divergence to infinity give
surjectivity onto the claimed closed real domain. The implementation uses
these facts to construct an actual order isomorphism; branch selection is
not assumed as an unproved property of a named inverse.

For an interior argument, the inverse lies strictly above $-1$. Therefore the
forward derivative is nonzero and the local inverse derivative theorem
applies. Substitution of $W(x)e^{W(x)}=x$ gives the source quotient when
$x\ne0$. The separate value at zero is necessary: the displayed quotient is
indeterminate there in ordinary mathematics, and Lean's totalized division
would evaluate it to zero rather than the derivative one. No derivative is
claimed at the branch endpoint.

For the fluid formula, the checked proof departure is to exponentiate the
already verified implicit equation

$$
\log g_\lambda(t)+\lambda g_\lambda(t)=\lambda(1-t).
$$

This gives

$$
(\lambda g_\lambda(t))e^{\lambda g_\lambda(t)}
=\lambda e^\lambda e^{-\lambda t}.
$$

Positivity puts $\lambda g_\lambda(t)$ on the principal branch. The inverse
characterization therefore identifies the explicit formula directly. This
does not merely define a second profile and leave its equality with the
existing ODE solution unproved. The source instead suggests checking the
ODE using the Lambert derivative. Both arguments are valid on the relevant
positive arguments.

The existing profile module supplies its positive values, initial condition,
ODE derivative, smoothness, strict decrease, strict convexity and limit zero.
The explicit Lambert formula is linked to that very same `fluidProfile`.
The source only requests nonnegative times; extension to negative times is
consistent with the globally constructed positive profile.

## Domain clarification and residual scope

There is no blocking mathematical defect in the implemented Lambert branch
or profile formula. The source's unqualified displayed quotient requires the
usual interior, nonzero-argument qualification. The implementation correctly
records the qualification and proves the missing value at zero separately.

The exact probes in `verification/SIRLambertWProbe.lean` check the endpoint,
one positive and one negative branch value, the derivative and failed
quotient at zero, positivity of the formula's argument, its initial value,
and a negative-time specialization. The command
`lake env lean -DautoImplicit=false verification/SIRLambertWProbe.lean`
passes with no diagnostics; its captured output is
`/tmp/sir-lambert-probe.log`. Root-owned project build and global axiom checks
are separate evidence.

The five independently printed axiom closures in
`/tmp/sir-lambert-audit-axioms.log` contain only `propext`, `Classical.choice`,
and `Quot.sound`: inverse characterization, quotient derivative, derivative
at zero, explicit profile formula, and the exact zero-quotient probe.

This audit concerns the analytic Lambert component of A70. It does not close
the SIR clock-history bridge, the corrected stochastic Grönwall estimate, or
the T07 limit theorems.
