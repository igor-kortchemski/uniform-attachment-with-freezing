# Independent scoped review of the late SIR Bennett argument

Reviewed source: `attachement-uniforme-1-final.tex`, lines 2326–2330. Reviewed root-authored modules: `RateFunctionAsymptotics.lean`, `BennettSmallMean.lean`, and `SIRLateBennett.lean`. Affected definitions and the actual fixed-word tail dependency in `SIRLateMaximum.lean` were read, including its first-extinction stopping, pre-birth charge comparison, and the relevant actual cut-maximum exponential estimate and geometry in `ForwardCutMaximum.lean`. The reviewer did not write the three reviewed modules. This is an independent automated review, not human review.

## Exact scalar statements

The source rate is exactly $g(u)=(1+u)\log(1+u)-u$. `bennettRate_div_mul_log_tendsto_one` proves

$$
\frac{g(u)}{u\log u}\longrightarrow1
\qquad (u\longrightarrow\infty),
$$

and the exported `IsEquivalent` theorem has the same content. The proof works eventually on $u>1$, so both logarithmic factorization and division by $u\log u$ are justified. It uses the exact rate; no coarser quadratic or linear rate is substituted.

`smallMean_bennettExponent_tendsto_atTop` proves $r g(\varepsilon/r)\to\infty$ as $r\downarrow0$ for every $\varepsilon>0$. The identity $r g(\varepsilon/r)=\varepsilon g(u)/u$ with $u=\varepsilon/r$ is justified on strictly positive $r$. `bennett_unionBound_tendsto_zero` then proves the deterministic positive-small-mean implication

$$
m_n=o(\log n),\quad m_n>0\text{ eventually}
\quad\Longrightarrow\quad
n\exp\!\left(-m_n g\!\left(\frac{\varepsilon\log n}{m_n}\right)\right)\longrightarrow0.
$$

The proof derives an eventual upper bound $1/n$. Its eventual positivity premise is necessary for this quotient expression under Lean's total real division; the theorem does not silently include $m_n=0$. It is a deterministic scalar implication, and does not by itself assert a future-conditioned epidemic domination or a random-mean probability limit.

## Corrected actual fixed-word bound

For every genuinely feasible terminal SIR word, every positive charge bound $D$, and every $a>0$, the reviewed theorem proves

$$
\mathbb P\!\left(\operatorname{cutMaximum}_n\geq1+D+a\mid\text{fixed word}\right)
\leq(2n+2)\exp\!\left(-Dg\!\left(\frac aD\right)\right).
$$

Here the probability is the actual original forward tree law for that word at horizon $2n+1$. The condition $\text{wordLateBirthCharge}\leq D$ is a deterministic inequality about the supplied word, not an assumed coupling. The charge records actual susceptible-consuming transitions and uses pre-birth infectious populations; the true first-zero bound stops all reciprocal comparisons before extinction. The original tree law is held afterward.

The proof chooses $\theta=\log(1+a/D)$ in the already proved actual cut-height exponential estimate. Positivity of $D,a,1+a/D$ and nonnegativity of $\theta$ are proved. The extra factor $e^\theta$ is absorbed by the explicit extra edge in the threshold $1+D+a$. The factor $2n+2$ is the complete event-horizon vertex bound, and does not discard the initial root. The algebraic identity giving $-Dg(a/D)$ is exact.

For zero charge, `terminal_word_cutMaximum_zero_charge` proves zero probability of cut maximum at least $L$ for every $L>1$, by taking the exponential parameter to infinity. No quotient at $D=0$ is used. This is a genuine zero-charge branch for the corrected cut-height bound.

## Source correspondence and limits

The exact rate asymptotic and its positive-small-mean scalar consequence are faithful and proved. The fixed-word Bennett statement is a proved corrected alternative using the actual cut-height MGF. Its extra edge, horizon factor, and corrected pre-step charge are visible, so it is not passed off as the printed unshifted, factor-$n$ conditional inequality for the terminal height difference.

The literal per-vertex Bernoulli stochastic domination conditional on the random extinction time and count history remains open. The source also calls variables with varying parameters “i.i.d.”; the required construction would be independent with those parameters, not identically distributed in general. The present modules do not certify that construction. The zero-charge theorem covers the corrected cut-height event, not the undefined quotient expression in the printed bound. Existing actual terminal-height convergence through forward harmonic/MGF estimates remains a separate verified route. These modules therefore do not close all of A87.

The independently reconstructed probe is `SIRLateBennettIndependentStatements.lean`: six expanded examples and eight transitive axiom queries. Its ordinary imported check passes with exit zero and no diagnostics beyond the requested axiom output, recorded in `sir-late-bennett-independent-statements.log`. All eight closures contain exactly `propext`, `Classical.choice`, and `Quot.sound`. No source or scope changes beyond this isolated milestone were made.
