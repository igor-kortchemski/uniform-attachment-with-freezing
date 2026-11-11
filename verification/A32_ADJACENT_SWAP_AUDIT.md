# Independent A32 adjacent-swap and sorting audit

This review was performed independently of the author of
`HeightScaleAdjacentSwap.lean` and `HeightScaleSorting.lean`. The source
scope is the complete adjacent-transposition argument at lines 1240–1242
of `attachement-uniforme-1-final.tex`. The existing main lower-bound proof
is unchanged.

## One actual adjacent swap

`attachmentSwap x i` is the actual schedule obtained by changing the two
entries $x_i=-1,x_{i+1}=+1$ to $+1,-1$. The time index satisfies
$1\leq i$ and $i+1\leq n$. The map is defined on the whole infinite
schedule, not on a numerical surrogate for its height.

The proof checks the complete prefix counts: the attachment count
increases by one exactly at prefix $i$, and otherwise stays unchanged;
the active count increases by two exactly at prefix $i$, and otherwise
stays unchanged. Thus positivity through $n$ is preserved. The exact
height-scale identity is

$$
h_n^+(x')+\frac1{S_{i+1}(x)}
=h_n^+(x)+\frac1{S_{i+1}(x)+1}.
$$

Under `PositiveThrough x n`, the displayed denominators are positive,
and the reciprocal comparison gives $h_n^+(x')\leq h_n^+(x)$. These are
the actual post-step counts in the defined height scale. No assertion
about an individual forward vertex's selection probability is used.

## Finite reachability of the sorted schedule

`AttachmentSwapChain n x y` is an inductive finite chain of precisely those
actual swaps; every step retains its two sign and index hypotheses. A
sorted target is not a premise of the reachability theorem.

The termination argument uses the integer

$$
\operatorname{attachmentArea}(x,n)=\sum_{k=0}^{n-1}P_k(x).
$$

Every permitted swap increases this area by exactly one. The area is
bounded above by $n^2$ for every schedule. Among the finitely many reachable
area values, the proof chooses a maximal attained value. An adjacent
$-1,+1$ at that attained target would permit a further actual swap and
contradict maximality. This proves existence of a finite actual chain to
a target with no such inversion. It does not assume that a sorted
permutation is reachable, and it does not replace the swap chain by a
bare permutation certificate.

The no-inversion predicate `PrefixSorted` is proved to mean literally

$$
y_k=\begin{cases}
+1,&1\leq k\leq P_n(x),\\
-1,&P_n(x)<k\leq n.
\end{cases}
$$

The whole original tail at times $k>n$, as well as the unused time-zero
entry, is retained. The attachment count is preserved; the freezing count
is therefore preserved as well. Positivity and the decreasing height-scale
comparison are propagated along the genuine chain.

## Harmonic identity and the printed logarithmic chain

For the actual sorted prefix the proof gives the exact identity

$$
h_n^+(y)=\sum_{i=1}^{P_n(x)}\frac1{i+1}
=\operatorname{shiftedHarmonic}(P_n(x)).
$$

This is checked directly from the defined active populations on the initial
attachment block. The independent probe also reconstructs the literal
$\{1,\ldots,P_n\}$ indexing from the formal zero-based finite sum.

The last theorem checks every displayed inequality in the source:

$$
\log(n/4)
\leq\log\bigl((P_n+1)/2\bigr)
\leq\sum_{i=1}^{P_n}\frac1{i+1}
\leq h_n^+(x).
$$

Its hypotheses are precisely $n\geq1$ and positivity through $n$, equivalent
to the source's $\tau>n$. The bound $n\leq2P_n$ comes from the earlier
proved count identity. The logarithmic harmonic estimate uses the earlier
proved slightly stronger $\log((P_n+2)/2)$ bound and then obtains the
source's original weaker intermediate bound explicitly.

## Evidence and conclusion

The root artifact build passed with 3783 jobs in
`verification/height-sorting-tall-statistics-build.log`. The independent
expanded probe `verification/A32AdjacentSwapStatements.lean` passed its
actual-file direct Lean check with exit code zero and no diagnostics. Its
nine expanded examples include reconstruction of both preserved sign
counts and the literal source harmonic indexing. All ten axiom closures
use only `propext`, `Classical.choice`, and `Quot.sound`. The durable log is
`verification/a32-adjacent-swap-independent-statements.log`, also available
in a local log (not retained).

No semantic mismatch was found in the two audited modules. The source's
one-swap comparison, finite actual-swap iteration, literal sorted prefix,
preserved tail and counts, exact harmonic identity, and original logarithmic
chain are all covered. The old direct harmonic proof remains a separate
valid implementation route; this milestone additionally checks the paper's
previously unverified sorting argument itself.
