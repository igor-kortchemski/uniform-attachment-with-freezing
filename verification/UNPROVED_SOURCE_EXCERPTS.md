# Passages de la source correspondant aux obligations non prouvées

Source : `attachement-uniforme-1-final.tex` (SHA-256 inchangé). Chaque bloc donne les lignes exactes du fichier.

## A85–A86 : couplage inverse iid (tex 2271–2321)

Non prouvé : la phrase « on the event A^n_ε, one can couple … ξ^ε_i ≤ X̂^n_i ≤ 1 » (ligne 2295) comme loi jointe réelle, et par suite les majorations 2297–2299, 2306–2311, 2318–2319. Les équations (2292) et (2302) sont prouvées.

```latex
2271: 		\frac{I^{n_j}_{\lfloor 3n_j/2\rfloor }}{n_j} \ge \frac{\widetilde{Y}^\e_{\lfloor 3n_j/2\rfloor}}{n_j}  \cvproba[n] 1+ \frac{2\e -1 }{2},
2272: 		$$
2273: 		which is absurd in view of \eqref{eq:limite fluide presque recursif}. This proves \eqref{eq convergence des transitions cas presque recursif}.
2274: 		
2275: 		Next, let us prove that 
2276: 		\begin{equation}\label{eq h n tend vers zero}
2277: 			\frac{\h^n}{\log n} \cvproba[n]0.
2278: 		\end{equation}
2279: 		Define $\hat\XX_i^n = -\XX_{\tau'_n-i+1}^n$ {for all $i \in \llbracket 1, \tau'_n \rrbracket$} and $\hat S_i^n = I_{\tau'_n-i}^n = \hat\XX_1^n + \cdots + \hat\XX_i^n$ for all $i \in \llbracket 0, \tau'_n \rrbracket$. Then
2280: 		\[
2281: 		\h^n = \sum_{i=1}^{\tau'_n-n} \frac{1}{\hat S_i^n} \mathbbm{1}_{\{\hat\XX^n_i=-1\}}.
2282: 		\]
2283: 		By \eqref{eq:limite fluide presque recursif}, to prove \eqref{eq h n tend vers zero}, it suffices to prove that 
2284: 		\begin{equation}\label{eq somme jusque n sur 2 tend vers zero}
2285: 			\frac{1}{\log n} \sum_{i=1}^{\lfloor n/2 \rfloor \wedge (\tau'_n -n)}  \frac{1}{\hat S_i^n} \mathbbm{1}_{\{\hat\XX^n_i=-1\}} \cvproba[n] 0.
2286: 		\end{equation}
2287: 		For all $\e>0$, for all $n\ge 1$, define the event
2288: 		$$
2289: 		\mathcal{A}^n_\e = \left\{ \sup_{3n/2 \le k \le 2n} \frac{\lambda_n U^n_k}{1+ \lambda_n U^n_k} \le \e\right\}.
2290: 		$$
2291: 		By \eqref{eq convergence des transitions cas presque recursif}, we know that
2292: 		\begin{equation}\label{eq limite proba A n epsilon tend vers 1}
2293: 			\lim_{\e \to 0} \liminf_{n\to \infty} \P(\mathcal{A}^n_\e)  = 1.
2294: 		\end{equation}
2295: 		Besides, on the event $\mathcal{A}^n_\e$, one can couple the $(\hat{\XX}^n_i)_{1 \le i \le n/2 \wedge (\tau_n -n)}$'s with i.i.d.\@ random variables $(\xi^\e_i)_{i\ge 1}$ such that $\P(\xi^\e_i = -1)= \e$ and $\P(\xi^\e_i = 1) = 1-\e$ so that for all $i \le  n/2\wedge (\tau_n-n)$, we have $\xi^\e_i \le \hat{\XX}^n_i \le 1$. For all $i \ge 0$, let $\hat{Y}^\e_i = \xi^\e_1+ \ldots + \xi^\e_i$. Then, for all $i \le n/2  \wedge (\tau_n-n)$, we have $\hat{Y}^\e_i \le \hat{S}^n_i $. In particular, on the event $\mathcal{A}^n_\e \cap \{\forall i \in \llbracket 1, n/2 \rrbracket , \ \hat{Y}^\e_i >0 \}$,
2296: 		$$
2297: 		\sum_{i=1}^{\lfloor n/2 \rfloor \wedge (\tau'_n -n)}  \frac{1}{\hat S_i^n} \mathbbm{1}_{\{\hat\XX^n_i=-1\}}
2298: 		\le
2299: 		\sum_{i=1}^{\lfloor n/2 \rfloor}  \frac{1}{\hat{Y}_i^\e} \mathbbm{1}_{\{\xi^\e_i=-1\}}.
2300: 		$$
2301: 		But, by the strong law of large numbers, we have
2302: 		\begin{equation}\label{eq limite proba Y epsilon toujours plus grand que i sur 2}
2303: 			\P\left( \forall i \ge 0, \ \hat{Y}^\e_i \ge  i/2\right)
2304: 			\mathop{\longrightarrow}\limits_{\e\to 0} 1 .
2305: 		\end{equation}
2306: 		For all $\e>0$, on the event $\mathcal{A}^n_\e \cap \{\forall i \ge 0, \hat{Y}^\e_i \ge i/2 \}$, we obtain that 
2307: 		$$
2308: 		\sum_{i=1}^{\lfloor n/2 \rfloor \wedge (\tau'_n -n)}  \frac{1}{\hat S_i^n} \mathbbm{1}_{\{\hat\XX^n_i=-1\}}
2309: 		\le
2310: 		\sum_{i=1}^{\lfloor n/2 \rfloor}  \frac{2}{ i} \mathbbm{1}_{\{\xi^\e_i=-1\}}.
2311: 		$$
2312: 		Besides,
2313: 		$$
2314: 		\E\left[\sum_{i=1}^{\lfloor n/2 \rfloor}  \frac{2}{i} \mathbbm{1}_{\{\xi^\e_i=-1\}}\right] =2\e \sum_{i=1}^{\lfloor n/2 \rfloor} \frac{1}{i}.
2315: 		$$
2316: 		Therefore, we obtain that
2317: 		$$
2318: 		\E \left[\1_{\mathcal{A}^n_{\e} \cap \{\forall i \ge 0, \ \hat{Y}^{\e}_i \ge  i/2\}}\sum_{i=1}^{\lfloor n/2 \rfloor \wedge (\tau'_n -n)}  \frac{1}{\hat S_i^n} \mathbbm{1}_{\{\hat\XX^n_i=-1\}}
2319: 		\right] \le 2\e \sum_{i=1}^{\lfloor n/2 \rfloor} \frac{1}{i}.
2320: 		$$
2321: 		After letting $\e\to 0$, using \eqref{eq limite proba A n epsilon tend vers 1} and \eqref{eq limite proba Y epsilon toujours plus grand que i sur 2}, we deduce \eqref{eq somme jusque n sur 2 tend vers zero}.
```

## L13 : lemme de Pólya, hypothèse « état courant seulement » (tex 2001–2007)

Non prouvé tel quel : l'hypothèse ne conditionne que sur U_n. La version avec lois de chemin markoviennes complètes est prouvée.

```latex
2001: \begin{lemma} 
2002: \label{P\'olya}
2003: Fix an integer $z_{0}>0$ and set $U_{0}=1$. Let $(z_n)_{n\geq 1}\in \{-1,1\}^\N$, set $Z_{n}=\sum_{i=0}^{n}z_{i}$. Assume that $Z_{n}>0$ for every $n \geq 1$ and  $\sum_{n=0}^\infty 1/Z_n^2<\infty$. Let $(U_n)_{n\geq 1}$ be a sequence of random non-negative integers such that for every $n\geq 0$, 
2004: \[ \proba{ \left . U_{n+1}=U_n+z_{n+1} \right | U_n }=\frac{U_n}{Z_n} \quad ; \quad \proba{ \left . U_{n+1}=U_n \right | U_n }=\frac{Z_n-U_n}{Z_n}.\]
2005: Almost surely for every $t \geq 0$
2006: \[ \proba{   \sup_{i\geq 1} \left | \frac{U_i}{Z_i} - \frac{1}{z_0} \right  | >   t\frac{1}{z_0}   } \leq 2 \exp \left (-\frac{(t^2/4)(1/z_0)}{\sum_{n \geq 1} 1/Z_n^2+t\max \left (\sum_{n \geq 1} 1/Z_n^2,  \max_{n \geq 1} 1/Z_n \right )}\right ). \]
2007: \end{lemma}
```

## A87 : domination conditionnelle et borne de Bennett (tex 2326–2330)

Non certifié tel quel : la domination « par Height(T_n)+Σ Y_i » (sans le +1), la borne (2327–2329) à moyenne décalée et seuil non décalé, et l'argument conditionné au futur (τ'_n, I_i). La version corrigée à mot fixé est prouvée.

```latex
2326: 	It remains to show how {\eqref{eq h n tend vers zero}} implies that $\Height({\mathscr{T}^n})=\Height(\T_{n}(\XXb^n))+o(\ln n)$. To do so we will use, once again, the coalescence construction and Bennett's inequality. By Algorithm \ref{algo2}, conditionally on $\tau'_n$ and $(I_i^n)_{0\leqslant i\leqslant \tau'_n}$, the height of any new vertex added between time $n$ and $\tau'_n$ is stochastically dominated by $\Height(\T_n(\XXb^n))+\sum_{i=n}^{\tau'_n-1} Y_i$ where $(Y_i^n)_{n\leqslant i\leqslant \tau'_n-1}$ are i.i.d Bernoulli random variables of respective parameters $(1/I_i^n\mathbbm{1}_{\{\XX^n_i=1\}})_{n\leqslant i\leqslant \tau'_n-1}$. Using Bennett's inequality and a union bound{, as in Sec.~\ref{ssec:limitheightBennet},}  for all $\e>0$ we obtain that
2327: 	\[
2328: 	\proba{\Height({\mathscr{T}^n}) - \Height(\T_n(\XXb^n)) \geq \h^n + \e \ln n \, \middle| \,  {\tau'_n, (I_i^n)_{0\leqslant i\leqslant \tau'_n}} } \leq n\exp\left(-\h^n g\left(\frac{\e \ln n}{\h^n}\right)\right) 
2329: 	\]
2330: 	where $g(u) = (u+1)\ln(u+1)-u \sim u\ln u$ as $u\to+\infty$. Since $\h^n=o(\ln n)$ {in probability}, the above upper bound goes to $0$ when $n$ goes to $\infty$ and thus $\Height({\mathscr{T}^n})$ is of order $e\ln n$.
```

## A06 : non-tension GHP et convergence vers le dendron long (tex 357)

Non formalisé : non-tension GHP (seule la version GH est prouvée), convergence dans la topologie de [ET21, Jan21], identification avec Υ_ν.

```latex
357: Let us mention that it is possible to check that $(\T_{n}/\ln(n))_{n \geq 1}$ is not tight for the so-called Gromov--Hausdorff--Prokhorov topology. However, for the topology considered in \cite{ET21,Jan21},  $\T_{n}/\ln(n)$ converges to the so-called long dendron $\Upsilon_{\nu}$ (we use the notation of \cite[Example 3.12]{Jan21}) with $\nu$ being the Dirac mass $\nu=\delta_{(c+1)/2c}$.
```

## A24 : couplage des préfixes (tex 909–921)

Couplage commun et inférence par union diagonale non monotone (915–919) : contournés ; la conclusion est prouvée par tension marginale.

```latex
909: {Finally we show that {(I)} implies  {(II)}.} Assume {(I)} and suppose that $\T_n(\Xb)$ does not converge locally {almost surely}. Then there exists $i$ such that $\X_i=+1$ and the vertex $v_i$ added at time $i$ in $\T_n(\Xb)$ has a degree converging towards $+\infty$ with positive probability. In other words
910: \[
911: \proba{\deg(v_i,\T_n(\Xb)) \rightarrow +\infty} = \lim_{m\to\infty} \proba{\bigcup_{n\geq i} \{\deg(v_i,\T_n(\Xb))\geq m \}} >0.
912: \]
913: Let $\varphi$ be an increasing function such that for all $k \leq n$, $\Xb_k^{\varphi(n)} = \Xb_k$. There is an obvious coupling such that $\T_n(\Xb) = \T_n(\Xb^{\varphi(n)})$ for all $n$. Therefore, for all $m$,
914: \[
915: \bigcup_{n\geq i} \{\deg(v_i,\T_n(\Xb))\geq m \} = \bigcup_{n\geq i} \{\deg(v_i,\T_n(\Xb^{\varphi(n)}))\geq m \},
916: \]
917: and
918: \[
919: \lim_{m\to\infty} \proba{\bigcup_{n\geq i} \{\deg(v_i,\T_{\varphi(n)}(\Xb^{\varphi(n)}))\geq m \}} \geq \lim_{m\to\infty} \proba{\bigcup_{n\geq i} \{\deg(v_i,\T_n(\Xb^{\varphi(n)}))\geq m \}} >0.
920: \]
921: We deduce that {under this coupling} the degree of $v_i$ in $\T_{\varphi(n)}(\Xb^{\varphi(n)})$ tends to $\infty$ with positive probability so $\T_n(\Xb^n)$ can't converge locally.\qed
```

## A67 : couplage avec la marche aléatoire et Skorokhod (tex 2059–2070)

Couplage jusqu'au temps k_0 et représentation de Skorokhod : contournés ; la conclusion est prouvée directement.

```latex
2059: 	For {(I)},  assume that $\lambda_n \sim \lambda/n$ as $n \to \infty$ for some $\lambda >0$. {We first prove} that $(I^n_k)_{k\ge 0}$ converges in distribution for the product topology towards the random walk $(S_k)_{k\ge 0}$ such that $S_{k+1}-S_k=1$ with probability $\lambda/(1+\lambda)$ and $S_{k+1}-S_k=-1$ with probability $1/(1+\lambda)$. Indeed, the local convergence of $\T_n(\XXb^n)$ implies the local convergence of ${\mathscr{T}^n}$. So as to achieve this, one can first see that since $U^n_k \le n$ for all $k \ge 0$, we have
2060: 	\[
2061: 	\frac{\lambda_n U^n_k}{1+\lambda_n U^n_k} \le \frac{n \lambda_n}{1+ n \lambda_n} \cv[n] \frac{\lambda}{1+\lambda}.
2062: 	\]
2063: 	But we also have
2064: 	\[
2065: 	\inf_{k \le \sqrt{n}} \frac{\lambda_n U^n_{k}}{1+ \lambda_n U^n_{k}}
2066: 	\ge \frac{\lambda_n (n-\sqrt{n})}{1+ n\lambda_n } \cv[n] \frac{\lambda}{1+\lambda}.
2067: 	\]
2068: 	For all $k_0 \ge 0$, one can thus build a coupling between $(I^n_k)_{0\le k\le k_0}$ and $(S_k)_{0\le k\le k_0}$ such that the two walks coincide w.h.p. until time $k_0$ as $n \to \infty$. 
2069: 	
2070: 	{Thus, by Skorokhod's representation theorem we may assume that almost surely, for every $k_{0} \geq1$, $(I^n_k)_{0\le k\le k_0}=(S_k)_{0\le k\le k_0}$ for $n$ sufficiently large. By Theorem \ref{thm:cvlocale}, ${\mathscr{T}^n}$ converges locally in distribution to a uniform attachment tree with freezing built using the sequence $(S_{k+1}-S_k)_{k \geq 0}$. By Theorem \ref{thm:BGW}, this is a Bienaym\'e tree with offspring distribution $\mathcal{G}(1/(1+\lambda))$. This proves {(I)}.}
```

## A73 : couplages de marches inférieure/supérieure (tex 2144–2159)

Couplage (2151–2158) : contourné ; la probabilité d'extinction est prouvée par une borne exponentielle sur le vrai noyau.

```latex
2144: 	uniformly on compacts. Let us check that this implies  \eqref{limite fluide I}. Since $t\mapsto 2- 2g_\lambda(t)-t$ is concave, starts from zero at time zero, stays positive and then goes below zero, it is thus enough to identify the limit of the probability that the chain $\widetilde{I}^n$ reaches zero before time $\e n$ as {first} $n\to \infty$ and {then} $\e \to 0$ as  the probability of extinction of a $\mathcal{G}(1/(1+\lambda))$-Bienaym\'e process. To this end, for all $\e >0$, for $n$ large enough, for all $k\le \e n$, since $n\ge \widetilde{U}^n_k\ge (1-\e)n$ we have
2145: 	\[
2146: 	\frac{\lambda}{1+\lambda} -\e  \le 
2147: 	(1-\e)\frac{n \lambda_n}{1+ n \lambda_n} \le \frac{\lambda_n \widetilde{U}^n_k}{1+\lambda_n \widetilde{U}^n_k}
2148: 	\le \frac{n \lambda_n}{1+ n \lambda_n} 
2149: 	\le \frac{\lambda}{1+\lambda} +\e.
2150: 	\]
2151: 	Thus, one can couple $(I^n, U^n)$ until time $\e n$ with two simple random walks $(\overline{Y}^\e_k)_{k\ge 0}$ and $(\underline{Y}^\e_k)_{k\ge 0}$ starting from one such that
2152: 	\[
2153: 	\P(\overline{Y}^\e_1 = 1) =  \frac{\lambda}{1+\lambda}  + \e \qquad \text{and} \qquad \P(\underline{Y}^\e_1 = 1) =\frac{\lambda}{1+\lambda} -\e
2154: 	\]
2155: 	so that for all $n$ large enough, for all $k\le \e n$,
2156: 	\begin{equation}\label{eq couplage marches}
2157: 		\underline{Y}^\e_k \le \widetilde{I}^n_k \le \overline{Y}^\e_k.
2158: 	\end{equation}
2159: 	Since the probabilities that the random walks $\underline{Y}^\e$ and $\overline{Y}^\e$ starting from $1$ reach the negative integers {both} converge as $\e \to 0$ to the probability of extinction of a $\mathcal{G}(1/(1+\lambda))$-Bienaym\'e process, we get the desired result.
```

