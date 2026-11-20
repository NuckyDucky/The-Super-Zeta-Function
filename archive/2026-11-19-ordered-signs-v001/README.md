# Chronological sign words and the two finite period-640 multiplier minima

I use a **rooted word** to specify the first stage and the direction of iteration. These two choices distinguish a measured orbit from a cyclic list with no marked starting phase.

## The order of the signed exponentials

Fix a complex logarithmic lift $L$. Write $E_a(z)=e^{az}$. For signs $\sigma_j\in\{+1,-1\}$, put $a_j=\sigma_jL$ and start with $z_0=z$. Apply the letters from left to right:

```math
z_j=E_{a_j}(z_{j-1}),\qquad
W_{\sigma_1\cdots\sigma_m}(z)=z_m,\qquad W_{uv}=W_v\circ W_u .
```

In the weave $X_{j,n+1}=\exp(s_j L X_{j+1,n})$ the index $j$ names the **receiving phase**. To follow one input forward, read the receiving edges in the order they act. For the ordered pair $F_L(P,Q)=(e^{LQ},e^{-LP})$, $P$ first enters the minus stage on its way to the second coordinate and then the plus stage on its way back. Thus $F_L^2(P,Q)=(W_{-+}(P),W_{+-}(Q))$. I retain the actual exponents $U=LQ,\ V=-LP$. They recover the input as $(P,Q)=(-V/L,U/L)$ whenever $L\ne0$. [My phase-indexed definition and the operations on a cyclic word](../2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L404-L445) · [Lean proof of exponent recovery](../../lean/SuperZeta/Oriented/OrderedStages.lean)

| Operation on a rooted word | Effect on the map |
| --- | --- |
| Append $v$ after $u$ | Apply $W_u$ first, then $W_v$. |
| Move the starting phase past $u$ in $uv$ | The new word is $vu$. The identity $W_u\circ W_{uv}=W_{vu}\circ W_u$ carries a periodic point to its new starting phase. |
| Reverse the letters | Apply the stages in the opposite order. At fixed $L\ne0$, reversal changes the map exactly when it changes the list of letters. |
| Flip every sign | Evaluate the original word at $-L$. On $L=iy$ with a real starting point, complementary words give conjugate endpoints. |

**Theorem.** For every fixed $L\in\mathbb C$ with $L\ne0$, equality of the entire functions $W_u=W_v$ implies equality of the rooted words $u=v$. More generally, a finite list of arbitrary nonzero complex rates is uniquely determined by its entire composition of the maps $E_a$. [Lean proofs of concatenation, phase rotation, complement, conjugation and injectivity](../../lean/SuperZeta/SignWords.lean)

**Proof.** Let the empty word be the identity. Each nonempty composition has image precisely $\mathbb C\setminus\{0\}$. It always omits zero, and every nonzero target has a nonzero logarithm, giving a nonzero input to the last stage and hence a preimage by induction. Prove the stronger claim that $W=cV$, $c\ne0$, forces identical rate lists and $c=1$. An empty and a nonempty list have different images. For two empty lists evaluate at $1$. Otherwise remove the two outer stages and write $e^{aA}=c\,e^{bB}$. The entire function $aA-bB$ is constant since its exponential is constant and nowhere zero. Write $aA=bB+k$. If both prefixes are nonempty, the two sides omit $0$ and $k$, so $k=0$. If exactly one prefix is empty, one side has image $\mathbb C$ and the other omits a point. If both are empty, evaluate at zero to get $k=0$. Thus $A=(b/a)B$. Induction identifies the prefixes and gives $b/a=1$. Substitution gives $c=1$. Finally $L$ and $-L$ are distinct for $L\ne0$. This proves the signed case.

## Reading a word from one value

For real $L>0$, **one endpoint from the cap $z_0=1$ determines every sign of a finite word**. All states are positive. A last plus gives $x>1$, a last minus gives $0<x<1$, and in either case the previous value is $|\log x|/L$. Repeat until $x=1$, the endpoint of the empty word. For example, at $L=\log 2$, the word $+-$ sends $1\to2\to1/4$, while $-+$ sends $1\to1/2\to\sqrt2$. At complex lifts, evaluating once can merge different words: at $L=\pi i$, both single signs send $1$ to $-1$. [Lean decoder, cap injectivity and the collision at $\pi i$](../../lean/SuperZeta/SignWords.lean)

On the imaginary centerline I evaluated all six balanced four-letter words at the same cap and the same $L=iy$, throughout the second minimum’s bracket below. Each row gives two complex values, in the order the words are printed. Directed disks separate all six.

| Chronological words | Approximate endpoints from $1$ |
| --- | --- |
| `++--` / `--++` | $0.682245293388 \mp 0.433966376273i$ |
| `+-+-` / `-+-+` | $1.23303577004 \mp 0.775374783799i$ |
| `+--+` / `-++-` | $1.17606722460 \pm 0.389305774542i$ |

Balancing specifies the sign count. Ordering selects a particular map. In the reciprocal pair the physical update prescribes the alternating word. The six-word comparison evaluates other sign histories from the same cap. [Balanced-history construction](../2026-11-16-super-zeta-v001/research/ordered-signed-histories.md) · [Six disjoint enclosures](bounds.json)

## Recovering one alternating stage from derivative measurements

Let $C_0=1$ and let $C_j$ be the complex derivative of the first $j$ stages with respect to their common starting value, evaluated there. Each stage has derivative $a_j z_j$, so each $C_j$ is nonzero. For consecutive alternating rates,

```math
d_j=\frac{C_j}{C_{j-1}}=a_jz_j,\qquad
z_{j+1}=\exp(-d_j),\qquad
a_{j+1}=d_{j+1}\exp(d_j).
```

The second equality uses $a_{j+1}=-a_j$. The third divides the next stage derivative by its recovered output. Three consecutive prefix derivatives therefore suffice to read the second signed rate and its output. For a measurement of the actual complex exponent $a_j z_{j-1}$, the corresponding predecessor is obtained simply by dividing by $a_j$. [Lean proof using derivatives of the actual composed maps](../../lean/SuperZeta/SignWords.lean) · [Original derivative formula from the ordered exponents](../../lean/SuperZeta/Oriented/OrderedStages.lean)

For the marked orbit at the secondary minimum I formed the prefix derivatives, then decoded stages 2–641. Stage 641 reads the first position on its next lap. All 640 rate disks distinguish the sign, with absolute error below $7.43\times10^{-15}$ against the prescribed complex rate. The recovered states agree with forward propagation within $2.91\times10^{-14}$. This checks recovery from overlapping derivative measurements. The measured lap multiplier by itself is only the last prefix derivative. [Directed-arithmetic replay](verify.py) · [Enclosures](bounds.json)

<details>
<summary>Sliding the 160- and 161-stage windows around the marked orbit</summary>

Let $P_m(j)$ be the derivative of $m$ stages starting at $z_j$. I measure the same two lengths at each of the 640 starting phases. The longer window contains exactly one additional factor, so

```math
A_j=\frac{P_{161}(j)}{P_{160}(j)}=a_{j+161}z_{j+161},\qquad
z_{j+162}=e^{-A_j},\qquad a_{j+162}=A_{j+1}e^{A_j}.
```

I form each 160-stage derivative by the chain rule. I compute the 161-stage derivative separately from the product of its rates times the exponential of the sum of its actual exponents. The decoder receives their ratios in starting-phase order. Over one lap it reads each sign once, including those across the marked start. The largest certified absolute error was below $9.78\times10^{-15}$ in the signed rate and $2.90\times10^{-14}$ in the stage output. The theorem also applies to other consecutive window lengths. [Lean proof for sliding windows](../../lean/SuperZeta/SignWords.lean) · [All 640 comparisons](bounds.json)

</details>

## Two minima on the imaginary centerline

Put $L=iy$, $H_y(z)=\exp(iy\overline z)$ and $G_y=H_y^{640}=g_{iy}^{320}$. The cap is $1$. I mark the periodic phase $p_y$ selected by iteration from this cap and measure $\mu(y)=G_y'(p_y)$. The two rows are local minima of $|\mu|$ at different **heights on the centerline**. The table rounds heights for readability. The first verifier encloses each in a rational bracket of radius $10^{-24}$. [Finite data and the previous secondary interval, preprint §8](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L553-L604)

| Local minimum | $y$ | Return modulus | Canonical detuning |
| --- | ---: | ---: | ---: |
| Primary | 0.509892983538669107707 | $6.35078306251\times10^{-17}$ | 0.154803575052210 |
| Secondary | 0.509893023733322309247 | 0.000301541911322723 | 0.592055820765009 |

For the secondary family I continue the marked orbit across the entire interval $0.5098930229215867\le y\le0.50989302375$. The previous upper endpoint was $0.5098930237215867$. On their overlap my radius-$10^{-6}$ disk about $1$ lies strictly inside the original radius-$0.0007$ disk. Both returns contract there, so the marked phase agrees with the previously isolated continuation. The second minimum lies about $1.17356\times10^{-11}$ beyond the previous endpoint.

The same 25/295 itinerary holds on the extended interval. With the cap phase indexed by $j=0$, the scalar orbit is outside the manuscript’s radius-$0.08$ gate at $j=0,\ldots,10$ and $306,\ldots,319$, and inside at all the other indices. I use its fixed coordinate $\beta(z-Z_*)$, with $d=\cos d$ in $(0,1)$, $\alpha=\sin d+id$, $Z_*=e^\alpha$, $y_*=e^{-\sin d}$ and $\beta=(1+\alpha)(-iy_*)/2$. The gate records the location of the orbit. The plus and minus signs record which exponential acts. The open matching question is how these finite minima continue to particular minima of the limiting horn map as the period increases. [Original finite records and conditional rail law](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L580-L635)

### Proof by interval enclosures

1. Divide the secondary interval into 32 closed rational tiles. On every tile $G_y$ sends the cap disk within $5.384\times10^{-7}$ of its center, with derivative modulus below $0.000444$. The contraction principle gives one marked fixed phase. The same disk works on each tile, so the phases agree at shared endpoints. The implicit function theorem makes the phase real-analytic in $y$. Since $640=2^7\cdot5$, disjoint returns at steps 320 and 128 exclude every proper divisor of 640. At even indices the alternating holomorphic stages equal the iterates of $H_y$. Its primitive period is therefore 640, and that of $H_y^2$ is 320. The original paired map on $(p_y,\overline{p_y})$ has the same period as $H_y$. [Centerline identification in Lean](../../lean/SuperZeta/Reciprocal.lean) · [Uniform disk and gate bounds](bounds.json)
2. Along the closed orbit, $\ell(y)=\log|\mu(y)|=640\log y+\Re\sum_{j=1}^{640}a_jz_{j-1}$. To differentiate, solve $(1-\mu)p_y'=\partial_yG_y(p_y)$, and differentiate the closure a second time for $p_y''$. The code bounds both derivatives through every exponential. In each bracket $\ell'$ is negative on the left and positive on the right, and $\ell''>0$ throughout. Thus each bracket contains exactly one critical point, a strict local minimum. At the secondary minimum $\ell''\approx9.46013315384\times10^{17}$. [Derivative recurrences and sign tests](verify.py)
3. As a separate check I used the original antiholomorphic half-step with three real unknowns $(\Re p,\Im p,y)$. A Krawczyk calculation encloses the two closure equations together with the cleared stationarity equation in a box of radius $10^{-130}$ in each coordinate around the saved Newton center. The derivative defect is below $9.72\times10^{-26}$ in the infinity norm. The enclosed solution lies inside the marked cap disk and the secondary bracket. The file also checks positive curvature and the proper-period exclusions directly. [Independent implementation](crosscheck.py) · [Three exact decimal inputs](secondary-center.json) · [Independent result](independent-bounds.json)
4. For the detuning, enclose the positive-imaginary inverse of $Y(u)=u\sec u\,e^{-u\tan u}$ in the indicated box near $d$. A contraction around a numerical seed verifies the inverse on the full parameter bracket. With $\Lambda=2\log(u/\cos u)$ on the principal branch near $1$, the conjugate pair gives $\delta=640-4\pi|\Im(1/\Lambda)|$. The finite values in the table come from these enclosures. [Canonical coordinates in the preprint](../2026-11-18-lean-foundations-v001/papers/dottie-spire/main.tex#L305-L347) · [Enclosed $u$ and $\delta$](bounds.json)

## Reproduction

From the repository root, with Lean 4.19.0 and the pinned mathlib revision, run:

```sh
python tools/check_lean.py --fetch-cache
```

The Lean kernel checks the finite-word theorem, the one-value real decoder, rotation and complement, and recovery from actual prefix derivatives. The repository audit checks their transitive axiom dependencies. For the numerical results, use Python 3.12 with `python-flint==0.9.0` and `mpmath==1.3.0`:

```sh
cd archive/2026-11-19-ordered-signs-v001
python verify.py --bits 384
python verify.py --bits 640
python crosscheck.py
```

I obtained the same reported bounds at 384 and 640 bits. The independent half-step calculation uses 230 decimal digits for interval arithmetic. Each program raises an error if its proof inequalities fail. [Source history, conventions and software versions](provenance.json)
