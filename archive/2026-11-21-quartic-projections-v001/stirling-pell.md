# The factorial correction in a Pell unit

The Brocard–Ramanujan equation asks when $n!+1=m^2$. At $n=7$ the squarefree part of $7!$ is $35$. Keeping that part fixed, I can determine every factorial on the resulting Pell sequence. Only $7!$ occurs, at its second power. At $n=8$ the squarefree part changes to $70$, and every power on that sequence misses. The primes dividing $n!$ give both classifications. My dyadic Stirling correction also distinguishes these two indices using four central binomial readings each.

## Every factorial with squarefree part 35

Write $n!=q s^2$ with $q$ squarefree and $n\ge2$, and let $P$ be the largest prime divisor of $q$. Then

$$
P\le n<2P.
$$

Indeed, Bertrand’s postulate gives a prime $p$ with $n/2<p\le n$. There is just one multiple of $p$ in $1,\ldots,n$, namely $p$. Its exponent in $n!$ is one, so $p\mid q$ and $n/2<p\le P$. The other inequality follows from $P\mid n!$. This argument also shows $q>1$ for every $n\ge2$. Erdős’s elementary proof of Bertrand’s postulate tracks primes in the central binomial coefficient $\binom{2a}{a}$, the same coefficient I normalize in the factorial correction below. [Erdős, §§1, 5](https://users.renyi.hu/~p_erdos/1932-01.pdf)

For $q=35$ this leaves just seven factorials to check. In increasing order of $n$ their squarefree parts are

| $n$ | 7 | 8 | 9 | 10 | 11 | 12 | 13 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Squarefree part of $n!$ | 35 | 70 | 70 | 7 | 77 | 231 | 3003 |

At the sole match, $7!=35\cdot12^2=71^2-1$. The smallest norm-one unit greater than $1$ in $\mathbb Z[\sqrt{35}]$ is $\epsilon=6+\sqrt{35}$. Its $\sqrt{35}$ coefficient is the smallest possible positive integer, and $6^2-35=1$. Its second power is $71+12\sqrt{35}$. The next power predicts $846+143\sqrt{35}$, whose target $846^2-1=715\,715$ falls between $9!$ and $10!$. The classification at $q=35$ covers **every** higher power as well. When the squarefree part varies with $n$, its largest prime can grow and the bound moves with it. [Exact enumeration](stirling_pell.py)

## Reading the exponent from the Stirling correction

Prince Anand’s displayed abstract for *The Arithmetic of the Brocard–Ramanujan Equation* writes a solution as $m+s\sqrt q=\epsilon^k$. Here I choose the generator $\epsilon>1$ of the positive norm-one units of the order $\mathbb Z[\sqrt q]$ and $m>0$. With this convention the candidate index for any $n$ with squarefree part $q$ is

$$
K(n)=\frac{\operatorname{arsinh}\sqrt{n!}}{\log\epsilon}.
$$

If $m^2=n!+1$, the logarithm of $m+s\sqrt q$ gives $K(n)=k$. Conversely, if $K(n)=k$ is an integer, writing $\epsilon^k=x+y\sqrt q$ gives $y\sqrt q=\sinh(k\log\epsilon)=\sqrt{n!}$. Its norm equation gives $x^2=n!+1$. An interval excluding integers therefore rules out a solution. When an interval selects a candidate integer, raising the unit to that power checks it exactly.

For $S_n=\sqrt{2\pi n}(n/e)^n$ and $\rho_n=\log(n!/S_n)$, the logarithm of the candidate unit splits exactly as

$$
\operatorname{arsinh}\sqrt{n!}
=\log 2+\tfrac12\log S_n+\tfrac12\rho_n
+\log\!\left(\frac{1+\sqrt{1+1/n!}}{2}\right).
$$

The last logarithm lies strictly between $0$ and $1/(4n!)$ by $\sqrt{1+x}<1+x/2$ and $\log(1+x)<x$ for $x>0$. The leading term $\tfrac12 n\log n$ recovers the size of $k\log\epsilon$ stated in Anand’s abstract. The two smaller terms identify separately the Stirling error and the change caused by adding $1$ before taking the square root.

Put $B_m=4^{-m}\binom{2m}{m}$ and $I(m)=-\log(\pi m B_m^2)$. After $J$ readings the lower estimate for $\rho_n$ is $\tfrac14\sum_{j=0}^{J-1}2^{-j}I(2^j n)$, with an omitted positive term smaller than $4^{-J}/(12n)$. Since the derivative of $t\mapsto\operatorname{arsinh}(e^{t/2})$ is $1/(2\sqrt{1+e^{-t}})<1/2$, those readings enclose $K(n)$ in an interval of width less than

$$
\frac{4^{-J}}{24n\log\epsilon}.
$$

Lean verifies the bound $P\le n<2P$, the classification at $q=35$ and the exact factorial identity. The index bound above follows by the mean value theorem. The replay computes its endpoints using directed interval arithmetic. [Factorial bound and classification in Lean](../../lean/SuperZeta/FactorialPell.lean) · [Stirling reconstruction in Lean](../../lean/SuperZeta/StirlingCorrection.lean#L355)

| $n$ | Squarefree part $q$ | Norm-one generator $\epsilon$ | Enclosure from four readings | Integer candidates |
|---:|---:|---|---|---|
| 7 | 35 | $6+\sqrt{35}$ | $(1.99999061736726,\;2.00000000002494)$ | $2$, confirmed by squaring |
| 8 | 70 | $251+30\sqrt{70}$ | $(0.96411381949754,\;0.96411709110408)$ | None |

## The range of Pell powers at a fixed squarefree part

For each fixed $q$, the largest prime $P\mid q$ bounds the factorial and the fundamental unit $\epsilon$ bounds the number of powers one must test. Together they give

$$
k\log\epsilon\le \operatorname{arsinh}\sqrt{(2P-1)!}.
$$

For $q=70$ the largest prime is again $7$. Its generator $251+30\sqrt{70}$ has first factorial target $251^2-1=63\,000$, strictly between $8!$ and $9!$. Its square has real part $126\,001$ and target $126\,001^2-1>13!$. Every subsequent target is larger since the real part of $\epsilon^k$ equals $\cosh(k\log\epsilon)$. Thus **no power in the $q=70$ sequence lands on a factorial**, including at $8$ and $9$, the two indices with this squarefree part. Once $q$ is specified this is a finite test. Its ceiling varies as $q$ varies. [Exact powers and inequalities](stirling_pell.py)

The interval bound works for any known generator in this convention. An estimate for the size of the fundamental unit as $q$ varies is a separate arithmetic input in a claim about all large solutions. The comparison with Anand uses his supplied abstract. The argument about all powers at $q=70$ has a second verification in Lean by exact checks on the seven remaining factorials. The replay uses Python and python-flint 0.9.0 at 192 bits. Run `python stirling_pell.py` from this directory. [Replay](stirling_pell.py) · [Berndt and Galway on the Brocard–Ramanujan equation](https://experts.illinois.edu/en/publications/on-the-brocard-ramanujan-diophantine-equation-n-1-msup2sup/)
