# Recovering an unknown integral lift from two cap derivatives

I start the reciprocal exponential stages at the cap $`z=1`$. I hide the sign of every stage, the number of stages and the integer $`m`$ in the logarithmic lift $`L=m\pi i`$. I measure the first two complex derivatives with respect to the starting value. These measurements determine the ordered rates $`m\sigma_1,\ldots,m\sigma_n`$ for every nonzero integer lift and every nonempty finite word. One independently recorded prime-power coefficient determines which of the two labels for those rates I originally used. This extends the [fixed-lift theorem](../2026-11-20-cap-derivative-recovery-v001/README.md).

## The inverse theorem

**Two derivatives determine the whole map in this family.** For any two integer lifts and any two finite words, equality of the first derivatives at 1 and equality of the second derivatives there are together equivalent to equality of the composed functions at every complex input. This formulation includes the identity and the constant map. It means that measuring the response to a nudge at one cap determines how the composition acts at every other cap. [Lean theorem `cap_derivatives_iff_map`](../../lean/SuperZeta/CapRecovery/HiddenLift.lean)

Apply the letters in chronological order. Write $`W_0(z)=z`$ and $`W_j(z)=\exp(\sigma_j L W_{j-1}(z))`$, where $`\sigma_j\in\{-1,1\}`$. Let $`W=W_n`$. The two one-stage maps agree at the cap exactly when $`e^{2L}=1`$, or equivalently $`L=m\pi i`$ for some integer $`m`$. In this family every nonempty word sends the cap to $`q=(-1)^m`$.

**Theorem.** For two nonempty words $`u,v`$ with nonzero integer lifts $`m,k`$, the measured ratios $`K_m(u)=W''(1)/W'(1)`$ and $`K_k(v)`$ agree exactly in the following two cases.

~~~math
(k,v)=(m,u)\qquad\text{or}\qquad(k,v)=(-m,\bar u).
~~~

Here $`\bar u`$ flips every letter in place, preserving their order. The second labeling gives the identical entire function of the cap, since negating both factors in each rate $`\sigma_j L`$ preserves every stage. The converse says this is the complete list of coincidences, even across different proposed lengths. [Formal classification](../../lean/SuperZeta/CapRecovery/HiddenLift.lean)

### Derivatives at every integer lift

Set $`t=q m\pi i`$, and write $`c_0=1`$, $`c_j=\sigma_1\cdots\sigma_j`$. The chain rule at the cap gives

~~~math
D_j=W_j'(1)=\sigma_j t D_{j-1}=c_jt^j,\qquad
K_j=K_{j-1}+qD_j,\qquad D_0=1,\quad K_0=0 .
~~~

Indeed, for $`g=\exp(\sigma_j L f)`$ the ratio $`g''/g'`$ equals $`f''/f'+\sigma_j L f'`$. At the cap the added term is $`qD_j`$. Each $`D_j`$ is nonzero when $`m\ne0`$, so these are ordinary complex divisions. Summing gives

~~~math
K_m(w)=q\sum_{j=1}^n c_jt^j .
~~~

At the exceptional lift $`m=0`$, every nonempty word is the constant map $`1`$, giving derivative pair $`(0,0)`$ and an undefined ratio. The empty word is the identity at every lift, giving $`(1,0)`$ and ratio zero. The division-free derivative formula covers both controls. [Formal derivatives and integral-lift classification](../../lean/SuperZeta/CapRecovery/Resonant.lean)

### Reading the lift, the length and the signs

Put $`a=|m|\pi`$. A single letter gives a purely imaginary $`K`$ with $`|K|=a`$. With two or more letters, even powers of $`t`$ lie on the real axis and odd powers on the imaginary axis. One component starts with a term of magnitude $`a^n`$, the other with $`a^{n-1}`$. In each component, successive lower powers are smaller by a factor $`a^2`$. After dividing each by its own leading magnitude, its absolute value differs from one by at most $`\eta=1/(a^2-1)`$.

Write $`H=\max(|\Re K|,|\Im K|)`$ and $`J=\min(|\Re K|,|\Im K|)`$. Since $`a\ge\pi>3`$, the leading component is the larger one and $`J>0`$. The quotient obeys

~~~math
a\frac{1-\eta}{1+\eta}\ \le\ \frac HJ\ \le\ a\frac{1+\eta}{1-\eta},
\qquad
\left|\frac HJ-a\right|\le\frac{2a}{a^2-2}<1 .
~~~

Divide $`H/J`$ by $`\pi`$ and round to the nearest integer. This gives $`|m|`$ independently of the number of stages. Having picked its positive representative, locate the length from $`a^n/2<H<a^{n+1}/2`$, which follows from the same tail bounds. In $`qK`$, divide by the highest power $`t^n`$. The leading coefficient is $`c_n=\pm1`$ and the total magnitude of the lower terms is less than $`1/(a-1)<1/2`$. The sign of the real part therefore reads $`c_n`$. Subtract its term and repeat down to $`c_1`$. Finally $`\sigma_j=c_{j-1}c_j`$. This recovers the positive-lift word. A supplied signed lift chooses the corresponding word directly. [Component bounds](../../lean/SuperZeta/CapRecovery/SpectrumRatio.lean) · [Ratio estimate and uniqueness](../../lean/SuperZeta/CapRecovery/HiddenLift.lean)

### An example with both labels hidden

Suppose the cap derivatives give

~~~math
K=4\pi^2+(2\pi-8\pi^3)i .
~~~

The imaginary component is larger. Its magnitude divided by the real component and then by $`\pi`$ is $`2-1/(2\pi^2)=1.9493394\ldots`$. Rounding recovers 2. With $`t=2\pi i`$, the polynomial is $`t-t^2+t^3`$. The recovered prefix signs are $`+,-,+`$, giving the chronological word $`+,-,-`$. The other labels are $`m=-2`$ and the word $`-,+,+`$. Both descriptions apply rates $`2\pi i,-2\pi i,-2\pi i`$ in that order.

## Which arithmetic measurement recovers the original orientation?

In my [prime-power convention](../2026-11-20-cap-derivative-recovery-v001/README.md) I increase the exponent of 2 by one for each minus letter and by two for each plus. Since $`\chi_{-3}(2)=-1`$, its character value at the selected power after stage $`j`$ is exactly $`c_j`$. At detector weight $`b`$ the normalized reading is $`A_j=1+b c_j`$. Flipping every letter multiplies $`c_j`$ by $`(-1)^j`$. Thus any independently retained odd-stage reading differs by exactly $`2|b|`$ between the two candidate labels. Every even-stage reading agrees. At $`b=1/7`$, the example's first stage distinguishes $`8/7`$ from $`6/7`$. At the field weight $`b=1`$, the two readings are 2 and 0.

If both the signed weight and the lift are hidden, an even reading fixes $`b`$ once the two possible words have been recovered, since both give the same even $`c_j`$. The odd reading then distinguishes the two words. The first two readings suffice for every word of length at least two and every nonzero weight. For a single stage and unknown signed weight, simultaneously reversing the word, the lift and the weight preserves the sole reading. The measurements must retain their stage labels and the selected coefficient independently of the derivative decoder. Recomputing both proposed coefficients from $`K`$ supplies both possibilities. [Formal prime-reading identities](../../lean/SuperZeta/CapRecovery/OrientationMark.lean) · [Joint identification theorems](../../lean/SuperZeta/CapRecovery/Coalescence.lean)

The [marked norm-73 calculation](../2026-11-20-gaussian-branch-spectrum-v001/README.md) provides a separate example of an orientation convention. It reads the two prime ideals above 73 in a fixed order, starting with the generator $`3+8i`$, to produce the two words $`-,+`$ and $`+,-`$. The dyadic theorem above specifies exactly how to use a labeled arithmetic observation to resolve the sign ambiguity in the cap derivatives. The [super-zeta determinant and Mellin comparison](../../docs/proofs/quartet-spectrum.md) and the [three Riemann zero counts](../2026-11-20-liu-angular-velocity-v002/README.md) address different observables. The result proved here concerns the identification of ordered stages in the underlying exponential maps.

## Blind test and reproduction

The [protocol](protocol.md) fixes every integer lift from −5 through 5 and every word of length zero through five, giving 693 assignments. Starting from the Taylor series of $`1+h`$, the [generator](blind_trial.py) composes the actual exponentials with directed complex-ball arithmetic at 192 bits. I shuffled the assignments, withheld their labels and compared two decoders. One compared interval enclosures with every possible finite candidate. The other received the ratio and recovered the positive lift, length and word directly, with no candidate list or cutoff in its decoding rule.

| Inputs | What the direct decoder recovered | Number of packets |
| --- | --- | ---: |
| Nonempty word, nonzero lift | Exact positive-lift representative, with its simultaneous-flip partner | 620 |
| Empty word | Identity map, lift unobservable | 11 |
| Nonempty word, zero lift | Constant map, word unobservable | 62 |

The exhaustive comparison gave precisely 310 two-member classes on the 620 regular inputs. Every incompatible finite ratio in this sample had certified separation greater than 3.14. The largest observed displacement from the correct integer before rounding was below 0.236913. All 693 calls, including the two controls, matched the reveal. [Anonymous packets](blind-packets.json) · [Calls](blind-calls.json) · [Reveal](blind-reveal.json) · [Results](blind-results.json)

Run `python -B blind_trial.py verify` in this directory with Python 3.12 and `python-flint==0.9.0` to regenerate the calls, check every enclosed derivative against the revealed exponential composition, and compare with the saved results. From the repository root, `python tools/check_lean.py` builds the Lean 4.19 project and audits its theorem dependencies. The Lean classification covers all nonzero integer lifts and all nonempty finite words. The interval results describe the finite sample above.
