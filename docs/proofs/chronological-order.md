# Lemma. Unique chronological order of the signed stages

I write a word in the order its stages act. At a fixed positive real lift, the value reached from the cap $1$ determines every sign in that order. If I first group the stages into phrases, the same value determines the sequence of letters across all the phrases. It contains no record of where I put the spaces.

## Statement and proof

Let $L>0$ be real, put $E_\pm(x)=\exp(\pm Lx)$, and set $W_{\varnothing}(x)=x$. For a letter $\sigma$ appended on the right, define $W_{u\sigma}=E_\sigma\circ W_u$. If $u$ acts before $v$, then $W_{uv}=W_v\circ W_u$. For finite lists of phrases $P,Q$, let $p,q$ be their respective concatenations. Then

~~~math
W_p(1)=W_q(1)\quad\Longleftrightarrow\quad p=q
\quad\text{letter for letter}.
~~~

**Proof.** Every stage sends a positive input to a positive value. If the input is $y>0$, its two possible outputs satisfy $e^{-Ly}<1<e^{Ly}$. The endpoint $x$ therefore gives the last sign by its position relative to 1, and the preceding value is $|\log x|/L$ in either case. A nonempty word can never land on 1. Starting from an endpoint in the image, I can repeat this operation until I reach 1, then reverse the signs I recovered. Thus equal endpoints give equal chronological words, and identical words give equal endpoints by definition. Phrases with any placement of spaces give the same evaluation whenever their concatenations agree. [Lean proof and inverse](../../lean/SuperZeta/SignWords.lean)

Associativity explains precisely which changes the calculation permits. In the word with letters “plus, plus, minus”, applying the first two stages as a block gives the same result as applying the last two as a block. Both execute the same three letters. Exchanging a plus and a minus changes the chronological word. Already at $L=\log 2$, the two-letter orders $-+$ and $+-$ give $\sqrt{2}$ and $1/4$. More generally, exchanging whole blocks $u,v$ gives the same cap value exactly when the concatenations $uv$ and $vu$ spell the same word. For example, the blocks $+-$ and $+-+-$ can trade places because either concatenation spells $+-+-+-$. [Arithmetic signs above 73 and both exact endpoints](../../lean/SuperZeta/MarkedBranch.lean)

## Six balanced histories and two cyclic orders

In the earlier balanced-history count, all six rows below contribute one history, giving $B_2=\binom42/2^4=3/8$. If I keep the cyclic order but erase the starting phase, four are rotations of the block pattern and two are rotations of the alternating pattern. Restoring the first stage and applying every word to the same cap distinguishes all six. These cyclic classes describe the **order of the signs**. An orbit period counts the stages required for the value itself to return. [Balanced-history construction](../../archive/2026-11-16-super-zeta-v001/research/ordered-signed-histories.md) · [Phase rotation in my reciprocal-tetration preprint](../../archive/2026-11-18-lean-foundations-v001/papers/foundations/main.tex#L404-L445)

| First stage at left | Cyclic order | Exact endpoint from 1 at base 2 | Approximation |
| --- | --- | --- | ---: |
| `++--` | Block | $2^{-1/16}$ | 0.957603 |
| `+--+` | Block | $2^{2^{-1/4}}$ | 1.791163 |
| `--++` | Block | $2^{2^{1/\sqrt2}}$ | 3.100556 |
| `-++-` | Block | $2^{-2^{\sqrt2}}$ | 0.157656 |
| `+-+-` | Alternating | $2^{-2^{1/4}}$ | 0.438544 |
| `-+-+` | Alternating | $2^{2^{-\sqrt2}}$ | 1.297032 |

The first row, for example, runs through $1,2,4,1/16,2^{-1/16}$. Rotating the four-stage word from `++--` to `--++` moves the start forward two places. The resulting endpoint changes even though the cyclic ordering is preserved. Likewise, at norm 73 a scalar measurement adds $+1$ and $-1$ in either order. The angular coefficient supplies their difference once I specify which marked prime comes first. This is the input needed to feed the correct two stages into the lemma. [Local two-reading inverse](../../archive/2026-11-20-gaussian-branch-spectrum-v001/README.md)

## A complex lift where the cap loses every sign

At $L=\pi i$, both stages send 1 to $-1$, and both send $-1$ to $-1$. Consequently **every nonempty finite word**, of any length, has endpoint $-1$ from the cap. I can still recover every sign by measuring how the endpoint changes when I move the starting cap. For this lift, the single complex ratio $W''(1)/W'(1)$ distinguishes every finite word, including its length. Among the six balanced words the first derivatives coincide, so the ordinary second derivative alone suffices. [Common endpoint](../../lean/SuperZeta/SignWords.lean#L189) · [Recovery theorem and hidden-label experiment](../../archive/2026-11-20-cap-derivative-recovery-v001/README.md)
