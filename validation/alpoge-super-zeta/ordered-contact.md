# Reading a canceled zero order from the two rooted phases

At the same input $w=2s_0$, let $m$ be the order of ordinary zeta and $n$ the order of a Dirichlet $L$-function. The two logarithmic derivatives, divided by two after pulling them back to the $s$ scale, have residues $m/2$ and $n/2$. The ordinary slope uses my actual corrected channel $(Z-J)/A$, with $A(s)=2\pi^{-2s}(2^{2s}-1)$. If I subtract the two slopes, I see $(m-n)/2$. If $m=n$, the pole cancels. [Original signed-contact proof](SignedContact.lean)

I take the two existing phase origins of my reciprocal pair and start both from $1$. The word in the first phase is `-+`. The word in the second is `+-`. Their readings are

$$
a=e^{L e^{-L}},\qquad b=e^{-L e^L}.
$$

If I weight the ordinary and character slopes by $a,b$ before subtracting, the residue is $R_{ab}=(am-bn)/2$. If I exchange the phase assignments, the residue becomes $R_{ba}=(bm-an)/2$. Therefore

$$
R_{ab}-R_{ba}=\frac{(a-b)(m+n)}2.
$$

The usual signed residue gives the difference of the orders. The swapped comparison gives their sum after dividing by $(a-b)/2$. If both readings vanish with the same order $m$, one weighted residue already gives $m=2R_{ab}/(a-b)$. [The original ordered stages](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/archive/2026-11-19-ordered-signs-v001/README.md#the-order-of-the-signed-exponentials) · [Lean proof](OrderedContact.lean)

## Control on the imaginary-lift section

If $L=iy$ and $0<y<\pi/2$, then $a,b$ have opposite nonzero imaginary parts. Indeed their exponents have imaginary parts $\pm y\cos y$. That makes $a-b$ nonzero throughout this part of the Dottie centerline. For the principal character modulo two, $L(w,\chi_0)=(1-2^{-w})\zeta(w)$. The factor is nonzero in the open strip, so Lean proves equality of the orders at every strip input. It then checks that the ordinary signed residue vanishes and the normalized weighted residue recovers the ordinary order for every such input and imaginary lift. The control requires only the strip and lift inequalities. [Exact modulus-two control](OrderedContact.lean)

The chronological word theorem recovers the whole word from its entire map at fixed nonzero $L$. The oriented Dottie archive also has an example of what two labeled spectral readings remember. The reference at the native angles $\pm\pi/6$ agrees, while the first determinant corrections are $0$ and $8/3$. The next native calculation is to trace these first corrections to the Laurent expansion at the same spectral input $s_0$ and compare their effect with the swap formula above. The present test uses the phase weights explicitly on the two slopes. [Native first corrections](https://github.com/NuckyDucky/The-Super-Zeta-Function/blob/eaa526828cf700a2f43aeeb1c81de4309be5afee/archive/2026-11-19-oriented-return-v001/README.md#the-arithmetic-reference-at-the-two-absolute-angles)
