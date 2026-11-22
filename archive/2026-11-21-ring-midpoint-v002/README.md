# One class reading and the quartic field statement

In the [first midpoint proof](../2026-11-21-ring-midpoint-v001/README.md) I fixed a single input and compared two ideal-class readings with two tower readings. Here I keep that input and ask what a midpoint hit would imply for the quartic field in the [Formal Conjectures definition](https://github.com/google-deepmind/formal-conjectures/blob/bcb1cdc179c8868c3a7ca651f617c433dcd5102e/FormalConjectures/Wikipedia/ArtinPrimitiveRootsConjecture.lean#L57-L64).

The center is $33/64+i(T-1/512)$ and the open radii are $30/2048$ and $31/2048$. The proof takes any real $T$, including $T_D$. At the same $w$ I use $D=Z_0+Z_2$ and $G=Z_0-Z_2$. If either class sum equals $D/2$, subtraction gives that same value for the other one, so $G(w)=0$. Assuming the product $\zeta\,\beta\,G$ continues the quartic's ideal-counting series, the product vanishes at this $w$. Every input in this ring satisfies $1/2<\Re w<1$. The product and $w$ therefore witness the failure of the field's RH statement. To infer a midpoint hit from a zero of any admissible continuation, I also use nonvanishing of $\zeta(w)$ and $\beta(w)$. [Lean proof](../../lean-ideal73/QuarticRingMidpoint.lean) · [Product identification from prime-power counts](../../lean-ideal73/FieldCoefficientTransfer.lean)

The ideal character sorts the ideals into four groups. On the rational side write $S=\zeta L(AB)+L(A)L(B)$, with $A=\chi_{-4}$ and $B=\chi_{26509772707289}$. The arithmetic identity selects the two even groups and gives $Z_0+Z_2=S/2$. Lean checks exactly how far each reading is from $S/4$, as a complex value with its direction:

$$Z_0-S/4=G/2,\qquad Z_2-S/4=-G/2.$$

The Lean theorem takes the even-group identity and the signed identity as inputs. The [arithmetic derivation](../2026-11-21-quartic-projections-v001/fields-and-windows.md) identifies the characters. The [circle calculation](../2026-11-20-gaussian-common-sector-v001/README.md) excludes zeros of the 193 finite sums and their fixed convex combinations in both closed disks. Whether the full quartic class sums reach their midpoint in the open ring is still open.

## Reproduce the formal check

From `lean-ideal73`, run `lake build` with the pinned Lean 4.33.1 and mathlib dependencies. The [field audit](../../lean-ideal73/IdealCount73.lean) checks the five new theorems against the project's three allowed foundational axioms.
