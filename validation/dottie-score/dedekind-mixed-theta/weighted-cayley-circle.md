# Weighted Cayley readings on the Dottie circle

Take $c=3/4+100000001i$ and $r=31/128$. The orange reading is the normalized completed ordinary zeta

$$
F(w)=\frac{15+8i}{17}\frac{\Gamma_{\mathbb R}(w)\zeta(w)}{|\Gamma_{\mathbb R}(c)|}.
$$

The blue reading is $H(w)=e^{-\alpha(w-c)}F(w)$, where $\alpha=\tfrac12\log(100000001/(2\pi))$. The plotted coordinate is $(z+i)/(z-i)$ for each reading $z$. Ordinary zero is at $-1$ in that coordinate. The unit rim comes from real readings, and the lower half-plane maps inside it.

## Compare the input angles

The plotted crossings pair an orange and a blue input. The approximate orange and blue angles are $(200.77^\circ,166.52^\circ)$ at A and $(236.85^\circ,171.88^\circ)$ at B. If I take both readings at the same point $w$ anywhere in the closed disk, Lean proves

$$
H(w)=F(w)\quad\Longleftrightarrow\quad w=c\ \text{or}\ \zeta(w)=0.
$$

The factor $e^{-\alpha(w-c)}$ equals one only at the center because $0<\alpha r<2\pi$. [Lean same-input theorem](DottieCayleySameInput.lean)

## Cover the boundary

If each of the four rational quarter arcs has $\Im H\le -1/16$ on every closed parameter cell, Lean proves $\zeta(w)\ne0$ on the whole closed disk. The center, radius, weight, and coverage lemma are part of the proof. [Lean arc coverage](DottieRationalContour.lean) · [Lean disk theorem](DottieCayleyWeightedRiemann.lean) · [Build and axioms](weighted-cayley-release-replay.txt)

The external interval replay evaluates $\zeta$ at 96 points on the circle of radius $5/16$. It reconstructs a degree-64 polynomial. The Cauchy bound on the radius-$1/2$ disk gives a uniform zeta error below $5.6\cdot10^{-11}$. The checker verifies $-\Im H>1/16$ on 168 closed intervals that cover all 512 cells of the uniform mesh. The minimum certified lower bound is about $0.0645883$. The arc inequalities are explicit inputs in the Lean theorem. [Interval checker](check-completed-circle.py) · [Interval output](completed-circle-interval-audit.txt) · [Euler summation bound](https://dlmf.nist.gov/25.2.E8)

Run the Lean replay with `-SampledContours` as in the [replay instructions](README.md#replay). Run `uv run --with python-flint==0.9.0 check-completed-circle.py` from this directory to reproduce the external check.
