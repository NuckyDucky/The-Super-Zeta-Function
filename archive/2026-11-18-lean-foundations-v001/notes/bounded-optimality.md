# Exact finite optimality certificate

Let `v=(a,b,c,d,f,g)` and `x=(1,e,e²,-T,-Te,-Te²)`. The ratio error is

`|(a+b e+c e²)/(d+f e+g e²)-T| = |x·v|/|d+f e+g e²|`.

Given a height bound `H`, a known candidate, a positive rational upper bound `E` on that candidate's absolute ratio error, and an integer embedding scale `M`, set

* `Dcap = ceil(H(1+e_upper+e_squared_upper))`;
* `q_i = nearest_integer(M x_i)`;
* `K = ceil(M E Dcap + 3H)`;
* `radius_squared = 6H²+K²`.

If any admissible coefficient vector improves the initial candidate, then

`|x·v| < E Dcap`,

and, because every rounding error has magnitude below one half,

`|q·v| <= M|x·v| + (1/2)sum |v_i| < M E Dcap+3H <= K`.

Consequently the integer lattice vector `(v,q·v)` lies in the specified Euclidean ball. The script constructs the rank-six lattice with rows `(unit_i,q_i)`, reduces that basis, and exhaustively enumerates the lattice ball using exact rational Gram–Schmidt arithmetic. It verifies that the first six columns of the reduced rows form a unimodular matrix and that their last coordinates remain the exact dot products with `q`. Therefore correctness does not require any unverified assumption about the LLL implementation. LLL merely makes the exact enumeration fast.

The final checks keep coefficient vectors inside the box, remove the zero vector, divide out simultaneous gcd, identify simultaneous sign reversal, and discard the zero denominator. All error comparisons use rational interval bounds. Thus the winner is the global minimum throughout the entire original box, rather than only the best LLL row.

## Rigorous constants

For `e`, the lower bound is the factorial series through `1/100!`. Its omitted positive tail is strictly less than `1/(100*100!)`. For `pi`, use Machin's identity `pi=16 atan(1/5)-4 atan(1/239)`, bounding each arctangent by its alternating series partial sum and the first omitted term after 100 terms. Interval arithmetic uses exact `fractions.Fraction` values. Rounding `M*x_i` is accepted only if both certified endpoints give the same nearest integer and both rounding errors are strictly between `-1/2` and `1/2`. Exported decimal interval endpoints round outward.

## Results

* `H=935`, initial error cap `1.239e-19`, `M=10^18`: 3,341 lattice points; the unique primitive winning sign class is `(180,-622,-547,289,-723,-197)` (actual height 723), with absolute error `1.2386338239192639570751972607820153527585987001663407423290141403...e-19`.
* `H=936`, error cap `2.63e-20`, `M=10^19`: `Dcap=10397`, `K=5543`, radius squared `35981425`. Exact enumeration finds 1,515 lattice points including zero; only eight nonzero points survive the coefficient box, giving four primitive sign classes. The unique winner is the user's original vector, up to simultaneous sign reversal. Its error is `2.6231439430444399476624471357955737453844278834972120088725343528...e-20`.
* `H=1204`, using the same original error cap and scale: 6,769 lattice points, six primitive sign classes. Exactly one sign class improves the original: `(594,1036,997,470,-1204,1202)`, error `5.5077723896187391107832875237420498335737476874457033284753950627...e-22`. Its height is exactly 1204. Since enumeration covers every improvement through height 1204, **1204 is the first height at which any improvement becomes possible**. The original is uniquely optimal for every `936 <= H <= 1203`.
* `H=5000`, error cap `1.50e-23`, `M=10^22`: 10,733 lattice points, 18 primitive sign classes. Unique winner up to sign: `(-1004,-4010,4188,-1808,-3699,3059)` (actual height 4188), error `1.4970846687673789712062035087250072707065595853839561062747323685...e-23`.
* `H=10000`, error cap `3.03e-25`, `M=10^24`: 32,143 lattice points, 15 primitive sign classes. Unique winner `(8333,5458,6110,-4878,-7578,8663)` (actual height 8663), error `3.0248352512919431464158515295204873990017026056281525591559279566...e-25`.

The other vectors printed in each certificate are **not necessarily global runners-up**: the ball is guaranteed to contain all improvements of the known candidate, but can omit worse ratios whose residuals lie outside it.

## API

`certify(height=936, candidate=ORIGINAL, error_cap=Fraction(263,10**22), scale=10**19, out_path=None)` returns a JSON-serializable certificate and optionally saves it. The command-line interface supplies matching `--height`, `--candidate` (six integers), `--error-cap`, `--scale`, and `--output` flags. The original-height theorem also explicitly asserts that the winner matches the original primitive sign class.

The scale controls efficiency and does not affect correctness. Scales around `0.08/E` often work well for these bounds. A much larger scale makes the enclosing ball needlessly large; the delivered `H=5000` certificate uses `M=10^22`, reducing an earlier three-million-point enclosure to 10,733 points without changing the theorem.

## Height-counting caution

The six-tuple has five projective shape parameters after simultaneous scaling, but bounded primitive integer vectors grow in number like `H^6`, not `H^5`. Familiar analogy: reduced fractions `a/b` have one projective parameter, while the number with both `|a|,|b|<=H` grows like `H²`. Counting dimension alone does not justify an `H^-5` accuracy heuristic.
